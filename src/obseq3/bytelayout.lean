import obseq3.bytemem
import obseq3.types

/-!
# Byte layouts — stage 1 of byte-addressed memory

A layout says where each scalar of a value lives, in bytes: integers of a
given width, 8-byte pointers, and tuples whose fields sit at explicit
offsets inside a block of explicit size and alignment. Explicit offsets
let the loader take Rust's own layout for user types (Charon's
`field_offsets`; rustc reorders `repr(Rust)` fields); `reprC` computes the
C layout (fields in order, each aligned) for tuples the model builds
itself.

A value is handled through its LEAVES — the `(offset, scalar)` pairs of
its integers and pointers — which is the flat shape the semantics already
works with (`List MemValue`). `ofLayoutTy` is the uniform layout of a
layout type (every integer a `usize`-sized leaf, tuples in C layout).
-/

namespace obseq3.bytes

/-- A byte layout. `int n` is an `n`-byte integer (bool = 1, char = 4,
    u128 = 16; signedness is an interpretation of the bits); `ptr` a thin
    pointer (its pointee gives the extent and the scaling of pointer
    arithmetic); `tup fs os size align` fields `fs` at offsets `os`. -/
inductive BLayout where
  | int (size : Nat) -- size in bytes
  | ptr (pointee : BLayout)
  | tup (fields : List BLayout) (offsets : List Nat) (size align : Nat)
deriving Repr, Inhabited, BEq

def BLayout.size : BLayout → Nat
  | .int n => n
  | .ptr _ => ptrSize
  | .tup _ _ s _ => s

/-- Alignment (x86_64: an integer is aligned to its size, u128 included
    since Rust 1.77). -/
def BLayout.align : BLayout → Nat
  | .int n => n
  | .ptr _ => ptrSize
  | .tup _ _ _ a => a

mutual
/-- The scalars of a layout and their offsets, in field order. -/
def BLayout.leaves : BLayout → List (Nat × Scalar)
  | .int n => [(0, .int n)]
  | .ptr _ => [(0, .ptr)]
  | .tup fs os _ _ => BLayout.leavesFields fs os

def BLayout.leavesFields : List BLayout → List Nat → List (Nat × Scalar)
  | f :: fs, o :: os => (f.leaves.map fun p => (o + p.1, p.2)) ++ BLayout.leavesFields fs os
  | _, _ => []
end

/-! ## The C layout -/

/-- Place fields in order from offset `cur`, each at the next multiple of
    its alignment. Returns the offsets and the end. -/
def placeFields (cur : Nat) : List BLayout → List Nat × Nat
  | [] => ([], cur)
  | f :: fs =>
      let o := alignUp cur f.align
      let r := placeFields (o + f.size) fs
      (o :: r.1, r.2)

/-- The largest field alignment (1 for no fields). -/
def fieldsAlign (fs : List BLayout) : Nat := fs.foldr (fun f a => max f.align a) 1

/-- `repr(C)`: fields in order, each aligned, size rounded up to the
    alignment (trailing padding). -/
def reprC (fs : List BLayout) : BLayout :=
  let r := placeFields 0 fs
  .tup fs r.1 (alignUp r.2 (fieldsAlign fs)) (fieldsAlign fs)

@[simp] theorem placeFields_length (cur : Nat) (fs : List BLayout) :
    (placeFields cur fs).1.length = fs.length := by
  induction fs generalizing cur <;> simp_all [placeFields]

/-! ## Leaves are separated and in bounds -/

/-- Leaf `p` ends at or before leaf `q` starts. -/
def LeafSep (p q : Nat × Scalar) : Prop := p.1 + p.2.size ≤ q.1

/-- A leaf list whose leaves do not overlap, come in address order, and fit
    in `sz` bytes.
    This is true of scalars, pointers, and well formed tuples.
-/
def Good (ls : List (Nat × Scalar)) (sz : Nat) : Prop :=
  ls.Pairwise LeafSep ∧ ∀ p ∈ ls, p.1 + p.2.size ≤ sz

/-- `Good` is preserved under increasing the size. -/
theorem Good.mono {ls : List (Nat × Scalar)} {sz sz' : Nat}
    (h : Good ls sz) (hle : sz ≤ sz') : Good ls sz' :=
  ⟨h.1, fun p hp => Nat.le_trans (h.2 p hp) hle⟩

/-- `Good` is preserved under shifting all leaves by an offset. -/
theorem Good.shift {ls : List (Nat × Scalar)} {sz : Nat} (h : Good ls sz) (o : Nat) :
    Good (ls.map fun p => (o + p.1, p.2)) (o + sz) := by
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_map]
    exact h.1.imp fun hpq => by unfold LeafSep at *; simp only at *; omega
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have := h.2 q hq
    simp only; omega

theorem placeFields_good (cur : Nat) (fs : List BLayout)
    (hfs : ∀ f ∈ fs, Good f.leaves f.size) :
    Good (BLayout.leavesFields fs (placeFields cur fs).1) (placeFields cur fs).2 ∧
    (∀ p ∈ BLayout.leavesFields fs (placeFields cur fs).1, cur ≤ p.1) ∧
    cur ≤ (placeFields cur fs).2 := by
  induction fs generalizing cur with
  | nil => simp [placeFields, BLayout.leavesFields, Good]
  | cons f fs ih =>
    have hf := hfs f (by simp)
    have hrest := ih (alignUp cur f.align + f.size) (fun g hg => hfs g (by simp [hg]))
    obtain ⟨⟨hpw, hin⟩, hlow, hend⟩ := hrest
    have hsh := hf.shift (alignUp cur f.align)
    have hcur := le_alignUp cur f.align
    simp only [placeFields, BLayout.leavesFields]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨hsh.1, hpw, ?_⟩
      intro a ha b hb
      have := hsh.2 a ha
      have := hlow b hb
      unfold LeafSep; omega
    · intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · have := hsh.2 p hp; omega
      · exact hin p hp
    · intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · rw [List.mem_map] at hp
        obtain ⟨q, -, rfl⟩ := hp
        simp only; omega
      · have := hlow p hp; omega
    · omega

theorem reprC_good (fs : List BLayout) (hfs : ∀ f ∈ fs, Good f.leaves f.size) :
    Good (reprC fs).leaves (reprC fs).size := by
  have := (placeFields_good 0 fs hfs).1
  exact this.mono (le_alignUp _ _)

/-! ## From the cell layouts -/

mutual
/-- The uniform byte layout of a layout type: every integer 8 bytes
    whatever its width (the uniform layout), a pointer a thin
    pointer, a tuple the C layout of its fields. The loader's layouts give
    integers their real width instead (`Agrees` checks it). -/
def ofLayoutTy : LayoutTy → BLayout
  | .IntL _ => .int ptrSize
  | .PtrL τ => .ptr (ofLayoutTy τ)
  | .TupL ts => reprC (ofLayoutTyList ts)

def ofLayoutTyList : List LayoutTy → List BLayout
  | [] => []
  | t :: ts => ofLayoutTy t :: ofLayoutTyList ts
end

mutual
theorem ofLayoutTy_good : (τ : LayoutTy) →
    Good (ofLayoutTy τ).leaves (ofLayoutTy τ).size
  | .IntL _ => by
      simp [ofLayoutTy, BLayout.leaves, BLayout.size, Good, Scalar.size]
  | .PtrL _ => by
      simp [ofLayoutTy, BLayout.leaves, BLayout.size, Good, Scalar.size]
  | .TupL ts => by
      rw [ofLayoutTy]
      exact reprC_good _ (ofLayoutTyList_good ts)

theorem ofLayoutTyList_good : (ts : List LayoutTy) →
    ∀ f ∈ ofLayoutTyList ts, Good f.leaves f.size
  | [] => by simp [ofLayoutTyList]
  | t :: ts => by
      intro f hf
      rw [ofLayoutTyList, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact ofLayoutTy_good t
      · exact ofLayoutTyList_good ts f hf
end

/-! ## Whole values, leaf by leaf -/

/-- Read every leaf of a value at base address `a`. -/
def Mem.loadLeaves (m : Mem) (a : Nat) (ls : List (Nat × Scalar)) : Option (List SVal) :=
  ls.mapM fun p => m.load (a + p.1) p.2

/-- Write the values `vs` to the leaves `ls` at base `a`, in order. -/
def Mem.storeLeaves (m : Mem) (a : Nat) : List (Nat × Scalar) → List SVal → Option Mem
  | [], [] => some m
  | p :: ps, v :: vs => do
      let m' ← m.store (a + p.1) p.2 v
      m'.storeLeaves a ps vs
  | _, _ => none

def Mem.loadL (m : Mem) (a : Nat) (L : BLayout) : Option (List SVal) :=
  m.loadLeaves a L.leaves

def Mem.storeL (m : Mem) (a : Nat) (L : BLayout) (vs : List SVal) : Option Mem :=
  m.storeLeaves a L.leaves vs

/-- Storing leaves leaves alone any scalar disjoint from all of them. -/
theorem Mem.storeLeaves_frame {m m' : Mem} {a : Nat} {ls : List (Nat × Scalar)}
    {vs : List SVal} {x : Nat} {t : Scalar}
    (h : m.storeLeaves a ls vs = some m')
    (hd : ∀ p ∈ ls, x + t.size ≤ a + p.1 ∨ a + p.1 + p.2.size ≤ x) :
    m'.load x t = m.load x t := by
  induction ls generalizing m vs with
  | nil => cases vs <;> simp [Mem.storeLeaves] at h; subst h; rfl
  | cons p ps ih =>
    cases vs with
    | nil => simp [Mem.storeLeaves] at h
    | cons v vs =>
      simp only [Mem.storeLeaves, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨m1, h1, h2⟩ := h
      rw [ih h2 (fun q hq => hd q (by simp [hq])),
        Mem.load_store_disjoint h1 (hd p (by simp))]

/-- What is stored is what is loaded back, leaf by leaf, as long as the
    leaves do not overlap (`Good`). -/
theorem Mem.loadLeaves_storeLeaves {m m' : Mem} {a : Nat} {ls : List (Nat × Scalar)}
    {vs : List SVal} (hsep : ls.Pairwise LeafSep)
    (h : m.storeLeaves a ls vs = some m') : m'.loadLeaves a ls = some vs := by
  induction ls generalizing m vs with
  | nil => cases vs <;> simp [Mem.storeLeaves, Mem.loadLeaves] at h ⊢
  | cons p ps ih =>
    cases vs with
    | nil => simp [Mem.storeLeaves] at h
    | cons v vs =>
      simp only [Mem.storeLeaves, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨m1, h1, h2⟩ := h
      rw [List.pairwise_cons] at hsep
      have hhead : m'.load (a + p.1) p.2 = some v := by
        rw [Mem.storeLeaves_frame h2 (fun q hq => Or.inl (by
          have := hsep.1 q hq; unfold LeafSep at this; omega))]
        exact Mem.load_store_same h1
      have hrest := ih hsep.2 h2
      simp only [Mem.loadLeaves, List.mapM_cons] at hrest ⊢
      rw [hhead, hrest]; rfl

theorem Mem.loadL_storeL {m m' : Mem} {a : Nat} {L : BLayout} {vs : List SVal}
    (hL : Good L.leaves L.size) (h : m.storeL a L vs = some m') :
    m'.loadL a L = some vs :=
  Mem.loadLeaves_storeLeaves hL.1 h

end obseq3.bytes
