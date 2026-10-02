import obseq3.sb

/-!
# Byte-addressed memory — foundation layer

The memory of rustc's MIR interpreter, which Miri runs on, is
byte-addressed: an allocation is a byte array, a provenance map (whole
pointers, plus per-byte fragments when a pointer is copied bytewise) and a
per-byte init mask (`rustc_middle/src/mir/interpret/allocation.rs`; see
notes/durable/miri-is-rustcs-mir-interpreter-plus-a-machine.md on the
`conformance-drop-in-place` branch). This module is that memory, in the
form MiniRust (Ralf Jung's executable specification of Rust's operational
semantics) gives it:

- an `AbstractByte` is `uninit`, or a concrete byte that may carry
  provenance: `init b prov`;
- integers are stored little-endian; integer READS strip provenance;
- a pointer is stored as the little-endian bytes of its address, EVERY byte
  carrying the pointer's provenance; a pointer READ keeps the provenance
  only when all its bytes carry the same one (otherwise the result is a
  pointer without provenance), so a bytewise copy of raw bytes preserves a
  pointer, while a copy through integers does not.

Pointers are 8 bytes (x86_64, the target the conformance corpus is built
for). Addresses are bump-allocated, aligned, and never 0.

STATUS (branch `byteaddress`, 2026-10-02): standalone. Nothing in mirlite
or oseair uses it yet; migrating `Mem`/`MemValue` (mirlite) and `Mem`/`Val`
(oseair) onto it is the next stage (see
notes/journal/2026-10/2026-10-02-byte-memory-design.md).

Deviations from the cell model this layer will replace:
- the cell model's pointer carries `extent` (cells it claims) in the
  value; here the extent of a thin pointer is its pointee's size (from the
  type) and a slice's length is fat-pointer METADATA, a second word —
  that change belongs to the layout stage, not to this layer;
- there are no unbounded words: an integer of `n` bytes is a bit pattern
  below `256 ^ n`; signedness is an interpretation of that pattern.
-/

namespace obseq3.bytes

open obseq3

/-! ## Bytes, provenance, pointers -/

/-- What a pointer may access: the allocation `[base, base + size)` and the
    SB tag the borrow tracker checks the access against. (Miri: an
    `AllocId` plus a `BorTag`; the model names the allocation by its range,
    as the cell model does.) -/
structure Prov where
  base : Nat
  size : Nat
  tag : Tag
  /-- TEMPORARY (stage 2): the bytes the pointer claims from its address —
      the cell model's `extent`, which a slice uses as its length. Miri
      keeps a slice's length as fat-pointer METADATA (a second word), not
      in provenance; this field goes when fat pointers become two words. -/
  extent : Nat := 0
deriving Repr, BEq, DecidableEq, Inhabited

/-- One byte of memory (MiniRust `AbstractByte`). -/
inductive AbstractByte where
  | uninit
  | init (b : Fin 256) (prov : Option Prov)
deriving Repr, BEq, DecidableEq, Inhabited

/-- A thin pointer: an address and maybe a provenance. A pointer without
    provenance (from an integer, or a partial copy) can be compared and
    printed but never dereferenced (beyond zero-sized accesses). -/
structure Pointer where
  addr : Nat
  prov : Option Prov
deriving Repr, BEq, DecidableEq, Inhabited

/-- Bytes in a pointer (x86_64). -/
def ptrSize : Nat := 8

/-- The byte value, if initialized. -/
def AbstractByte.byte? : AbstractByte → Option (Fin 256)
  | .uninit => none
  | .init b _ => some b

/-- The provenance slot, if initialized (`some none`: a byte without
    provenance). -/
def AbstractByte.prov? : AbstractByte → Option (Option Prov)
  | .uninit => none
  | .init _ p => some p

/-! ## Little-endian encoding -/

/-- The `n` low bytes of `v`, least significant first. -/
def encodeLE : Nat → Nat → List (Fin 256)
  | 0, _ => []
  | n + 1, v => ⟨v % 256, Nat.mod_lt _ (by decide)⟩ :: encodeLE n (v / 256)

def decodeLE : List (Fin 256) → Nat
  | [] => 0
  | b :: bs => b.val + 256 * decodeLE bs

@[simp] theorem encodeLE_length (n v : Nat) : (encodeLE n v).length = n := by
  induction n generalizing v <;> simp_all [encodeLE]

theorem decodeLE_encodeLE (n v : Nat) : decodeLE (encodeLE n v) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [encodeLE, decodeLE, Nat.mod_one]
  | succ n ih => simp [encodeLE, decodeLE, ih, Nat.pow_succ', Nat.mod_mul]

theorem decodeLE_encodeLE_of_lt {n v : Nat} (h : v < 256 ^ n) :
    decodeLE (encodeLE n v) = v := by
  rw [decodeLE_encodeLE, Nat.mod_eq_of_lt h]

/-- Bytes all carrying the same provenance slot `p`. -/
def tagBytes (p : Option Prov) (l : List (Fin 256)) : List AbstractByte :=
  l.map (AbstractByte.init · p)

@[simp] theorem tagBytes_length (p : Option Prov) (l : List (Fin 256)) :
    (tagBytes p l).length = l.length := by simp [tagBytes]

theorem tagBytes_bytes (p : Option Prov) (l : List (Fin 256)) :
    (tagBytes p l).mapM AbstractByte.byte? = some l := by
  induction l <;> simp_all [tagBytes, AbstractByte.byte?]

theorem tagBytes_provs (p : Option Prov) (l : List (Fin 256)) :
    (tagBytes p l).mapM AbstractByte.prov? = some (l.map fun _ => p) := by
  induction l <;> simp_all [tagBytes, AbstractByte.prov?]

/-! ## Scalars: integers and pointers -/

/-- An `n`-byte integer's bytes: no provenance. -/
def encodeInt (n v : Nat) : List AbstractByte := tagBytes none (encodeLE n v)

/-- An integer read: every byte initialized; provenance is STRIPPED
    (MiniRust; Miri in its default mode). Reading part of a pointer as an
    integer is therefore defined and yields address bytes. -/
def decodeInt (bs : List AbstractByte) : Option Nat :=
  (bs.mapM AbstractByte.byte?).map decodeLE

def encodePtr (p : Pointer) : List AbstractByte := tagBytes p.prov (encodeLE ptrSize p.addr)

/-- The provenance a pointer read recovers: the common provenance of all
    its bytes, or none when they disagree. -/
def commonProv : List (Option Prov) → Option Prov
  | [] => none
  | p :: ps => if ps.all (fun x => decide (x = p)) then p else none

/-- A pointer read: `ptrSize` initialized bytes; the address is their
    little-endian value; the provenance survives only if every byte
    carries the same one. -/
def decodePtr (bs : List AbstractByte) : Option Pointer :=
  if bs.length = ptrSize then do
    let raw ← bs.mapM AbstractByte.byte?
    let provs ← bs.mapM AbstractByte.prov?
    pure ⟨decodeLE raw, commonProv provs⟩
  else none

theorem decodeInt_encodeInt {n v : Nat} (h : v < 256 ^ n) :
    decodeInt (encodeInt n v) = some v := by
  simp [decodeInt, encodeInt, tagBytes_bytes, decodeLE_encodeLE_of_lt h]

theorem commonProv_replicate (q : Option Prov) (l : List α) (h : l ≠ []) :
    commonProv (l.map fun _ => q) = q := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp [commonProv]

theorem decodePtr_encodePtr {p : Pointer} (h : p.addr < 256 ^ ptrSize) :
    decodePtr (encodePtr p) = some p := by
  have hne : encodeLE ptrSize p.addr ≠ [] := by simp [ptrSize, encodeLE]
  simp [decodePtr, encodePtr, tagBytes_bytes, tagBytes_provs,
    decodeLE_encodeLE_of_lt h, commonProv_replicate _ _ hne]

/-- A pointer's bytes read as an integer: its address, provenance gone. -/
theorem decodeInt_encodePtr {p : Pointer} (h : p.addr < 256 ^ ptrSize) :
    decodeInt (encodePtr p) = some p.addr := by
  simp [decodeInt, encodePtr, tagBytes_bytes, decodeLE_encodeLE_of_lt h]

/-- An integer's bytes read as a pointer: that address, no provenance. -/
theorem decodePtr_encodeInt {v : Nat} (h : v < 256 ^ ptrSize) :
    decodePtr (encodeInt ptrSize v) = some ⟨v, none⟩ := by
  have hne : encodeLE ptrSize v ≠ [] := by simp [ptrSize, encodeLE]
  simp [decodePtr, encodeInt, tagBytes_bytes, tagBytes_provs,
    decodeLE_encodeLE_of_lt h, commonProv_replicate _ _ hne]

/-- Scalar types the memory reads and writes. -/
inductive Scalar where
  | int (size : Nat)
  | ptr
deriving Repr, BEq, DecidableEq, Inhabited

def Scalar.size : Scalar → Nat
  | .int n => n
  | .ptr => ptrSize

inductive SVal where
  | int (v : Nat)
  | ptr (p : Pointer)
deriving Repr, BEq, DecidableEq, Inhabited

/-- Encode a scalar value at a scalar type; `none` for a type mismatch or
    an integer / address that does not fit. -/
def encodeS : Scalar → SVal → Option (List AbstractByte)
  | .int n, .int v => if v < 256 ^ n then some (encodeInt n v) else none
  | .ptr, .ptr p => if p.addr < 256 ^ ptrSize then some (encodePtr p) else none
  | _, _ => none

def decodeS : Scalar → List AbstractByte → Option SVal
  | .int n, bs => if bs.length = n then (decodeInt bs).map .int else none
  | .ptr, bs => (decodePtr bs).map .ptr

theorem encodeS_length {t : Scalar} {v : SVal} {bs : List AbstractByte}
    (h : encodeS t v = some bs) : bs.length = t.size := by
  cases t <;> cases v <;> simp [encodeS] at h <;>
    (obtain ⟨-, rfl⟩ := h; simp [encodeInt, encodePtr, Scalar.size])

theorem decodeS_encodeS {t : Scalar} {v : SVal} {bs : List AbstractByte}
    (h : encodeS t v = some bs) : decodeS t bs = some v := by
  cases t <;> cases v <;> simp [encodeS] at h <;> obtain ⟨hlt, rfl⟩ := h
  · rw [decodeS, if_pos (by simp [encodeInt]), decodeInt_encodeInt hlt]; rfl
  · simp [decodeS, decodePtr_encodePtr hlt]

/-! ## Memory -/

/-- Byte-addressed memory. `bytes` is total: a byte never written is
    `uninit`. `allocs` lists live `(base, size)` ranges; `next` is the bump
    pointer. -/
structure Mem where
  bytes : Nat → AbstractByte := fun _ => .uninit
  allocs : List (Nat × Nat) := []
  next : Nat := 1

def Mem.read (m : Mem) (a n : Nat) : List AbstractByte :=
  (List.range n).map fun i => m.bytes (a + i)

def Mem.write (m : Mem) (a : Nat) (bs : List AbstractByte) : Mem :=
  { m with bytes := fun x =>
      if a ≤ x ∧ x < a + bs.length then bs.getD (x - a) .uninit else m.bytes x }

@[simp] theorem Mem.read_length (m : Mem) (a n : Nat) : (m.read a n).length = n := by
  simp [Mem.read]

theorem Mem.read_write_same (m : Mem) (a : Nat) (bs : List AbstractByte) :
    (m.write a bs).read a bs.length = bs := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [Mem.read, Mem.write]
  grind

theorem Mem.read_write_disjoint (m : Mem) (a a' n : Nat) (bs : List AbstractByte)
    (h : a' + n ≤ a ∨ a + bs.length ≤ a') :
    (m.write a bs).read a' n = m.read a' n := by
  simp only [Mem.read, Mem.write]
  apply List.map_congr_left
  intro i hi
  simp at hi
  grind

/-- Round `a` up to a multiple of `k` (`k = 0` leaves it). -/
def alignUp (a k : Nat) : Nat := if k = 0 then a else (a + k - 1) / k * k

theorem le_alignUp (a k : Nat) : a ≤ alignUp a k := by
  unfold alignUp
  split
  · exact Nat.le_refl a
  · have hk : 0 < k := Nat.pos_of_ne_zero ‹_›
    have := Nat.div_add_mod' (a + k - 1) k
    have := Nat.mod_lt (a + k - 1) hk
    omega

theorem alignUp_dvd {a k : Nat} (hk : 0 < k) : k ∣ alignUp a k := by
  unfold alignUp
  rw [if_neg (Nat.pos_iff_ne_zero.mp hk)]
  exact Nat.dvd_mul_left k _

/-- Allocate `size` bytes aligned to `align`: a fresh range above every
    live one, never at address 0. Zero-sized allocations still advance the
    bump pointer, so distinct allocations have distinct base addresses. -/
def Mem.allocate (m : Mem) (size align : Nat) : Nat × Mem :=
  let base := alignUp m.next align
  (base, { m with allocs := (base, size) :: m.allocs, next := base + max size 1 })

/-- Every live allocation ends at or below the bump pointer, which is
    positive. -/
def Mem.WF (m : Mem) : Prop :=
  0 < m.next ∧ ∀ b s, (b, s) ∈ m.allocs → b + s ≤ m.next

theorem Mem.allocate_wf {m : Mem} (hwf : m.WF) (size align : Nat) :
    (m.allocate size align).2.WF := by
  obtain ⟨hpos, hall⟩ := hwf
  have hle := le_alignUp m.next align
  refine ⟨by simp [Mem.allocate]; omega, ?_⟩
  intro b s hmem
  simp [Mem.allocate] at hmem ⊢
  rcases hmem with ⟨rfl, rfl⟩ | hmem
  · omega
  · have := hall b s hmem; omega

/-- The new range is disjoint from every live one, and not at 0. -/
theorem Mem.allocate_fresh {m : Mem} (hwf : m.WF) (size align : Nat) :
    0 < (m.allocate size align).1 ∧
    ∀ b s, (b, s) ∈ m.allocs → b + s ≤ (m.allocate size align).1 := by
  obtain ⟨hpos, hall⟩ := hwf
  have hle := le_alignUp m.next align
  refine ⟨by simp [Mem.allocate]; omega, ?_⟩
  intro b s hmem
  have := hall b s hmem
  simp [Mem.allocate]; omega

/-- The live allocation containing address `a`, if any. -/
def Mem.allocOf (m : Mem) (a : Nat) : Option (Nat × Nat) :=
  m.allocs.find? fun (b, s) => decide (b ≤ a) && decide (a < b + s)

/-! ## Typed scalar access -/

def Mem.load (m : Mem) (a : Nat) (t : Scalar) : Option SVal :=
  decodeS t (m.read a t.size)

def Mem.store (m : Mem) (a : Nat) (t : Scalar) (v : SVal) : Option Mem :=
  (encodeS t v).map (m.write a)

theorem Mem.load_store_same {m m' : Mem} {a : Nat} {t : Scalar} {v : SVal}
    (h : m.store a t v = some m') : m'.load a t = some v := by
  simp only [Mem.store, Option.map_eq_some_iff] at h
  obtain ⟨bs, henc, rfl⟩ := h
  simp only [Mem.load, ← encodeS_length henc, Mem.read_write_same, decodeS_encodeS henc]

theorem Mem.load_store_disjoint {m m' : Mem} {a a' : Nat} {t t' : Scalar} {v : SVal}
    (h : m.store a t v = some m')
    (hd : a' + t'.size ≤ a ∨ a + t.size ≤ a') :
    m'.load a' t' = m.load a' t' := by
  simp only [Mem.store, Option.map_eq_some_iff] at h
  obtain ⟨bs, henc, rfl⟩ := h
  have hlen := encodeS_length henc
  simp only [Mem.load]
  rw [Mem.read_write_disjoint _ _ _ _ _ (by omega)]

/-- Copy `n` raw bytes (a `MaybeUninit<u8>`-typed bytewise copy, or
    `ptr::copy_nonoverlapping`): provenance travels with the bytes. -/
def Mem.copyBytes (m : Mem) (dst src n : Nat) : Mem :=
  m.write dst (m.read src n)

end obseq3.bytes
