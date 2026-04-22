import obseq.proof.state_helpers

/-!
# `obseq.proof.struct_init_common`

Shared definitions and helper lemmas for the tuple-construction fragment proved
through `StructInitOp`.

This pass only proves the constant-field tuple fragment:

- `StructInitOp [ConstOp n1, ..., ConstOp nk]`

That is enough to realign the development with the paper grammar:

- `ConstOp` is word-only again, and
- tuples are built through `StructInitOp`.
-/

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

variable {A_o : oseair.AllocatorSpec}

def wordStructFields (fields : List Word) : List mirlite.RExpr :=
  fields.map mirlite.RExpr.ConstOp

def wordStructRhs (fields : List Word) : mirlite.RExpr :=
  mirlite.RExpr.StructInitOp (wordStructFields fields)

def wordStructLayout (fields : List Word) : LayoutTy :=
  LayoutTy.TupL (List.replicate fields.length LayoutTy.NatL)

def wordStructTy (fields : List Word) : TyVal :=
  TyVal.TupTy (List.replicate fields.length TyVal.NatTy)

def wordStructMirVals (fields : List Word) : List mirlite.MemValue :=
  fields.map mirlite.MemValue.Val

def wordStructOseaVals (fields : List Word) : List oseair.Val :=
  fields.map oseair.Val.Dat

theorem layoutToTyValList_replicate_natl (n : Nat) :
  layoutToTyValList (List.replicate n LayoutTy.NatL) = List.replicate n TyVal.NatTy := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [List.replicate, layoutToTyVal, layoutToTyValList, ih]

theorem typeSizeList_replicate_natty (n : Nat) :
  typeSizeList (List.replicate n TyVal.NatTy) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [List.replicate, typeSizeList, typeSize, ih, Nat.add_comm]

@[simp] theorem layoutToTyVal_wordStructLayout (fields : List Word) :
  layoutToTyVal (wordStructLayout fields) = wordStructTy fields := by
  simp [wordStructLayout, wordStructTy, layoutToTyVal, layoutToTyValList, layoutToTyValList_replicate_natl]

@[simp] theorem blockSize_wordStructLayout (fields : List Word) :
  blockSize (wordStructLayout fields) = fields.length := by
  simp [blockSize, layoutToTyVal_wordStructLayout, wordStructTy, typeSize, typeSizeList_replicate_natty]

@[simp] theorem wordStructMirVals_length (fields : List Word) :
  (wordStructMirVals fields).length = blockSize (wordStructLayout fields) := by
  rw [blockSize_wordStructLayout]
  simp [wordStructMirVals]

@[simp] theorem wordStructOseaVals_length (fields : List Word) :
  (wordStructOseaVals fields).length = blockSize (wordStructLayout fields) := by
  rw [blockSize_wordStructLayout]
  simp [wordStructOseaVals]

theorem mem_vals_eq_words
  {ptr_sim : PtrSimPred}
  (fields : List Word) :
  mem_vals_eq ptr_sim (wordStructMirVals fields) (wordStructOseaVals fields) := by
  induction fields with
  | nil =>
      exact mem_vals_eq.nil
  | cons n ns ih =>
      exact mem_vals_eq.cons rfl ih

@[simp] theorem mirlite_structConstWords_wordStructFields
  (fields : List Word) :
  mirlite.structConstWords? (wordStructFields fields) = some fields := by
  induction fields with
  | nil =>
      rfl
  | cons n ns ih =>
      simpa [wordStructFields, mirlite.structConstWords?] using ih

@[simp] theorem compile_structConstWords_wordStructFields
  (fields : List Word) :
  compile.structConstWords? (wordStructFields fields) = some fields := by
  induction fields with
  | nil =>
      rfl
  | cons n ns ih =>
      simpa [wordStructFields, compile.structConstWords?] using ih

theorem wordStruct_nonempty_size
  {fields : List Word}
  (h_fields : fields ≠ []) :
  0 < blockSize (wordStructLayout fields) := by
  cases fields with
  | nil =>
      contradiction
  | cons head tail =>
      have h_size :
          blockSize (wordStructLayout (head :: tail)) = Nat.succ tail.length := by
        rw [show blockSize (wordStructLayout (head :: tail)) =
              typeSize (wordStructTy (head :: tail)) by
              simp [blockSize, layoutToTyVal_wordStructLayout]]
        simp [wordStructTy, typeSize, typeSizeList, List.replicate, typeSizeList_replicate_natty, Nat.add_comm]
      rw [h_size]
      exact Nat.succ_pos _

theorem osea_step_cstore_ok
  (s_osea : oseair.State)
  (layout : LayoutTy)
  (vals : List oseair.Val)
  (addr tag : Word)
  (reg : Register)
  (ap' : AccessPerms)
  (h_size : 0 < blockSize layout)
  (h_reg :
    s_osea.reg.lookup reg =
      some (TyVal.PTy, [oseair.Val.Ptr addr 0 (blockSize layout) tag]))
  (h_use : sb_use_mb s_osea.ap addr tag = SBResult.Ok ap') :
  oseair.step { s_osea with pc := 0 }
    [oseair.Instr.CStore (layoutToTyVal layout) vals reg] =
    oseair.Result.Ok
      { s_osea with
        ap := ap',
        mem := oseair.writeWordSeq s_osea.mem addr vals,
        pc := 1 } := by
  have h_pc : 0 < [oseair.Instr.CStore (layoutToTyVal layout) vals reg].length := Nat.succ_pos 0
  have h_get : [oseair.Instr.CStore (layoutToTyVal layout) vals reg].get ⟨0, h_pc⟩ =
      oseair.Instr.CStore (layoutToTyVal layout) vals reg := rfl
  have h_off : addr + 0 < addr + blockSize layout := Nat.add_lt_add_left h_size addr
  exact step_CStore { s_osea with pc := 0 } _ (layoutToTyVal layout) vals reg
    addr 0 (blockSize layout) tag ap' h_pc h_get h_reg h_off h_use

theorem osea_run_cstore_embedded_ok
  (s_osea : oseair.State)
  (prog : oseair.Prog)
  (layout : LayoutTy)
  (vals : List oseair.Val)
  (addr tag : Word)
  (reg : Register)
  (ap' : AccessPerms)
  (h_start : StartsAt prog s_osea.pc [oseair.Instr.CStore (layoutToTyVal layout) vals reg])
  (h_size : 0 < blockSize layout)
  (h_reg :
    s_osea.reg.lookup reg =
      some (TyVal.PTy, [oseair.Val.Ptr addr 0 (blockSize layout) tag]))
  (h_use : sb_use_mb s_osea.ap addr tag = SBResult.Ok ap') :
  oseair.runNWith A_o 1 s_osea prog =
    oseair.Result.Ok
      { s_osea with
        ap := ap',
        mem := oseair.writeWordSeq s_osea.mem addr vals,
        pc := s_osea.pc + 1 } := by
  simpa [Nat.zero_add] using
    osea_run_ptr_cstore_embedded_ok
      s_osea prog layout vals
      addr 0 (blockSize layout) tag reg ap'
      h_start h_reg h_size
      (by simpa [Nat.zero_add] using h_use)

theorem osea_steps_alloc_cstore_ok
  (s_osea : oseair.State)
  (layout : LayoutTy)
  (vals : List oseair.Val)
  (reg : Register)
  (allocBase : Word)
  (allocMem : oseair.Mem)
  (tag : Word)
  (ap2 ap3 : AccessPerms)
  (h_size : 0 < blockSize layout)
  (h_alloc_pair : A_o.alloc s_osea.mem (blockSize layout) = (allocBase, allocMem))
  (h_own : sb_own s_osea.ap allocBase = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 allocBase tag = SBResult.Ok ap3) :
  StepStarWith A_o
    { s_osea with pc := 0 }
    [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)),
     oseair.Instr.CStore (layoutToTyVal layout) vals reg]
    { s_osea with
      reg := s_osea.reg.insert reg
        (TyVal.PTy, [oseair.Val.Ptr allocBase 0 (blockSize layout) tag]),
      mem := oseair.writeWordSeq allocMem allocBase vals,
      ap := ap3,
      pc := 2 } := by
  let s1 : oseair.State :=
    { s_osea with
      reg := s_osea.reg.insert reg
        (TyVal.PTy, [oseair.Val.Ptr allocBase 0 (blockSize layout) tag]),
      mem := allocMem,
      ap := ap2,
      pc := 1 }
  have h_pc0 : 0 < [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)),
      oseair.Instr.CStore (layoutToTyVal layout) vals reg].length := Nat.succ_pos 1
  have h_get0 : [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)),
      oseair.Instr.CStore (layoutToTyVal layout) vals reg].get ⟨0, h_pc0⟩ =
      oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)) := rfl
  have h_step1 := step_Assgn_AllocWith A_o { s_osea with pc := 0 } _ reg (layoutToTyVal layout)
    allocBase allocMem ap2 tag (blockSize layout) h_pc0 h_get0 rfl h_alloc_pair h_own
  have h_reg : s1.reg.lookup reg =
      some (TyVal.PTy, [oseair.Val.Ptr allocBase 0 (blockSize layout) tag]) := by simp [s1]
  have h_pc1 : (1 : Nat) < [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)),
      oseair.Instr.CStore (layoutToTyVal layout) vals reg].length := Nat.succ_lt_succ (Nat.succ_pos 0)
  have h_get1 : [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)),
      oseair.Instr.CStore (layoutToTyVal layout) vals reg].get ⟨1, h_pc1⟩ =
      oseair.Instr.CStore (layoutToTyVal layout) vals reg := rfl
  have h_off : allocBase + 0 < allocBase + blockSize layout :=
    Nat.add_lt_add_left h_size allocBase
  have h_step2 := step_CStoreWith A_o s1 _ (layoutToTyVal layout) vals reg
    allocBase 0 (blockSize layout) tag ap3 h_pc1 h_get1 h_reg h_off h_use
  simp only [s1] at h_step2
  exact StepStarWith.trans (StepStarWith.single h_step1) (StepStarWith.single h_step2)

theorem osea_run_alloc_cstore_ok
  (s_osea : oseair.State)
  (layout : LayoutTy)
  (vals : List oseair.Val)
  (reg : Register)
  (allocBase : Word)
  (allocMem : oseair.Mem)
  (tag : Word)
  (ap2 ap3 : AccessPerms)
  (h_size : 0 < blockSize layout)
  (h_alloc_pair : A_o.alloc s_osea.mem (blockSize layout) = (allocBase, allocMem))
  (h_own : sb_own s_osea.ap allocBase = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 allocBase tag = SBResult.Ok ap3) :
  oseair.runNWith A_o 2
    { s_osea with pc := 0 }
    [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)),
     oseair.Instr.CStore (layoutToTyVal layout) vals reg] =
    oseair.Result.Ok
      { s_osea with
        reg := s_osea.reg.insert reg
          (TyVal.PTy, [oseair.Val.Ptr allocBase 0 (blockSize layout) tag]),
        mem := oseair.writeWordSeq allocMem allocBase vals,
        ap := ap3,
        pc := 2 } := by
  simp only [blockSize_eq_layoutSize]
  let s1 : oseair.State :=
    { s_osea with
      reg := s_osea.reg.insert reg
        (TyVal.PTy, [oseair.Val.Ptr allocBase 0 (layoutSize layout) tag]),
      mem := allocMem,
      ap := ap2,
      pc := 1 }
  have h_pc0 : 0 < [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)),
      oseair.Instr.CStore (layoutToTyVal layout) vals reg].length := Nat.succ_pos 1
  have h_get0 : [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)),
      oseair.Instr.CStore (layoutToTyVal layout) vals reg].get ⟨0, h_pc0⟩ =
      oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)) := rfl
  have h_alloc_pair' :
      A_o.alloc s_osea.mem (layoutSize layout) = (allocBase, allocMem) := by
    simpa [blockSize_eq_layoutSize] using h_alloc_pair
  have h_step1 := step_Assgn_AllocWith A_o { s_osea with pc := 0 } _ reg (layoutToTyVal layout)
    allocBase allocMem ap2 tag (layoutSize layout)
    h_pc0 h_get0 (typeSize_layoutToTyVal layout) h_alloc_pair' h_own
  have h_reg : s1.reg.lookup reg =
      some (TyVal.PTy, [oseair.Val.Ptr allocBase 0 (layoutSize layout) tag]) := by simp [s1]
  have h_pc1 : (1 : Nat) < [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)),
      oseair.Instr.CStore (layoutToTyVal layout) vals reg].length := Nat.succ_lt_succ (Nat.succ_pos 0)
  have h_get1 : [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)),
      oseair.Instr.CStore (layoutToTyVal layout) vals reg].get ⟨1, h_pc1⟩ =
      oseair.Instr.CStore (layoutToTyVal layout) vals reg := rfl
  have h_off : allocBase + 0 < allocBase + layoutSize layout :=
    Nat.add_lt_add_left (by simpa [blockSize_eq_layoutSize] using h_size) allocBase
  have h_step2 := step_CStoreWith A_o s1 _ (layoutToTyVal layout) vals reg
    allocBase 0 (layoutSize layout) tag ap3 h_pc1 h_get1 h_reg h_off h_use
  simp only [s1] at h_step2
  simp only [oseair.runNWith, h_step1, h_step2, Nat.add_zero]

theorem osea_run_alloc_cstore_embedded_ok
  (s_osea : oseair.State)
  (prog : oseair.Prog)
  (layout : LayoutTy)
  (vals : List oseair.Val)
  (reg : Register)
  (allocBase : Word)
  (allocMem : oseair.Mem)
  (tag : Word)
  (ap2 ap3 : AccessPerms)
  (h_start :
    StartsAt prog s_osea.pc
      [oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout)),
       oseair.Instr.CStore (layoutToTyVal layout) vals reg])
  (h_size : 0 < blockSize layout)
  (h_alloc_pair : A_o.alloc s_osea.mem (blockSize layout) = (allocBase, allocMem))
  (h_own : sb_own s_osea.ap allocBase = (SBResult.Ok ap2, tag))
  (h_use : sb_use_mb ap2 allocBase tag = SBResult.Ok ap3) :
  oseair.runNWith A_o 2 s_osea prog =
    oseair.Result.Ok
      { s_osea with
        reg := s_osea.reg.insert reg
          (TyVal.PTy, [oseair.Val.Ptr allocBase 0 (blockSize layout) tag]),
        mem := oseair.writeWordSeq allocMem allocBase vals,
        ap := ap3,
        pc := s_osea.pc + 2 } := by
  simp only [blockSize_eq_layoutSize]
  have h_stmt0 :
      prog.get? s_osea.pc =
        some (oseair.Instr.Assgn reg (oseair.Rhs.Alloc (layoutToTyVal layout))) := by
    have h_head := h_start 0 (by decide : 0 < 2)
    simpa [Nat.zero_add, List.get?] using h_head.symm
  have h_tail := StartsAt.tail h_start
  have h_stmt1 :
      prog.get? (s_osea.pc + 1) =
        some (oseair.Instr.CStore (layoutToTyVal layout) vals reg) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using StartsAt.singleton h_tail
  rcases List.get?_eq_some_iff.mp h_stmt0 with ⟨h_pc0, h_get0⟩
  rcases List.get?_eq_some_iff.mp h_stmt1 with ⟨h_pc1, h_get1⟩
  let s1 : oseair.State :=
    { s_osea with
      reg := s_osea.reg.insert reg
        (TyVal.PTy, [oseair.Val.Ptr allocBase 0 (layoutSize layout) tag]),
      mem := allocMem,
      ap := ap2,
      pc := s_osea.pc + 1 }
  have h_step1 := step_Assgn_AllocWith A_o s_osea prog reg (layoutToTyVal layout)
    allocBase allocMem ap2 tag (layoutSize layout)
    h_pc0 h_get0 (typeSize_layoutToTyVal layout)
    (by simpa [blockSize_eq_layoutSize] using h_alloc_pair) h_own
  have h_reg1 : s1.reg.lookup reg =
      some (TyVal.PTy, [oseair.Val.Ptr allocBase 0 (layoutSize layout) tag]) := by
    simp [s1]
  have h_off : allocBase + 0 < allocBase + layoutSize layout :=
    Nat.add_lt_add_left (by simpa [blockSize_eq_layoutSize] using h_size) allocBase
  have h_step2 := step_CStoreWith A_o s1 prog (layoutToTyVal layout) vals reg
    allocBase 0 (layoutSize layout) tag ap3 h_pc1 h_get1 h_reg1 h_off h_use
  simp only [s1] at h_step2
  simp only [oseair.runNWith, h_step1, h_step2, Nat.add_zero]

end obseq.proof
