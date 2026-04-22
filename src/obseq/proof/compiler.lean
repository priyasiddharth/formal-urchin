import obseq.sb
import obseq.proof.core
import obseq.proof.const_existing
import obseq.proof.const_fresh
import obseq.proof.struct_init_existing
import obseq.proof.struct_init_fresh
import obseq.proof.copy_existing
import obseq.proof.ref
import obseq.proof.deref

namespace obseq.proof

open obseq
open obseq.mirlite
open obseq.oseair hiding State Result
open obseq.compile
open scoped obseq.notation

variable {A_o : oseair.AllocatorSpec}

def resetInstrs (cs : CompilerState) : CompilerState :=
  { cs with instrs := [] }

def prefixCompileState
  (cs0 : CompilerState)
  (prog : mirlite.Prog)
  (pc : Nat) : CompilerState :=
  List.foldl compileStmt cs0 (prog.take pc)

def withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState) : CompilerState :=
  { cs with instrs := instrPrefix ++ cs.instrs }

def csAt
  (cs0 : CompilerState)
  (prog : mirlite.Prog)
  (pc : Nat) : CompilerState :=
  resetInstrs (prefixCompileState cs0 prog pc)

def targetPcAt
  (cs0 : CompilerState)
  (prog : mirlite.Prog)
  (pc : Nat) : Nat :=
  (prefixCompileState cs0 prog pc).instrs.length

def compileProgFrom
  (cs0 : CompilerState)
  (prog : mirlite.Prog) : oseair.Prog :=
  (List.foldl compileStmt cs0 prog).instrs

@[simp] theorem withInstrPrefix_instrs
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState) :
  (withInstrPrefix instrPrefix cs).instrs = instrPrefix ++ cs.instrs := rfl

@[simp] theorem withInstrPrefix_nextReg
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState) :
  (withInstrPrefix instrPrefix cs).nextReg = cs.nextReg := rfl

@[simp] theorem withInstrPrefix_placeMap
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState) :
  (withInstrPrefix instrPrefix cs).placeMap = cs.placeMap := rfl

@[simp] theorem getPlaceInfo_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState)
  (base : Word) :
  getPlaceInfo (withInstrPrefix instrPrefix cs) base = getPlaceInfo cs base := rfl

@[simp] theorem freshReg_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState) :
  freshReg (withInstrPrefix instrPrefix cs) =
    let (reg, cs') := freshReg cs
    (reg, withInstrPrefix instrPrefix cs') := by
  simp [freshReg, withInstrPrefix]

@[simp] theorem setPlace_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState)
  (base : Word)
  (reg : Register)
  (layout : LayoutTy) :
  setPlace (withInstrPrefix instrPrefix cs) base reg layout =
    withInstrPrefix instrPrefix (setPlace cs base reg layout) := by
  simp [setPlace, withInstrPrefix]

@[simp] theorem emit_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState)
  (instrs : List oseair.Instr) :
  emit (withInstrPrefix instrPrefix cs) instrs =
    withInstrPrefix instrPrefix (emit cs instrs) := by
  simp [emit, withInstrPrefix, List.append_assoc]

@[simp] theorem placeLayout?_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState)
  (p : mirlite.Place) :
  placeLayout? (withInstrPrefix instrPrefix cs) p = placeLayout? cs p := by
  simp [placeLayout?, getPlaceInfo_withInstrPrefix]

theorem inferRExprLayout_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState) :
  ∀ expr,
    inferRExprLayout (withInstrPrefix instrPrefix cs) expr = inferRExprLayout cs expr
  | mirlite.RExpr.ConstOp _ => rfl
  | mirlite.RExpr.CopyOp _ => by simp [inferRExprLayout, placeLayout?_withInstrPrefix]
  | mirlite.RExpr.MoveOp _ => by simp [inferRExprLayout, placeLayout?_withInstrPrefix]
  | mirlite.RExpr.RefOp _ _ => by simp [inferRExprLayout, placeLayout?_withInstrPrefix]
  | mirlite.RExpr.DrefOp _ => by simp [inferRExprLayout, placeLayout?_withInstrPrefix]
  | mirlite.RExpr.StructInitOp [] => rfl
  | mirlite.RExpr.StructInitOp (field :: rest) => by
      have h_field := inferRExprLayout_withInstrPrefix instrPrefix cs field
      have h_rest_struct :=
        inferRExprLayout_withInstrPrefix instrPrefix cs (mirlite.RExpr.StructInitOp rest)
      have h_rest :
          inferRExprLayoutList (withInstrPrefix instrPrefix cs) rest =
            inferRExprLayoutList cs rest := by
        simpa [inferRExprLayout] using h_rest_struct
      simp [inferRExprLayout, inferRExprLayoutList, h_field, h_rest]
  | mirlite.RExpr.BinaryOp _ _ => rfl
termination_by expr => mirlite.rExprFuel expr
decreasing_by
  · exact Nat.lt_trans (mirlite.rExprFuel_lt_listFuel_head field rest)
      (mirlite.rExprListFuel_lt_struct (field :: rest))
  · simpa [mirlite.rExprFuel] using Nat.succ_lt_succ (mirlite.rExprListFuel_lt_cons field rest)

theorem inferRExprLayoutList_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState) :
  ∀ exprs,
    inferRExprLayoutList (withInstrPrefix instrPrefix cs) exprs =
      inferRExprLayoutList cs exprs
  | [] => rfl
  | expr :: rest => by
      simp [inferRExprLayoutList, inferRExprLayout_withInstrPrefix,
        inferRExprLayoutList_withInstrPrefix]

@[simp] theorem placeToBorrowReg_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState)
  (p : mirlite.Place)
  (kind : mirlite.RefKind) :
  placeToBorrowReg (withInstrPrefix instrPrefix cs) p kind =
    let res := placeToBorrowReg cs p kind
    { res with cs := withInstrPrefix instrPrefix res.cs } := by
  unfold placeToBorrowReg
  cases h_base : getPlaceInfo cs p.base with
  | none =>
      simp [getPlaceInfo_withInstrPrefix, h_base]
  | some info =>
      cases info with
      | mk baseReg baseLayout =>
          cases h_path : layoutResolvePath baseLayout p.path with
          | none =>
              simp [getPlaceInfo_withInstrPrefix, h_base, h_path]
          | some pathInfo =>
              cases pathInfo with
              | mk offset placeLayout =>
                  simp [getPlaceInfo_withInstrPrefix, h_base, h_path]

@[simp] theorem placeToReg_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState)
  (p : mirlite.Place)
  (kind : mirlite.RefKind)
  (expected : Option LayoutTy := none) :
  placeToReg (withInstrPrefix instrPrefix cs) p kind expected =
    let res := placeToReg cs p kind expected
    { res with cs := withInstrPrefix instrPrefix res.cs } := by
  unfold placeToReg
  cases h_base : getPlaceInfo cs p.base with
  | some info =>
      cases info with
      | mk baseReg baseLayout =>
          cases h_path : layoutResolvePath baseLayout p.path with
          | none =>
              simp [getPlaceInfo_withInstrPrefix, h_base, h_path]
          | some pathInfo =>
              cases pathInfo with
              | mk offset placeLayout =>
                  by_cases h_off : offset = 0
                  · simp [getPlaceInfo_withInstrPrefix, h_base, h_path, h_off]
                  · simp [getPlaceInfo_withInstrPrefix, h_base, h_path, h_off]
  | none =>
      cases expected with
      | none =>
          simp [getPlaceInfo_withInstrPrefix, h_base]
      | some baseLayout =>
          by_cases h_path : p.path == []
          · simp [getPlaceInfo_withInstrPrefix, h_base, h_path]
          · simp [getPlaceInfo_withInstrPrefix, h_base, h_path]

@[simp] theorem storePtrAtOffset_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState)
  (basePtr : Register)
  (offset : Word) :
  storePtrAtOffset (withInstrPrefix instrPrefix cs) basePtr offset =
    let (ptr, cleanup, cs') := storePtrAtOffset cs basePtr offset
    (ptr, cleanup, withInstrPrefix instrPrefix cs') := by
  unfold storePtrAtOffset
  by_cases h_off : offset = 0
  · simp [h_off, withInstrPrefix]
  · simp [h_off]

mutual
  theorem compileStructFieldsToFuel_withInstrPrefix :
      ∀ fuel dstPtr cs curOffset fields instrPrefix,
        compileStructFieldsToFuel fuel dstPtr (withInstrPrefix instrPrefix cs) curOffset fields =
          withInstrPrefix instrPrefix (compileStructFieldsToFuel fuel dstPtr cs curOffset fields)
    | 0, _, cs, _, _, instrPrefix => by
        simp [compileStructFieldsToFuel]
    | fuel + 1, _, cs, _, [], instrPrefix => by
        simp [compileStructFieldsToFuel]
    | fuel + 1, dstPtr, cs, curOffset, field :: tail, instrPrefix => by
      have h_layout := inferRExprLayout_withInstrPrefix instrPrefix cs field
      simp [compileStructFieldsToFuel, h_layout,
        compileRExprToFuel_withInstrPrefix,
        compileStructFieldsToFuel_withInstrPrefix]

  theorem compileRExprToFuel_withInstrPrefix :
      ∀ fuel cs dstPtr expr instrPrefix,
        compileRExprToFuel fuel (withInstrPrefix instrPrefix cs) dstPtr expr =
          withInstrPrefix instrPrefix (compileRExprToFuel fuel cs dstPtr expr)
    | 0, cs, _, _, instrPrefix => by
        simp [compileRExprToFuel]
    | fuel + 1, cs, dstPtr, expr, instrPrefix => by
        cases h_static : staticRExprData? expr with
        | some data =>
            rcases data with ⟨layout, vals⟩
            simp [compileRExprToFuel, h_static]
        | none =>
            cases expr with
            | ConstOp value =>
                simp [staticRExprData?] at h_static
            | CopyOp p =>
                simp [compileRExprToFuel, h_static, placeToReg_withInstrPrefix]
            | MoveOp p =>
                simp [compileRExprToFuel, h_static]
            | RefOp kind p =>
                simp [compileRExprToFuel, h_static, placeToBorrowReg_withInstrPrefix]
            | DrefOp p =>
                cases h_deref : layoutDeref? (placeToReg cs p mirlite.RefKind.Shared).layout <;>
                  simp [compileRExprToFuel, h_static, h_deref, placeToReg_withInstrPrefix]
            | StructInitOp fields =>
                simpa [compileRExprToFuel, h_static] using
                  (compileStructFieldsToFuel_withInstrPrefix
                    (fuel := fuel)
                    (dstPtr := dstPtr)
                    (cs := cs)
                    (curOffset := 0)
                    (fields := fields)
                    (instrPrefix := instrPrefix))
            | BinaryOp lhs rhs =>
                simp [compileRExprToFuel, h_static, compileRExprFuel_withInstrPrefix]

  theorem compileRExprFuel_withInstrPrefix :
      ∀ fuel cs expr instrPrefix,
        compileRExprFuel fuel (withInstrPrefix instrPrefix cs) expr =
          let res := compileRExprFuel fuel cs expr
          { res with cs := withInstrPrefix instrPrefix res.cs }
    | 0, cs, expr, instrPrefix => by
        simp [compileRExprFuel, inferRExprLayout_withInstrPrefix]
    | fuel + 1, cs, expr, instrPrefix => by
      have h_layout := inferRExprLayout_withInstrPrefix instrPrefix cs expr
      simp [compileRExprFuel, h_layout, compileRExprToFuel_withInstrPrefix]
end

attribute [simp] compileStructFieldsToFuel_withInstrPrefix
attribute [simp] compileRExprToFuel_withInstrPrefix
attribute [simp] compileRExprFuel_withInstrPrefix

@[simp] theorem compileRExprTo_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState)
  (dstPtr : Register)
  (expr : mirlite.RExpr) :
  compileRExprTo (withInstrPrefix instrPrefix cs) dstPtr expr =
    withInstrPrefix instrPrefix (compileRExprTo cs dstPtr expr) := by
  simp [compileRExprTo]

@[simp] theorem compileRExpr_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState)
  (expr : mirlite.RExpr) :
  compileRExpr (withInstrPrefix instrPrefix cs) expr =
    let res := compileRExpr cs expr
    { res with cs := withInstrPrefix instrPrefix res.cs } := by
  simp [compileRExpr]

@[simp] theorem freshReg_placeMap
  (cs : CompilerState) :
  (freshReg cs).2.placeMap = cs.placeMap := by
  simp [freshReg]

@[simp] theorem emit_placeMap
  (cs : CompilerState)
  (instrs : List oseair.Instr) :
  (emit cs instrs).placeMap = cs.placeMap := rfl

@[simp] theorem storePtrAtOffset_placeMap
  (cs : CompilerState)
  (basePtr : Register)
  (offset : Word) :
  (storePtrAtOffset cs basePtr offset).2.2.placeMap = cs.placeMap := by
  unfold storePtrAtOffset
  by_cases h_off : offset = 0
  · simp [h_off]
  · simp [h_off]

@[simp] theorem placeToBorrowReg_placeMap
  (cs : CompilerState)
  (p : mirlite.Place)
  (kind : mirlite.RefKind) :
  (placeToBorrowReg cs p kind).cs.placeMap = cs.placeMap := by
  unfold placeToBorrowReg
  cases h_base : getPlaceInfo cs p.base with
  | none =>
      simp [h_base]
  | some info =>
      cases info with
      | mk baseReg baseLayout =>
          cases h_path : layoutResolvePath baseLayout p.path with
          | none =>
              simp [h_base, h_path]
          | some pathInfo =>
              cases pathInfo with
              | mk offset placeLayout =>
                  simp [h_base, h_path]

theorem placeToReg_placeMap_of_lookup
  {cs : CompilerState}
  {p : mirlite.Place}
  {kind : mirlite.RefKind}
  {expected : Option LayoutTy}
  {reg : Register}
  {baseLayout : LayoutTy}
  (h_lookup : getPlaceInfo cs p.base = some (reg, baseLayout)) :
  (placeToReg cs p kind expected).cs.placeMap = cs.placeMap := by
  unfold placeToReg
  rw [h_lookup]
  cases h_path : layoutResolvePath baseLayout p.path with
  | none =>
      simp [h_path]
  | some pathInfo =>
      cases pathInfo with
      | mk offset placeLayout =>
          by_cases h_off : offset = 0
          · simp [h_path, h_off]
          · simp [h_path, h_off]

@[simp] theorem placeToReg_placeMap_no_expected
  (cs : CompilerState)
  (p : mirlite.Place)
  (kind : mirlite.RefKind) :
  (placeToReg cs p kind none).cs.placeMap = cs.placeMap := by
  unfold placeToReg
  cases h_base : getPlaceInfo cs p.base with
  | none =>
      simp [h_base]
  | some info =>
      cases info with
      | mk reg baseLayout =>
          cases h_path : layoutResolvePath baseLayout p.path with
          | none =>
              simp [h_base, h_path]
          | some pathInfo =>
              cases pathInfo with
              | mk offset placeLayout =>
                  by_cases h_off : offset = 0
                  · simp [h_base, h_path, h_off]
                  · simp [h_base, h_path, h_off]

theorem placeToReg_placeMap_of_absent_base
  {cs : CompilerState}
  {p : mirlite.Place}
  {kind : mirlite.RefKind}
  {layout : LayoutTy}
  (h_absent : getPlaceInfo cs p.base = none)
  (h_base : p.path = []) :
  (placeToReg cs p kind (some layout)).cs.placeMap =
    (p.base, (Register.R cs.nextReg, layout)) :: cs.placeMap := by
  unfold placeToReg
  rw [h_absent]
  simp [h_base, freshReg, emit, setPlace]

mutual
  theorem compileStructFieldsToFuel_placeMap :
      ∀ fuel dstPtr cs curOffset fields,
        (compileStructFieldsToFuel fuel dstPtr cs curOffset fields).placeMap = cs.placeMap
    | 0, _, cs, _, _ => rfl
    | _ + 1, _, cs, _, [] => rfl
    | fuel + 1, dstPtr, cs, curOffset, field :: tail => by
        simp [compileStructFieldsToFuel, compileRExprToFuel_placeMap,
          compileStructFieldsToFuel_placeMap]

  theorem compileRExprToFuel_placeMap :
      ∀ fuel cs dstPtr expr,
        (compileRExprToFuel fuel cs dstPtr expr).placeMap = cs.placeMap
    | 0, cs, _, _ => rfl
    | fuel + 1, cs, dstPtr, expr => by
        cases h_static : staticRExprData? expr with
        | some data =>
            rcases data with ⟨layout, vals⟩
            simp [compileRExprToFuel, h_static]
        | none =>
            cases expr with
            | ConstOp value =>
                simp [staticRExprData?] at h_static
            | CopyOp p =>
                simp [compileRExprToFuel, h_static, placeToReg_placeMap_no_expected]
            | MoveOp p =>
                simp [compileRExprToFuel, h_static]
            | RefOp kind p =>
                simp [compileRExprToFuel, h_static, placeToBorrowReg_placeMap]
            | DrefOp p =>
                cases h_deref : layoutDeref? (placeToReg cs p mirlite.RefKind.Shared).layout <;>
                  simp [compileRExprToFuel, h_static, h_deref, placeToReg_placeMap_no_expected]
            | StructInitOp fields =>
                simpa [compileRExprToFuel, h_static] using
                  (compileStructFieldsToFuel_placeMap
                    (fuel := fuel)
                    (dstPtr := dstPtr)
                    (cs := cs)
                    (curOffset := 0)
                    (fields := fields))
            | BinaryOp lhs rhs =>
                simp [compileRExprToFuel, h_static, compileRExprFuel_placeMap]

  theorem compileRExprFuel_placeMap :
      ∀ fuel cs expr,
        (compileRExprFuel fuel cs expr).cs.placeMap = cs.placeMap
    | 0, cs, expr => by
        simp [compileRExprFuel]
    | fuel + 1, cs, expr => by
        simp [compileRExprFuel, compileRExprToFuel_placeMap]
end

attribute [simp] compileStructFieldsToFuel_placeMap
attribute [simp] compileRExprToFuel_placeMap
attribute [simp] compileRExprFuel_placeMap

@[simp] theorem compileRExprTo_placeMap
  (cs : CompilerState)
  (dstPtr : Register)
  (expr : mirlite.RExpr) :
  (compileRExprTo cs dstPtr expr).placeMap = cs.placeMap := by
  simp [compileRExprTo]

@[simp] theorem compileRExpr_placeMap
  (cs : CompilerState)
  (expr : mirlite.RExpr) :
  (compileRExpr cs expr).cs.placeMap = cs.placeMap := by
  simp [compileRExpr]

theorem compileStmt_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState)
  (stmt : mirlite.Stmt) :
  compileStmt (withInstrPrefix instrPrefix cs) stmt =
    withInstrPrefix instrPrefix (compileStmt cs stmt) := by
  cases stmt with
  | Assgn lhs rhs =>
      cases lhs with
      | Place p =>
          cases rhs with
          | StructInitOp fields =>
              cases h_words : obseq.compile.structConstWords? fields with
              | some words =>
                  simp [compileStmt, h_words]
              | none =>
                  have h_layout :=
                    inferRExprLayout_withInstrPrefix instrPrefix cs (mirlite.RExpr.StructInitOp fields)
                  simp [compileStmt, h_words, h_layout]
          | BinaryOp lhs rhs =>
              cases lhs <;> cases rhs <;>
                simp [compileStmt]
          | _ =>
              simp [compileStmt]
      | DrefOp p =>
          cases h_deref : layoutDeref? (placeToReg (compileRExpr cs rhs).cs p mirlite.RefKind.Shared).layout <;>
            simp [compileStmt, h_deref]
  | Halt =>
      simp [compileStmt]

theorem foldl_compileStmt_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState)
  (prog : mirlite.Prog) :
  List.foldl compileStmt (withInstrPrefix instrPrefix cs) prog =
    withInstrPrefix instrPrefix (List.foldl compileStmt cs prog) := by
  induction prog generalizing cs with
  | nil =>
      simp [withInstrPrefix]
  | cons stmt rest ih =>
      simp [List.foldl, compileStmt_withInstrPrefix, ih]

theorem compileStmt_eq_prefix_append
  (cs : CompilerState)
  (stmt : mirlite.Stmt) :
  compileStmt cs stmt =
    withInstrPrefix cs.instrs (compileStmt (resetInstrs cs) stmt) := by
  simpa [withInstrPrefix, resetInstrs] using
    (compileStmt_withInstrPrefix (instrPrefix := cs.instrs) (cs := resetInstrs cs) stmt)

@[simp] theorem resetInstrs_instrs (cs : CompilerState) :
  (resetInstrs cs).instrs = [] := rfl

@[simp] theorem resetInstrs_nextReg (cs : CompilerState) :
  (resetInstrs cs).nextReg = cs.nextReg := rfl

@[simp] theorem resetInstrs_placeMap (cs : CompilerState) :
  (resetInstrs cs).placeMap = cs.placeMap := rfl

@[simp] theorem resetInstrs_withInstrPrefix
  (instrPrefix : List oseair.Instr)
  (cs : CompilerState) :
  resetInstrs (withInstrPrefix instrPrefix cs) = resetInstrs cs := by
  cases cs
  simp [resetInstrs, withInstrPrefix]

@[simp] theorem compilerEmpty_csAt
  (cs0 : CompilerState)
  (prog : mirlite.Prog)
  (pc : Nat) :
  CompilerEmpty (csAt cs0 prog pc) := rfl

@[simp] theorem prefixCompileState_zero
  (cs0 : CompilerState)
  (prog : mirlite.Prog) :
  prefixCompileState cs0 prog 0 = cs0 := by
  simp [prefixCompileState]

@[simp] theorem csAt_zero
  (cs0 : CompilerState)
  (prog : mirlite.Prog) :
  csAt cs0 prog 0 = resetInstrs cs0 := by
  simp [csAt]

@[simp] theorem targetPcAt_zero
  (cs0 : CompilerState)
  (prog : mirlite.Prog) :
  targetPcAt cs0 prog 0 = cs0.instrs.length := by
  simp [targetPcAt]

@[simp] theorem compileProgFrom_nil
  (cs : CompilerState) :
  compileProgFrom cs [] = cs.instrs := by
  simp [compileProgFrom]

theorem take_succ_eq_take_append_get
  {xs : List α}
  {n : Nat}
  {x : α}
  (h_get : xs.get? n = some x) :
  xs.take (n + 1) = xs.take n ++ [x] := by
  induction xs generalizing n with
  | nil =>
      cases n <;> cases h_get
  | cons y ys ih =>
      cases n with
      | zero =>
          simp [List.get?] at h_get
          cases h_get
          simp
      | succ n =>
          simp [List.get?] at h_get ⊢
          exact ih h_get

theorem prefixCompileState_succ
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {pc : Nat}
  {stmt : mirlite.Stmt}
  (h_get : prog.get? pc = some stmt) :
  prefixCompileState cs0 prog (pc + 1) =
    compileStmt (prefixCompileState cs0 prog pc) stmt := by
  rw [prefixCompileState, prefixCompileState]
  rw [take_succ_eq_take_append_get h_get]
  simp [List.foldl_append]

theorem drop_eq_get_cons
  {xs : List α}
  {n : Nat}
  {x : α}
  (h_get : xs.get? n = some x) :
  xs.drop n = x :: xs.drop (n + 1) := by
  induction xs generalizing n with
  | nil =>
      cases n <;> cases h_get
  | cons y ys ih =>
      cases n with
      | zero =>
          simp at h_get
          cases h_get
          simp
      | succ n =>
          simp [List.get?, List.drop] at h_get ⊢
          exact ih h_get

theorem StartsAt.of_append
  (prefixInstrs frag : List α) :
  StartsAt (prefixInstrs ++ frag) prefixInstrs.length frag := by
  intro i
  induction prefixInstrs generalizing i with
  | nil =>
      simp
  | cons x xs ih =>
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, List.get?] using ih i

theorem StartsAt.of_get?_take
  {prog : List α}
  {pc : Nat}
  {x : α}
  (h_get : prog.get? pc = some x) :
  StartsAt (prog.take (pc + 1)) pc [x] := by
  rcases List.get?_eq_some_iff.mp h_get with ⟨h_pc, _h_get⟩
  have h_take_len : (prog.take pc).length = pc := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt h_pc)]
  rw [take_succ_eq_take_append_get h_get]
  simpa [h_take_len] using (StartsAt.of_append (prefixInstrs := prog.take pc) (frag := [x]))

theorem StartsAt.prefix
  {prog : List α}
  {pc : Nat}
  {pref suff : List α}
  (h_start : StartsAt prog pc (pref ++ suff)) :
  StartsAt prog pc pref := by
  induction pref generalizing pc suff with
  | nil =>
      exact fun i hi => False.elim (Nat.not_lt_zero _ hi)
  | cons x pref ih =>
      intro i
      cases i with
      | zero =>
          simpa [Nat.zero_add, List.get?] using h_start 0
      | succ j =>
          have h_tail : StartsAt prog (pc + 1) (pref ++ suff) := by
            simpa using (StartsAt.tail h_start)
          have h_pref_tail : StartsAt prog (pc + 1) pref := ih h_tail
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.get?] using h_pref_tail j

theorem layoutResolvePath_append
  {baseLayout midLayout finalLayout : LayoutTy}
  {path₁ path₂ : List Nat}
  {off₁ off₂ : Word}
  (h₁ : layoutResolvePath baseLayout path₁ = some (off₁, midLayout))
  (h₂ : layoutResolvePath midLayout path₂ = some (off₂, finalLayout)) :
  layoutResolvePath baseLayout (path₁ ++ path₂) = some (off₁ + off₂, finalLayout) := by
  induction path₁ generalizing baseLayout off₁ midLayout with
  | nil =>
      simp [layoutResolvePath] at h₁
      rcases h₁ with ⟨rfl, rfl⟩
      simpa [layoutResolvePath] using h₂
  | cons idx rest ih =>
      cases baseLayout with
      | NatL =>
          simp [layoutResolvePath] at h₁
      | PtrL inner =>
          simp [layoutResolvePath] at h₁
      | TupL tys =>
          simp [layoutResolvePath] at h₁ ⊢
          cases h_get : listGetOpt tys idx <;> simp [h_get] at h₁ ⊢
          rename_i subLayout
          cases h_rest : layoutResolvePath subLayout rest with
          | none =>
              simp [h_rest] at h₁
          | some pair =>
              cases pair with
              | mk off_rest midLayout' =>
                  simp [h_rest] at h₁
                  rcases h₁ with ⟨rfl, rfl⟩
                  have h_tail :
                      layoutResolvePath subLayout (rest ++ path₂) =
                        some (off_rest + off₂, finalLayout) :=
                    ih h_rest h₂
                  simp [h_tail, Nat.add_assoc]

theorem layoutSizeList_take_mono :
    ∀ tys i j,
      i ≤ j →
  layoutSizeList (List.take i tys) ≤ layoutSizeList (List.take j tys)
  | [], i, j, _h_le => by
    simp [layoutSizeList]
  | _ :: tys, 0, j, _h_le => by
    simp [List.take, layoutSizeList]
  | _ :: _, i + 1, 0, h_le => by
    cases h_le
  | ty :: tys, i + 1, j + 1, h_le => by
    simpa [List.take, layoutSizeList] using
    Nat.add_le_add_left
      (layoutSizeList_take_mono tys i j (Nat.succ_le_succ_iff.mp h_le))
      (layoutSize ty)

theorem layoutSizeList_take_succ_get :
    ∀ tys idx subTy,
      listGetOpt tys idx = some subTy →
      layoutSizeList (List.take (idx + 1) tys) =
        layoutSizeList (List.take idx tys) + layoutSize subTy
  | [], _, _, h_get => by
      cases h_get
  | ty :: tys, 0, subTy, h_get => by
      cases h_get
      simp [List.take, layoutSizeList]
  | ty :: tys, idx + 1, subTy, h_get => by
      simp [listGetOpt] at h_get
      have ih := layoutSizeList_take_succ_get tys idx subTy h_get
      simp [List.take, layoutSizeList, ih, Nat.add_left_comm, Nat.add_comm]

    theorem listGetOpt_mem :
      ∀ {xs : List α} {idx : Nat} {x : α},
        listGetOpt xs idx = some x → x ∈ xs
      | [], _, _, h_get => by
        cases h_get
      | y :: ys, 0, x, h_get => by
        simp [listGetOpt] at h_get
        cases h_get
        simp
      | y :: ys, idx + 1, x, h_get => by
        simp [listGetOpt] at h_get
        exact List.mem_cons_of_mem y (listGetOpt_mem h_get)

theorem layoutResolvePath_within_field_ptr
  {tys : List LayoutTy}
  {idx : Nat}
  {subLayout innerLayout : LayoutTy}
  {path : List Nat}
  {off : Word}
  (h_get : listGetOpt tys idx = some subLayout)
  (h_res :
    layoutResolvePath (LayoutTy.TupL tys) path =
      some (layoutSizeList (List.take idx tys) + off, LayoutTy.PtrL innerLayout))
  (h_fit : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize subLayout) :
  ∃ tail,
    path = idx :: tail ∧
    layoutResolvePath subLayout tail = some (off, LayoutTy.PtrL innerLayout) := by
  cases path with
  | nil =>
      simp [layoutResolvePath] at h_res
  | cons j rest =>
      simp [layoutResolvePath] at h_res
      cases h_get' : listGetOpt tys j with
      | none =>
          simp [h_get'] at h_res
      | some subLayout' =>
          cases h_rest : layoutResolvePath subLayout' rest with
          | none =>
              simp [h_get', h_rest] at h_res
          | some pair =>
              rcases pair with ⟨off', finalLayout⟩
              simp [h_get', h_rest] at h_res
              rcases h_res with ⟨h_off_eq, h_layout_eq⟩
              subst h_layout_eq
              have h_fit' : off' + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize subLayout' :=
                layoutResolvePath_blockSize_le h_rest
              have h_off_lt : off < blockSize subLayout := by
                exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_fit)
              have h_off'_lt : off' < blockSize subLayout' := by
                exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off') (by simpa [blockSize] using h_fit')
              have h_off_lt_layout : off < layoutSize subLayout := by
                simpa [blockSize] using h_off_lt
              have h_off'_lt_layout : off' < layoutSize subLayout' := by
                simpa [blockSize] using h_off'_lt
              by_cases h_eq : j = idx
              · subst h_eq
                have h_sub_eq : subLayout' = subLayout := by
                  exact Option.some.inj (h_get'.symm.trans h_get)
                subst h_sub_eq
                have h_off_eq' : off' = off := Nat.add_left_cancel h_off_eq
                subst h_off_eq'
                exact ⟨rest, rfl, h_rest⟩
              · cases Nat.lt_or_gt_of_ne h_eq with
                | inl h_lt =>
                    have h_prefix_eq :
                        layoutSizeList (List.take (j + 1) tys) =
                          layoutSizeList (List.take j tys) + layoutSize subLayout' :=
                      layoutSizeList_take_succ_get tys j subLayout' h_get'
                    have h_prefix_le :
                        layoutSizeList (List.take (j + 1) tys) ≤ layoutSizeList (List.take idx tys) :=
                      layoutSizeList_take_mono tys (j + 1) idx (Nat.succ_le_of_lt h_lt)
                    have h_lt_prefix :
                        layoutSizeList (List.take j tys) + off' < layoutSizeList (List.take idx tys) := by
                      have h_lt_size :
                          layoutSizeList (List.take j tys) + off' <
                            layoutSizeList (List.take j tys) + layoutSize subLayout' :=
                        Nat.add_lt_add_left h_off'_lt_layout _
                      rw [← h_prefix_eq] at h_lt_size
                      exact Nat.lt_of_lt_of_le h_lt_size h_prefix_le
                    have : layoutSizeList (List.take idx tys) + off < layoutSizeList (List.take idx tys) := by
                      simpa [h_off_eq] using h_lt_prefix
                    exact False.elim ((Nat.not_lt_of_ge (Nat.le_add_right _ _)) this)
                | inr h_gt =>
                    have h_prefix_eq :
                        layoutSizeList (List.take (idx + 1) tys) =
                          layoutSizeList (List.take idx tys) + layoutSize subLayout :=
                      layoutSizeList_take_succ_get tys idx subLayout h_get
                    have h_prefix_le :
                        layoutSizeList (List.take (idx + 1) tys) ≤ layoutSizeList (List.take j tys) :=
                      layoutSizeList_take_mono tys (idx + 1) j (Nat.succ_le_of_lt h_gt)
                    have h_lt_prefix :
                        layoutSizeList (List.take idx tys) + off < layoutSizeList (List.take j tys) := by
                      have h_lt_size :
                          layoutSizeList (List.take idx tys) + off <
                            layoutSizeList (List.take idx tys) + layoutSize subLayout :=
                        Nat.add_lt_add_left h_off_lt_layout _
                      rw [← h_prefix_eq] at h_lt_size
                      exact Nat.lt_of_lt_of_le h_lt_size h_prefix_le
                    have : layoutSizeList (List.take j tys) + off' < layoutSizeList (List.take j tys) := by
                      simpa [h_off_eq] using h_lt_prefix
                    exact False.elim ((Nat.not_lt_of_ge (Nat.le_add_right _ _)) this)

theorem layoutResolvePath_suffix_ptr
  {baseLayout dstLayout innerLayout : LayoutTy}
  {path₁ path : List Nat}
  {dstOff off : Word}
  (h_dst : layoutResolvePath baseLayout path₁ = some (dstOff, dstLayout))
  (h_ptr : layoutResolvePath baseLayout path = some (dstOff + off, LayoutTy.PtrL innerLayout))
  (h_fit : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize dstLayout) :
  ∃ path₂,
    path = path₁ ++ path₂ ∧
    layoutResolvePath dstLayout path₂ = some (off, LayoutTy.PtrL innerLayout) := by
  induction path₁ generalizing baseLayout dstLayout dstOff path off with
  | nil =>
      simp [layoutResolvePath] at h_dst
      rcases h_dst with ⟨rfl, rfl⟩
      exact ⟨path, by simp, by simpa [Nat.zero_add] using h_ptr⟩
  | cons idx rest ih =>
      cases baseLayout with
      | NatL =>
          simp [layoutResolvePath] at h_dst
      | PtrL inner =>
          simp [layoutResolvePath] at h_dst
      | TupL tys =>
          cases h_get : listGetOpt tys idx with
          | none =>
              simp [layoutResolvePath, h_get] at h_dst
          | some subLayout =>
              cases h_rest : layoutResolvePath subLayout rest with
              | none =>
                  simp [layoutResolvePath, h_get, h_rest] at h_dst
              | some pair =>
                  rcases pair with ⟨off₁, dstLayout'⟩
                  simp [layoutResolvePath, h_get, h_rest] at h_dst
                  rcases h_dst with ⟨rfl, rfl⟩
                  have h_sub_fit :
                      off₁ + off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize subLayout := by
                    have h_mid_fit : off₁ + blockSize dstLayout' ≤ blockSize subLayout :=
                      layoutResolvePath_blockSize_le h_rest
                    have h_lift :
                        off₁ + (off + blockSize (LayoutTy.PtrL innerLayout)) ≤
                          off₁ + blockSize dstLayout' :=
                      Nat.add_le_add_left h_fit off₁
                    exact Nat.le_trans (by simpa [Nat.add_assoc] using h_lift) h_mid_fit
                  have h_ptr' :
                      layoutResolvePath (LayoutTy.TupL tys) path =
                        some (layoutSizeList (List.take idx tys) + (off₁ + off), LayoutTy.PtrL innerLayout) := by
                    simpa [Nat.add_assoc] using h_ptr
                  obtain ⟨tail, h_path, h_tail⟩ :=
                    layoutResolvePath_within_field_ptr h_get h_ptr' h_sub_fit
                  obtain ⟨path₂, h_tail_path, h_suffix⟩ :=
                    ih h_rest h_tail h_fit
                  refine ⟨path₂, ?_, h_suffix⟩
                  rw [h_path, h_tail_path]
                  simp

          theorem layoutResolvePath_ptr_zero
            {inner inner' : LayoutTy}
            {path : List Nat}
            (h : layoutResolvePath (LayoutTy.PtrL inner) path = some (0, LayoutTy.PtrL inner')) :
            path = [] ∧ inner' = inner := by
            cases path with
            | nil =>
              simp [layoutResolvePath] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨rfl, rfl⟩
            | cons idx rest =>
              simp [layoutResolvePath] at h

theorem layoutResolvePath_sizeOf_lt_of_nonempty :
    ∀ {layout subLayout : LayoutTy} {path : List Nat} {off : Word},
      path ≠ [] →
      layoutResolvePath layout path = some (off, subLayout) →
      sizeOf subLayout < sizeOf layout
  | _, _, [], _, h_ne, _ => by
    cases h_ne rfl
  | .NatL, _, _ :: _, _, _, h_res => by
    simp [layoutResolvePath] at h_res
  | .PtrL inner, _, _ :: _, _, _, h_res => by
    simp [layoutResolvePath] at h_res
  | .TupL tys, _, [idx], _, _, h_res => by
    cases h_get : listGetOpt tys idx with
    | none =>
      simp [layoutResolvePath, h_get] at h_res
    | some fieldLayout =>
      simp [layoutResolvePath, h_get] at h_res
      rcases h_res with ⟨rfl, rfl⟩
      have h_mem : fieldLayout ∈ tys := listGetOpt_mem h_get
      have h_lt_list : sizeOf fieldLayout < sizeOf tys :=
      List.sizeOf_lt_of_mem h_mem
      exact Nat.lt_trans h_lt_list (by simp)
  | .TupL tys, _, idx :: j :: rest, _, _, h_res => by
    cases h_get : listGetOpt tys idx with
    | none =>
      simp [layoutResolvePath, h_get] at h_res
    | some fieldLayout =>
      cases fieldLayout with
      | NatL =>
          simp [layoutResolvePath, h_get] at h_res
      | PtrL inner =>
          simp [layoutResolvePath, h_get] at h_res
      | TupL fieldTys =>
          have h_mem : LayoutTy.TupL fieldTys ∈ tys := by
            simpa using listGetOpt_mem h_get
          have h_field_lt : sizeOf (LayoutTy.TupL fieldTys) < sizeOf (LayoutTy.TupL tys) := by
            exact Nat.lt_trans (List.sizeOf_lt_of_mem h_mem) (by simp)
          simp [layoutResolvePath, h_get] at h_res
          cases h_get' : listGetOpt fieldTys j with
          | none =>
              simp [h_get'] at h_res
          | some subField =>
              cases h_short : layoutResolvePath subField rest with
              | none =>
                  simp [h_get', h_short] at h_res
              | some pair =>
                  rcases pair with ⟨off', subLayout'⟩
                  simp [h_get', h_short] at h_res
                  rcases h_res with ⟨rfl, rfl⟩
                  have h_short_full :
                      layoutResolvePath (LayoutTy.TupL fieldTys) (j :: rest) =
                        some (layoutSizeList (List.take j fieldTys) + off', subLayout') := by
                    simp [layoutResolvePath, h_get', h_short]
                  have h_short_lt : sizeOf subLayout' < sizeOf (LayoutTy.TupL fieldTys) :=
                    layoutResolvePath_sizeOf_lt_of_nonempty
                      (layout := LayoutTy.TupL fieldTys)
                      (subLayout := subLayout')
                      (path := j :: rest)
                      (off := layoutSizeList (List.take j fieldTys) + off')
                      (by simp)
                      h_short_full
                  exact Nat.lt_trans h_short_lt h_field_lt

theorem layoutResolvePath_zero_self_ptr_impossible
  {layout : LayoutTy}
  {path : List Nat}
  (h_res : layoutResolvePath layout path = some (0, LayoutTy.PtrL layout)) :
  False := by
  cases path with
  | nil =>
      simp [layoutResolvePath] at h_res
      have h_lt : sizeOf layout < sizeOf (LayoutTy.PtrL layout) := by
        simp
      have h_eq_size : sizeOf layout = sizeOf (LayoutTy.PtrL layout) := by
        simpa using congrArg sizeOf h_res
      rw [← h_eq_size] at h_lt
      exact (Nat.lt_irrefl _ h_lt)
  | cons idx rest =>
      have h_lt : sizeOf (LayoutTy.PtrL layout) < sizeOf layout :=
        layoutResolvePath_sizeOf_lt_of_nonempty
          (layout := layout)
          (subLayout := LayoutTy.PtrL layout)
          (path := idx :: rest)
          (off := 0)
          (by simp)
          h_res
      have h_gt : sizeOf layout < sizeOf (LayoutTy.PtrL layout) := by
        simp
      exact (Nat.lt_asymm h_lt h_gt)

theorem ref_src_dst_offset_ne_of_same_base
  {baseLayout srcLayout : LayoutTy}
  {srcPath dstPath : List Nat}
  {srcOff dstOff : Word}
  (h_src : layoutResolvePath baseLayout srcPath = some (srcOff, srcLayout))
  (h_dst : layoutResolvePath baseLayout dstPath = some (dstOff, LayoutTy.PtrL srcLayout))
  (h_src_nonempty : 0 < blockSize srcLayout) :
  srcOff ≠ dstOff := by
  intro h_eq
  have h_ptr_fit : 0 + blockSize (LayoutTy.PtrL srcLayout) ≤ blockSize srcLayout := by
    simpa [blockSize, layoutSize] using Nat.succ_le_of_lt h_src_nonempty
  obtain ⟨path₂, _h_path, h_tail⟩ :=
    layoutResolvePath_suffix_ptr
      (dstLayout := srcLayout)
      (innerLayout := srcLayout)
      (dstOff := srcOff)
      (off := 0)
      h_src
      (by simpa [h_eq, Nat.add_zero] using h_dst)
      h_ptr_fit
  exact layoutResolvePath_zero_self_ptr_impossible h_tail

theorem compileProgFrom_cons
  (cs : CompilerState)
  (stmt : mirlite.Stmt)
  (prog : mirlite.Prog) :
  compileProgFrom cs (stmt :: prog) =
    (compileStmt cs stmt).instrs ++
      compileProgFrom (resetInstrs (compileStmt cs stmt)) prog := by
  unfold compileProgFrom
  simp only [List.foldl]
  have h_fold := foldl_compileStmt_withInstrPrefix
    (instrPrefix := (compileStmt cs stmt).instrs)
    (cs := resetInstrs (compileStmt cs stmt))
    (prog := prog)
  simpa [withInstrPrefix, resetInstrs] using congrArg CompilerState.instrs h_fold

theorem compileProgFrom_suffix
  (cs0 : CompilerState)
  (prog : mirlite.Prog)
  (pc : Nat) :
  compileProgFrom cs0 prog =
    (prefixCompileState cs0 prog pc).instrs ++
      compileProgFrom (csAt cs0 prog pc) (prog.drop pc) := by
  unfold compileProgFrom prefixCompileState csAt
  rw [← List.take_append_drop pc prog]
  simp only [List.foldl_append]
  let prefixState := List.foldl compileStmt cs0 (prog.take pc)
  have h_prefix :
      withInstrPrefix prefixState.instrs (resetInstrs prefixState) = prefixState := by
    cases prefixState
    simp [withInstrPrefix, resetInstrs]
  have h_fold := foldl_compileStmt_withInstrPrefix
    (instrPrefix := prefixState.instrs)
    (cs := resetInstrs prefixState)
    (prog := prog.drop pc)
  rw [h_prefix] at h_fold
  simpa [prefixState, withInstrPrefix, resetInstrs] using congrArg CompilerState.instrs h_fold

theorem compileProgFrom_startsAt
  (cs0 : CompilerState)
  (prog : mirlite.Prog)
  (pc : Nat) :
  StartsAt
    (compileProgFrom cs0 prog)
    (targetPcAt cs0 prog pc)
    (compileProgFrom (csAt cs0 prog pc) (prog.drop pc)) := by
  rw [compileProgFrom_suffix cs0 prog pc]
  simpa [targetPcAt] using
    (StartsAt.of_append
      (prefixInstrs := (prefixCompileState cs0 prog pc).instrs)
      (frag := compileProgFrom (csAt cs0 prog pc) (prog.drop pc)))

theorem targetPcAt_succ
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {pc : Nat}
  {stmt : mirlite.Stmt}
  (h_get : prog.get? pc = some stmt) :
  targetPcAt cs0 prog (pc + 1) =
    targetPcAt cs0 prog pc + (compileStmt (csAt cs0 prog pc) stmt).instrs.length := by
  rw [targetPcAt, prefixCompileState_succ h_get]
  have h_prefix := compileStmt_eq_prefix_append (prefixCompileState cs0 prog pc) stmt
  have h_instrs := congrArg CompilerState.instrs h_prefix
  have h_lengths := congrArg List.length h_instrs
  simpa [targetPcAt, csAt, withInstrPrefix] using h_lengths

theorem csAt_succ
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {pc : Nat}
  {stmt : mirlite.Stmt}
  (h_get : prog.get? pc = some stmt) :
  csAt cs0 prog (pc + 1) = resetInstrs (compileStmt (csAt cs0 prog pc) stmt) := by
  rw [csAt, prefixCompileState_succ h_get]
  let prefixState := prefixCompileState cs0 prog pc
  have h_stmt := compileStmt_eq_prefix_append prefixState stmt
  rw [show csAt cs0 prog pc = resetInstrs prefixState by rfl]
  simpa [prefixState, csAt] using congrArg resetInstrs h_stmt

inductive SupportedStmt (cs : CompilerState) : mirlite.Stmt → Prop
  | const_existing
      (ctx : ConstExistingCtx)
      (h_cs : ctx.cs = cs) :
      SupportedStmt cs (ConstExistingCtx.stmt ctx)
  | const_fresh
      (ctx : ConstFreshCtx)
      (h_cs : ctx.cs = cs) :
      SupportedStmt cs (ConstFreshCtx.stmt ctx)
  | struct_init_existing
      (ctx : StructInitExistingCtx)
      (h_cs : ctx.cs = cs) :
      SupportedStmt cs (StructInitExistingCtx.stmt ctx)
  | struct_init_fresh
      (ctx : StructInitFreshCtx)
      (h_cs : ctx.cs = cs) :
      SupportedStmt cs (StructInitFreshCtx.stmt ctx)
  | copy_existing
      (ctx : CopyExistingCtx)
      (h_cs : ctx.cs = cs) :
      SupportedStmt cs (CopyExistingCtx.stmt ctx)
  | ref_existing
      (ctx : RefExistingCtx)
      (h_cs : ctx.cs = cs)
      (h_src_nonempty : 0 < blockSize ctx.srcLayout) :
      SupportedStmt cs (RefExistingCtx.stmt ctx)
  | deref_projected_existing
      (ctx : DerefProjectedExistingCtx)
      (h_cs : ctx.cs = cs)
      (h_inner_nonempty : 0 < blockSize ctx.innerLayout) :
      SupportedStmt cs (DerefProjectedExistingCtx.stmt ctx)
  | deref_fresh
      (ctx : DerefFreshCtx)
      (h_cs : ctx.cs = cs)
      (h_inner_nonempty : 0 < blockSize ctx.innerLayout) :
      SupportedStmt cs (DerefFreshCtx.stmt ctx)

def SupportedProgFrom
  (cs0 : CompilerState)
  (prog : mirlite.Prog) : Prop :=
  ∀ pc stmt, prog.get? pc = some stmt → SupportedStmt (csAt cs0 prog pc) stmt

def TrackedPlaceTagClosure
  (π : PlaceMap)
  (s_mir : mirlite.State) : Prop :=
  ∀ (p : mirlite.Place) reg baseLayout baseAddr baseTag off innerLayout q gq,
    π.lookup p.base = some (reg, baseLayout) →
    layoutResolvePath baseLayout p.path = some (off, LayoutTy.PtrL innerLayout) →
    s_mir.env.lookup p.base = some (baseAddr, layoutToTyVal baseLayout, baseTag) →
    s_mir.mem.find? (baseAddr + off) = some (mirlite.MemValue.PlaceTag q gq) →
    ∃ targetReg targetBaseLayout targetOff targetBaseAddr targetBaseTag,
      π.lookup q.base = some (targetReg, targetBaseLayout) ∧
      layoutResolvePath targetBaseLayout q.path = some (targetOff, innerLayout) ∧
      s_mir.env.lookup q.base =
        some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag)

def TrackedPlaceTagLive
  (π : PlaceMap)
  (s_mir : mirlite.State) : Prop :=
  ∀ (p : mirlite.Place) reg baseLayout baseAddr baseTag off innerLayout q gq,
    π.lookup p.base = some (reg, baseLayout) →
    layoutResolvePath baseLayout p.path = some (off, LayoutTy.PtrL innerLayout) →
    s_mir.env.lookup p.base = some (baseAddr, layoutToTyVal baseLayout, baseTag) →
    s_mir.mem.find? (baseAddr + off) = some (mirlite.MemValue.PlaceTag q gq) →
    ∃ targetReg targetBaseLayout targetOff targetBaseAddr targetBaseTag stack item,
      π.lookup q.base = some (targetReg, targetBaseLayout) ∧
      layoutResolvePath targetBaseLayout q.path = some (targetOff, innerLayout) ∧
      s_mir.env.lookup q.base =
        some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag) ∧
      s_mir.ap.StackMap.find? (targetBaseAddr + targetOff) = some stack ∧
      item ∈ stack ∧
      item.tag = gq

def TagRenameFreshFrom
  (ρt : TagRenameMap)
  (nextTag : Tag) : Prop :=
  ∀ tag, nextTag ≤ tag → ρt tag = none

theorem sb_own_tag_eq_nextTag
  {ap ap' : AccessPerms}
  {addr tag : Word}
  (h_own : sb_own ap addr = (SBResult.Ok ap', tag)) :
  tag = ap.NextTag := by
  unfold sb_own at h_own
  cases h_find : ap.StackMap.find? addr with
  | none =>
      rw [h_find] at h_own
      unfold freshTag at h_own
      injection h_own with h_ok h_tag
      cases h_ok
      exact h_tag.symm
  | some stack =>
      cases stack with
      | nil =>
          rw [h_find] at h_own
          unfold freshTag at h_own
          injection h_own with h_ok h_tag
          cases h_ok
          exact h_tag.symm
      | cons item rest =>
          simp [h_find] at h_own

theorem sb_ref_nextTag_succ_local
  {ap ap' : AccessPerms} {addr tag newTag : Word} {kind : RefOpKind}
  (h_ref : sb_ref ap addr tag kind = (SBResult.Ok ap', newTag)) :
  ap'.NextTag = ap.NextTag + 1 := by
  cases kind with
  | Shared =>
      unfold sb_ref at h_ref
      cases h_parent : sb_read ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_next : ap_parent.NextTag = ap.NextTag :=
            sb_read_nextTag_eq h_parent
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨h_ap, _h_tag⟩
              have h_next_eq : ap'.NextTag = ap_parent.NextTag + 1 := by
                simpa using congrArg AccessPerms.NextTag h_ap.symm
              simpa [h_parent_next] using h_next_eq
  | Mut =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_next : ap_parent.NextTag = ap.NextTag :=
            sb_use_mb_nextTag_eq h_parent
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨h_ap, _h_tag⟩
              have h_next_eq : ap'.NextTag = ap_parent.NextTag + 1 := by
                simpa using congrArg AccessPerms.NextTag h_ap.symm
              simpa [h_parent_next] using h_next_eq
  | Raw =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          have h_parent_next : ap_parent.NextTag = ap.NextTag :=
            sb_use_mb_nextTag_eq h_parent
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨h_ap, _h_tag⟩
              have h_next_eq : ap'.NextTag = ap_parent.NextTag + 1 := by
                simpa using congrArg AccessPerms.NextTag h_ap.symm
              simpa [h_parent_next] using h_next_eq

theorem sb_use_mb_find_item_of_ok
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_use : sb_use_mb ap addr tag = SBResult.Ok ap') :
  ∃ stack item,
    ap'.StackMap.find? addr = some stack ∧
    item ∈ stack ∧
    item.tag = tag := by
  unfold sb_use_mb at h_use
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_use
  | some stack0 =>
      cases h_split : splitStack stack0 tag with
      | none =>
          simp [h_find, h_split] at h_use
      | some triple =>
          rcases triple with ⟨x, item, y⟩
          have h_item_tag := splitStack_found_tag h_split
          cases item with
          | Own t =>
              simp [h_find, h_split] at h_use
              subst ap'
              exact ⟨RefKind.Own t :: y, RefKind.Own t,
                SB.find?_insert_eq _ _ _, by simp, by simpa using h_item_tag⟩
          | MutRef t =>
              simp [h_find, h_split] at h_use
              subst ap'
              exact ⟨RefKind.MutRef t :: y, RefKind.MutRef t,
                SB.find?_insert_eq _ _ _, by simp, by simpa using h_item_tag⟩
          | Ref t =>
              simp [h_find, h_split] at h_use
          | RawPtr t =>
              simp [h_find, h_split] at h_use

theorem sb_read_find_item_of_ok
  {ap ap' : AccessPerms} {addr tag : Word}
  (h_read : sb_read ap addr tag = SBResult.Ok ap') :
  ∃ stack item,
    ap'.StackMap.find? addr = some stack ∧
    item ∈ stack ∧
    item.tag = tag := by
  unfold sb_read at h_read
  cases h_find : ap.StackMap.find? addr with
  | none =>
      simp [h_find] at h_read
  | some stack0 =>
      cases h_split : splitStack stack0 tag with
      | none =>
          simp [h_find, h_split] at h_read
      | some triple =>
          rcases triple with ⟨x, item, y⟩
          have h_item_tag := splitStack_found_tag h_split
          cases item with
          | Own t =>
              simp [h_find, h_split] at h_read
              subst ap'
              exact ⟨x.filter (fun k => !k.isMb) ++ RefKind.Own t :: y,
                RefKind.Own t, SB.find?_insert_eq _ _ _, by simp, by simpa using h_item_tag⟩
          | MutRef t =>
              simp [h_find, h_split] at h_read
              subst ap'
              exact ⟨x.filter (fun k => !k.isMb) ++ RefKind.MutRef t :: y,
                RefKind.MutRef t, SB.find?_insert_eq _ _ _, by simp, by simpa using h_item_tag⟩
          | Ref t =>
              simp [h_find, h_split] at h_read
              subst ap'
              exact ⟨x.filter (fun k => !k.isMb) ++ RefKind.Ref t :: y,
                RefKind.Ref t, SB.find?_insert_eq _ _ _, by simp, by simpa using h_item_tag⟩
          | RawPtr t =>
              simp [h_find, h_split] at h_read
              subst ap'
              exact ⟨x.filter (fun k => !k.isMb) ++ RefKind.RawPtr t :: y,
                RefKind.RawPtr t, SB.find?_insert_eq _ _ _, by simp, by simpa using h_item_tag⟩

theorem sb_ref_find_old_item_of_ok
  {ap ap' : AccessPerms} {addr tag newTag : Word} {kind : RefOpKind}
  (h_ref : sb_ref ap addr tag kind = (SBResult.Ok ap', newTag)) :
  ∃ stack item,
    ap'.StackMap.find? addr = some stack ∧
    item ∈ stack ∧
    item.tag = tag := by
  cases kind with
  | Shared =>
      unfold sb_ref at h_ref
      cases h_parent : sb_read ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          obtain ⟨parentStack, item, h_parent_find, h_item_mem, h_item_tag⟩ :=
            sb_read_find_item_of_ok h_parent
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨rfl, rfl⟩
              have h_find_parent : ap_parent.StackMap.find? addr = some stack := by
                simpa using h_find
              have h_stack_eq : parentStack = stack := by
                exact Option.some.inj (h_parent_find.symm.trans h_find_parent)
              subst parentStack
              exact ⟨RefKind.Ref ap_parent.NextTag :: stack, item,
                SB.find?_insert_eq _ _ _, by simp [h_item_mem], h_item_tag⟩
  | Mut =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          obtain ⟨parentStack, item, h_parent_find, h_item_mem, h_item_tag⟩ :=
            sb_use_mb_find_item_of_ok h_parent
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨rfl, rfl⟩
              have h_find_parent : ap_parent.StackMap.find? addr = some stack := by
                simpa using h_find
              have h_stack_eq : parentStack = stack := by
                exact Option.some.inj (h_parent_find.symm.trans h_find_parent)
              subst parentStack
              exact ⟨RefKind.MutRef ap_parent.NextTag :: stack, item,
                SB.find?_insert_eq _ _ _, by simp [h_item_mem], h_item_tag⟩
  | Raw =>
      unfold sb_ref at h_ref
      cases h_parent : sb_use_mb ap addr tag with
      | Err msg =>
          simp [h_parent] at h_ref
      | Ok ap_parent =>
          obtain ⟨parentStack, item, h_parent_find, h_item_mem, h_item_tag⟩ :=
            sb_use_mb_find_item_of_ok h_parent
          cases h_find : { ap_parent with NextTag := ap_parent.NextTag + 1 }.StackMap.find? addr with
          | none =>
              simp [h_parent, freshTag, h_find] at h_ref
          | some stack =>
              simp [h_parent, freshTag, h_find] at h_ref
              rcases h_ref with ⟨rfl, rfl⟩
              have h_find_parent : ap_parent.StackMap.find? addr = some stack := by
                simpa using h_find
              have h_stack_eq : parentStack = stack := by
                exact Option.some.inj (h_parent_find.symm.trans h_find_parent)
              subst parentStack
              exact ⟨RefKind.RawPtr ap_parent.NextTag :: stack, item,
                SB.find?_insert_eq _ _ _, by simp [h_item_mem], h_item_tag⟩

theorem TagRenameFreshFrom.lt_of_mapped
  {ρt : TagRenameMap}
  {nextTag tag tag_o : Tag}
  (h_fresh : TagRenameFreshFrom ρt nextTag)
  (h_map : ρt tag = some tag_o) :
  tag < nextTag := by
  by_cases h_lt : tag < nextTag
  · exact h_lt
  · exfalso
    have h_none : ρt tag = none := h_fresh tag (Nat.le_of_not_gt h_lt)
    rw [h_map] at h_none
    cases h_none

theorem TagRenameFreshFrom.extendTagRename
  {ρt : TagRenameMap}
  {nextTag freshTag_o : Tag}
  (h_fresh : TagRenameFreshFrom ρt nextTag) :
  TagRenameFreshFrom (extendTagRenameMap ρt nextTag freshTag_o) (nextTag + 1) := by
  intro tag h_ge
  have h_ne : tag ≠ nextTag := by
    intro h_eq
    have h_bad : nextTag + 1 ≤ nextTag := by
      simpa [h_eq] using h_ge
    exact (Nat.not_succ_le_self nextTag) h_bad
  have h_old_ge : nextTag ≤ tag :=
    Nat.le_trans (Nat.le_succ nextTag) h_ge
  simpa [extendTagRenameMap, h_ne] using h_fresh tag h_old_ge

theorem ptrSimOfCtx_extendTagRename_of_fresh
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {env : mirlite.Env}
  {nextTag tag_m tag_o : Tag}
  {freshTag_o : Tag}
  {p : mirlite.Place}
  {base off size : Word}
  (h_ptr : ptrSimOfCtx ρa ρt env p tag_m base off size tag_o)
  (h_fresh : TagRenameFreshFrom ρt nextTag) :
  ptrSimOfCtx ρa (extendTagRenameMap ρt nextTag freshTag_o) env p tag_m base off size tag_o := by
  rcases h_ptr with
    ⟨addr_m, baseLayout, subLayout, pathOff, baseTag,
      h_env, h_path, h_addr, h_off, h_tag, h_size⟩
  have h_tag_lt : tag_m < nextTag := TagRenameFreshFrom.lt_of_mapped h_fresh h_tag
  have h_tag_ne : tag_m ≠ nextTag := Nat.ne_of_lt h_tag_lt
  exact ⟨addr_m, baseLayout, subLayout, pathOff, baseTag,
    h_env, h_path, h_addr, h_off,
    by simpa [extendTagRenameMap, h_tag_ne] using h_tag,
    h_size⟩

theorem ptrSimOfCtx_extend_fresh_of_absent
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {freshBase : Word}
  {freshLayout : LayoutTy}
  {freshAddr_m freshAddr_o : Word}
  {freshTag_m freshTag_o : Tag}
  {p : mirlite.Place}
  {tag_m base off size tag_o : Word}
  (h_sim : StateSim π ρa ρt s_mir s_osea (ptrSimOfCtx ρa ρt s_mir.env))
  (h_absent : ∀ base, π.lookup base = none → s_mir.env.lookup base = none)
  (h_lookup_none : π.lookup freshBase = none)
  (h_source_below : SourceBlocksBelowAddrStart π s_mir)
  (h_fresh_addr : freshAddr_m = s_mir.mem.addrStart)
  (h_tag_fresh : TagRenameFreshFrom ρt freshTag_m)
  (h_ptr : ptrSimOfCtx ρa ρt s_mir.env p tag_m base off size tag_o) :
  ptrSimOfCtx
    (extendAddrRenameMap ρa freshAddr_m freshAddr_o)
    (extendTagRenameMap ρt freshTag_m freshTag_o)
    (s_mir.env.insert freshBase (freshAddr_m, layoutToTyVal freshLayout, freshTag_m))
    p tag_m base off size tag_o := by
  rcases h_ptr with
    ⟨addr_m, baseLayout, subLayout, pathOff, baseTag,
      h_env, h_path, h_addr, h_off, h_tag, h_size⟩
  have h_base_ne : p.base ≠ freshBase := by
    intro h_eq
    have h_env_none : s_mir.env.lookup freshBase = none := h_absent freshBase h_lookup_none
    have h_env_some :
        s_mir.env.lookup freshBase = some (addr_m, layoutToTyVal baseLayout, baseTag) := by
      simpa [h_eq] using h_env
    rw [h_env_some] at h_env_none
    cases h_env_none
  have h_lookup_some : ∃ reg layout, π.lookup p.base = some (reg, layout) := by
    cases h_lookup : π.lookup p.base with
    | none =>
        have h_env_none : s_mir.env.lookup p.base = none := h_absent p.base h_lookup
        rw [h_env] at h_env_none
        cases h_env_none
    | some entry =>
        cases entry with
        | mk reg layout =>
        exact ⟨reg, layout, rfl⟩
  rcases h_lookup_some with ⟨reg, layout, h_lookup⟩
  rcases StateSim.place h_sim h_lookup with
    ⟨addr_m', addr_o', tag_m', tag_o', h_place, _h_block⟩
  have h_env_place :
      s_mir.env.lookup p.base = some (addr_m', layoutToTyVal layout, tag_m') :=
    place_runtime_sim.env h_place
  have h_env_eq :
      (addr_m', layoutToTyVal layout, tag_m') =
        (addr_m, layoutToTyVal baseLayout, baseTag) :=
    Option.some.inj (h_env_place.symm.trans h_env)
  have h_addr_eq : addr_m' = addr_m := congrArg Prod.fst h_env_eq
  have h_addr_ne' : addr_m' ≠ freshAddr_m := by
    rw [h_fresh_addr]
    exact Nat.ne_of_lt (SourceBlocksBelowAddrStart.of_place_runtime_sim h_source_below h_place).1
  have h_addr_ne : addr_m ≠ freshAddr_m := by
    simpa [h_addr_eq] using h_addr_ne'
  have h_tag_lt : tag_m < freshTag_m :=
    TagRenameFreshFrom.lt_of_mapped h_tag_fresh h_tag
  have h_tag_ne : tag_m ≠ freshTag_m := Nat.ne_of_lt h_tag_lt
  refine ⟨addr_m, baseLayout, subLayout, pathOff, baseTag, ?_, h_path, ?_, h_off, ?_, h_size⟩
  · rw [env_lookup_insert_ne s_mir.env freshBase p.base
      (freshAddr_m, layoutToTyVal freshLayout, freshTag_m) h_base_ne]
    exact h_env
  · simpa [extendAddrRenameMap, h_addr_ne] using h_addr
  · simpa [extendTagRenameMap, h_tag_ne] using h_tag

theorem absent_env_insert_of_lookup_none
  {π : PlaceMap}
  {s_mir : mirlite.State}
  {freshBase : Word}
  {freshReg : Register}
  {freshLayout : LayoutTy}
  {freshAddr : Word}
  {freshTy : TyVal}
  {freshTag : Tag}
  (h_absent : ∀ base, π.lookup base = none → s_mir.env.lookup base = none) :
  ∀ base,
    ((freshBase, (freshReg, freshLayout)) :: π).lookup base = none →
    (s_mir.env.insert freshBase (freshAddr, freshTy, freshTag)).lookup base = none := by
  intro base h_lookup
  by_cases h_eq : base = freshBase
  · subst base
    have h_some :
        ((freshBase, (freshReg, freshLayout)) :: π).lookup freshBase =
          some (freshReg, freshLayout) := by
      simp [List.lookup]
    rw [h_some] at h_lookup
    cases h_lookup
  · have h_beq : (base == freshBase) = false := by
      simp [h_eq]
    have h_lookup_old : π.lookup base = none := by
      simpa [List.lookup, h_beq] using h_lookup
    rw [env_lookup_insert_ne s_mir.env freshBase base
      (freshAddr, freshTy, freshTag) h_eq]
    exact h_absent base h_lookup_old

def CompilerInv
  (cs0 : CompilerState)
  (prog : mirlite.Prog)
  (ρa : AddrRenameMap)
  (ρt : TagRenameMap)
  (s_mir : mirlite.State)
  (s_osea : oseair.State) : Prop :=
  s_osea.pc = targetPcAt cs0 prog s_mir.pc ∧
  StateSim (csAt cs0 prog s_mir.pc).placeMap ρa ρt s_mir s_osea
    (ptrSimOfCtx ρa ρt s_mir.env) ∧
  TrackedPlaceTagClosure (csAt cs0 prog s_mir.pc).placeMap s_mir ∧
  SourceBlocksBelowAddrStart (csAt cs0 prog s_mir.pc).placeMap s_mir ∧
  TagRenameFreshFrom ρt s_mir.ap.NextTag ∧
  (∀ base, (csAt cs0 prog s_mir.pc).placeMap.lookup base = none →
    s_mir.env.lookup base = none) ∧
  TargetNonInterference ρa s_osea

theorem StateSim.mono_ptr_sim
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {ptr_sim ptr_sim' : PtrSimPred}
  (h_sim : StateSim π ρa ρt s_mir s_osea ptr_sim)
  (h_mono :
    ∀ p tag_m base off size tag_o,
      ptr_sim p tag_m base off size tag_o →
      ptr_sim' p tag_m base off size tag_o) :
  StateSim π ρa ρt s_mir s_osea ptr_sim' := by
  rcases h_sim with ⟨h_sb, h_places, h_disj⟩
  refine ⟨h_sb, ?_, h_disj⟩
  intro base reg layout h_lookup
  rcases h_places base reg layout h_lookup with
    ⟨addr_m, addr_o, tag_m, tag_o, h_ptr, h_block⟩
  exact ⟨addr_m, addr_o, tag_m, tag_o, h_ptr, block_sim_at_mono h_mono h_block⟩

theorem ptrSimOfCtx_extend_fresh_of_live
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {freshBase : Word}
  {freshReg : Register}
  {freshLayout : LayoutTy}
  {freshAddr freshAddr_o : Word}
  {freshTag freshTag_o : Tag}
  {ap2 ap3 : AccessPerms}
  {mem_post : mirlite.Mem}
  {pc_post : Nat}
  {p : mirlite.Place}
  {reg : Register}
  {baseLayout : LayoutTy}
  {baseAddr baseTag off : Word}
  {innerLayout : LayoutTy}
  {q : mirlite.Place}
  {gq : Tag}
  {base off_o size tag_o : Word}
  (h_sim : StateSim π ρa ρt s_mir s_osea (ptrSimOfCtx ρa ρt s_mir.env))
  (h_live :
    TrackedPlaceTagLive ((freshBase, (freshReg, freshLayout)) :: π)
      { s_mir with
        env := s_mir.env.insert freshBase (freshAddr, layoutToTyVal freshLayout, freshTag),
        mem := mem_post,
        ap := ap3,
        pc := pc_post })
  (h_source_below : SourceBlocksBelowAddrStart π s_mir)
  (h_own : sb_own s_mir.ap freshAddr = (SBResult.Ok ap2, freshTag))
  (h_use : sb_use_mb ap2 freshAddr freshTag = SBResult.Ok ap3)
  (h_fresh_addr : freshAddr = s_mir.mem.addrStart)
  (h_fresh_nonempty : 0 < blockSize freshLayout)
  (h_inner_nonempty : 0 < blockSize innerLayout)
  (h_q_base_ne : q.base ≠ freshBase)
  (h_lookup :
    ((freshBase, (freshReg, freshLayout)) :: π).lookup p.base = some (reg, baseLayout))
  (h_path : layoutResolvePath baseLayout p.path = some (off, LayoutTy.PtrL innerLayout))
  (h_env :
    (s_mir.env.insert freshBase (freshAddr, layoutToTyVal freshLayout, freshTag)).lookup p.base =
      some (baseAddr, layoutToTyVal baseLayout, baseTag))
  (h_mem : mem_post.find? (baseAddr + off) = some (mirlite.MemValue.PlaceTag q gq))
  (h_ptr : ptrSimOfCtx ρa ρt s_mir.env q gq base off_o size tag_o) :
  ptrSimOfCtx
    (extendAddrRenameMap ρa freshAddr freshAddr_o)
    (extendTagRenameMap ρt freshTag freshTag_o)
    (s_mir.env.insert freshBase (freshAddr, layoutToTyVal freshLayout, freshTag))
    q gq base off_o size tag_o := by
  obtain ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag, stack, item,
      h_q_lookup, h_q_path, h_q_env, h_stack, h_item_mem, h_item_tag⟩ :=
    h_live p reg baseLayout baseAddr baseTag off innerLayout q gq
      h_lookup h_path h_env h_mem
  have h_q_lookup_old : π.lookup q.base = some (targetReg, targetBaseLayout) := by
    exact place_map_lookup_cons_ne h_q_base_ne h_q_lookup
  have h_q_env_old :
      s_mir.env.lookup q.base = some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag) := by
    rw [env_lookup_insert_ne s_mir.env freshBase q.base
      (freshAddr, layoutToTyVal freshLayout, freshTag) h_q_base_ne] at h_q_env
    exact h_q_env
  rcases StateSim.place h_sim h_q_lookup_old with
    ⟨targetBaseAddr_old, targetBaseAddr_o, targetBaseTag_old, targetBaseTag_o,
      h_q_ptr, _h_q_block⟩
  have h_q_env_eq :
      (targetBaseAddr_old, layoutToTyVal targetBaseLayout, targetBaseTag_old) =
        (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag) := by
    exact Option.some.inj ((place_runtime_sim.env h_q_ptr).symm.trans h_q_env_old)
  have h_target_addr_eq : targetBaseAddr_old = targetBaseAddr := congrArg Prod.fst h_q_env_eq
  have h_q_below := SourceBlocksBelowAddrStart.of_place_runtime_sim h_source_below h_q_ptr
  have h_targetOff_fit :
      targetOff + blockSize innerLayout ≤ blockSize targetBaseLayout :=
    layoutResolvePath_blockSize_le h_q_path
  have h_targetOff_lt : targetOff < blockSize targetBaseLayout := by
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right h_inner_nonempty) h_targetOff_fit
  have h_target_end : targetBaseAddr + blockSize targetBaseLayout ≤ s_mir.mem.addrStart := by
    simpa [h_target_addr_eq] using h_q_below.2
  have h_stack_addr_ne : targetBaseAddr + targetOff ≠ freshAddr := by
    have h_stack_addr_lt : targetBaseAddr + targetOff < s_mir.mem.addrStart := by
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left h_targetOff_lt targetBaseAddr) h_target_end
    rw [h_fresh_addr]
    exact Nat.ne_of_lt h_stack_addr_lt
  have h_valid_pre : SBValid s_mir.ap := (StateSim.sb h_sim).valid_mir
  have h_stack_pre_eq :
      ap3.StackMap.find? (targetBaseAddr + targetOff) =
        s_mir.ap.StackMap.find? (targetBaseAddr + targetOff) := by
    have h_valid_own : SBValid ap2 := sb_own_preserves_valid h_valid_pre h_own
    calc
      ap3.StackMap.find? (targetBaseAddr + targetOff) =
          ap2.StackMap.find? (targetBaseAddr + targetOff) :=
        sb_use_mb_preserves_find_ne h_valid_own h_use h_stack_addr_ne
      _ = s_mir.ap.StackMap.find? (targetBaseAddr + targetOff) :=
        sb_own_preserves_find_ne h_valid_pre h_own h_stack_addr_ne
  have h_stack_pre :
      s_mir.ap.StackMap.find? (targetBaseAddr + targetOff) = some stack := by
    rw [← h_stack_pre_eq]
    exact h_stack
  have h_gq_live : tag_live s_mir.ap gq := by
    have h_item_live : tag_live s_mir.ap item.tag := tag_live_of_find_mem h_stack_pre h_item_mem
    simpa [h_item_tag] using h_item_live
  have h_fresh_tag_eq : freshTag = s_mir.ap.NextTag := sb_own_tag_eq_nextTag h_own
  have h_fresh_tag_not_live : ¬ tag_live s_mir.ap freshTag := by
    simpa [h_fresh_tag_eq] using (freshTag_fresh (ap := s_mir.ap))
  have h_gq_ne : gq ≠ freshTag := by
    intro h_eq
    subst h_eq
    exact h_fresh_tag_not_live h_gq_live
  have h_ptr_elim := ptrSimOfCtx_elim h_ptr h_q_env_old h_q_path
  rcases h_ptr_elim with ⟨h_addr_map, h_off_eq, h_tag_map, h_size_eq⟩
  have h_targetBaseAddr_ne : targetBaseAddr ≠ freshAddr := by
    rw [h_fresh_addr]
    exact Nat.ne_of_lt (by simpa [h_target_addr_eq] using h_q_below.1)
  refine ⟨targetBaseAddr, targetBaseLayout, innerLayout, targetOff, targetBaseTag,
    h_q_env, h_q_path, ?_, h_off_eq, ?_, h_size_eq⟩
  · simpa [extendAddrRenameMap, h_targetBaseAddr_ne] using h_addr_map
  · simpa [extendTagRenameMap, h_gq_ne] using h_tag_map

theorem TrackedPlaceTagClosure.resolve_pointee
  {π : PlaceMap}
  {s_mir : mirlite.State}
  {src : mirlite.Place}
  {srcReg : Register}
  {srcBaseLayout innerLayout : LayoutTy}
  {srcBaseAddr_m srcTag_m srcOff : Word}
  {q : mirlite.Place}
  {gq : Tag}
  {ap_src_read_m : AccessPerms}
  {targetRes : mirlite.PlaceRes}
  (h_closure : TrackedPlaceTagClosure π s_mir)
  (h_lookup : π.lookup src.base = some (srcReg, srcBaseLayout))
  (h_path : layoutResolvePath srcBaseLayout src.path = some (srcOff, LayoutTy.PtrL innerLayout))
  (h_env :
    s_mir.env.lookup src.base =
      some (srcBaseAddr_m, layoutToTyVal srcBaseLayout, srcTag_m))
  (h_ptr_val :
    s_mir.mem.find? (srcBaseAddr_m + srcOff) =
      some (mirlite.MemValue.PlaceTag q gq))
  (h_resolve :
    mirlite.resolveDirectPlace { s_mir with ap := ap_src_read_m } q =
      (mirlite.Result.Ok { s_mir with ap := ap_src_read_m }, targetRes)) :
  ∃ targetReg targetBaseLayout targetOff targetBaseAddr,
    π.lookup q.base = some (targetReg, targetBaseLayout) ∧
    layoutResolvePath targetBaseLayout q.path = some (targetOff, innerLayout) ∧
    s_mir.env.lookup q.base =
      some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetRes.tag) ∧
    targetRes.addr = targetBaseAddr + targetOff ∧
    targetRes.ty = layoutToTyVal innerLayout := by
  obtain ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
      h_q_lookup, h_q_path, h_q_env⟩ :=
    h_closure src srcReg srcBaseLayout srcBaseAddr_m srcTag_m srcOff innerLayout q gq
      h_lookup h_path h_env h_ptr_val
  have h_expected :
      mirlite.resolveDirectPlace { s_mir with ap := ap_src_read_m } q =
        (mirlite.Result.Ok { s_mir with ap := ap_src_read_m },
          { addr := targetBaseAddr + targetOff,
            tag := targetBaseTag,
            ty := layoutToTyVal innerLayout,
            state := { s_mir with ap := ap_src_read_m } }) := by
    simpa using
      (resolveDirectPlace_eq_of_env_lookup
        (state := { s_mir with ap := ap_src_read_m })
        (p := q)
        (addr := targetBaseAddr)
        (tag := targetBaseTag)
        (off := targetOff)
        (baseLayout := targetBaseLayout)
        (subLayout := innerLayout)
        h_q_env h_q_path)
  have h_res_eq :
      targetRes =
        { addr := targetBaseAddr + targetOff,
          tag := targetBaseTag,
          ty := layoutToTyVal innerLayout,
          state := { s_mir with ap := ap_src_read_m } } := by
    have h_pair :
        (mirlite.Result.Ok { s_mir with ap := ap_src_read_m }, targetRes) =
          (mirlite.Result.Ok { s_mir with ap := ap_src_read_m },
            { addr := targetBaseAddr + targetOff,
              tag := targetBaseTag,
              ty := layoutToTyVal innerLayout,
              state := { s_mir with ap := ap_src_read_m } }) := by
      exact h_resolve.symm.trans h_expected
    exact congrArg Prod.snd h_pair
  refine ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_q_lookup
  · exact h_q_path
  · simpa [h_res_eq] using h_q_env
  · simp [h_res_eq]
  · simp [h_res_eq]

theorem mirlite_find_of_readWordSeq_get_placeTag
  {m : mirlite.Mem}
  {addr : Word}
  {n : Nat}
  {i : Nat}
  {q : mirlite.Place}
  {gq : Tag}
  (h_i : i < n)
  (h_get :
    (mirlite.readWordSeq m addr n).get
      ⟨i, by simpa [mirlite_readWordSeq_length] using h_i⟩ =
        mirlite.MemValue.PlaceTag q gq) :
  m.find? (addr + i) = some (mirlite.MemValue.PlaceTag q gq) := by
  induction n generalizing m addr i q gq with
  | zero =>
      cases h_i
  | succ n ih =>
      cases i with
      | zero =>
          cases h_find : m.find? addr with
          | none =>
              simp [mirlite.readWordSeq, h_find] at h_get
          | some v =>
              simp [mirlite.readWordSeq, h_find] at h_get
              cases h_get
              simpa [Nat.add_zero] using h_find
      | succ i =>
          cases h_find : m.find? addr with
          | none =>
              simp [mirlite.readWordSeq, h_find] at h_get
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih (m := m) (addr := addr + 1) (i := i)
                  (q := q) (gq := gq) (Nat.lt_of_succ_lt_succ h_i) h_get
          | some v =>
              simp [mirlite.readWordSeq, h_find] at h_get
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih (m := m) (addr := addr + 1) (i := i)
                  (q := q) (gq := gq) (Nat.lt_of_succ_lt_succ h_i) h_get

theorem TrackedPlaceTagClosure.writeWordSeq_of_nonptr
  {π : PlaceMap}
  {s_mir : mirlite.State}
  {addr : Word}
  {vals : List mirlite.MemValue}
  (h_closure : TrackedPlaceTagClosure π s_mir)
  (h_vals_nonptr :
    ∀ i (h_i : i < vals.length) q gq,
      vals.get ⟨i, h_i⟩ ≠ mirlite.MemValue.PlaceTag q gq) :
  TrackedPlaceTagClosure π { s_mir with mem := mirlite.writeWordSeq s_mir.mem addr vals } := by
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env h_mem
  by_cases h_hit : ∃ i, i < vals.length ∧ baseAddr + off = addr + i
  · rcases h_hit with ⟨i, h_i, h_eq⟩
    have h_find :
        (mirlite.writeWordSeq s_mir.mem addr vals).find? (addr + i) =
          some (vals.get ⟨i, h_i⟩) :=
      mirlite_find_writeWordSeq_at (m := s_mir.mem) (addr := addr) (vals := vals) h_i
    rw [← h_eq] at h_find
    rw [h_find] at h_mem
    have h_val_eq : vals.get ⟨i, h_i⟩ = mirlite.MemValue.PlaceTag q gq := by
      simpa using Option.some.inj h_mem
    exact False.elim (h_vals_nonptr i h_i q gq h_val_eq)
  · have h_keep :
      (mirlite.writeWordSeq s_mir.mem addr vals).find? (baseAddr + off) =
        s_mir.mem.find? (baseAddr + off) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro i h_i h_eq
      exact h_hit ⟨i, h_i, h_eq⟩
    rw [h_keep] at h_mem
    exact h_closure p reg baseLayout baseAddr baseTag off innerLayout q gq
      h_lookup h_path h_env h_mem

theorem TrackedPlaceTagLive.writeWordSeq_of_nonptr
  {π : PlaceMap}
  {s_mir : mirlite.State}
  {addr : Word}
  {vals : List mirlite.MemValue}
  (h_live : TrackedPlaceTagLive π s_mir)
  (h_vals_nonptr :
    ∀ i (h_i : i < vals.length) q gq,
      vals.get ⟨i, h_i⟩ ≠ mirlite.MemValue.PlaceTag q gq) :
  TrackedPlaceTagLive π { s_mir with mem := mirlite.writeWordSeq s_mir.mem addr vals } := by
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env h_mem
  by_cases h_hit : ∃ i, i < vals.length ∧ baseAddr + off = addr + i
  · rcases h_hit with ⟨i, h_i, h_eq⟩
    have h_find :
        (mirlite.writeWordSeq s_mir.mem addr vals).find? (addr + i) =
          some (vals.get ⟨i, h_i⟩) :=
      mirlite_find_writeWordSeq_at (m := s_mir.mem) (addr := addr) (vals := vals) h_i
    rw [← h_eq] at h_find
    rw [h_find] at h_mem
    have h_val_eq : vals.get ⟨i, h_i⟩ = mirlite.MemValue.PlaceTag q gq := by
      simpa using Option.some.inj h_mem
    exact False.elim (h_vals_nonptr i h_i q gq h_val_eq)
  · have h_keep :
      (mirlite.writeWordSeq s_mir.mem addr vals).find? (baseAddr + off) =
        s_mir.mem.find? (baseAddr + off) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro i h_i h_eq
      exact h_hit ⟨i, h_i, h_eq⟩
    rw [h_keep] at h_mem
    exact h_live p reg baseLayout baseAddr baseTag off innerLayout q gq
      h_lookup h_path h_env h_mem

theorem TrackedPlaceTagClosure.of_env_mem_mMap_eq
  {π : PlaceMap}
  {s_mir s_mir' : mirlite.State}
  (h_closure : TrackedPlaceTagClosure π s_mir)
  (h_env : s_mir'.env = s_mir.env)
  (h_mem : s_mir'.mem.mMap = s_mir.mem.mMap) :
  TrackedPlaceTagClosure π s_mir' := by
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env' h_mem'
  have h_find_eq :
      s_mir'.mem.find? (baseAddr + off) = s_mir.mem.find? (baseAddr + off) := by
    simp [mirlite.Mem.find?, h_mem]
  have h_env'' :
      s_mir.env.lookup p.base = some (baseAddr, layoutToTyVal baseLayout, baseTag) := by
    simpa [h_env] using h_env'
  have h_mem'' :
      s_mir.mem.find? (baseAddr + off) = some (mirlite.MemValue.PlaceTag q gq) := by
    simpa [h_find_eq] using h_mem'
  rcases h_closure p reg baseLayout baseAddr baseTag off innerLayout q gq
      h_lookup h_path h_env'' h_mem'' with
    ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
      h_q_lookup, h_q_path, h_q_env⟩
  refine ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
    h_q_lookup, h_q_path, ?_⟩
  simpa [h_env] using h_q_env

theorem TrackedPlaceTagLive.of_env_mem_mMap_eq
  {π : PlaceMap}
  {s_mir s_mir' : mirlite.State}
  (h_live : TrackedPlaceTagLive π s_mir)
  (h_env : s_mir'.env = s_mir.env)
  (h_mem : s_mir'.mem.mMap = s_mir.mem.mMap)
  (h_stack : s_mir'.ap.StackMap = s_mir.ap.StackMap) :
  TrackedPlaceTagLive π s_mir' := by
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env' h_mem'
  have h_find_eq :
      s_mir'.mem.find? (baseAddr + off) = s_mir.mem.find? (baseAddr + off) := by
    simp [mirlite.Mem.find?, h_mem]
  have h_env'' :
      s_mir.env.lookup p.base = some (baseAddr, layoutToTyVal baseLayout, baseTag) := by
    simpa [h_env] using h_env'
  have h_mem'' :
      s_mir.mem.find? (baseAddr + off) = some (mirlite.MemValue.PlaceTag q gq) := by
    simpa [h_find_eq] using h_mem'
  rcases h_live p reg baseLayout baseAddr baseTag off innerLayout q gq
      h_lookup h_path h_env'' h_mem'' with
    ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag, stack, item,
      h_q_lookup, h_q_path, h_q_env, h_q_stack, h_item_mem, h_item_tag⟩
  refine ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag, stack, item,
    h_q_lookup, h_q_path, ?_, ?_, h_item_mem, h_item_tag⟩
  · simpa [h_env] using h_q_env
  · simpa [h_stack] using h_q_stack

theorem TrackedPlaceTagClosure.copy_from_place_to_base
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  {src : mirlite.Place}
  {srcReg : Register}
  {srcBaseLayout dstLayout : LayoutTy}
  {srcOff : Word}
  {srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o : Word}
  {dstBase : Word}
  {dstReg : Register}
  {dstBaseAddr dstBaseAddr_o dstBaseTag dstBaseTag_o : Word}
  (h_sim : StateSim π ρa ρt s_mir s_osea ptr_sim)
  (h_closure : TrackedPlaceTagClosure π s_mir)
  (h_src_lookup : π.lookup src.base = some (srcReg, srcBaseLayout))
  (h_src_path : layoutResolvePath srcBaseLayout src.path = some (srcOff, dstLayout))
  (h_src_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      src.base srcReg srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o srcBaseLayout)
  (h_dst_lookup : π.lookup dstBase = some (dstReg, dstLayout))
  (h_dst_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      dstBase dstReg dstBaseAddr dstBaseAddr_o dstBaseTag dstBaseTag_o dstLayout) :
  TrackedPlaceTagClosure π
    { s_mir with
      mem :=
        mirlite.writeWordSeq s_mir.mem dstBaseAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)) } := by
  classical
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env h_mem
  rcases StateSim.place h_sim h_lookup with
    ⟨baseAddr_old, baseAddr_old_o, baseTag_old, baseTag_old_o, h_ptr_old, _h_block_old⟩
  have h_env_ptr_eq :
      (baseAddr_old, layoutToTyVal baseLayout, baseTag_old) =
        (baseAddr, layoutToTyVal baseLayout, baseTag) := by
    exact Option.some.inj ((place_runtime_sim.env h_ptr_old).symm.trans h_env)
  have h_addr_eq : baseAddr_old = baseAddr := congrArg Prod.fst h_env_ptr_eq
  have _h_tag_eq : baseTag_old = baseTag := congrArg (fun triple => triple.2.2) h_env_ptr_eq
  by_cases h_base_eq : p.base = dstBase
  · subst h_base_eq
    have h_lookup_eq : (reg, baseLayout) = (dstReg, dstLayout) := by
      exact Option.some.inj (h_lookup.symm.trans h_dst_lookup)
    rcases h_lookup_eq with ⟨rfl, rfl⟩
    have h_env_eq :
        (baseAddr, layoutToTyVal dstLayout, baseTag) =
          (dstBaseAddr, layoutToTyVal dstLayout, dstBaseTag) := by
      exact Option.some.inj (h_env.symm.trans (place_runtime_sim.env h_dst_ptr))
    rcases h_env_eq with ⟨rfl, _h_ty_eq, rfl⟩
    have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize dstLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize dstLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa using h_off_le)
    have h_find :
        (mirlite.writeWordSeq s_mir.mem dstBaseAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
          (dstBaseAddr + off) =
            some ((mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)).get
              ⟨off, by simpa [mirlite_readWordSeq_length] using h_off_lt⟩) :=
      mirlite_find_writeWordSeq_at
        (m := s_mir.mem)
        (addr := dstBaseAddr)
        (vals := mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))
        (i := off)
        (by simpa [mirlite_readWordSeq_length] using h_off_lt)
    rw [h_find] at h_mem
    have h_src_mem :
        s_mir.mem.find? (srcBaseAddr + srcOff + off) = some (mirlite.MemValue.PlaceTag q gq) := by
      have h_get :
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)).get
            ⟨off, by simpa [mirlite_readWordSeq_length] using h_off_lt⟩ =
              mirlite.MemValue.PlaceTag q gq := by
        exact Option.some.inj h_mem
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (mirlite_find_of_readWordSeq_get_placeTag
          (m := s_mir.mem)
          (addr := srcBaseAddr + srcOff)
          (n := blockSize dstLayout)
          (i := off)
          (q := q)
          (gq := gq)
          h_off_lt h_get)
    have h_src_env :
        s_mir.env.lookup src.base =
          some (srcBaseAddr, layoutToTyVal srcBaseLayout, srcBaseTag) :=
      place_runtime_sim.env h_src_ptr
    have h_src_full_path :
        layoutResolvePath srcBaseLayout (src.path ++ p.path) =
          some (srcOff + off, LayoutTy.PtrL innerLayout) :=
      layoutResolvePath_append h_src_path h_path
    have h_src_mem' :
        s_mir.mem.find? (srcBaseAddr + (srcOff + off)) = some (mirlite.MemValue.PlaceTag q gq) := by
      simpa [Nat.add_assoc] using h_src_mem
    exact h_closure
      { base := src.base, path := src.path ++ p.path }
      srcReg srcBaseLayout srcBaseAddr srcBaseTag (srcOff + off) innerLayout q gq
      h_src_lookup h_src_full_path h_src_env h_src_mem'
  · have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa using h_off_le)
    have h_base_ne : p.base ≠ dstBase := h_base_eq
    have h_disj :=
      StateSim.disjoint h_sim h_lookup h_dst_lookup h_base_ne h_ptr_old h_dst_ptr
    have h_keep :
        (mirlite.writeWordSeq s_mir.mem dstBaseAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
          (baseAddr + off) =
            s_mir.mem.find? (baseAddr + off) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro i h_i h_eq
      have h_i' : i < blockSize dstLayout := by
        simpa [mirlite_readWordSeq_length] using h_i
      exact h_disj.1 off h_off_lt i h_i' (by simpa [h_addr_eq] using h_eq)
    rw [h_keep] at h_mem
    exact h_closure p reg baseLayout baseAddr baseTag off innerLayout q gq
      h_lookup h_path h_env h_mem

theorem TrackedPlaceTagLive.copy_from_place_to_base
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  {src : mirlite.Place}
  {srcReg : Register}
  {srcBaseLayout dstLayout : LayoutTy}
  {srcOff : Word}
  {srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o : Word}
  {dstBase : Word}
  {dstReg : Register}
  {dstBaseAddr dstBaseAddr_o dstBaseTag dstBaseTag_o : Word}
  (h_sim : StateSim π ρa ρt s_mir s_osea ptr_sim)
  (h_live : TrackedPlaceTagLive π s_mir)
  (h_src_lookup : π.lookup src.base = some (srcReg, srcBaseLayout))
  (h_src_path : layoutResolvePath srcBaseLayout src.path = some (srcOff, dstLayout))
  (h_src_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      src.base srcReg srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o srcBaseLayout)
  (h_dst_lookup : π.lookup dstBase = some (dstReg, dstLayout))
  (h_dst_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      dstBase dstReg dstBaseAddr dstBaseAddr_o dstBaseTag dstBaseTag_o dstLayout) :
  TrackedPlaceTagLive π
    { s_mir with
      mem :=
        mirlite.writeWordSeq s_mir.mem dstBaseAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)) } := by
  classical
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env h_mem
  rcases StateSim.place h_sim h_lookup with
    ⟨baseAddr_old, baseAddr_old_o, baseTag_old, baseTag_old_o, h_ptr_old, _h_block_old⟩
  have h_env_ptr_eq :
      (baseAddr_old, layoutToTyVal baseLayout, baseTag_old) =
        (baseAddr, layoutToTyVal baseLayout, baseTag) := by
    exact Option.some.inj ((place_runtime_sim.env h_ptr_old).symm.trans h_env)
  have h_addr_eq : baseAddr_old = baseAddr := congrArg Prod.fst h_env_ptr_eq
  have _h_tag_eq : baseTag_old = baseTag := congrArg (fun triple => triple.2.2) h_env_ptr_eq
  by_cases h_base_eq : p.base = dstBase
  · subst h_base_eq
    have h_lookup_eq : (reg, baseLayout) = (dstReg, dstLayout) := by
      exact Option.some.inj (h_lookup.symm.trans h_dst_lookup)
    rcases h_lookup_eq with ⟨rfl, rfl⟩
    have h_env_eq :
        (baseAddr, layoutToTyVal dstLayout, baseTag) =
          (dstBaseAddr, layoutToTyVal dstLayout, dstBaseTag) := by
      exact Option.some.inj (h_env.symm.trans (place_runtime_sim.env h_dst_ptr))
    rcases h_env_eq with ⟨rfl, _h_ty_eq, rfl⟩
    have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize dstLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize dstLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa using h_off_le)
    have h_find :
        (mirlite.writeWordSeq s_mir.mem dstBaseAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
          (dstBaseAddr + off) =
            some ((mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)).get
              ⟨off, by simpa [mirlite_readWordSeq_length] using h_off_lt⟩) :=
      mirlite_find_writeWordSeq_at
        (m := s_mir.mem)
        (addr := dstBaseAddr)
        (vals := mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))
        (i := off)
        (by simpa [mirlite_readWordSeq_length] using h_off_lt)
    rw [h_find] at h_mem
    have h_src_mem :
        s_mir.mem.find? (srcBaseAddr + srcOff + off) = some (mirlite.MemValue.PlaceTag q gq) := by
      have h_get :
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)).get
            ⟨off, by simpa [mirlite_readWordSeq_length] using h_off_lt⟩ =
              mirlite.MemValue.PlaceTag q gq := by
        exact Option.some.inj h_mem
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (mirlite_find_of_readWordSeq_get_placeTag
          (m := s_mir.mem)
          (addr := srcBaseAddr + srcOff)
          (n := blockSize dstLayout)
          (i := off)
          (q := q)
          (gq := gq)
          h_off_lt h_get)
    have h_src_env :
        s_mir.env.lookup src.base =
          some (srcBaseAddr, layoutToTyVal srcBaseLayout, srcBaseTag) :=
      place_runtime_sim.env h_src_ptr
    have h_src_full_path :
        layoutResolvePath srcBaseLayout (src.path ++ p.path) =
          some (srcOff + off, LayoutTy.PtrL innerLayout) :=
      layoutResolvePath_append h_src_path h_path
    have h_src_mem' :
        s_mir.mem.find? (srcBaseAddr + (srcOff + off)) = some (mirlite.MemValue.PlaceTag q gq) := by
      simpa [Nat.add_assoc] using h_src_mem
    exact h_live
      { base := src.base, path := src.path ++ p.path }
      srcReg srcBaseLayout srcBaseAddr srcBaseTag (srcOff + off) innerLayout q gq
      h_src_lookup h_src_full_path h_src_env h_src_mem'
  · have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa using h_off_le)
    have h_base_ne : p.base ≠ dstBase := h_base_eq
    have h_disj :=
      StateSim.disjoint h_sim h_lookup h_dst_lookup h_base_ne h_ptr_old h_dst_ptr
    have h_keep :
        (mirlite.writeWordSeq s_mir.mem dstBaseAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
          (baseAddr + off) =
            s_mir.mem.find? (baseAddr + off) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro i h_i h_eq
      have h_i' : i < blockSize dstLayout := by
        simpa [mirlite_readWordSeq_length] using h_i
      exact h_disj.1 off h_off_lt i h_i' (by simpa [h_addr_eq] using h_eq)
    rw [h_keep] at h_mem
    exact h_live p reg baseLayout baseAddr baseTag off innerLayout q gq
      h_lookup h_path h_env h_mem

theorem TrackedPlaceTagClosure.copy_from_place_to_projected
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  {src dst : mirlite.Place}
  {srcReg dstReg : Register}
  {srcBaseLayout dstBaseLayout dstLayout : LayoutTy}
  {srcOff dstOff : Word}
  {srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o : Word}
  {dstBaseAddr dstBaseAddr_o dstBaseTag dstBaseTag_o : Word}
  (h_sim : StateSim π ρa ρt s_mir s_osea ptr_sim)
  (h_closure : TrackedPlaceTagClosure π s_mir)
  (h_src_lookup : π.lookup src.base = some (srcReg, srcBaseLayout))
  (h_src_path : layoutResolvePath srcBaseLayout src.path = some (srcOff, dstLayout))
  (h_src_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      src.base srcReg srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o srcBaseLayout)
  (h_dst_lookup : π.lookup dst.base = some (dstReg, dstBaseLayout))
  (h_dst_path : layoutResolvePath dstBaseLayout dst.path = some (dstOff, dstLayout))
  (h_dst_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      dst.base dstReg dstBaseAddr dstBaseAddr_o dstBaseTag dstBaseTag_o dstBaseLayout) :
  TrackedPlaceTagClosure π
    { s_mir with
      mem :=
        mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)) } := by
  classical
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env h_mem
  rcases StateSim.place h_sim h_lookup with
    ⟨baseAddr_old, baseAddr_old_o, baseTag_old, baseTag_old_o, h_ptr_old, _h_block_old⟩
  have h_env_ptr_eq :
      (baseAddr_old, layoutToTyVal baseLayout, baseTag_old) =
        (baseAddr, layoutToTyVal baseLayout, baseTag) := by
    exact Option.some.inj ((place_runtime_sim.env h_ptr_old).symm.trans h_env)
  have h_addr_eq : baseAddr_old = baseAddr := congrArg Prod.fst h_env_ptr_eq
  by_cases h_base_eq : p.base = dst.base
  · have h_lookup_dst : π.lookup dst.base = some (reg, baseLayout) := by
      simpa [h_base_eq] using h_lookup
    have h_lookup_eq : (reg, baseLayout) = (dstReg, dstBaseLayout) := by
      exact Option.some.inj (h_lookup_dst.symm.trans h_dst_lookup)
    rcases h_lookup_eq with ⟨rfl, rfl⟩
    have h_env_dst :
        s_mir.env.lookup dst.base = some (baseAddr, layoutToTyVal dstBaseLayout, baseTag) := by
      simpa [h_base_eq] using h_env
    have h_env_eq :
        (baseAddr, layoutToTyVal dstBaseLayout, baseTag) =
          (dstBaseAddr, layoutToTyVal dstBaseLayout, dstBaseTag) := by
      exact Option.some.inj (h_env_dst.symm.trans (place_runtime_sim.env h_dst_ptr))
    rcases h_env_eq with ⟨rfl, _h_ty_eq, rfl⟩
    by_cases h_hit : ∃ i, i < blockSize dstLayout ∧ off = dstOff + i
    · rcases h_hit with ⟨i, h_i, h_off_eq⟩
      have h_addr_hit : dstBaseAddr + off = (dstBaseAddr + dstOff) + i := by
        simp [h_off_eq, Nat.add_left_comm, Nat.add_comm]
      have h_find :
          (mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
            (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
            ((dstBaseAddr + dstOff) + i) =
              some ((mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)).get
                ⟨i, by simpa [mirlite_readWordSeq_length] using h_i⟩) :=
        mirlite_find_writeWordSeq_at
          (m := s_mir.mem)
          (addr := dstBaseAddr + dstOff)
          (vals := mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))
          (i := i)
          (by simpa [mirlite_readWordSeq_length] using h_i)
      rw [h_addr_hit] at h_mem
      rw [h_find] at h_mem
      have h_src_mem :
          s_mir.mem.find? (srcBaseAddr + srcOff + i) = some (mirlite.MemValue.PlaceTag q gq) := by
        have h_get :
            (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)).get
              ⟨i, by simpa [mirlite_readWordSeq_length] using h_i⟩ =
                mirlite.MemValue.PlaceTag q gq := by
          exact Option.some.inj h_mem
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (mirlite_find_of_readWordSeq_get_placeTag
            (m := s_mir.mem)
            (addr := srcBaseAddr + srcOff)
            (n := blockSize dstLayout)
            (i := i)
            (q := q)
            (gq := gq)
            h_i h_get)
      have h_src_env :
          s_mir.env.lookup src.base =
            some (srcBaseAddr, layoutToTyVal srcBaseLayout, srcBaseTag) :=
        place_runtime_sim.env h_src_ptr
      have h_path' :
          layoutResolvePath dstBaseLayout p.path = some (dstOff + i, LayoutTy.PtrL innerLayout) := by
        simpa [h_off_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_path
      have h_i_fit : i + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize dstLayout := by
        simpa [blockSize] using Nat.succ_le_of_lt h_i
      obtain ⟨path₂, h_p_path, h_suffix_path⟩ :=
        layoutResolvePath_suffix_ptr h_dst_path h_path' h_i_fit
      have h_src_full_path :
          layoutResolvePath srcBaseLayout (src.path ++ path₂) =
            some (srcOff + i, LayoutTy.PtrL innerLayout) :=
        layoutResolvePath_append h_src_path h_suffix_path
      have h_src_mem' :
          s_mir.mem.find? (srcBaseAddr + (srcOff + i)) = some (mirlite.MemValue.PlaceTag q gq) := by
        simpa [Nat.add_assoc] using h_src_mem
      exact h_closure
        { base := src.base, path := src.path ++ path₂ }
        srcReg srcBaseLayout srcBaseAddr srcBaseTag (srcOff + i) innerLayout q gq
        h_src_lookup h_src_full_path h_src_env h_src_mem'
    · have h_keep :
        (mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
          (dstBaseAddr + off) = s_mir.mem.find? (dstBaseAddr + off) := by
        apply mirlite_find_writeWordSeq_of_ne
        intro i h_i h_eq
        have h_i' : i < blockSize dstLayout := by
          simpa [mirlite_readWordSeq_length] using h_i
        have h_eq' : off = dstOff + i := by
          have h_eq'' : dstBaseAddr + off = dstBaseAddr + (dstOff + i) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_eq
          exact Nat.add_left_cancel h_eq''
        exact h_hit ⟨i, h_i', h_eq'⟩
      rw [h_keep] at h_mem
      obtain ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
          h_q_lookup, h_q_path, h_q_env⟩ :=
        h_closure p dstReg dstBaseLayout dstBaseAddr dstBaseTag off innerLayout q gq
          h_lookup h_path h_env h_mem
      exact ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
        h_q_lookup, h_q_path, by simpa using h_q_env⟩
  · have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_off_le)
    have h_dst_fit : dstOff + blockSize dstLayout ≤ blockSize dstBaseLayout :=
      layoutResolvePath_blockSize_le h_dst_path
    have h_base_ne : p.base ≠ dst.base := h_base_eq
    have h_disj :=
      StateSim.disjoint h_sim h_lookup h_dst_lookup h_base_ne h_ptr_old h_dst_ptr
    have h_keep :
        (mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
          (baseAddr + off) = s_mir.mem.find? (baseAddr + off) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro i h_i h_eq
      have h_i' : i < blockSize dstLayout := by
        simpa [mirlite_readWordSeq_length] using h_i
      have h_j_lt : dstOff + i < blockSize dstBaseLayout := by
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left h_i' dstOff) h_dst_fit
      have h_eq' : baseAddr_old + off = dstBaseAddr + (dstOff + i) := by
        simpa [h_addr_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_eq
      exact h_disj.1 off h_off_lt (dstOff + i) h_j_lt h_eq'
    rw [h_keep] at h_mem
    obtain ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
        h_q_lookup, h_q_path, h_q_env⟩ :=
      h_closure p reg baseLayout baseAddr baseTag off innerLayout q gq
        h_lookup h_path h_env h_mem
    exact ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
      h_q_lookup, h_q_path, by simpa using h_q_env⟩

theorem TrackedPlaceTagLive.copy_from_place_to_projected
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  {src dst : mirlite.Place}
  {srcReg dstReg : Register}
  {srcBaseLayout dstBaseLayout dstLayout : LayoutTy}
  {srcOff dstOff : Word}
  {srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o : Word}
  {dstBaseAddr dstBaseAddr_o dstBaseTag dstBaseTag_o : Word}
  (h_sim : StateSim π ρa ρt s_mir s_osea ptr_sim)
  (h_live : TrackedPlaceTagLive π s_mir)
  (h_src_lookup : π.lookup src.base = some (srcReg, srcBaseLayout))
  (h_src_path : layoutResolvePath srcBaseLayout src.path = some (srcOff, dstLayout))
  (h_src_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      src.base srcReg srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o srcBaseLayout)
  (h_dst_lookup : π.lookup dst.base = some (dstReg, dstBaseLayout))
  (h_dst_path : layoutResolvePath dstBaseLayout dst.path = some (dstOff, dstLayout))
  (h_dst_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      dst.base dstReg dstBaseAddr dstBaseAddr_o dstBaseTag dstBaseTag_o dstBaseLayout) :
  TrackedPlaceTagLive π
    { s_mir with
      mem :=
        mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)) } := by
  classical
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env h_mem
  rcases StateSim.place h_sim h_lookup with
    ⟨baseAddr_old, baseAddr_old_o, baseTag_old, baseTag_old_o, h_ptr_old, _h_block_old⟩
  have h_env_ptr_eq :
      (baseAddr_old, layoutToTyVal baseLayout, baseTag_old) =
        (baseAddr, layoutToTyVal baseLayout, baseTag) := by
    exact Option.some.inj ((place_runtime_sim.env h_ptr_old).symm.trans h_env)
  have h_addr_eq : baseAddr_old = baseAddr := congrArg Prod.fst h_env_ptr_eq
  by_cases h_base_eq : p.base = dst.base
  · have h_lookup_dst : π.lookup dst.base = some (reg, baseLayout) := by
      simpa [h_base_eq] using h_lookup
    have h_lookup_eq : (reg, baseLayout) = (dstReg, dstBaseLayout) := by
      exact Option.some.inj (h_lookup_dst.symm.trans h_dst_lookup)
    rcases h_lookup_eq with ⟨rfl, rfl⟩
    have h_env_dst :
        s_mir.env.lookup dst.base = some (baseAddr, layoutToTyVal dstBaseLayout, baseTag) := by
      simpa [h_base_eq] using h_env
    have h_env_eq :
        (baseAddr, layoutToTyVal dstBaseLayout, baseTag) =
          (dstBaseAddr, layoutToTyVal dstBaseLayout, dstBaseTag) := by
      exact Option.some.inj (h_env_dst.symm.trans (place_runtime_sim.env h_dst_ptr))
    rcases h_env_eq with ⟨rfl, _h_ty_eq, rfl⟩
    by_cases h_hit : ∃ i, i < blockSize dstLayout ∧ off = dstOff + i
    · rcases h_hit with ⟨i, h_i, h_off_eq⟩
      have h_addr_hit : dstBaseAddr + off = (dstBaseAddr + dstOff) + i := by
        simp [h_off_eq, Nat.add_left_comm, Nat.add_comm]
      have h_find :
          (mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
            (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
            ((dstBaseAddr + dstOff) + i) =
              some ((mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)).get
                ⟨i, by simpa [mirlite_readWordSeq_length] using h_i⟩) :=
        mirlite_find_writeWordSeq_at
          (m := s_mir.mem)
          (addr := dstBaseAddr + dstOff)
          (vals := mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))
          (i := i)
          (by simpa [mirlite_readWordSeq_length] using h_i)
      rw [h_addr_hit] at h_mem
      rw [h_find] at h_mem
      have h_src_mem :
          s_mir.mem.find? (srcBaseAddr + srcOff + i) = some (mirlite.MemValue.PlaceTag q gq) := by
        have h_get :
            (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)).get
              ⟨i, by simpa [mirlite_readWordSeq_length] using h_i⟩ =
                mirlite.MemValue.PlaceTag q gq := by
          exact Option.some.inj h_mem
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (mirlite_find_of_readWordSeq_get_placeTag
            (m := s_mir.mem)
            (addr := srcBaseAddr + srcOff)
            (n := blockSize dstLayout)
            (i := i)
            (q := q)
            (gq := gq)
            h_i h_get)
      have h_src_env :
          s_mir.env.lookup src.base =
            some (srcBaseAddr, layoutToTyVal srcBaseLayout, srcBaseTag) :=
        place_runtime_sim.env h_src_ptr
      have h_path' :
          layoutResolvePath dstBaseLayout p.path = some (dstOff + i, LayoutTy.PtrL innerLayout) := by
        simpa [h_off_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_path
      have h_i_fit : i + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize dstLayout := by
        simpa [blockSize] using Nat.succ_le_of_lt h_i
      obtain ⟨path₂, h_p_path, h_suffix_path⟩ :=
        layoutResolvePath_suffix_ptr h_dst_path h_path' h_i_fit
      have h_src_full_path :
          layoutResolvePath srcBaseLayout (src.path ++ path₂) =
            some (srcOff + i, LayoutTy.PtrL innerLayout) :=
        layoutResolvePath_append h_src_path h_suffix_path
      have h_src_mem' :
          s_mir.mem.find? (srcBaseAddr + (srcOff + i)) = some (mirlite.MemValue.PlaceTag q gq) := by
        simpa [Nat.add_assoc] using h_src_mem
      exact h_live
        { base := src.base, path := src.path ++ path₂ }
        srcReg srcBaseLayout srcBaseAddr srcBaseTag (srcOff + i) innerLayout q gq
        h_src_lookup h_src_full_path h_src_env h_src_mem'
    · have h_keep :
        (mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
          (dstBaseAddr + off) = s_mir.mem.find? (dstBaseAddr + off) := by
        apply mirlite_find_writeWordSeq_of_ne
        intro i h_i h_eq
        have h_i' : i < blockSize dstLayout := by
          simpa [mirlite_readWordSeq_length] using h_i
        have h_eq' : off = dstOff + i := by
          have h_eq'' : dstBaseAddr + off = dstBaseAddr + (dstOff + i) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_eq
          exact Nat.add_left_cancel h_eq''
        exact h_hit ⟨i, h_i', h_eq'⟩
      rw [h_keep] at h_mem
      exact h_live p dstReg dstBaseLayout dstBaseAddr dstBaseTag off innerLayout q gq
        h_lookup h_path h_env h_mem
  · have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_off_le)
    have h_dst_fit : dstOff + blockSize dstLayout ≤ blockSize dstBaseLayout :=
      layoutResolvePath_blockSize_le h_dst_path
    have h_base_ne : p.base ≠ dst.base := h_base_eq
    have h_disj :=
      StateSim.disjoint h_sim h_lookup h_dst_lookup h_base_ne h_ptr_old h_dst_ptr
    have h_keep :
        (mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
          (baseAddr + off) = s_mir.mem.find? (baseAddr + off) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro i h_i h_eq
      have h_i' : i < blockSize dstLayout := by
        simpa [mirlite_readWordSeq_length] using h_i
      have h_j_lt : dstOff + i < blockSize dstBaseLayout := by
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left h_i' dstOff) h_dst_fit
      have h_eq' : baseAddr_old + off = dstBaseAddr + (dstOff + i) := by
        simpa [h_addr_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_eq
      exact h_disj.1 off h_off_lt (dstOff + i) h_j_lt h_eq'
    rw [h_keep] at h_mem
    exact h_live p reg baseLayout baseAddr baseTag off innerLayout q gq
      h_lookup h_path h_env h_mem

theorem TrackedPlaceTagClosure.ref_to_projected
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  {src dst : mirlite.Place}
  {srcReg dstReg : Register}
  {srcBaseLayout srcLayout dstBaseLayout : LayoutTy}
  {srcOff dstOff : Word}
  {srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o : Word}
  {dstBaseAddr dstBaseAddr_o dstBaseTag dstBaseTag_o : Word}
  {newTag : Tag}
  (h_sim : StateSim π ρa ρt s_mir s_osea ptr_sim)
  (h_closure : TrackedPlaceTagClosure π s_mir)
  (h_src_lookup : π.lookup src.base = some (srcReg, srcBaseLayout))
  (h_src_path : layoutResolvePath srcBaseLayout src.path = some (srcOff, srcLayout))
  (h_src_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      src.base srcReg srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o srcBaseLayout)
  (h_dst_lookup : π.lookup dst.base = some (dstReg, dstBaseLayout))
  (h_dst_path : layoutResolvePath dstBaseLayout dst.path = some (dstOff, LayoutTy.PtrL srcLayout))
  (h_dst_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      dst.base dstReg dstBaseAddr dstBaseAddr_o dstBaseTag dstBaseTag_o dstBaseLayout) :
  TrackedPlaceTagClosure π
    { s_mir with
      mem :=
        mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
          [mirlite.MemValue.PlaceTag src newTag] } := by
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env h_mem
  rcases StateSim.place h_sim h_lookup with
    ⟨baseAddr_old, baseAddr_old_o, baseTag_old, baseTag_old_o, h_ptr_old, _h_block_old⟩
  have h_env_ptr_eq :
      (baseAddr_old, layoutToTyVal baseLayout, baseTag_old) =
        (baseAddr, layoutToTyVal baseLayout, baseTag) := by
    exact Option.some.inj ((place_runtime_sim.env h_ptr_old).symm.trans h_env)
  have h_addr_eq : baseAddr_old = baseAddr := congrArg Prod.fst h_env_ptr_eq
  by_cases h_base_eq : p.base = dst.base
  · have h_lookup_dst : π.lookup dst.base = some (reg, baseLayout) := by
      simpa [h_base_eq] using h_lookup
    have h_lookup_eq : (reg, baseLayout) = (dstReg, dstBaseLayout) := by
      exact Option.some.inj (h_lookup_dst.symm.trans h_dst_lookup)
    rcases h_lookup_eq with ⟨rfl, rfl⟩
    have h_env_dst :
        s_mir.env.lookup dst.base = some (baseAddr, layoutToTyVal dstBaseLayout, baseTag) := by
      simpa [h_base_eq] using h_env
    have h_env_eq :
        (baseAddr, layoutToTyVal dstBaseLayout, baseTag) =
          (dstBaseAddr, layoutToTyVal dstBaseLayout, dstBaseTag) := by
      exact Option.some.inj (h_env_dst.symm.trans (place_runtime_sim.env h_dst_ptr))
    rcases h_env_eq with ⟨rfl, _h_ty_eq, rfl⟩
    by_cases h_hit : off = dstOff
    · have h_write :
        (mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
          [mirlite.MemValue.PlaceTag src newTag]).find? (dstBaseAddr + dstOff) =
            some (mirlite.MemValue.PlaceTag src newTag) := by
        simpa using
          (mirlite_find_writeWordSeq_at
            (m := s_mir.mem)
            (addr := dstBaseAddr + dstOff)
            (vals := [mirlite.MemValue.PlaceTag src newTag])
            (i := 0)
            (by simp))
      have h_addr_hit : dstBaseAddr + off = dstBaseAddr + dstOff := by
        simp [h_hit]
      rw [h_addr_hit] at h_mem
      rw [h_write] at h_mem
      have h_path_hit :
          layoutResolvePath dstBaseLayout p.path =
            some (dstOff + 0, LayoutTy.PtrL innerLayout) := by
        simpa [h_hit, Nat.add_zero] using h_path
      obtain ⟨path₂, _h_p_path, h_suffix_path⟩ :=
        layoutResolvePath_suffix_ptr h_dst_path h_path_hit (by simp [blockSize, layoutSize])
      have h_ptr_zero := layoutResolvePath_ptr_zero h_suffix_path
      rcases h_ptr_zero with ⟨_h_nil, h_inner_eq⟩
      subst h_inner_eq
      cases h_mem
      exact ⟨srcReg, srcBaseLayout, srcOff, srcBaseAddr, srcBaseTag,
        h_src_lookup, h_src_path, place_runtime_sim.env h_src_ptr⟩
    · have h_keep :
        (mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
          [mirlite.MemValue.PlaceTag src newTag]).find? (dstBaseAddr + off) =
            s_mir.mem.find? (dstBaseAddr + off) := by
        apply mirlite_find_writeWordSeq_of_ne
        intro i h_i h_eq
        have h_i0 : i = 0 := by
          have : i < 1 := by simpa using h_i
          omega
        subst h_i0
        have h_eq' : off = dstOff := by
          have h_eq'' : dstBaseAddr + off = dstBaseAddr + (dstOff + 0) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_eq
          simpa using Nat.add_left_cancel h_eq''
        exact h_hit h_eq'
      rw [h_keep] at h_mem
      exact h_closure p dstReg dstBaseLayout dstBaseAddr dstBaseTag off innerLayout q gq
        h_lookup h_path h_env h_mem
  · have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_off_le)
    have h_dst_fit : dstOff + blockSize (LayoutTy.PtrL srcLayout) ≤ blockSize dstBaseLayout :=
      layoutResolvePath_blockSize_le h_dst_path
    have h_base_ne : p.base ≠ dst.base := h_base_eq
    have h_disj :=
      StateSim.disjoint h_sim h_lookup h_dst_lookup h_base_ne h_ptr_old h_dst_ptr
    have h_keep :
        (mirlite.writeWordSeq s_mir.mem (dstBaseAddr + dstOff)
          [mirlite.MemValue.PlaceTag src newTag]).find? (baseAddr + off) =
            s_mir.mem.find? (baseAddr + off) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro i h_i h_eq
      have h_i0 : i = 0 := by
        have : i < 1 := by simpa using h_i
        omega
      subst h_i0
      have h_dst_off_lt : dstOff < blockSize dstBaseLayout := by
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self dstOff) (by simpa [blockSize] using h_dst_fit)
      have h_eq' : baseAddr_old + off = dstBaseAddr + dstOff := by
        simpa [h_addr_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_eq
      exact h_disj.1 off h_off_lt dstOff h_dst_off_lt h_eq'
    rw [h_keep] at h_mem
    exact h_closure p reg baseLayout baseAddr baseTag off innerLayout q gq
      h_lookup h_path h_env h_mem

theorem TrackedPlaceTagClosure.extend_fresh_nonptr
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  {freshBase : Word}
  {freshReg : Register}
  {freshLayout : LayoutTy}
  {freshAddr freshTag : Word}
  {vals : List mirlite.MemValue}
  (h_sim : StateSim π ρa ρt s_mir s_osea ptr_sim)
  (h_closure : TrackedPlaceTagClosure π s_mir)
  (h_lookup_none : π.lookup freshBase = none)
  (h_vals_len : vals.length = blockSize freshLayout)
  (h_vals_nonptr :
    ∀ i (h_i : i < vals.length) q gq,
      vals.get ⟨i, h_i⟩ ≠ mirlite.MemValue.PlaceTag q gq)
  (h_disj :
    ∀ base reg layout addr_m addr_o tag_m tag_o,
      π.lookup base = some (reg, layout) →
      place_runtime_sim π ρa ρt s_mir s_osea
        base reg addr_m addr_o tag_m tag_o layout →
      blocks_disjoint addr_m (blockSize layout) freshAddr (blockSize freshLayout)) :
  TrackedPlaceTagClosure ((freshBase, (freshReg, freshLayout)) :: π)
    { s_mir with
      env := s_mir.env.insert freshBase (freshAddr, layoutToTyVal freshLayout, freshTag),
      mem := mirlite.writeWordSeq s_mir.mem freshAddr vals } := by
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env h_mem
  by_cases h_base_eq : p.base = freshBase
  · have h_lookup_self :
      ((freshBase, (freshReg, freshLayout)) :: π).lookup freshBase = some (reg, baseLayout) := by
      simpa [h_base_eq] using h_lookup
    have h_lookup_eq : reg = freshReg ∧ baseLayout = freshLayout := by
      exact place_map_lookup_cons_self h_lookup_self
    rcases h_lookup_eq with ⟨rfl, rfl⟩
    have h_env_self :
        ({ s_mir with
          env := s_mir.env.insert freshBase (freshAddr, layoutToTyVal baseLayout, freshTag),
          mem := mirlite.writeWordSeq s_mir.mem freshAddr vals }).env.lookup freshBase =
          some (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      simpa [h_base_eq] using h_env
    have h_env_eq :
        (freshAddr, layoutToTyVal baseLayout, freshTag) =
          (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      exact Option.some.inj <| (env_lookup_insert_eq s_mir.env freshBase
        (freshAddr, layoutToTyVal baseLayout, freshTag)).symm.trans h_env_self
    rcases h_env_eq with ⟨rfl, _h_ty_eq, rfl⟩
    have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_off_le)
    have h_i : off < vals.length := by
      simpa [h_vals_len] using h_off_lt
    have h_find :
        (mirlite.writeWordSeq s_mir.mem freshAddr vals).find? (freshAddr + off) =
          some (vals.get ⟨off, h_i⟩) :=
      mirlite_find_writeWordSeq_at (m := s_mir.mem) (addr := freshAddr) (vals := vals) h_i
    rw [h_find] at h_mem
    have h_val_eq : vals.get ⟨off, h_i⟩ = mirlite.MemValue.PlaceTag q gq := by
      exact Option.some.inj h_mem
    exact False.elim (h_vals_nonptr off h_i q gq h_val_eq)
  · have h_lookup_old : π.lookup p.base = some (reg, baseLayout) :=
      place_map_lookup_cons_ne h_base_eq h_lookup
    have h_env_old :
        s_mir.env.lookup p.base = some (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      have h_keep :=
        env_lookup_insert_ne s_mir.env freshBase p.base
          (freshAddr, layoutToTyVal freshLayout, freshTag) h_base_eq
      rw [h_keep] at h_env
      exact h_env
    rcases StateSim.place h_sim h_lookup_old with
      ⟨baseAddr_old, baseAddr_old_o, baseTag_old, baseTag_old_o, h_ptr_old, _h_block_old⟩
    have h_env_ptr_eq :
        (baseAddr_old, layoutToTyVal baseLayout, baseTag_old) =
          (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      exact Option.some.inj ((place_runtime_sim.env h_ptr_old).symm.trans h_env_old)
    have h_addr_eq : baseAddr_old = baseAddr := congrArg Prod.fst h_env_ptr_eq
    have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_off_le)
    have h_keep :
        (mirlite.writeWordSeq s_mir.mem freshAddr vals).find? (baseAddr + off) =
          s_mir.mem.find? (baseAddr + off) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro i h_i h_eq
      have h_i' : i < blockSize freshLayout := by
        simpa [h_vals_len] using h_i
      have h_eq' : baseAddr_old + off = freshAddr + i := by
        simpa [h_addr_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_eq
      exact h_disj p.base reg baseLayout baseAddr_old baseAddr_old_o baseTag_old baseTag_old_o
        h_lookup_old h_ptr_old off h_off_lt i h_i' h_eq'
    rw [h_keep] at h_mem
    obtain ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
        h_q_lookup, h_q_path, h_q_env⟩ :=
      h_closure p reg baseLayout baseAddr baseTag off innerLayout q gq
        h_lookup_old h_path h_env_old h_mem
    have h_q_base_ne : q.base ≠ freshBase := by
      intro h_eq_q
      have h_some : π.lookup freshBase = some (targetReg, targetBaseLayout) := by
        simpa [h_eq_q] using h_q_lookup
      rw [h_lookup_none] at h_some
      cases h_some
    have h_q_lookup' :
        ((freshBase, (freshReg, freshLayout)) :: π).lookup q.base =
          some (targetReg, targetBaseLayout) := by
      have h_q_beq : (q.base == freshBase) = false := by
        simp [h_q_base_ne]
      simpa [List.lookup, h_q_beq] using h_q_lookup
    have h_q_env' :
        (s_mir.env.insert freshBase (freshAddr, layoutToTyVal freshLayout, freshTag)).lookup q.base =
          some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag) := by
      rw [env_lookup_insert_ne s_mir.env freshBase q.base
        (freshAddr, layoutToTyVal freshLayout, freshTag) h_q_base_ne]
      exact h_q_env
    exact ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
      h_q_lookup',
      h_q_path,
      h_q_env'⟩

theorem TrackedPlaceTagLive.extend_fresh_nonptr
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  {freshBase : Word}
  {freshReg : Register}
  {freshLayout : LayoutTy}
  {freshAddr freshTag : Word}
  {vals : List mirlite.MemValue}
  (h_sim : StateSim π ρa ρt s_mir s_osea ptr_sim)
  (h_live : TrackedPlaceTagLive π s_mir)
  (h_lookup_none : π.lookup freshBase = none)
  (h_vals_len : vals.length = blockSize freshLayout)
  (h_vals_nonptr :
    ∀ i (h_i : i < vals.length) q gq,
      vals.get ⟨i, h_i⟩ ≠ mirlite.MemValue.PlaceTag q gq)
  (h_disj :
    ∀ base reg layout addr_m addr_o tag_m tag_o,
      π.lookup base = some (reg, layout) →
      place_runtime_sim π ρa ρt s_mir s_osea
        base reg addr_m addr_o tag_m tag_o layout →
      blocks_disjoint addr_m (blockSize layout) freshAddr (blockSize freshLayout)) :
  TrackedPlaceTagLive ((freshBase, (freshReg, freshLayout)) :: π)
    { s_mir with
      env := s_mir.env.insert freshBase (freshAddr, layoutToTyVal freshLayout, freshTag),
      mem := mirlite.writeWordSeq s_mir.mem freshAddr vals } := by
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env h_mem
  by_cases h_base_eq : p.base = freshBase
  · have h_lookup_self :
      ((freshBase, (freshReg, freshLayout)) :: π).lookup freshBase = some (reg, baseLayout) := by
      simpa [h_base_eq] using h_lookup
    have h_lookup_eq : reg = freshReg ∧ baseLayout = freshLayout := by
      exact place_map_lookup_cons_self h_lookup_self
    rcases h_lookup_eq with ⟨rfl, rfl⟩
    have h_env_self :
        ({ s_mir with
          env := s_mir.env.insert freshBase (freshAddr, layoutToTyVal baseLayout, freshTag),
          mem := mirlite.writeWordSeq s_mir.mem freshAddr vals }).env.lookup freshBase =
          some (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      simpa [h_base_eq] using h_env
    have h_env_eq :
        (freshAddr, layoutToTyVal baseLayout, freshTag) =
          (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      exact Option.some.inj <| (env_lookup_insert_eq s_mir.env freshBase
        (freshAddr, layoutToTyVal baseLayout, freshTag)).symm.trans h_env_self
    rcases h_env_eq with ⟨rfl, _h_ty_eq, rfl⟩
    have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_off_le)
    have h_i : off < vals.length := by
      simpa [h_vals_len] using h_off_lt
    have h_find :
        (mirlite.writeWordSeq s_mir.mem freshAddr vals).find? (freshAddr + off) =
          some (vals.get ⟨off, h_i⟩) :=
      mirlite_find_writeWordSeq_at (m := s_mir.mem) (addr := freshAddr) (vals := vals) h_i
    rw [h_find] at h_mem
    have h_val_eq : vals.get ⟨off, h_i⟩ = mirlite.MemValue.PlaceTag q gq := by
      exact Option.some.inj h_mem
    exact False.elim (h_vals_nonptr off h_i q gq h_val_eq)
  · have h_lookup_old : π.lookup p.base = some (reg, baseLayout) :=
      place_map_lookup_cons_ne h_base_eq h_lookup
    have h_env_old :
        s_mir.env.lookup p.base = some (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      have h_keep :=
        env_lookup_insert_ne s_mir.env freshBase p.base
          (freshAddr, layoutToTyVal freshLayout, freshTag) h_base_eq
      rw [h_keep] at h_env
      exact h_env
    rcases StateSim.place h_sim h_lookup_old with
      ⟨baseAddr_old, baseAddr_old_o, baseTag_old, baseTag_old_o, h_ptr_old, _h_block_old⟩
    have h_env_ptr_eq :
        (baseAddr_old, layoutToTyVal baseLayout, baseTag_old) =
          (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      exact Option.some.inj ((place_runtime_sim.env h_ptr_old).symm.trans h_env_old)
    have h_addr_eq : baseAddr_old = baseAddr := congrArg Prod.fst h_env_ptr_eq
    have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_off_le)
    have h_keep :
        (mirlite.writeWordSeq s_mir.mem freshAddr vals).find? (baseAddr + off) =
          s_mir.mem.find? (baseAddr + off) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro i h_i h_eq
      have h_i' : i < blockSize freshLayout := by
        simpa [h_vals_len] using h_i
      have h_eq' : baseAddr_old + off = freshAddr + i := by
        simpa [h_addr_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_eq
      exact h_disj p.base reg baseLayout baseAddr_old baseAddr_old_o baseTag_old baseTag_old_o
        h_lookup_old h_ptr_old off h_off_lt i h_i' h_eq'
    rw [h_keep] at h_mem
    obtain ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag, stack, item,
        h_q_lookup, h_q_path, h_q_env, h_stack, h_item_mem, h_item_tag⟩ :=
      h_live p reg baseLayout baseAddr baseTag off innerLayout q gq
        h_lookup_old h_path h_env_old h_mem
    have h_q_base_ne : q.base ≠ freshBase := by
      intro h_eq_q
      have h_some : π.lookup freshBase = some (targetReg, targetBaseLayout) := by
        simpa [h_eq_q] using h_q_lookup
      rw [h_lookup_none] at h_some
      cases h_some
    have h_q_beq : (q.base == freshBase) = false := by
      simp [h_q_base_ne]
    have h_q_lookup' :
        ((freshBase, (freshReg, freshLayout)) :: π).lookup q.base =
          some (targetReg, targetBaseLayout) := by
      simpa [List.lookup, h_q_beq] using h_q_lookup
    have h_q_env' :
        (s_mir.env.insert freshBase (freshAddr, layoutToTyVal freshLayout, freshTag)).lookup q.base =
          some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag) := by
      rw [env_lookup_insert_ne s_mir.env freshBase q.base
        (freshAddr, layoutToTyVal freshLayout, freshTag) h_q_base_ne]
      exact h_q_env
    exact ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag, stack, item,
      h_q_lookup', h_q_path, h_q_env', h_stack, h_item_mem, h_item_tag⟩

theorem TrackedPlaceTagClosure.extend_fresh_copy_from_place
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  {src : mirlite.Place}
  {srcReg : Register}
  {srcBaseLayout dstLayout : LayoutTy}
  {srcOff : Word}
  {srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o : Word}
  {freshBase : Word}
  {freshReg : Register}
  {freshAddr freshTag : Word}
  (h_sim : StateSim π ρa ρt s_mir s_osea ptr_sim)
  (h_closure : TrackedPlaceTagClosure π s_mir)
  (h_lookup_none : π.lookup freshBase = none)
  (h_src_lookup : π.lookup src.base = some (srcReg, srcBaseLayout))
  (h_src_path : layoutResolvePath srcBaseLayout src.path = some (srcOff, dstLayout))
  (h_src_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      src.base srcReg srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o srcBaseLayout)
  (h_disj :
    ∀ base reg layout addr_m addr_o tag_m tag_o,
      π.lookup base = some (reg, layout) →
      place_runtime_sim π ρa ρt s_mir s_osea
        base reg addr_m addr_o tag_m tag_o layout →
      blocks_disjoint addr_m (blockSize layout) freshAddr (blockSize dstLayout)) :
  TrackedPlaceTagClosure ((freshBase, (freshReg, dstLayout)) :: π)
    { s_mir with
      env := s_mir.env.insert freshBase (freshAddr, layoutToTyVal dstLayout, freshTag),
      mem :=
        mirlite.writeWordSeq s_mir.mem freshAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)) } := by
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env h_mem
  by_cases h_base_eq : p.base = freshBase
  · have h_lookup_self :
      ((freshBase, (freshReg, dstLayout)) :: π).lookup freshBase = some (reg, baseLayout) := by
      simpa [h_base_eq] using h_lookup
    have h_lookup_eq : reg = freshReg ∧ baseLayout = dstLayout := by
      exact place_map_lookup_cons_self h_lookup_self
    rcases h_lookup_eq with ⟨rfl, rfl⟩
    have h_env_self :
        ({ s_mir with
          env := s_mir.env.insert freshBase (freshAddr, layoutToTyVal baseLayout, freshTag),
          mem :=
            mirlite.writeWordSeq s_mir.mem freshAddr
              (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize baseLayout)) }).env.lookup
          freshBase =
          some (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      simpa [h_base_eq] using h_env
    have h_env_eq :
        (freshAddr, layoutToTyVal baseLayout, freshTag) =
          (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      exact Option.some.inj <| (env_lookup_insert_eq s_mir.env freshBase
        (freshAddr, layoutToTyVal baseLayout, freshTag)).symm.trans h_env_self
    rcases h_env_eq with ⟨rfl, _h_ty_eq, rfl⟩
    have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_off_le)
    have h_find :
        (mirlite.writeWordSeq s_mir.mem freshAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize baseLayout))).find?
          (freshAddr + off) =
            some ((mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize baseLayout)).get
              ⟨off, by simpa [mirlite_readWordSeq_length] using h_off_lt⟩) :=
      mirlite_find_writeWordSeq_at
        (m := s_mir.mem)
        (addr := freshAddr)
        (vals := mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize baseLayout))
        (i := off)
        (by simpa [mirlite_readWordSeq_length] using h_off_lt)
    rw [h_find] at h_mem
    have h_src_mem :
        s_mir.mem.find? (srcBaseAddr + srcOff + off) = some (mirlite.MemValue.PlaceTag q gq) := by
      have h_get :
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize baseLayout)).get
            ⟨off, by simpa [mirlite_readWordSeq_length] using h_off_lt⟩ =
              mirlite.MemValue.PlaceTag q gq := by
        exact Option.some.inj h_mem
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (mirlite_find_of_readWordSeq_get_placeTag
          (m := s_mir.mem)
          (addr := srcBaseAddr + srcOff)
          (n := blockSize baseLayout)
          (i := off)
          (q := q)
          (gq := gq)
          h_off_lt h_get)
    have h_src_env :
        s_mir.env.lookup src.base =
          some (srcBaseAddr, layoutToTyVal srcBaseLayout, srcBaseTag) :=
      place_runtime_sim.env h_src_ptr
    have h_src_full_path :
        layoutResolvePath srcBaseLayout (src.path ++ p.path) =
          some (srcOff + off, LayoutTy.PtrL innerLayout) :=
      layoutResolvePath_append h_src_path h_path
    have h_src_mem' :
        s_mir.mem.find? (srcBaseAddr + (srcOff + off)) = some (mirlite.MemValue.PlaceTag q gq) := by
      simpa [Nat.add_assoc] using h_src_mem
    obtain ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
        h_q_lookup, h_q_path, h_q_env⟩ :=
      h_closure
        { base := src.base, path := src.path ++ p.path }
        srcReg srcBaseLayout srcBaseAddr srcBaseTag (srcOff + off) innerLayout q gq
        h_src_lookup h_src_full_path h_src_env h_src_mem'
    have h_q_base_ne : q.base ≠ freshBase := by
      intro h_eq_q
      have h_some : π.lookup freshBase = some (targetReg, targetBaseLayout) := by
        simpa [h_eq_q] using h_q_lookup
      rw [h_lookup_none] at h_some
      cases h_some
    have h_q_beq : (q.base == freshBase) = false := by
      simp [h_q_base_ne]
    have h_q_lookup' :
        ((freshBase, (reg, baseLayout)) :: π).lookup q.base =
          some (targetReg, targetBaseLayout) := by
      simpa [List.lookup, h_q_beq] using h_q_lookup
    have h_q_env' :
        (s_mir.env.insert freshBase (freshAddr, layoutToTyVal baseLayout, freshTag)).lookup q.base =
          some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag) := by
      rw [env_lookup_insert_ne s_mir.env freshBase q.base
        (freshAddr, layoutToTyVal baseLayout, freshTag) h_q_base_ne]
      exact h_q_env
    exact ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
      h_q_lookup', h_q_path, h_q_env'⟩
  · have h_lookup_old : π.lookup p.base = some (reg, baseLayout) :=
      place_map_lookup_cons_ne h_base_eq h_lookup
    have h_env_old :
        s_mir.env.lookup p.base = some (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      rw [env_lookup_insert_ne s_mir.env freshBase p.base
        (freshAddr, layoutToTyVal dstLayout, freshTag) h_base_eq] at h_env
      exact h_env
    rcases StateSim.place h_sim h_lookup_old with
      ⟨baseAddr_old, baseAddr_old_o, baseTag_old, baseTag_old_o, h_ptr_old, _h_block_old⟩
    have h_env_ptr_eq :
        (baseAddr_old, layoutToTyVal baseLayout, baseTag_old) =
          (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      exact Option.some.inj ((place_runtime_sim.env h_ptr_old).symm.trans h_env_old)
    have h_addr_eq : baseAddr_old = baseAddr := congrArg Prod.fst h_env_ptr_eq
    have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_off_le)
    have h_keep :
        (mirlite.writeWordSeq s_mir.mem freshAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
          (baseAddr + off) =
            s_mir.mem.find? (baseAddr + off) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro i h_i h_eq
      have h_i' : i < blockSize dstLayout := by
        simpa [mirlite_readWordSeq_length] using h_i
      have h_eq' : baseAddr_old + off = freshAddr + i := by
        simpa [h_addr_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_eq
      exact h_disj p.base reg baseLayout baseAddr_old baseAddr_old_o baseTag_old baseTag_old_o
        h_lookup_old h_ptr_old off h_off_lt i h_i' h_eq'
    rw [h_keep] at h_mem
    obtain ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
        h_q_lookup, h_q_path, h_q_env⟩ :=
      h_closure p reg baseLayout baseAddr baseTag off innerLayout q gq
        h_lookup_old h_path h_env_old h_mem
    have h_q_base_ne : q.base ≠ freshBase := by
      intro h_eq_q
      have h_some : π.lookup freshBase = some (targetReg, targetBaseLayout) := by
        simpa [h_eq_q] using h_q_lookup
      rw [h_lookup_none] at h_some
      cases h_some
    have h_q_beq : (q.base == freshBase) = false := by
      simp [h_q_base_ne]
    have h_q_lookup' :
        ((freshBase, (freshReg, dstLayout)) :: π).lookup q.base =
          some (targetReg, targetBaseLayout) := by
      simpa [List.lookup, h_q_beq] using h_q_lookup
    have h_q_env' :
        (s_mir.env.insert freshBase (freshAddr, layoutToTyVal dstLayout, freshTag)).lookup q.base =
          some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag) := by
      rw [env_lookup_insert_ne s_mir.env freshBase q.base
        (freshAddr, layoutToTyVal dstLayout, freshTag) h_q_base_ne]
      exact h_q_env
    exact ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag,
      h_q_lookup', h_q_path, h_q_env'⟩

theorem TrackedPlaceTagLive.extend_fresh_copy_from_place
  {π : PlaceMap}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  {ptr_sim : PtrSimPred}
  {src : mirlite.Place}
  {srcReg : Register}
  {srcBaseLayout dstLayout : LayoutTy}
  {srcOff : Word}
  {srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o : Word}
  {freshBase : Word}
  {freshReg : Register}
  {freshAddr freshTag : Word}
  (h_sim : StateSim π ρa ρt s_mir s_osea ptr_sim)
  (h_live : TrackedPlaceTagLive π s_mir)
  (h_lookup_none : π.lookup freshBase = none)
  (h_src_lookup : π.lookup src.base = some (srcReg, srcBaseLayout))
  (h_src_path : layoutResolvePath srcBaseLayout src.path = some (srcOff, dstLayout))
  (h_src_ptr :
    place_runtime_sim π ρa ρt s_mir s_osea
      src.base srcReg srcBaseAddr srcBaseAddr_o srcBaseTag srcBaseTag_o srcBaseLayout)
  (h_disj :
    ∀ base reg layout addr_m addr_o tag_m tag_o,
      π.lookup base = some (reg, layout) →
      place_runtime_sim π ρa ρt s_mir s_osea
        base reg addr_m addr_o tag_m tag_o layout →
      blocks_disjoint addr_m (blockSize layout) freshAddr (blockSize dstLayout)) :
  TrackedPlaceTagLive ((freshBase, (freshReg, dstLayout)) :: π)
    { s_mir with
      env := s_mir.env.insert freshBase (freshAddr, layoutToTyVal dstLayout, freshTag),
      mem :=
        mirlite.writeWordSeq s_mir.mem freshAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout)) } := by
  intro p reg baseLayout baseAddr baseTag off innerLayout q gq
    h_lookup h_path h_env h_mem
  by_cases h_base_eq : p.base = freshBase
  · have h_lookup_self :
      ((freshBase, (freshReg, dstLayout)) :: π).lookup freshBase = some (reg, baseLayout) := by
      simpa [h_base_eq] using h_lookup
    have h_lookup_eq : reg = freshReg ∧ baseLayout = dstLayout := by
      exact place_map_lookup_cons_self h_lookup_self
    rcases h_lookup_eq with ⟨rfl, rfl⟩
    have h_env_self :
        ({ s_mir with
          env := s_mir.env.insert freshBase (freshAddr, layoutToTyVal baseLayout, freshTag),
          mem :=
            mirlite.writeWordSeq s_mir.mem freshAddr
              (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize baseLayout)) }).env.lookup
          freshBase =
          some (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      simpa [h_base_eq] using h_env
    have h_env_eq :
        (freshAddr, layoutToTyVal baseLayout, freshTag) =
          (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      exact Option.some.inj <| (env_lookup_insert_eq s_mir.env freshBase
        (freshAddr, layoutToTyVal baseLayout, freshTag)).symm.trans h_env_self
    rcases h_env_eq with ⟨rfl, _h_ty_eq, rfl⟩
    have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_off_le)
    have h_find :
        (mirlite.writeWordSeq s_mir.mem freshAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize baseLayout))).find?
          (freshAddr + off) =
            some ((mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize baseLayout)).get
              ⟨off, by simpa [mirlite_readWordSeq_length] using h_off_lt⟩) :=
      mirlite_find_writeWordSeq_at
        (m := s_mir.mem)
        (addr := freshAddr)
        (vals := mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize baseLayout))
        (i := off)
        (by simpa [mirlite_readWordSeq_length] using h_off_lt)
    rw [h_find] at h_mem
    have h_src_mem :
        s_mir.mem.find? (srcBaseAddr + srcOff + off) = some (mirlite.MemValue.PlaceTag q gq) := by
      have h_get :
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize baseLayout)).get
            ⟨off, by simpa [mirlite_readWordSeq_length] using h_off_lt⟩ =
              mirlite.MemValue.PlaceTag q gq := by
        exact Option.some.inj h_mem
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (mirlite_find_of_readWordSeq_get_placeTag
          (m := s_mir.mem)
          (addr := srcBaseAddr + srcOff)
          (n := blockSize baseLayout)
          (i := off)
          (q := q)
          (gq := gq)
          h_off_lt h_get)
    have h_src_env :
        s_mir.env.lookup src.base =
          some (srcBaseAddr, layoutToTyVal srcBaseLayout, srcBaseTag) :=
      place_runtime_sim.env h_src_ptr
    have h_src_full_path :
        layoutResolvePath srcBaseLayout (src.path ++ p.path) =
          some (srcOff + off, LayoutTy.PtrL innerLayout) :=
      layoutResolvePath_append h_src_path h_path
    have h_src_mem' :
        s_mir.mem.find? (srcBaseAddr + (srcOff + off)) = some (mirlite.MemValue.PlaceTag q gq) := by
      simpa [Nat.add_assoc] using h_src_mem
    obtain ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag, stack, item,
        h_q_lookup, h_q_path, h_q_env, h_stack, h_item_mem, h_item_tag⟩ :=
      h_live
        { base := src.base, path := src.path ++ p.path }
        srcReg srcBaseLayout srcBaseAddr srcBaseTag (srcOff + off) innerLayout q gq
        h_src_lookup h_src_full_path h_src_env h_src_mem'
    have h_q_base_ne : q.base ≠ freshBase := by
      intro h_eq_q
      have h_some : π.lookup freshBase = some (targetReg, targetBaseLayout) := by
        simpa [h_eq_q] using h_q_lookup
      rw [h_lookup_none] at h_some
      cases h_some
    have h_q_beq : (q.base == freshBase) = false := by
      simp [h_q_base_ne]
    have h_q_lookup' :
        ((freshBase, (reg, baseLayout)) :: π).lookup q.base =
          some (targetReg, targetBaseLayout) := by
      simpa [List.lookup, h_q_beq] using h_q_lookup
    have h_q_env' :
        (s_mir.env.insert freshBase (freshAddr, layoutToTyVal baseLayout, freshTag)).lookup q.base =
          some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag) := by
      rw [env_lookup_insert_ne s_mir.env freshBase q.base
        (freshAddr, layoutToTyVal baseLayout, freshTag) h_q_base_ne]
      exact h_q_env
    exact ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag, stack, item,
      h_q_lookup', h_q_path, h_q_env', h_stack, h_item_mem, h_item_tag⟩
  · have h_lookup_old : π.lookup p.base = some (reg, baseLayout) :=
      place_map_lookup_cons_ne h_base_eq h_lookup
    have h_env_old :
        s_mir.env.lookup p.base = some (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      rw [env_lookup_insert_ne s_mir.env freshBase p.base
        (freshAddr, layoutToTyVal dstLayout, freshTag) h_base_eq] at h_env
      exact h_env
    rcases StateSim.place h_sim h_lookup_old with
      ⟨baseAddr_old, baseAddr_old_o, baseTag_old, baseTag_old_o, h_ptr_old, _h_block_old⟩
    have h_env_ptr_eq :
        (baseAddr_old, layoutToTyVal baseLayout, baseTag_old) =
          (baseAddr, layoutToTyVal baseLayout, baseTag) := by
      exact Option.some.inj ((place_runtime_sim.env h_ptr_old).symm.trans h_env_old)
    have h_addr_eq : baseAddr_old = baseAddr := congrArg Prod.fst h_env_ptr_eq
    have h_off_le : off + blockSize (LayoutTy.PtrL innerLayout) ≤ blockSize baseLayout :=
      layoutResolvePath_blockSize_le h_path
    have h_off_lt : off < blockSize baseLayout := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self off) (by simpa [blockSize] using h_off_le)
    have h_keep :
        (mirlite.writeWordSeq s_mir.mem freshAddr
          (mirlite.readWordSeq s_mir.mem (srcBaseAddr + srcOff) (blockSize dstLayout))).find?
          (baseAddr + off) =
            s_mir.mem.find? (baseAddr + off) := by
      apply mirlite_find_writeWordSeq_of_ne
      intro i h_i h_eq
      have h_i' : i < blockSize dstLayout := by
        simpa [mirlite_readWordSeq_length] using h_i
      have h_eq' : baseAddr_old + off = freshAddr + i := by
        simpa [h_addr_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_eq
      exact h_disj p.base reg baseLayout baseAddr_old baseAddr_old_o baseTag_old baseTag_old_o
        h_lookup_old h_ptr_old off h_off_lt i h_i' h_eq'
    rw [h_keep] at h_mem
    obtain ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag, stack, item,
        h_q_lookup, h_q_path, h_q_env, h_stack, h_item_mem, h_item_tag⟩ :=
      h_live p reg baseLayout baseAddr baseTag off innerLayout q gq
        h_lookup_old h_path h_env_old h_mem
    have h_q_base_ne : q.base ≠ freshBase := by
      intro h_eq_q
      have h_some : π.lookup freshBase = some (targetReg, targetBaseLayout) := by
        simpa [h_eq_q] using h_q_lookup
      rw [h_lookup_none] at h_some
      cases h_some
    have h_q_beq : (q.base == freshBase) = false := by
      simp [h_q_base_ne]
    have h_q_lookup' :
        ((freshBase, (freshReg, dstLayout)) :: π).lookup q.base =
          some (targetReg, targetBaseLayout) := by
      simpa [List.lookup, h_q_beq] using h_q_lookup
    have h_q_env' :
        (s_mir.env.insert freshBase (freshAddr, layoutToTyVal dstLayout, freshTag)).lookup q.base =
          some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetBaseTag) := by
      rw [env_lookup_insert_ne s_mir.env freshBase q.base
        (freshAddr, layoutToTyVal dstLayout, freshTag) h_q_base_ne]
      exact h_q_env
    exact ⟨targetReg, targetBaseLayout, targetOff, targetBaseAddr, targetBaseTag, stack, item,
      h_q_lookup', h_q_path, h_q_env', h_stack, h_item_mem, h_item_tag⟩

theorem CompilerInv.ref_temp_safe
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (ctx : RefExistingCtx)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (_h_cs : ctx.cs = csAt cs0 prog s_mir.pc) :
  NextAllocClear (A_o := oseair.bumpAllocator) ρa s_osea 1 := by
  rcases h_inv with
    ⟨_h_pc, _h_sim, _h_closure, _h_source_below, _h_tag_fresh, _h_absent, h_noninterference⟩
  exact TargetNonInterference.next_alloc_clear
    (ρa := ρa) (s_osea := s_osea) (sz := 1) h_noninterference

theorem CompilerInv.deref_projected_temp_safe
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (ctx : DerefProjectedExistingCtx)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (_h_cs : ctx.cs = csAt cs0 prog s_mir.pc) :
  NextAllocClear (A_o := oseair.bumpAllocator) ρa s_osea (blockSize ctx.innerLayout) := by
  rcases h_inv with
    ⟨_h_pc, _h_sim, _h_closure, _h_source_below, _h_tag_fresh, _h_absent, h_noninterference⟩
  exact TargetNonInterference.next_alloc_clear
    (ρa := ρa) (s_osea := s_osea) (sz := blockSize ctx.innerLayout) h_noninterference

theorem CompilerInv.deref_fresh_temp_safe
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (ctx : DerefFreshCtx)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (_h_cs : ctx.cs = csAt cs0 prog s_mir.pc) :
  NextAllocClear (A_o := oseair.bumpAllocator) ρa s_osea (blockSize ctx.innerLayout) := by
  rcases h_inv with
    ⟨_h_pc, _h_sim, _h_closure, _h_source_below, _h_tag_fresh, _h_absent, h_noninterference⟩
  exact TargetNonInterference.next_alloc_clear
    (ρa := ρa) (s_osea := s_osea) (sz := blockSize ctx.innerLayout) h_noninterference

theorem CompilerInv.tag_rename_fresh
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea) :
  TagRenameFreshFrom ρt s_mir.ap.NextTag := by
  rcases h_inv with
    ⟨_h_pc, _h_sim, _h_closure, _h_source_below, h_tag_fresh, _h_absent, _h_noninterference⟩
  exact h_tag_fresh

theorem CompilerInv.deref_projected_pointee_tracked
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (ctx : DerefProjectedExistingCtx)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (h_cs : ctx.cs = csAt cs0 prog s_mir.pc) :
  ∀ srcBaseAddr_m srcTag_m q gq ap_src_read_m targetRes,
    s_mir.env.lookup ctx.src.base =
      some (srcBaseAddr_m, layoutToTyVal ctx.srcBaseLayout, srcTag_m) →
    s_mir.mem.find? (srcBaseAddr_m + ctx.srcOff) =
      some (mirlite.MemValue.PlaceTag q gq) →
    mirlite.resolveDirectPlace { s_mir with ap := ap_src_read_m } q =
      (mirlite.Result.Ok { s_mir with ap := ap_src_read_m }, targetRes) →
    ∃ targetReg targetBaseLayout targetOff targetBaseAddr,
      ctx.cs.placeMap.lookup q.base = some (targetReg, targetBaseLayout) ∧
      layoutResolvePath targetBaseLayout q.path = some (targetOff, ctx.innerLayout) ∧
      s_mir.env.lookup q.base =
        some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetRes.tag) ∧
      targetRes.addr = targetBaseAddr + targetOff ∧
      targetRes.ty = layoutToTyVal ctx.innerLayout := by
  intro srcBaseAddr_m srcTag_m q gq ap_src_read_m targetRes h_env h_ptr h_resolve
  rcases h_inv with
    ⟨_h_pc, _h_sim, h_closure, _h_source_below, _h_tag_fresh, _h_absent, _h_noninterference⟩
  have h_src_lookup' :
      (csAt cs0 prog s_mir.pc).placeMap.lookup ctx.src.base =
        some (ctx.srcReg, ctx.srcBaseLayout) := by
    simpa [BaseReady, h_cs] using ctx.h_src_lookup
  simpa [h_cs] using
    (TrackedPlaceTagClosure.resolve_pointee
      (π := (csAt cs0 prog s_mir.pc).placeMap)
      (s_mir := s_mir)
      (src := ctx.src)
      (srcReg := ctx.srcReg)
      (srcBaseLayout := ctx.srcBaseLayout)
      (innerLayout := ctx.innerLayout)
      (srcBaseAddr_m := srcBaseAddr_m)
      (srcTag_m := srcTag_m)
      (srcOff := ctx.srcOff)
      (q := q)
      (gq := gq)
      (ap_src_read_m := ap_src_read_m)
      (targetRes := targetRes)
      h_closure h_src_lookup' ctx.h_src_path h_env h_ptr h_resolve)

theorem CompilerInv.deref_fresh_pointee_tracked
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (ctx : DerefFreshCtx)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (h_cs : ctx.cs = csAt cs0 prog s_mir.pc) :
  ∀ srcBaseAddr_m srcTag_m q gq ap_src_read_m targetRes,
    s_mir.env.lookup ctx.src.base =
      some (srcBaseAddr_m, layoutToTyVal ctx.srcBaseLayout, srcTag_m) →
    s_mir.mem.find? (srcBaseAddr_m + ctx.srcOff) =
      some (mirlite.MemValue.PlaceTag q gq) →
    mirlite.resolveDirectPlace { s_mir with ap := ap_src_read_m } q =
      (mirlite.Result.Ok { s_mir with ap := ap_src_read_m }, targetRes) →
    ∃ targetReg targetBaseLayout targetOff targetBaseAddr,
      ctx.cs.placeMap.lookup q.base = some (targetReg, targetBaseLayout) ∧
      layoutResolvePath targetBaseLayout q.path = some (targetOff, ctx.innerLayout) ∧
      s_mir.env.lookup q.base =
        some (targetBaseAddr, layoutToTyVal targetBaseLayout, targetRes.tag) ∧
      targetRes.addr = targetBaseAddr + targetOff ∧
      targetRes.ty = layoutToTyVal ctx.innerLayout := by
  intro srcBaseAddr_m srcTag_m q gq ap_src_read_m targetRes h_env h_ptr h_resolve
  rcases h_inv with
    ⟨_h_pc, _h_sim, h_closure, _h_source_below, _h_tag_fresh, _h_absent, _h_noninterference⟩
  have h_src_lookup' :
      (csAt cs0 prog s_mir.pc).placeMap.lookup ctx.src.base =
        some (ctx.srcReg, ctx.srcBaseLayout) := by
    simpa [BaseReady, h_cs] using ctx.h_src_lookup
  simpa [h_cs] using
    (TrackedPlaceTagClosure.resolve_pointee
      (π := (csAt cs0 prog s_mir.pc).placeMap)
      (s_mir := s_mir)
      (src := ctx.src)
      (srcReg := ctx.srcReg)
      (srcBaseLayout := ctx.srcBaseLayout)
      (innerLayout := ctx.innerLayout)
      (srcBaseAddr_m := srcBaseAddr_m)
      (srcTag_m := srcTag_m)
      (srcOff := ctx.srcOff)
      (q := q)
      (gq := gq)
      (ap_src_read_m := ap_src_read_m)
      (targetRes := targetRes)
      h_closure h_src_lookup' ctx.h_src_path h_env h_ptr h_resolve)

@[simp] theorem ConstExistingCtx.compileStmt_placeMap
  (ctx : ConstExistingCtx) :
  (compileStmt ctx.cs ctx.stmt).placeMap = ctx.cs.placeMap := by
  have h_place :
      (placeToReg ctx.cs ctx.dst mirlite.RefKind.Mut (some LayoutTy.NatL)).cs.placeMap =
        ctx.cs.placeMap :=
    placeToReg_placeMap_of_lookup
      (cs := ctx.cs)
      (p := ctx.dst)
      (kind := mirlite.RefKind.Mut)
      (expected := some LayoutTy.NatL)
      ctx.h_lookup
  unfold ConstExistingCtx.stmt compileStmt
  simpa [h_place]

@[simp] theorem ConstFreshCtx.compileStmt_placeMap
  (ctx : ConstFreshCtx) :
  (compileStmt ctx.cs ctx.stmt).placeMap = ctx.postPlaceMap := by
  have h_place :
      (placeToReg ctx.cs { base := ctx.base, path := [] } mirlite.RefKind.Mut
        (some LayoutTy.NatL)).cs.placeMap = ctx.postPlaceMap := by
    simpa [ConstFreshCtx.postPlaceMap, ConstFreshCtx.reg] using
      (placeToReg_placeMap_of_absent_base
        (cs := ctx.cs)
        (p := { base := ctx.base, path := [] })
        (kind := mirlite.RefKind.Mut)
        (layout := LayoutTy.NatL)
        ctx.h_absent rfl)
  unfold ConstFreshCtx.stmt compileStmt
  simpa [h_place]

@[simp] theorem StructInitExistingCtx.compileStmt_placeMap
  (ctx : StructInitExistingCtx) :
  (compileStmt ctx.cs ctx.stmt).placeMap = ctx.cs.placeMap := by
  have h_words :
      compile.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
    simpa [wordStructFields] using compile_structConstWords_wordStructFields ctx.fields
  by_cases h_off : ctx.off = 0
  · have h_place :
        placeToReg ctx.cs ctx.dst mirlite.RefKind.Mut (some (wordStructLayout ctx.fields)) =
          { reg := ctx.reg, layout := wordStructLayout ctx.fields, cleanup := [], cs := ctx.cs } := by
      unfold placeToReg
      rw [ctx.h_lookup]
      simp [ctx.h_path, h_off]
    have h_place' :
        placeToReg ctx.cs ctx.dst mirlite.RefKind.Mut
          (some (LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL))) =
          { reg := ctx.reg,
            layout := LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL),
            cleanup := [],
            cs := ctx.cs } := by
      simpa [wordStructLayout] using h_place
    unfold StructInitExistingCtx.stmt compileStmt
    simpa [h_off] using
      (by
        simp [h_words, h_place', emit, cleanupInstrs,
          obseq.notation.placeExpr, wordStructRhs, wordStructFields,
          wordStructTy, wordStructOseaVals, ctx.instrs_nil])
  · have h_place :
        placeToReg ctx.cs ctx.dst mirlite.RefKind.Mut (some (wordStructLayout ctx.fields)) =
          { reg := ctx.tmpReg,
            layout := wordStructLayout ctx.fields,
            cleanup := [ctx.tmpReg],
            cs :=
              { nextReg := ctx.cs.nextReg + 1,
                placeMap := ctx.cs.placeMap,
                instrs := ctx.cs.instrs ++
                  [oseair.Instr.Assgn ctx.tmpReg (oseair.Rhs.MutBorOffset ctx.reg ctx.off)] } } := by
      unfold placeToReg
      rw [ctx.h_lookup]
      simp [ctx.h_path, h_off, StructInitExistingCtx.tmpReg, freshReg, emit]
    have h_place' :
        placeToReg ctx.cs ctx.dst mirlite.RefKind.Mut
          (some (LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL))) =
          { reg := ctx.tmpReg,
            layout := LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL),
            cleanup := [ctx.tmpReg],
            cs :=
              { nextReg := ctx.cs.nextReg + 1,
                placeMap := ctx.cs.placeMap,
                instrs := ctx.cs.instrs ++
                  [oseair.Instr.Assgn ctx.tmpReg (oseair.Rhs.MutBorOffset ctx.reg ctx.off)] } } := by
      simpa [wordStructLayout] using h_place
    unfold StructInitExistingCtx.stmt compileStmt
    simpa [h_off] using
      (by
        simp [h_words, h_place', emit, cleanupInstrs,
          obseq.notation.placeExpr, wordStructRhs, wordStructFields,
          wordStructTy, wordStructOseaVals, StructInitExistingCtx.tmpReg, ctx.instrs_nil])

@[simp] theorem StructInitFreshCtx.compileStmt_placeMap
  (ctx : StructInitFreshCtx) :
  (compileStmt ctx.cs ctx.stmt).placeMap = ctx.postPlaceMap := by
  have h_place :
      placeToReg ctx.cs { base := ctx.base, path := [] } mirlite.RefKind.Mut
        (some (wordStructLayout ctx.fields)) =
        { reg := ctx.reg, layout := wordStructLayout ctx.fields, cleanup := [],
          cs :=
            { nextReg := ctx.cs.nextReg + 1,
              placeMap := (ctx.base, (ctx.reg, wordStructLayout ctx.fields)) :: ctx.cs.placeMap,
              instrs := ctx.cs.instrs ++
                [oseair.Instr.Assgn ctx.reg (oseair.Rhs.Alloc (wordStructTy ctx.fields))] } } := by
    unfold placeToReg StructInitFreshCtx.reg
    rw [ctx.h_absent]
    simp [freshReg, emit, setPlace, layoutToTyVal_wordStructLayout]
  have h_place' :
      placeToReg ctx.cs { base := ctx.base, path := [] } mirlite.RefKind.Mut
        (some (LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL))) =
        { reg := ctx.reg,
          layout := LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL),
          cleanup := [],
          cs :=
            { nextReg := ctx.cs.nextReg + 1,
              placeMap :=
                (ctx.base, (ctx.reg, LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL))) ::
                  ctx.cs.placeMap,
              instrs := ctx.cs.instrs ++
                [oseair.Instr.Assgn ctx.reg
                  (oseair.Rhs.Alloc (TyVal.TupTy (List.replicate ctx.fields.length TyVal.NatTy)))] } } := by
    simpa [wordStructLayout, wordStructTy] using h_place
  have h_words :
      compile.structConstWords? (List.map mirlite.RExpr.ConstOp ctx.fields) = some ctx.fields := by
    simpa [wordStructFields] using compile_structConstWords_wordStructFields ctx.fields
  have h_pm :
      (compileStmt ctx.cs ctx.stmt).placeMap =
        (ctx.base, (ctx.reg, LayoutTy.TupL (List.replicate ctx.fields.length LayoutTy.NatL))) ::
          ctx.cs.placeMap := by
    unfold StructInitFreshCtx.stmt
    simp [compileStmt, h_words, h_place', emit, cleanupInstrs,
      ctx.instrs_nil, obseq.notation.basePlace, wordStructRhs, wordStructFields,
      obseq.notation.placeExpr, obseq.notation.mkPlace]
  simpa [StructInitFreshCtx.postPlaceMap, StructInitFreshCtx.reg, wordStructLayout] using h_pm

@[simp] theorem CopyExistingCtx.compileStmt_placeMap
  (ctx : CopyExistingCtx) :
  (compileStmt ctx.cs ctx.stmt).placeMap = ctx.cs.placeMap := by
  have h_src_place :
      placeToReg ctx.cs { base := ctx.srcBase, path := [] } mirlite.RefKind.Shared none =
        { reg := ctx.srcReg, layout := ctx.layout, cleanup := [], cs := ctx.cs } := by
    unfold placeToReg
    rw [ctx.h_src_lookup]
    simp [layoutResolvePath]
  have h_dst_place :
      placeToReg ctx.cs { base := ctx.dstBase, path := [] } mirlite.RefKind.Mut (some ctx.layout) =
        { reg := ctx.dstReg, layout := ctx.layout, cleanup := [], cs := ctx.cs } := by
    unfold placeToReg
    rw [ctx.h_dst_lookup]
    simp [layoutResolvePath]
  unfold CopyExistingCtx.stmt
  simp [compileStmt, obseq.notation.placeExpr, obseq.notation.mkPlace,
    obseq.notation.copyPlaceRhs, obseq.notation.copyRhs, obseq.notation.basePlace,
    h_src_place, h_dst_place, emit, cleanupInstrs, ctx.instrs_nil]

@[simp] theorem RefExistingCtx.compileStmt_placeMap
  (ctx : RefExistingCtx) :
  (compileStmt ctx.cs ctx.stmt).placeMap = ctx.cs.placeMap := by
  let rhs := mirlite.RExpr.RefOp ctx.kind ctx.src
  let rhsCs := (compileRExpr ctx.cs rhs).cs
  have h_rhs_pm : rhsCs.placeMap = ctx.cs.placeMap := by
    simpa [rhsCs, rhs] using compileRExpr_placeMap ctx.cs rhs
  have h_dst_lookup' :
      getPlaceInfo rhsCs ctx.dst.base = some (ctx.dstReg, ctx.dstBaseLayout) := by
    simpa [getPlaceInfo, rhsCs] using ctx.h_dst_lookup
  have h_src_layout : placeLayout? ctx.cs ctx.src = some ctx.srcLayout := by
    unfold placeLayout?
    rw [ctx.h_src_lookup]
    simp [ctx.h_src_path]
  have h_rhs_layout : (compileRExpr ctx.cs rhs).layout = LayoutTy.PtrL ctx.srcLayout := by
    simp [compileRExpr, compileRExprFuel, rhs, inferRExprLayout, h_src_layout]
  have h_dst_pm :
      (placeToReg rhsCs ctx.dst mirlite.RefKind.Mut
        (some (compileRExpr ctx.cs rhs).layout)).cs.placeMap = rhsCs.placeMap :=
    placeToReg_placeMap_of_lookup
      (cs := rhsCs)
      (p := ctx.dst)
      (kind := mirlite.RefKind.Mut)
      (expected := some (compileRExpr ctx.cs rhs).layout)
      h_dst_lookup'
  simpa [RefExistingCtx.stmt, compileStmt, rhs, rhsCs, h_rhs_pm, h_rhs_layout] using h_dst_pm

@[simp] theorem DerefProjectedExistingCtx.compileStmt_placeMap
  (ctx : DerefProjectedExistingCtx) :
  (compileStmt ctx.cs ctx.stmt).placeMap = ctx.cs.placeMap := by
  let rhs := mirlite.RExpr.DrefOp ctx.src
  let rhsCs := (compileRExpr ctx.cs rhs).cs
  have h_rhs_pm : rhsCs.placeMap = ctx.cs.placeMap := by
    simpa [rhsCs, rhs] using compileRExpr_placeMap ctx.cs rhs
  have h_dst_lookup' :
      getPlaceInfo rhsCs ctx.dst.base = some (ctx.dstReg, ctx.dstBaseLayout) := by
    simpa [getPlaceInfo, rhsCs] using ctx.h_dst_lookup
  have h_src_layout : placeLayout? ctx.cs ctx.src = some (LayoutTy.PtrL ctx.innerLayout) := by
    unfold placeLayout?
    rw [ctx.h_src_lookup]
    simp [ctx.h_src_path]
  have h_rhs_layout : (compileRExpr ctx.cs rhs).layout = ctx.innerLayout := by
    simp [compileRExpr, compileRExprFuel, rhs, inferRExprLayout, h_src_layout]
  have h_dst_pm :
      (placeToReg rhsCs ctx.dst mirlite.RefKind.Mut
        (some (compileRExpr ctx.cs rhs).layout)).cs.placeMap =
        rhsCs.placeMap :=
    placeToReg_placeMap_of_lookup
      (cs := rhsCs)
      (p := ctx.dst)
      (kind := mirlite.RefKind.Mut)
      (expected := some (compileRExpr ctx.cs rhs).layout)
      h_dst_lookup'
  simpa [DerefProjectedExistingCtx.stmt, compileStmt, rhs, rhsCs, h_rhs_pm, h_rhs_layout] using h_dst_pm

theorem SupportedStmt.step_state_sim
  {A_m : mirlite.AllocatorSpec}
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_next : mirlite.State}
  {s_osea : oseair.State}
  {stmt : mirlite.Stmt}
  (h_stmt : SupportedStmt (csAt cs0 prog s_mir.pc) stmt)
  (h_get : prog.get? s_mir.pc = some stmt)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (h_alloc_base_any : ∀ mem sz, (A_m.alloc mem sz).1 = mem.addrStart)
  (h_alloc_addrStart_any : ∀ mem sz, (A_m.alloc mem sz).2.addrStart = mem.addrStart + sz)
  (h_mir_step : mirlite.stepWith A_m s_mir prog = mirlite.Result.Ok s_mir_next) :
  ∃ ρa' ρt' s_osea_next,
    StepStarWith oseair.bumpAllocator s_osea (compileProgFrom cs0 prog) s_osea_next ∧
    StateSim (csAt cs0 prog (s_mir.pc + 1)).placeMap ρa' ρt' s_mir_next s_osea_next
      (ptrSimOfCtx ρa' ρt' s_mir_next.env) ∧
    TrackedPlaceTagClosure (csAt cs0 prog (s_mir.pc + 1)).placeMap s_mir_next ∧
    SourceBlocksBelowAddrStart (csAt cs0 prog (s_mir.pc + 1)).placeMap s_mir_next ∧
    TagRenameFreshFrom ρt' s_mir_next.ap.NextTag ∧
    (∀ base,
      (csAt cs0 prog (s_mir.pc + 1)).placeMap.lookup base = none →
        s_mir_next.env.lookup base = none) ∧
    TargetNonInterference ρa' s_osea_next ∧
    s_mir_next.pc = s_mir.pc + 1 ∧
    s_osea_next.pc = targetPcAt cs0 prog (s_mir.pc + 1) := by
  have h_inv' := h_inv
  rcases h_inv with
    ⟨h_pc, h_sim, h_closure, h_source_below, h_tag_fresh, h_absent, h_noninterference⟩
  have h_mir_start : StartsAt prog s_mir.pc [stmt] := by
    intro i
    cases i with
    | zero =>
        intro h_i
        simpa [List.get?] using h_get.symm
    | succ j =>
      intro h_i
      simp at h_i
  have h_osea_start_stmt :
      StartsAt (compileProgFrom cs0 prog) s_osea.pc
        (compileStmt (csAt cs0 prog s_mir.pc) stmt).instrs := by
    have h_osea_start_full :=
      compileProgFrom_startsAt (cs0 := cs0) (prog := prog) (pc := s_mir.pc)
    rw [drop_eq_get_cons h_get, compileProgFrom_cons] at h_osea_start_full
    simpa [h_pc] using (StartsAt.prefix h_osea_start_full)
  have h_target_pc_stmt :
      targetPcAt cs0 prog (s_mir.pc + 1) =
        s_osea.pc + (compileStmt (csAt cs0 prog s_mir.pc) stmt).instrs.length := by
    rw [targetPcAt_succ h_get, h_pc]
  have h_bump_alloc_base (sz : Nat) :
      (oseair.bumpAllocator.alloc s_osea.mem sz).1 = s_osea.mem.addrStart := by
    simp [oseair.bumpAllocator, oseair.allocate]
  have h_bump_alloc_addrStart (sz : Nat) :
      (oseair.bumpAllocator.alloc s_osea.mem sz).2.addrStart = s_osea.mem.addrStart + sz := by
    simp [oseair.bumpAllocator, oseair.allocate]
  have h_bump_alloc_base_any (mem : oseair.Mem) (sz : Nat) :
      (oseair.bumpAllocator.alloc mem sz).1 = mem.addrStart := by
    simp [oseair.bumpAllocator, oseair.allocate]
  have h_bump_alloc_addrStart_any (mem : oseair.Mem) (sz : Nat) :
      (oseair.bumpAllocator.alloc mem sz).2.addrStart = mem.addrStart + sz := by
    simp [oseair.bumpAllocator, oseair.allocate]
  cases h_stmt with
  | const_existing ctx h_cs =>
      have h_sim_ctx :
          ConstExisting.LocalSim ctx ρa ρt s_mir s_osea (ptrSimOfCtx ρa ρt s_mir.env) := by
        simpa [ConstExisting.LocalSim, h_cs] using h_sim
      have h_closure_ctx : TrackedPlaceTagClosure ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_closure
      have h_source_below_ctx : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_source_below
      obtain ⟨addr_m, _addr_o, tag_m, _tag_o, h_dst_ptr, _h_dst_block⟩ :=
        StateSim.place_projected h_sim_ctx ctx.h_lookup ctx.h_path
      have h_dst_env := place_runtime_sim.env h_dst_ptr
      obtain ⟨ap_write, h_use, h_mir_next_eq⟩ :=
        ConstExisting.mirlite_step_inv ctx s_mir s_mir_next prog addr_m tag_m
          h_dst_env h_mir_start h_mir_step
      have h_closure_next :
          TrackedPlaceTagClosure ctx.cs.placeMap s_mir_next := by
        rw [h_mir_next_eq]
        exact TrackedPlaceTagClosure.writeWordSeq_of_nonptr h_closure_ctx (by
          intro i h_i q gq
          simp at h_i
          subst i
          simp)
      have h_osea_start :
          StartsAt (compileProgFrom cs0 prog) s_osea.pc ctx.compiled := by
        simpa [h_cs, ConstExistingCtx.compiled] using h_osea_start_stmt
      have h_target_pc :
          targetPcAt cs0 prog (s_mir.pc + 1) = s_osea.pc + ctx.compiled.length := by
        simpa [h_cs, ConstExistingCtx.compiled] using h_target_pc_stmt
      obtain ⟨s_osea_next, h_steps, h_sim_next, h_noninterference_next, h_pc_next⟩ :=
        ConstExisting.simulation
          (A_m := A_m) (A_o := oseair.bumpAllocator)
          (ctx := ctx)
          (s_mir := s_mir) (s_osea := s_osea) (s_mir_next := s_mir_next)
          (ρa := ρa) (ρt := ρt)
          prog (compileProgFrom cs0 prog)
          h_sim_ctx h_noninterference h_mir_start h_osea_start h_mir_step
      have h_tag_fresh_next :
          TagRenameFreshFrom ρt s_mir_next.ap.NextTag := by
        rw [h_mir_next_eq]
        simpa [sb_use_mb_nextTag_eq h_use] using h_tag_fresh
      have h_source_below_next :
          SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir_next := by
        refine SourceBlocksBelowAddrStart.mono h_source_below_ctx (by rw [h_mir_next_eq]) ?_
        rw [h_mir_next_eq]
        simp
      have h_absent_next :
          ∀ base, ctx.cs.placeMap.lookup base = none → s_mir_next.env.lookup base = none := by
        intro base h_lookup_none
        rw [h_mir_next_eq]
        exact h_absent base (by simpa [h_cs] using h_lookup_none)
      have h_next_placeMap :
          (csAt cs0 prog (s_mir.pc + 1)).placeMap = ctx.cs.placeMap := by
        rw [csAt_succ h_get, resetInstrs_placeMap]
        simpa [h_cs] using (ConstExistingCtx.compileStmt_placeMap ctx)
      have h_mir_pc_next : s_mir_next.pc = s_mir.pc + 1 := by
        rw [h_mir_next_eq]
      have h_sim_next_canon :
          StateSim (csAt cs0 prog (s_mir.pc + 1)).placeMap ρa ρt s_mir_next s_osea_next
            (ptrSimOfCtx ρa ρt s_mir_next.env) := by
        simpa [h_next_placeMap, h_mir_next_eq, ConstExisting.LocalSim] using h_sim_next
      refine ⟨ρa, ρt, s_osea_next, h_steps, h_sim_next_canon, ?_, ?_,
        h_tag_fresh_next, ?_, h_noninterference_next, h_mir_pc_next, ?_⟩
      · simpa [h_next_placeMap] using h_closure_next
      · simpa [h_next_placeMap] using h_source_below_next
      · simpa [h_next_placeMap] using h_absent_next
      · exact h_pc_next.trans h_target_pc.symm
  | const_fresh ctx h_cs =>
      have h_sim_ctx :
          StateSim ctx.cs.placeMap ρa ρt s_mir s_osea (ptrSimOfCtx ρa ρt s_mir.env) := by
        simpa [h_cs] using h_sim
      have h_closure_ctx : TrackedPlaceTagClosure ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_closure
      have h_source_below_ctx : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_source_below
      have h_base_absent :
          (csAt cs0 prog s_mir.pc).placeMap.lookup ctx.base = none := by
        simpa [BaseAbsent, getPlaceInfo, h_cs] using ctx.h_absent
      have h_base_absent_ctx : ctx.cs.placeMap.lookup ctx.base = none := by
        simpa [h_cs] using h_base_absent
      have h_env_none : s_mir.env.lookup ctx.base = none :=
        h_absent ctx.base h_base_absent
      obtain ⟨freshAddr_m_step, allocMem_m, freshTag_m_step, _ap2_m, _ap3_m,
          h_alloc_pair_m_step, h_alloc_mMap_m, _h_own_m, _h_use_m, h_mir_next_eq⟩ :=
        ConstFresh.mirlite_step_inv ctx s_mir s_mir_next prog h_env_none h_mir_start h_mir_step
      have h_alloc_base_m_step : freshAddr_m_step = s_mir.mem.addrStart := by
        have h_fst := congrArg Prod.fst h_alloc_pair_m_step
        exact h_fst.symm.trans (h_alloc_base_any s_mir.mem (typeSize TyVal.NatTy))
      have h_alloc_addrStart_m_step :
          allocMem_m.addrStart = s_mir.mem.addrStart + blockSize LayoutTy.NatL := by
        have h_snd := congrArg (fun p => p.2.addrStart) h_alloc_pair_m_step
        calc
          allocMem_m.addrStart = (A_m.alloc s_mir.mem (typeSize TyVal.NatTy)).2.addrStart := by
            simpa using h_snd.symm
          _ = s_mir.mem.addrStart + typeSize TyVal.NatTy := by
            exact h_alloc_addrStart_any s_mir.mem (typeSize TyVal.NatTy)
          _ = s_mir.mem.addrStart + blockSize LayoutTy.NatL := by
            simp [typeSize, blockSize, layoutSize]
      have h_osea_start :
          StartsAt (compileProgFrom cs0 prog) s_osea.pc ctx.compiled := by
        simpa [h_cs, ConstFreshCtx.compiled] using h_osea_start_stmt
      have h_target_pc :
          targetPcAt cs0 prog (s_mir.pc + 1) = s_osea.pc + ctx.compiled.length := by
        simpa [h_cs, ConstFreshCtx.compiled] using h_target_pc_stmt
      obtain ⟨freshAddr_m, allocBase_o, tag_m, tag_o, ρa', ρt', s_osea_next,
          h_tag_eq, h_ρa', h_ρt', h_steps, h_sim_next, h_noninterference_next,
          h_env_next, h_nextTag_post, h_pc_next⟩ :=
        ConstFresh.simulation_structured
          (A_m := A_m)
          (ctx := ctx)
          (s_mir := s_mir) (s_osea := s_osea) (s_mir_next := s_mir_next)
          (ρa := ρa) (ρt := ρt)
          prog (compileProgFrom cs0 prog)
          h_sim_ctx h_noninterference h_source_below_ctx h_tag_fresh
          (h_alloc_base_any s_mir.mem (typeSize TyVal.NatTy))
          h_env_none h_mir_start h_osea_start h_mir_step
      have h_tag_fresh' : TagRenameFreshFrom ρt tag_m := by
        simpa [h_tag_eq] using h_tag_fresh
      have h_env_next_step :
          s_mir_next.env = s_mir.env.insert ctx.base (freshAddr_m_step, TyVal.NatTy, freshTag_m_step) := by
        rw [h_mir_next_eq]
      have h_fresh_info_eq :
          (freshAddr_m, TyVal.NatTy, tag_m) = (freshAddr_m_step, TyVal.NatTy, freshTag_m_step) := by
        apply Option.some.inj
        calc
          some (freshAddr_m, TyVal.NatTy, tag_m)
              = (s_mir.env.insert ctx.base (freshAddr_m, TyVal.NatTy, tag_m)).lookup ctx.base := by simp
          _ = s_mir_next.env.lookup ctx.base := by simpa [h_env_next]
          _ = (s_mir.env.insert ctx.base (freshAddr_m_step, TyVal.NatTy, freshTag_m_step)).lookup ctx.base := by
                simpa [h_env_next_step]
          _ = some (freshAddr_m_step, TyVal.NatTy, freshTag_m_step) := by simp
      have h_freshAddr_eq : freshAddr_m = freshAddr_m_step := by
        exact congrArg Prod.fst h_fresh_info_eq
      have h_alloc_base_m : freshAddr_m = s_mir.mem.addrStart := by
        exact h_freshAddr_eq.trans h_alloc_base_m_step
      have h_sim_next_canon :
          StateSim ctx.postPlaceMap ρa' ρt' s_mir_next s_osea_next
            (ptrSimOfCtx ρa' ρt' s_mir_next.env) := by
        refine StateSim.mono_ptr_sim h_sim_next ?_
        intro p tag_m' base off size tag_o' h_ptr
        rw [h_ρa', h_ρt', h_env_next]
        exact ptrSimOfCtx_extend_fresh_of_absent
          (freshBase := ctx.base)
          (freshLayout := LayoutTy.NatL)
          (freshAddr_m := freshAddr_m)
          (freshAddr_o := allocBase_o)
          (freshTag_m := tag_m)
          (freshTag_o := tag_o)
          (h_sim := h_sim)
          (h_absent := h_absent)
          (h_lookup_none := h_base_absent)
          (h_source_below := h_source_below)
          (h_fresh_addr := h_alloc_base_m)
          (h_tag_fresh := h_tag_fresh')
          h_ptr
      have h_closure_next :
          TrackedPlaceTagClosure ctx.postPlaceMap s_mir_next := by
        rw [h_mir_next_eq]
        have h_closure_write :
            TrackedPlaceTagClosure ctx.postPlaceMap
              { s_mir with
                env := s_mir.env.insert
                  ctx.base (freshAddr_m_step, layoutToTyVal LayoutTy.NatL, freshTag_m_step)
                mem := mirlite.writeWordSeq s_mir.mem freshAddr_m_step [mirlite.MemValue.Val ctx.n] } := by
          simpa [ConstFreshCtx.postPlaceMap, ConstFreshCtx.reg] using
            (TrackedPlaceTagClosure.extend_fresh_nonptr
              (π := ctx.cs.placeMap)
              (ρa := ρa)
              (ρt := ρt)
              (s_mir := s_mir)
              (s_osea := s_osea)
              (ptr_sim := ptrSimOfCtx ρa ρt s_mir.env)
              (freshBase := ctx.base)
              (freshReg := ctx.reg)
              (freshLayout := LayoutTy.NatL)
              (freshAddr := freshAddr_m_step)
              (freshTag := freshTag_m_step)
              (vals := [mirlite.MemValue.Val ctx.n])
              (h_sim := h_sim_ctx)
              (h_closure := h_closure_ctx)
              (h_lookup_none := h_base_absent_ctx)
              (h_vals_len := by simp [blockSize, layoutSize])
              (h_vals_nonptr := by
                intro i h_i q gq
                simp at h_i
                subst i
                simp)
              (h_disj := by
                intro base reg layout addr_m addr_o tag_m' tag_o' h_lookup h_ptr
                rw [h_alloc_base_m_step]
                exact blocks_disjoint_of_end_le_start
                  (SourceBlocksBelowAddrStart.of_place_runtime_sim h_source_below_ctx h_ptr).2))
        have h_write_mMap :
            (mirlite.writeWordSeq allocMem_m freshAddr_m_step [mirlite.MemValue.Val ctx.n]).mMap =
              (mirlite.writeWordSeq s_mir.mem freshAddr_m_step [mirlite.MemValue.Val ctx.n]).mMap := by
          exact mirlite_writeWordSeq_mMap_eq_of_mMap_eq
            h_alloc_mMap_m freshAddr_m_step [mirlite.MemValue.Val ctx.n]
        exact TrackedPlaceTagClosure.of_env_mem_mMap_eq
          (s_mir :=
            { s_mir with
              env := s_mir.env.insert
                ctx.base (freshAddr_m_step, layoutToTyVal LayoutTy.NatL, freshTag_m_step)
              mem := mirlite.writeWordSeq s_mir.mem freshAddr_m_step [mirlite.MemValue.Val ctx.n] })
          h_closure_write rfl h_write_mMap
      have h_source_below_next :
          SourceBlocksBelowAddrStart ctx.postPlaceMap s_mir_next := by
        simpa [ConstFreshCtx.postPlaceMap, ConstFreshCtx.reg] using
          (SourceBlocksBelowAddrStart.extend_fresh
            (π := ctx.cs.placeMap)
            (s_mir := s_mir)
            (s_mir_next := s_mir_next)
            (freshBase := ctx.base)
            (freshReg := ctx.reg)
            (freshLayout := LayoutTy.NatL)
            (freshAddr := freshAddr_m)
            (freshTag := tag_m)
            h_source_below_ctx h_env_next h_alloc_base_m
            (by rw [h_mir_next_eq]; simpa [mirlite.writeWordSeq] using h_alloc_addrStart_m_step)
            (by decide))
      have h_tag_fresh_next :
          TagRenameFreshFrom ρt' s_mir_next.ap.NextTag := by
        rw [h_ρt', h_nextTag_post]
        simpa [h_tag_eq] using
          (TagRenameFreshFrom.extendTagRename
            (ρt := ρt)
            (nextTag := s_mir.ap.NextTag)
            (freshTag_o := tag_o)
            h_tag_fresh)
      have h_absent_ctx :
          ∀ base, ctx.cs.placeMap.lookup base = none → s_mir.env.lookup base = none := by
        intro base h_lookup_none
        exact h_absent base (by simpa [h_cs] using h_lookup_none)
      have h_absent_next :
          ∀ base, ctx.postPlaceMap.lookup base = none → s_mir_next.env.lookup base = none := by
        intro base h_lookup_none
        rw [h_env_next]
        exact absent_env_insert_of_lookup_none
          (π := ctx.cs.placeMap)
          (s_mir := s_mir)
          (freshBase := ctx.base)
          (freshReg := ctx.reg)
          (freshLayout := LayoutTy.NatL)
          (freshAddr := freshAddr_m)
          (freshTy := TyVal.NatTy)
          (freshTag := tag_m)
          h_absent_ctx base (by simpa [ConstFreshCtx.postPlaceMap, ConstFreshCtx.reg] using h_lookup_none)
      have h_next_placeMap :
          (csAt cs0 prog (s_mir.pc + 1)).placeMap = ctx.postPlaceMap := by
        rw [csAt_succ h_get, resetInstrs_placeMap]
        simpa [h_cs] using (ConstFreshCtx.compileStmt_placeMap ctx)
      have h_mir_pc_next : s_mir_next.pc = s_mir.pc + 1 := by
        rw [h_mir_next_eq]
      refine ⟨ρa', ρt', s_osea_next, h_steps, ?_, ?_, ?_, h_tag_fresh_next, ?_,
        h_noninterference_next, h_mir_pc_next, ?_⟩
      · simpa [h_next_placeMap] using h_sim_next_canon
      · simpa [h_next_placeMap] using h_closure_next
      · simpa [h_next_placeMap] using h_source_below_next
      · simpa [h_next_placeMap] using h_absent_next
      · exact h_pc_next.trans h_target_pc.symm
  | struct_init_existing ctx h_cs =>
      have h_sim_ctx :
          StructInitExisting.LocalSim ctx ρa ρt s_mir s_osea (ptrSimOfCtx ρa ρt s_mir.env) := by
        simpa [StructInitExisting.LocalSim, h_cs] using h_sim
      have h_closure_ctx : TrackedPlaceTagClosure ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_closure
      have h_source_below_ctx : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_source_below
      obtain ⟨addr_m, _addr_o, tag_m, _tag_o, h_dst_ptr, _h_dst_block⟩ :=
        StateSim.place_projected h_sim_ctx ctx.h_lookup ctx.h_path
      have h_dst_env := place_runtime_sim.env h_dst_ptr
      obtain ⟨ap_write, h_use, h_mir_next_eq⟩ :=
        StructInitExisting.mirlite_step_inv ctx s_mir s_mir_next prog addr_m tag_m
          h_dst_env h_mir_start h_mir_step
      have h_closure_next :
          TrackedPlaceTagClosure ctx.cs.placeMap s_mir_next := by
        rw [h_mir_next_eq]
        exact TrackedPlaceTagClosure.writeWordSeq_of_nonptr h_closure_ctx (by
          intro i h_i q gq
          unfold wordStructMirVals
          simp)
      have h_osea_start :
          StartsAt (compileProgFrom cs0 prog) s_osea.pc ctx.compiled := by
        simpa [h_cs, StructInitExistingCtx.compiled] using h_osea_start_stmt
      have h_target_pc :
          targetPcAt cs0 prog (s_mir.pc + 1) = s_osea.pc + ctx.compiled.length := by
        simpa [h_cs, StructInitExistingCtx.compiled] using h_target_pc_stmt
      obtain ⟨s_osea_next, h_steps, h_sim_next, h_noninterference_next, h_pc_next⟩ :=
        StructInitExisting.simulation
          (A_m := A_m) (A_o := oseair.bumpAllocator)
          (ctx := ctx)
          (s_mir := s_mir) (s_osea := s_osea) (s_mir_next := s_mir_next)
          (ρa := ρa) (ρt := ρt)
          prog (compileProgFrom cs0 prog)
          h_sim_ctx h_noninterference h_mir_start h_osea_start h_mir_step
      have h_tag_fresh_next :
          TagRenameFreshFrom ρt s_mir_next.ap.NextTag := by
        rw [h_mir_next_eq]
        simpa [sb_use_mb_nextTag_eq h_use] using h_tag_fresh
      have h_source_below_next :
          SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir_next := by
        rw [h_mir_next_eq]
        exact SourceBlocksBelowAddrStart.mono h_source_below_ctx rfl (by simp)
      have h_absent_next :
          ∀ base, ctx.cs.placeMap.lookup base = none → s_mir_next.env.lookup base = none := by
        intro base h_lookup_none
        rw [h_mir_next_eq]
        exact h_absent base (by simpa [h_cs] using h_lookup_none)
      have h_next_placeMap :
          (csAt cs0 prog (s_mir.pc + 1)).placeMap = ctx.cs.placeMap := by
        rw [csAt_succ h_get, resetInstrs_placeMap]
        simpa [h_cs] using (StructInitExistingCtx.compileStmt_placeMap ctx)
      have h_mir_pc_next : s_mir_next.pc = s_mir.pc + 1 := by
        rw [h_mir_next_eq]
      have h_sim_next_canon :
          StateSim (csAt cs0 prog (s_mir.pc + 1)).placeMap ρa ρt s_mir_next s_osea_next
            (ptrSimOfCtx ρa ρt s_mir_next.env) := by
        simpa [h_next_placeMap, h_mir_next_eq, StructInitExisting.LocalSim] using h_sim_next
      refine ⟨ρa, ρt, s_osea_next, h_steps, h_sim_next_canon, ?_, ?_,
        h_tag_fresh_next, ?_, h_noninterference_next, h_mir_pc_next, ?_⟩
      · simpa [h_next_placeMap] using h_closure_next
      · simpa [h_next_placeMap] using h_source_below_next
      · simpa [h_next_placeMap] using h_absent_next
      · exact h_pc_next.trans h_target_pc.symm
  | struct_init_fresh ctx h_cs =>
      have h_sim_ctx :
          StateSim ctx.cs.placeMap ρa ρt s_mir s_osea (ptrSimOfCtx ρa ρt s_mir.env) := by
        simpa [h_cs] using h_sim
      have h_closure_ctx : TrackedPlaceTagClosure ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_closure
      have h_source_below_ctx : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_source_below
      have h_base_absent :
          (csAt cs0 prog s_mir.pc).placeMap.lookup ctx.base = none := by
        simpa [BaseAbsent, getPlaceInfo, h_cs] using ctx.h_absent
      have h_base_absent_ctx : ctx.cs.placeMap.lookup ctx.base = none := by
        simpa [h_cs] using h_base_absent
      have h_env_none : s_mir.env.lookup ctx.base = none :=
        h_absent ctx.base h_base_absent
      obtain ⟨freshAddr_m_step, allocMem_m, freshTag_m_step, _ap2_m, _ap3_m,
          h_alloc_pair_m_step, h_alloc_mMap_m, _h_own_m, _h_use_m, h_mir_next_eq⟩ :=
        StructInitFresh.mirlite_step_inv ctx s_mir s_mir_next prog h_env_none h_mir_start h_mir_step
      have h_alloc_base_m_step : freshAddr_m_step = s_mir.mem.addrStart := by
        have h_fst := congrArg Prod.fst h_alloc_pair_m_step
        exact h_fst.symm.trans (h_alloc_base_any s_mir.mem (typeSize (wordStructTy ctx.fields)))
      have h_alloc_addrStart_m_step :
          allocMem_m.addrStart = s_mir.mem.addrStart + blockSize (wordStructLayout ctx.fields) := by
        have h_snd := congrArg (fun p => p.2.addrStart) h_alloc_pair_m_step
        exact h_snd.symm.trans (by
          rw [← layoutToTyVal_wordStructLayout]
          simpa [blockSize] using h_alloc_addrStart_any s_mir.mem (typeSize (wordStructTy ctx.fields)))
      have h_osea_start :
          StartsAt (compileProgFrom cs0 prog) s_osea.pc ctx.compiled := by
        simpa [h_cs, StructInitFreshCtx.compiled] using h_osea_start_stmt
      have h_target_pc :
          targetPcAt cs0 prog (s_mir.pc + 1) = s_osea.pc + ctx.compiled.length := by
        simpa [h_cs, StructInitFreshCtx.compiled] using h_target_pc_stmt
      obtain ⟨freshAddr_m, allocBase_o, tag_m, tag_o, ρa', ρt', s_osea_next,
          h_tag_eq, h_ρa', h_ρt', h_steps, h_sim_next, h_noninterference_next,
          h_env_next, h_nextTag_post, h_pc_next⟩ :=
        StructInitFresh.simulation_structured
          (A_m := A_m)
          (ctx := ctx)
          (s_mir := s_mir) (s_osea := s_osea) (s_mir_next := s_mir_next)
          (ρa := ρa) (ρt := ρt)
          prog (compileProgFrom cs0 prog)
          h_sim_ctx h_noninterference h_source_below_ctx h_tag_fresh
          (h_alloc_base_any s_mir.mem (typeSize (wordStructTy ctx.fields)))
          h_env_none h_mir_start h_osea_start h_mir_step
      have h_tag_fresh' : TagRenameFreshFrom ρt tag_m := by
        simpa [h_tag_eq] using h_tag_fresh
      have h_env_next_step :
          s_mir_next.env =
            s_mir.env.insert ctx.base
              (freshAddr_m_step, wordStructTy ctx.fields, freshTag_m_step) := by
        rw [h_mir_next_eq]
      have h_fresh_info_eq :
          (freshAddr_m, wordStructTy ctx.fields, tag_m) =
            (freshAddr_m_step, wordStructTy ctx.fields, freshTag_m_step) := by
        apply Option.some.inj
        calc
          some (freshAddr_m, wordStructTy ctx.fields, tag_m)
              = (s_mir.env.insert ctx.base
                  (freshAddr_m, wordStructTy ctx.fields, tag_m)).lookup ctx.base := by simp
          _ = s_mir_next.env.lookup ctx.base := by simpa [h_env_next]
          _ = (s_mir.env.insert ctx.base
                (freshAddr_m_step, wordStructTy ctx.fields, freshTag_m_step)).lookup ctx.base := by
                simpa [h_env_next_step]
          _ = some (freshAddr_m_step, wordStructTy ctx.fields, freshTag_m_step) := by simp
      have h_freshAddr_eq : freshAddr_m = freshAddr_m_step := by
        exact congrArg Prod.fst h_fresh_info_eq
      have h_alloc_base_m : freshAddr_m = s_mir.mem.addrStart := by
        exact h_freshAddr_eq.trans h_alloc_base_m_step
      have h_sim_next_canon :
          StateSim ctx.postPlaceMap ρa' ρt' s_mir_next s_osea_next
            (ptrSimOfCtx ρa' ρt' s_mir_next.env) := by
        refine StateSim.mono_ptr_sim h_sim_next ?_
        intro p tag_m' base off size tag_o' h_ptr
        rw [h_ρa', h_ρt', h_env_next]
        simpa [layoutToTyVal_wordStructLayout] using
          (ptrSimOfCtx_extend_fresh_of_absent
            (freshBase := ctx.base)
            (freshLayout := wordStructLayout ctx.fields)
            (freshAddr_m := freshAddr_m)
            (freshAddr_o := allocBase_o)
            (freshTag_m := tag_m)
            (freshTag_o := tag_o)
            (h_sim := h_sim)
            (h_absent := h_absent)
            (h_lookup_none := h_base_absent)
            (h_source_below := h_source_below)
            (h_fresh_addr := h_alloc_base_m)
            (h_tag_fresh := h_tag_fresh')
            h_ptr)
      have h_closure_next :
          TrackedPlaceTagClosure ctx.postPlaceMap s_mir_next := by
        rw [h_mir_next_eq]
        have h_closure_write :
            TrackedPlaceTagClosure ctx.postPlaceMap
              { s_mir with
                env := s_mir.env.insert ctx.base
                  (freshAddr_m_step,
                    layoutToTyVal (wordStructLayout ctx.fields), freshTag_m_step)
                mem :=
                  mirlite.writeWordSeq s_mir.mem freshAddr_m_step
                    (wordStructMirVals ctx.fields) } := by
          simpa [StructInitFreshCtx.postPlaceMap, StructInitFreshCtx.reg] using
            (TrackedPlaceTagClosure.extend_fresh_nonptr
              (π := ctx.cs.placeMap)
              (ρa := ρa)
              (ρt := ρt)
              (s_mir := s_mir)
              (s_osea := s_osea)
              (ptr_sim := ptrSimOfCtx ρa ρt s_mir.env)
              (freshBase := ctx.base)
              (freshReg := ctx.reg)
              (freshLayout := wordStructLayout ctx.fields)
              (freshAddr := freshAddr_m_step)
              (freshTag := freshTag_m_step)
              (vals := wordStructMirVals ctx.fields)
              (h_sim := h_sim_ctx)
              (h_closure := h_closure_ctx)
              (h_lookup_none := h_base_absent_ctx)
              (h_vals_len := by simp)
              (h_vals_nonptr := by
                intro i h_i q gq
                unfold wordStructMirVals
                simp)
              (h_disj := by
                intro base reg layout addr_m addr_o tag_m' tag_o' h_lookup h_ptr
                rw [h_alloc_base_m_step]
                exact blocks_disjoint_of_end_le_start
                  (SourceBlocksBelowAddrStart.of_place_runtime_sim h_source_below_ctx h_ptr).2))
        have h_write_mMap :
            (mirlite.writeWordSeq allocMem_m freshAddr_m_step (wordStructMirVals ctx.fields)).mMap =
              (mirlite.writeWordSeq s_mir.mem freshAddr_m_step (wordStructMirVals ctx.fields)).mMap := by
          exact mirlite_writeWordSeq_mMap_eq_of_mMap_eq
            h_alloc_mMap_m freshAddr_m_step (wordStructMirVals ctx.fields)
        exact TrackedPlaceTagClosure.of_env_mem_mMap_eq
          (s_mir :=
            { s_mir with
              env := s_mir.env.insert ctx.base
                (freshAddr_m_step,
                  layoutToTyVal (wordStructLayout ctx.fields), freshTag_m_step)
              mem :=
                mirlite.writeWordSeq s_mir.mem freshAddr_m_step
                  (wordStructMirVals ctx.fields) })
          h_closure_write (by simp [layoutToTyVal_wordStructLayout]) h_write_mMap
      have h_source_below_next :
          SourceBlocksBelowAddrStart ctx.postPlaceMap s_mir_next := by
        simpa [StructInitFreshCtx.postPlaceMap, StructInitFreshCtx.reg] using
          (SourceBlocksBelowAddrStart.extend_fresh
            (π := ctx.cs.placeMap)
            (s_mir := s_mir)
            (s_mir_next := s_mir_next)
            (freshBase := ctx.base)
            (freshReg := ctx.reg)
            (freshLayout := wordStructLayout ctx.fields)
            (freshAddr := freshAddr_m)
            (freshTag := tag_m)
            h_source_below_ctx
            (by simpa [layoutToTyVal_wordStructLayout] using h_env_next)
            h_alloc_base_m
            (by rw [h_mir_next_eq]; simpa using h_alloc_addrStart_m_step)
            (wordStruct_nonempty_size ctx.h_fields))
      have h_tag_fresh_next :
          TagRenameFreshFrom ρt' s_mir_next.ap.NextTag := by
        rw [h_ρt', h_nextTag_post]
        simpa [h_tag_eq] using
          (TagRenameFreshFrom.extendTagRename
            (ρt := ρt)
            (nextTag := s_mir.ap.NextTag)
            (freshTag_o := tag_o)
            h_tag_fresh)
      have h_absent_ctx :
          ∀ base, ctx.cs.placeMap.lookup base = none → s_mir.env.lookup base = none := by
        intro base h_lookup_none
        exact h_absent base (by simpa [h_cs] using h_lookup_none)
      have h_absent_next :
          ∀ base, ctx.postPlaceMap.lookup base = none → s_mir_next.env.lookup base = none := by
        intro base h_lookup_none
        rw [h_env_next]
        exact absent_env_insert_of_lookup_none
          (π := ctx.cs.placeMap)
          (s_mir := s_mir)
          (freshBase := ctx.base)
          (freshReg := ctx.reg)
          (freshLayout := wordStructLayout ctx.fields)
          (freshAddr := freshAddr_m)
          (freshTy := wordStructTy ctx.fields)
          (freshTag := tag_m)
          h_absent_ctx base (by simpa [StructInitFreshCtx.postPlaceMap, StructInitFreshCtx.reg] using h_lookup_none)
      have h_next_placeMap :
          (csAt cs0 prog (s_mir.pc + 1)).placeMap = ctx.postPlaceMap := by
        rw [csAt_succ h_get, resetInstrs_placeMap]
        simpa [h_cs] using (StructInitFreshCtx.compileStmt_placeMap ctx)
      have h_mir_pc_next : s_mir_next.pc = s_mir.pc + 1 := by
        rw [h_mir_next_eq]
      refine ⟨ρa', ρt', s_osea_next, h_steps, ?_, ?_, ?_, h_tag_fresh_next, ?_,
        h_noninterference_next, h_mir_pc_next, ?_⟩
      · simpa [h_next_placeMap] using h_sim_next_canon
      · simpa [h_next_placeMap] using h_closure_next
      · simpa [h_next_placeMap] using h_source_below_next
      · simpa [h_next_placeMap] using h_absent_next
      · exact h_pc_next.trans h_target_pc.symm
  | copy_existing ctx h_cs =>
      have h_sim_ctx :
          CopyExisting.LocalSim ctx ρa ρt s_mir s_osea (ptrSimOfCtx ρa ρt s_mir.env) := by
        simpa [CopyExisting.LocalSim, h_cs] using h_sim
      have h_closure_ctx : TrackedPlaceTagClosure ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_closure
      have h_source_below_ctx : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_source_below
      obtain ⟨srcAddr_m, srcAddr_o, srcTag_m, srcTag_o, h_src_ptr, _h_src_block⟩ :=
        StateSim.place h_sim_ctx ctx.h_src_lookup
      obtain ⟨dstAddr_m, dstAddr_o, dstTag_m, dstTag_o, h_dst_ptr, _h_dst_block⟩ :=
        StateSim.place h_sim_ctx ctx.h_dst_lookup
      have h_src_env := place_runtime_sim.env h_src_ptr
      have h_dst_env := place_runtime_sim.env h_dst_ptr
      obtain ⟨ap_read, ap_write, h_read, h_use, h_mir_next_eq⟩ :=
        CopyExisting.mirlite_step_inv ctx s_mir s_mir_next prog srcAddr_m srcTag_m dstAddr_m dstTag_m
          h_src_env h_dst_env h_mir_start h_mir_step
      have h_closure_next :
          TrackedPlaceTagClosure ctx.cs.placeMap s_mir_next := by
        rw [h_mir_next_eq]
        simpa [CopyMirPost, TrackedPlaceTagClosure] using
          (TrackedPlaceTagClosure.copy_from_place_to_base
            (π := ctx.cs.placeMap)
            (ρa := ρa)
            (ρt := ρt)
            (s_mir := s_mir)
            (s_osea := s_osea)
            (ptr_sim := ptrSimOfCtx ρa ρt s_mir.env)
            (src := { base := ctx.srcBase, path := [] })
            (srcReg := ctx.srcReg)
            (srcBaseLayout := ctx.layout)
            (dstLayout := ctx.layout)
            (srcOff := 0)
            (srcBaseAddr := srcAddr_m)
            (srcBaseAddr_o := srcAddr_o)
            (srcBaseTag := srcTag_m)
            (srcBaseTag_o := srcTag_o)
            (dstBase := ctx.dstBase)
            (dstReg := ctx.dstReg)
            (dstBaseAddr := dstAddr_m)
            (dstBaseAddr_o := dstAddr_o)
            (dstBaseTag := dstTag_m)
            (dstBaseTag_o := dstTag_o)
            (h_sim := h_sim_ctx)
            (h_closure := h_closure_ctx)
            (h_src_lookup := ctx.h_src_lookup)
            (h_src_path := by simp [layoutResolvePath])
            (h_src_ptr := h_src_ptr)
            (h_dst_lookup := ctx.h_dst_lookup)
            (h_dst_ptr := h_dst_ptr))
      have h_osea_start :
          StartsAt (compileProgFrom cs0 prog) s_osea.pc ctx.compiled := by
        simpa [h_cs, CopyExistingCtx.compiled] using h_osea_start_stmt
      have h_target_pc :
          targetPcAt cs0 prog (s_mir.pc + 1) = s_osea.pc + ctx.compiled.length := by
        simpa [h_cs, CopyExistingCtx.compiled] using h_target_pc_stmt
      obtain ⟨s_osea_next, h_steps, h_sim_next, h_noninterference_next, h_pc_next⟩ :=
        CopyExisting.simulation
          (A_m := A_m) (A_o := oseair.bumpAllocator)
          (ctx := ctx)
          (s_mir := s_mir) (s_osea := s_osea) (s_mir_next := s_mir_next)
          (ρa := ρa) (ρt := ρt)
          prog (compileProgFrom cs0 prog)
          h_sim_ctx h_noninterference h_mir_start h_osea_start h_mir_step
      have h_tag_fresh_next :
          TagRenameFreshFrom ρt s_mir_next.ap.NextTag := by
        rw [h_mir_next_eq]
        simpa [CopyMirPost, sb_use_mb_nextTag_eq h_use, sb_read_nextTag_eq h_read] using h_tag_fresh
      have h_source_below_next :
          SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir_next := by
        refine SourceBlocksBelowAddrStart.mono h_source_below_ctx (by rw [h_mir_next_eq]; simp [CopyMirPost]) ?_
        rw [h_mir_next_eq]
        simp [CopyMirPost]
      have h_absent_next :
          ∀ base, ctx.cs.placeMap.lookup base = none → s_mir_next.env.lookup base = none := by
        intro base h_lookup_none
        rw [h_mir_next_eq]
        simpa [CopyMirPost] using h_absent base (by simpa [h_cs] using h_lookup_none)
      have h_next_placeMap :
          (csAt cs0 prog (s_mir.pc + 1)).placeMap = ctx.cs.placeMap := by
        rw [csAt_succ h_get, resetInstrs_placeMap]
        simpa [h_cs] using (CopyExistingCtx.compileStmt_placeMap ctx)
      have h_mir_pc_next : s_mir_next.pc = s_mir.pc + 1 := by
        rw [h_mir_next_eq]
        simp [CopyMirPost]
      have h_sim_next_canon :
          StateSim (csAt cs0 prog (s_mir.pc + 1)).placeMap ρa ρt s_mir_next s_osea_next
            (ptrSimOfCtx ρa ρt s_mir_next.env) := by
        simpa [h_next_placeMap, h_mir_next_eq, CopyExisting.LocalSim, CopyMirPost] using h_sim_next
      refine ⟨ρa, ρt, s_osea_next, h_steps, h_sim_next_canon, ?_, ?_,
        h_tag_fresh_next, ?_, h_noninterference_next, h_mir_pc_next, ?_⟩
      · simpa [h_next_placeMap] using h_closure_next
      · simpa [h_next_placeMap] using h_source_below_next
      · simpa [h_next_placeMap] using h_absent_next
      · exact h_pc_next.trans h_target_pc.symm
  | ref_existing ctx h_cs h_src_nonempty =>
      have h_temp := CompilerInv.ref_temp_safe ctx h_inv' h_cs
      have h_sim_ctx :
          RefExisting.LocalSim ctx ρa ρt s_mir s_osea (ptrSimOfCtx ρa ρt s_mir.env) := by
        simpa [RefExisting.LocalSim, h_cs] using h_sim
      have h_closure_ctx : TrackedPlaceTagClosure ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_closure
      have h_source_below_ctx : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_source_below
      obtain ⟨srcBase_m0, srcBase_o0, srcTag_m0, srcTag_o0, h_src_ptr, _h_src_block⟩ :=
        StateSim.place_projected h_sim_ctx ctx.h_src_lookup ctx.h_src_path
      obtain ⟨dstBase_m0, dstBase_o0, dstTag_m0, dstTag_o0, h_dst_ptr, _h_dst_block⟩ :=
        StateSim.place_projected h_sim_ctx ctx.h_dst_lookup ctx.h_dst_path
      have h_src_env0 := place_runtime_sim.env h_src_ptr
      have h_dst_env0 := place_runtime_sim.env h_dst_ptr
      obtain ⟨ap_ref_m, newTag_m0, ap_write_m, h_mir_ref, h_mir_use, h_mir_next_eq⟩ :=
        RefExisting.mirlite_step_inv ctx s_mir s_mir_next prog
          srcBase_m0 srcTag_m0 dstBase_m0 dstTag_m0
          h_src_env0 h_dst_env0 h_mir_start h_mir_step
      have h_closure_next :
          TrackedPlaceTagClosure ctx.cs.placeMap s_mir_next := by
        rw [h_mir_next_eq]
        exact TrackedPlaceTagClosure.ref_to_projected
          (π := ctx.cs.placeMap)
          (ρa := ρa)
          (ρt := ρt)
          (s_mir := s_mir)
          (s_osea := s_osea)
          (ptr_sim := ptrSimOfCtx ρa ρt s_mir.env)
          (h_sim := h_sim_ctx)
          (h_closure := h_closure_ctx)
          (h_src_lookup := ctx.h_src_lookup)
          (h_src_path := ctx.h_src_path)
          (h_src_ptr := h_src_ptr)
          (h_dst_lookup := ctx.h_dst_lookup)
          (h_dst_path := ctx.h_dst_path)
          (h_dst_ptr := h_dst_ptr)
      have h_osea_start :
          StartsAt (compileProgFrom cs0 prog) s_osea.pc ctx.compiled := by
        simpa [h_cs, RefExistingCtx.compiled] using h_osea_start_stmt
      have h_target_pc :
          targetPcAt cs0 prog (s_mir.pc + 1) = s_osea.pc + ctx.compiled.length := by
        simpa [h_cs, RefExistingCtx.compiled] using h_target_pc_stmt
      obtain ⟨srcBase_m, srcBase_o, srcTag_m, newTag_m, borTag_o, ρt', ptr_sim', s_osea_next,
          h_src_env, h_src_addr_base, h_newTag_eq_next, h_ρt', h_ptr_sim',
          h_steps, h_sim_next, h_noninterference_next, h_env_next, h_pc_next⟩ :=
        RefExisting.simulation_structured
          (A_m := A_m)
          (ctx := ctx)
          (s_mir := s_mir) (s_osea := s_osea) (s_mir_next := s_mir_next)
          (ρa := ρa) (ρt := ρt)
          (prog_mir := prog)
          (prog_osea := compileProgFrom cs0 prog)
          h_sim_ctx h_noninterference
          h_tag_fresh
          h_mir_start h_mir_step h_osea_start
          h_src_nonempty
      have h_sim_next_canon :
          StateSim ctx.cs.placeMap ρa ρt' s_mir_next s_osea_next
            (ptrSimOfCtx ρa ρt' s_mir_next.env) := by
        refine StateSim.mono_ptr_sim h_sim_next ?_
        intro p tag_m base off size tag_o h_post
        rw [h_ptr_sim'] at h_post
        rw [h_env_next, h_ρt']
        cases h_post with
        | inl h_old =>
            exact ptrSimOfCtx_extendTagRename_of_fresh h_old
              (by simpa [h_newTag_eq_next] using h_tag_fresh)
        | inr h_new =>
            rcases h_new with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
            refine ⟨srcBase_m, ctx.srcBaseLayout, ctx.srcLayout, ctx.srcOff, srcTag_m,
              ?_, ctx.h_src_path, h_src_addr_base, rfl, ?_, rfl⟩
            · simpa [h_env_next] using h_src_env
            · simp
      have h_nextTag_post :
          s_mir_next.ap.NextTag = s_mir.ap.NextTag + 1 := by
        rw [h_mir_next_eq]
        rw [sb_use_mb_nextTag_eq h_mir_use]
        simpa [h_newTag_eq_next] using sb_ref_nextTag_succ_local h_mir_ref
      have h_tag_fresh_next :
          TagRenameFreshFrom ρt' s_mir_next.ap.NextTag := by
        rw [h_ρt', h_nextTag_post]
        simpa [h_newTag_eq_next] using
          (TagRenameFreshFrom.extendTagRename
            (ρt := ρt)
            (nextTag := s_mir.ap.NextTag)
            (freshTag_o := borTag_o)
            h_tag_fresh)
      have h_source_below_next :
          SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir_next := by
        refine SourceBlocksBelowAddrStart.mono h_source_below_ctx h_env_next ?_
        rw [h_mir_next_eq]
        simp
      have h_absent_next :
          ∀ base, ctx.cs.placeMap.lookup base = none → s_mir_next.env.lookup base = none := by
        intro base h_lookup_none
        rw [h_env_next]
        exact h_absent base (by simpa [h_cs] using h_lookup_none)
      have h_next_placeMap :
          (csAt cs0 prog (s_mir.pc + 1)).placeMap = ctx.cs.placeMap := by
        rw [csAt_succ h_get, resetInstrs_placeMap]
        simpa [h_cs] using (RefExistingCtx.compileStmt_placeMap ctx)
      have h_mir_pc_next : s_mir_next.pc = s_mir.pc + 1 := by
        rw [h_mir_next_eq]
      refine ⟨ρa, ρt', s_osea_next, h_steps, ?_, ?_, ?_, h_tag_fresh_next, ?_,
        h_noninterference_next, h_mir_pc_next, ?_⟩
      · simpa [h_next_placeMap] using h_sim_next_canon
      · simpa [h_next_placeMap] using h_closure_next
      · simpa [h_next_placeMap] using h_source_below_next
      · simpa [h_next_placeMap] using h_absent_next
      · exact h_pc_next.trans h_target_pc.symm
  | deref_projected_existing ctx h_cs h_inner_nonempty =>
      have h_temp := CompilerInv.deref_projected_temp_safe ctx h_inv' h_cs
      have h_pointee_tracked :=
        CompilerInv.deref_projected_pointee_tracked ctx h_inv' h_cs
      have h_sim_ctx :
          DerefProjectedExisting.LocalSim ctx ρa ρt s_mir s_osea
            (ptrSimOfCtx ρa ρt s_mir.env) := by
        simpa [DerefProjectedExisting.LocalSim, h_cs] using h_sim
      have h_closure_ctx : TrackedPlaceTagClosure ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_closure
      have h_source_below_ctx : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_source_below
      obtain ⟨srcBaseAddr_m, _srcBaseAddr_o, srcTag_m, _srcTag_o, h_src_ptr, _h_src_block⟩ :=
        StateSim.place_projected h_sim_ctx ctx.h_src_lookup ctx.h_src_path
      obtain ⟨dstBaseAddr_m, dstBaseAddr_o, dstTag_m, dstTag_o, h_dst_ptr, _h_dst_block⟩ :=
        StateSim.place h_sim_ctx ctx.h_dst_lookup
      have h_src_env := place_runtime_sim.env h_src_ptr
      have h_dst_env := place_runtime_sim.env h_dst_ptr
      obtain ⟨ap_src_read, q, gq, targetRes, ap_target_read, ap_write,
          h_src_read, h_src_mem, h_resolve, h_target_read, h_mir_use, h_mir_next_eq⟩ :=
        DerefProjectedExisting.mirlite_step_inv ctx s_mir s_mir_next prog
          srcBaseAddr_m srcTag_m dstBaseAddr_m dstTag_m
          h_src_env h_dst_env h_mir_start h_mir_step
      obtain ⟨targetReg, targetBaseLayout, targetOff, _targetBaseAddr,
          h_q_lookup, h_q_path, _h_q_env, h_target_addr, h_target_ty⟩ :=
        h_pointee_tracked srcBaseAddr_m srcTag_m q gq ap_src_read targetRes
          h_src_env h_src_mem h_resolve
      obtain ⟨targetBaseAddr_m, targetBaseAddr_o, targetBaseTag_m, targetBaseTag_o,
          h_q_ptr, _h_q_block⟩ :=
        StateSim.place h_sim_ctx h_q_lookup
      have h_q_env_eq :
          (targetBaseAddr_m, layoutToTyVal targetBaseLayout, targetBaseTag_m) =
            (_targetBaseAddr, layoutToTyVal targetBaseLayout, targetRes.tag) := by
        exact Option.some.inj ((place_runtime_sim.env h_q_ptr).symm.trans _h_q_env)
      have h_q_addr : targetBaseAddr_m = _targetBaseAddr := by
        exact congrArg Prod.fst h_q_env_eq
      have h_closure_next :
          TrackedPlaceTagClosure ctx.cs.placeMap s_mir_next := by
        rw [h_mir_next_eq]
        simpa [TrackedPlaceTagClosure, h_q_addr, h_target_addr, h_target_ty] using
          (TrackedPlaceTagClosure.copy_from_place_to_projected
            (π := ctx.cs.placeMap)
            (ρa := ρa)
            (ρt := ρt)
            (s_mir := s_mir)
            (s_osea := s_osea)
            (ptr_sim := ptrSimOfCtx ρa ρt s_mir.env)
            (src := q)
            (dst := ctx.dst)
            (srcReg := targetReg)
            (dstReg := ctx.dstReg)
            (srcBaseLayout := targetBaseLayout)
            (dstBaseLayout := ctx.dstBaseLayout)
            (dstLayout := ctx.innerLayout)
            (srcOff := targetOff)
            (dstOff := ctx.dstOff)
            (srcBaseAddr := targetBaseAddr_m)
            (srcBaseAddr_o := targetBaseAddr_o)
            (srcBaseTag := targetBaseTag_m)
            (srcBaseTag_o := targetBaseTag_o)
            (dstBaseAddr := dstBaseAddr_m)
            (dstBaseAddr_o := dstBaseAddr_o)
            (dstBaseTag := dstTag_m)
            (dstBaseTag_o := dstTag_o)
            (h_sim := h_sim_ctx)
            (h_closure := h_closure_ctx)
            (h_src_lookup := h_q_lookup)
            (h_src_path := h_q_path)
            (h_src_ptr := h_q_ptr)
            (h_dst_lookup := ctx.h_dst_lookup)
            (h_dst_path := ctx.h_dst_path)
            (h_dst_ptr := h_dst_ptr))
      have h_osea_start :
          StartsAt (compileProgFrom cs0 prog) s_osea.pc (DerefProjectedExistingCtx.compiled ctx) := by
        have h_osea_start' :
            StartsAt (compileProgFrom cs0 prog) s_osea.pc
              (compileStmt ctx.cs (DerefProjectedExisting.stmt ctx)).instrs := by
          simpa [h_cs, DerefProjectedExisting.stmt] using h_osea_start_stmt
        have h_compiled_eq :
            (compileStmt ctx.cs (DerefProjectedExisting.stmt ctx)).instrs =
              DerefProjectedExistingCtx.compiled ctx := by
          rfl
        simpa [h_compiled_eq] using h_osea_start'
      have h_target_pc :
          targetPcAt cs0 prog (s_mir.pc + 1) =
            s_osea.pc + (DerefProjectedExistingCtx.compiled ctx).length := by
        have h_target_pc' :
            targetPcAt cs0 prog (s_mir.pc + 1) =
              s_osea.pc + (compileStmt ctx.cs (DerefProjectedExisting.stmt ctx)).instrs.length := by
          simpa [h_cs, DerefProjectedExisting.stmt] using h_target_pc_stmt
        have h_compiled_eq :
            (compileStmt ctx.cs (DerefProjectedExisting.stmt ctx)).instrs =
              DerefProjectedExistingCtx.compiled ctx := by
          rfl
        simpa [h_compiled_eq] using h_target_pc'
      obtain ⟨s_osea_next, h_steps, h_sim_next, h_noninterference_next, h_pc_next⟩ :=
        DerefProjectedExisting.simulation
          (A_m := A_m)
          (ctx := ctx)
          h_sim_ctx h_noninterference
          h_mir_start h_mir_step h_pointee_tracked
          h_osea_start h_inner_nonempty
      have h_tag_fresh_next :
          TagRenameFreshFrom ρt s_mir_next.ap.NextTag := by
        rw [h_mir_next_eq]
        simpa [sb_use_mb_nextTag_eq h_mir_use, sb_read_nextTag_eq h_target_read,
          sb_read_nextTag_eq h_src_read] using h_tag_fresh
      have h_source_below_next :
          SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir_next := by
        refine SourceBlocksBelowAddrStart.mono h_source_below_ctx (by rw [h_mir_next_eq]) ?_
        rw [h_mir_next_eq]
        simp
      have h_absent_next :
          ∀ base, ctx.cs.placeMap.lookup base = none → s_mir_next.env.lookup base = none := by
        intro base h_lookup_none
        rw [h_mir_next_eq]
        exact h_absent base (by simpa [h_cs] using h_lookup_none)
      have h_next_placeMap :
          (csAt cs0 prog (s_mir.pc + 1)).placeMap = ctx.cs.placeMap := by
        rw [csAt_succ h_get, resetInstrs_placeMap]
        simpa [h_cs] using (DerefProjectedExistingCtx.compileStmt_placeMap ctx)
      have h_mir_pc_next : s_mir_next.pc = s_mir.pc + 1 := by
        rw [h_mir_next_eq]
      have h_sim_next_canon :
          StateSim (csAt cs0 prog (s_mir.pc + 1)).placeMap ρa ρt s_mir_next s_osea_next
            (ptrSimOfCtx ρa ρt s_mir_next.env) := by
        simpa [h_next_placeMap, h_mir_next_eq] using h_sim_next
      refine ⟨ρa, ρt, s_osea_next, h_steps, h_sim_next_canon, ?_, ?_,
        h_tag_fresh_next, ?_, h_noninterference_next, h_mir_pc_next, ?_⟩
      · simpa [h_next_placeMap] using h_closure_next
      · simpa [h_next_placeMap] using h_source_below_next
      · simpa [h_next_placeMap] using h_absent_next
      · exact h_pc_next.trans h_target_pc.symm
  | deref_fresh ctx h_cs h_inner_nonempty =>
      have h_temp := CompilerInv.deref_fresh_temp_safe ctx h_inv' h_cs
      have h_pointee_tracked :=
        CompilerInv.deref_fresh_pointee_tracked ctx h_inv' h_cs
      have h_sim_ctx :
          DerefFresh.LocalSim ctx ρa ρt s_mir s_osea (ptrSimOfCtx ρa ρt s_mir.env) := by
        simpa [DerefFresh.LocalSim, h_cs] using h_sim
      have h_closure_ctx : TrackedPlaceTagClosure ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_closure
      have h_source_below_ctx : SourceBlocksBelowAddrStart ctx.cs.placeMap s_mir := by
        simpa [h_cs] using h_source_below
      have h_base_absent :
          (csAt cs0 prog s_mir.pc).placeMap.lookup ctx.dst.base = none := by
        simpa [BaseAbsent, getPlaceInfo, h_cs] using ctx.h_dst_absent
      have h_base_absent_ctx : ctx.cs.placeMap.lookup ctx.dst.base = none := by
        simpa [h_cs] using h_base_absent
      have h_dst_env_none : s_mir.env.lookup ctx.dst.base = none :=
        h_absent ctx.dst.base h_base_absent
      obtain ⟨srcBaseAddr_m, _srcBaseAddr_o, srcTag_m, _srcTag_o, h_src_ptr, _h_src_block⟩ :=
        StateSim.place_projected h_sim_ctx ctx.h_src_lookup ctx.h_src_path
      have h_src_env := place_runtime_sim.env h_src_ptr
      obtain ⟨ap_src_read, q, gq, targetRes, ap_target_read,
          freshAddr_m_step, allocMem_m, freshTag_m_step, ap_alloc_m, ap_write_m,
          h_src_read, h_src_mem, h_resolve, h_target_read, h_alloc_pair_m_step,
          h_alloc_mMap, _h_own_m, h_mir_use, h_mir_next_eq⟩ :=
        DerefFresh.mirlite_step_inv ctx s_mir s_mir_next prog
          srcBaseAddr_m srcTag_m h_src_env h_dst_env_none h_mir_start h_mir_step
      have h_alloc_base_m_step : freshAddr_m_step = s_mir.mem.addrStart := by
        have h_fst := congrArg Prod.fst h_alloc_pair_m_step
        exact h_fst.symm.trans (h_alloc_base_any s_mir.mem (typeSize targetRes.ty))
      obtain ⟨targetReg, targetBaseLayout, targetOff, _targetBaseAddr,
          h_q_lookup, h_q_path, _h_q_env, h_target_addr, h_target_ty⟩ :=
        h_pointee_tracked srcBaseAddr_m srcTag_m q gq ap_src_read targetRes
          h_src_env h_src_mem h_resolve
      obtain ⟨targetBaseAddr_m, targetBaseAddr_o, targetBaseTag_m, targetBaseTag_o,
          h_q_ptr, _h_q_block⟩ :=
        StateSim.place h_sim_ctx h_q_lookup
      have h_q_env_eq :
          (targetBaseAddr_m, layoutToTyVal targetBaseLayout, targetBaseTag_m) =
            (_targetBaseAddr, layoutToTyVal targetBaseLayout, targetRes.tag) := by
        exact Option.some.inj ((place_runtime_sim.env h_q_ptr).symm.trans _h_q_env)
      have h_q_addr : targetBaseAddr_m = _targetBaseAddr := by
        exact congrArg Prod.fst h_q_env_eq
      have h_alloc_addrStart_m_step :
          allocMem_m.addrStart = s_mir.mem.addrStart + blockSize ctx.innerLayout := by
        have h_snd := congrArg (fun p => p.2.addrStart) h_alloc_pair_m_step
        calc
          allocMem_m.addrStart = (A_m.alloc s_mir.mem (typeSize targetRes.ty)).2.addrStart := by
            simpa using h_snd.symm
          _ = s_mir.mem.addrStart + typeSize targetRes.ty := by
            exact h_alloc_addrStart_any s_mir.mem (typeSize targetRes.ty)
          _ = s_mir.mem.addrStart + blockSize ctx.innerLayout := by
            rw [h_target_ty, typeSize_layoutToTyVal, blockSize_eq_layoutSize]
      have h_osea_start :
          StartsAt (compileProgFrom cs0 prog) s_osea.pc (DerefFreshCtx.compiled ctx) := by
        have h_osea_start' :
            StartsAt (compileProgFrom cs0 prog) s_osea.pc
              (compileStmt ctx.cs (DerefFresh.stmt ctx)).instrs := by
          simpa [h_cs, DerefFresh.stmt] using h_osea_start_stmt
        have h_compiled_eq :
            (compileStmt ctx.cs (DerefFresh.stmt ctx)).instrs =
              DerefFreshCtx.compiled ctx := by
          exact DerefFreshCtx.compiled_eq ctx
        simpa [h_compiled_eq] using h_osea_start'
      have h_target_pc :
          targetPcAt cs0 prog (s_mir.pc + 1) =
            s_osea.pc + (DerefFreshCtx.compiled ctx).length := by
        have h_target_pc' :
            targetPcAt cs0 prog (s_mir.pc + 1) =
              s_osea.pc + (compileStmt ctx.cs (DerefFresh.stmt ctx)).instrs.length := by
          simpa [h_cs, DerefFresh.stmt] using h_target_pc_stmt
        have h_compiled_eq :
            (compileStmt ctx.cs (DerefFresh.stmt ctx)).instrs =
              DerefFreshCtx.compiled ctx := by
          exact DerefFreshCtx.compiled_eq ctx
        simpa [h_compiled_eq] using h_target_pc'
      obtain ⟨freshAddr_m, allocBase_o, freshTag_m, _freshTag_o, ρa', ρt', s_osea_next,
          h_tag_eq, h_ρa', h_ρt', h_steps, h_sim_next, h_noninterference_next,
          h_env_next, h_nextTag_post, h_pc_next⟩ :=
        DerefFresh.simulation_structured
          (A_m := A_m)
          (ctx := ctx)
          h_sim_ctx h_noninterference h_source_below_ctx h_tag_fresh
          (h_alloc_base_any s_mir.mem (typeSize (layoutToTyVal ctx.innerLayout)))
          h_dst_env_none h_mir_start h_mir_step h_pointee_tracked
          h_osea_start h_inner_nonempty
      have h_tag_fresh' : TagRenameFreshFrom ρt freshTag_m := by
        simpa [h_tag_eq] using h_tag_fresh
      have h_env_next_step :
          s_mir_next.env =
            s_mir.env.insert ctx.dst.base
              (freshAddr_m_step, layoutToTyVal ctx.innerLayout, freshTag_m_step) := by
        rw [h_mir_next_eq]
        simp [h_target_ty]
      have h_fresh_info_eq :
          (freshAddr_m, layoutToTyVal ctx.innerLayout, freshTag_m) =
            (freshAddr_m_step, layoutToTyVal ctx.innerLayout, freshTag_m_step) := by
        apply Option.some.inj
        calc
          some (freshAddr_m, layoutToTyVal ctx.innerLayout, freshTag_m)
              = (s_mir.env.insert ctx.dst.base
                  (freshAddr_m, layoutToTyVal ctx.innerLayout, freshTag_m)).lookup ctx.dst.base := by simp
          _ = s_mir_next.env.lookup ctx.dst.base := by simpa [h_env_next]
          _ = (s_mir.env.insert ctx.dst.base
                (freshAddr_m_step, layoutToTyVal ctx.innerLayout, freshTag_m_step)).lookup ctx.dst.base := by
                simpa [h_env_next_step]
          _ = some (freshAddr_m_step, layoutToTyVal ctx.innerLayout, freshTag_m_step) := by simp
      have h_freshAddr_eq : freshAddr_m = freshAddr_m_step := by
        exact congrArg Prod.fst h_fresh_info_eq
      have h_alloc_base_m : freshAddr_m = s_mir.mem.addrStart := by
        exact h_freshAddr_eq.trans h_alloc_base_m_step
      have h_sim_next_canon :
          StateSim (DerefFreshCtx.postPlaceMap ctx) ρa' ρt' s_mir_next s_osea_next
            (ptrSimOfCtx ρa' ρt' s_mir_next.env) := by
        refine StateSim.mono_ptr_sim h_sim_next ?_
        intro p tag_m base off size tag_o h_ptr
        rw [h_env_next, h_ρa', h_ρt']
        exact ptrSimOfCtx_extend_fresh_of_absent
          (h_sim := h_sim)
          (h_absent := h_absent)
          (h_lookup_none := h_base_absent)
          (h_source_below := h_source_below)
          (h_fresh_addr := h_alloc_base_m)
          (h_tag_fresh := h_tag_fresh')
          h_ptr
      have h_closure_next :
          TrackedPlaceTagClosure (DerefFreshCtx.postPlaceMap ctx) s_mir_next := by
        rw [h_mir_next_eq]
        have h_closure_write :
            TrackedPlaceTagClosure (DerefFreshCtx.postPlaceMap ctx)
              { s_mir with
                env := s_mir.env.insert ctx.dst.base
                  (freshAddr_m_step, layoutToTyVal ctx.innerLayout, freshTag_m_step)
                mem :=
                  mirlite.writeWordSeq s_mir.mem freshAddr_m_step
                    (mirlite.readWordSeq s_mir.mem targetRes.addr (typeSize targetRes.ty)) } := by
          simpa [DerefFreshCtx.postPlaceMap, h_q_addr, h_target_addr, h_target_ty] using
            (TrackedPlaceTagClosure.extend_fresh_copy_from_place
              (π := ctx.cs.placeMap)
              (ρa := ρa)
              (ρt := ρt)
              (s_mir := s_mir)
              (s_osea := s_osea)
              (ptr_sim := ptrSimOfCtx ρa ρt s_mir.env)
              (src := q)
              (srcReg := targetReg)
              (srcBaseLayout := targetBaseLayout)
              (dstLayout := ctx.innerLayout)
              (srcOff := targetOff)
              (srcBaseAddr := targetBaseAddr_m)
              (srcBaseAddr_o := targetBaseAddr_o)
              (srcBaseTag := targetBaseTag_m)
              (srcBaseTag_o := targetBaseTag_o)
              (freshBase := ctx.dst.base)
              (freshReg := ctx.dstReg)
              (freshAddr := freshAddr_m_step)
              (freshTag := freshTag_m_step)
              (h_sim := h_sim_ctx)
              (h_closure := h_closure_ctx)
              (h_lookup_none := h_base_absent_ctx)
              (h_src_lookup := h_q_lookup)
              (h_src_path := h_q_path)
              (h_src_ptr := h_q_ptr)
              (h_disj := by
                intro base reg layout addr_m addr_o tag_m' tag_o' h_lookup h_ptr
                rw [h_alloc_base_m_step]
                exact blocks_disjoint_of_end_le_start
                  (SourceBlocksBelowAddrStart.of_place_runtime_sim h_source_below_ctx h_ptr).2))
        have h_write_mMap :
            (mirlite.writeWordSeq allocMem_m freshAddr_m_step
              (mirlite.readWordSeq s_mir.mem targetRes.addr (typeSize targetRes.ty))).mMap =
              (mirlite.writeWordSeq s_mir.mem freshAddr_m_step
                (mirlite.readWordSeq s_mir.mem targetRes.addr (typeSize targetRes.ty))).mMap := by
          exact mirlite_writeWordSeq_mMap_eq_of_mMap_eq
            h_alloc_mMap freshAddr_m_step
            (mirlite.readWordSeq s_mir.mem targetRes.addr (typeSize targetRes.ty))
        exact TrackedPlaceTagClosure.of_env_mem_mMap_eq
          (s_mir :=
            { s_mir with
              env := s_mir.env.insert ctx.dst.base
                (freshAddr_m_step, layoutToTyVal ctx.innerLayout, freshTag_m_step)
              mem :=
                mirlite.writeWordSeq s_mir.mem freshAddr_m_step
                  (mirlite.readWordSeq s_mir.mem targetRes.addr (typeSize targetRes.ty)) })
          h_closure_write (by simp [h_target_ty]) h_write_mMap
      have h_source_below_next :
          SourceBlocksBelowAddrStart (DerefFreshCtx.postPlaceMap ctx) s_mir_next := by
        simpa [DerefFreshCtx.postPlaceMap] using
          (SourceBlocksBelowAddrStart.extend_fresh
            (π := ctx.cs.placeMap)
            (s_mir := s_mir)
            (s_mir_next := s_mir_next)
            (freshBase := ctx.dst.base)
            (freshReg := ctx.dstReg)
            (freshLayout := ctx.innerLayout)
            (freshAddr := freshAddr_m)
            (freshTag := freshTag_m)
            h_source_below_ctx h_env_next h_alloc_base_m
            (by rw [h_mir_next_eq]; simpa using h_alloc_addrStart_m_step)
            h_inner_nonempty)
      have h_tag_fresh_next :
          TagRenameFreshFrom ρt' s_mir_next.ap.NextTag := by
        rw [h_ρt', h_nextTag_post]
        simpa [h_tag_eq] using
          (TagRenameFreshFrom.extendTagRename
            (ρt := ρt)
            (nextTag := s_mir.ap.NextTag)
            (freshTag_o := _freshTag_o)
            h_tag_fresh)
      have h_absent_ctx :
          ∀ base, ctx.cs.placeMap.lookup base = none → s_mir.env.lookup base = none := by
        intro base h_lookup_none
        exact h_absent base (by simpa [h_cs] using h_lookup_none)
      have h_absent_next :
          ∀ base, (DerefFreshCtx.postPlaceMap ctx).lookup base = none → s_mir_next.env.lookup base = none := by
        intro base h_lookup_none
        rw [h_env_next]
        exact absent_env_insert_of_lookup_none
          (π := ctx.cs.placeMap)
          (s_mir := s_mir)
          (freshBase := ctx.dst.base)
          (freshReg := ctx.dstReg)
          (freshLayout := ctx.innerLayout)
          (freshAddr := freshAddr_m)
          (freshTy := layoutToTyVal ctx.innerLayout)
          (freshTag := freshTag_m)
          h_absent_ctx base (by simpa [DerefFreshCtx.postPlaceMap] using h_lookup_none)
      have h_next_placeMap :
          (csAt cs0 prog (s_mir.pc + 1)).placeMap = DerefFreshCtx.postPlaceMap ctx := by
        rw [csAt_succ h_get, resetInstrs_placeMap]
        let rhs := mirlite.RExpr.DrefOp ctx.src
        let rhsCs := (compileRExpr ctx.cs rhs).cs
        have h_rhs_pm : rhsCs.placeMap = ctx.cs.placeMap := by
          simpa [rhsCs, rhs] using compileRExpr_placeMap ctx.cs rhs
        have h_dst_absent_rhs : getPlaceInfo rhsCs ctx.dst.base = none := by
          simpa [BaseAbsent, getPlaceInfo, h_rhs_pm] using ctx.h_dst_absent
        have h_rhs_layout : (compileRExpr ctx.cs rhs).layout = ctx.innerLayout := by
          have h_src_layout : placeLayout? ctx.cs ctx.src = some (LayoutTy.PtrL ctx.innerLayout) := by
            unfold placeLayout?
            rw [ctx.h_src_lookup]
            simp [ctx.h_src_path]
          simp [compileRExpr, compileRExprFuel, rhs, inferRExprLayout, h_src_layout]
        have h_dst_pm :
            (placeToReg rhsCs ctx.dst mirlite.RefKind.Mut
              (some (compileRExpr ctx.cs rhs).layout)).cs.placeMap =
              (ctx.dst.base, (Register.R rhsCs.nextReg, ctx.innerLayout)) :: ctx.cs.placeMap := by
          simpa [h_rhs_pm, h_rhs_layout] using
            (placeToReg_placeMap_of_absent_base
              (cs := rhsCs)
              (p := ctx.dst)
              (kind := mirlite.RefKind.Mut)
              (layout := ctx.innerLayout)
              h_dst_absent_rhs ctx.h_dst_base)
        have h_rhs_nextReg :
            rhsCs.nextReg = if ctx.srcOff = 0 then ctx.cs.nextReg + 2 else ctx.cs.nextReg + 3 := by
          simpa [rhsCs, rhs] using DerefFreshCtx.rhs_nextReg ctx
        have h_dst_pm' :
            (placeToReg rhsCs ctx.dst mirlite.RefKind.Mut
              (some (compileRExpr ctx.cs rhs).layout)).cs.placeMap =
              (ctx.dst.base,
                if ctx.srcOff = 0 then Register.R (ctx.cs.nextReg + 2)
                else Register.R (ctx.cs.nextReg + 3),
                ctx.innerLayout) :: ctx.cs.placeMap := by
          by_cases h_zero : ctx.srcOff = 0
          · simp [h_zero] at h_rhs_nextReg h_dst_pm ⊢
            simpa [h_rhs_nextReg] using h_dst_pm
          · simp [h_zero] at h_rhs_nextReg h_dst_pm ⊢
            simpa [h_rhs_nextReg] using h_dst_pm
        unfold DerefFreshCtx.stmt compileStmt
        simpa [h_cs, rhs, rhsCs, h_rhs_layout, h_rhs_nextReg, DerefFreshCtx.postPlaceMap,
          DerefFreshCtx.dstReg, DerefFreshCtx.rhs_nextReg] using h_dst_pm'
      have h_mir_pc_next : s_mir_next.pc = s_mir.pc + 1 := by
        rw [h_mir_next_eq]
      refine ⟨ρa', ρt', s_osea_next, h_steps, ?_, ?_, ?_, h_tag_fresh_next, ?_,
        h_noninterference_next, h_mir_pc_next, ?_⟩
      · simpa [h_next_placeMap] using h_sim_next_canon
      · simpa [h_next_placeMap] using h_closure_next
      · simpa [h_next_placeMap] using h_source_below_next
      · simpa [h_next_placeMap] using h_absent_next
      · exact h_pc_next.trans h_target_pc.symm

theorem CompilerInv.step
  {A_m : mirlite.AllocatorSpec}
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_next : mirlite.State}
  {s_osea : oseair.State}
  {stmt : mirlite.Stmt}
  (h_supported : SupportedProgFrom cs0 prog)
  (h_get : prog.get? s_mir.pc = some stmt)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (h_alloc_base_any : ∀ mem sz, (A_m.alloc mem sz).1 = mem.addrStart)
  (h_alloc_addrStart_any : ∀ mem sz, (A_m.alloc mem sz).2.addrStart = mem.addrStart + sz)
  (h_mir_step : mirlite.stepWith A_m s_mir prog = mirlite.Result.Ok s_mir_next) :
  ∃ ρa' ρt' s_osea_next,
    StepStarWith oseair.bumpAllocator s_osea (compileProgFrom cs0 prog) s_osea_next ∧
    CompilerInv cs0 prog ρa' ρt' s_mir_next s_osea_next := by
  have h_stmt : SupportedStmt (csAt cs0 prog s_mir.pc) stmt :=
    h_supported s_mir.pc stmt h_get
  obtain ⟨ρa', ρt', s_osea_next, h_steps, h_sim_next, h_closure_next,
      h_source_below_next, h_tag_fresh_next, h_absent_next, h_noninterference_next,
      h_mir_pc_next, h_osea_pc_next⟩ :=
    SupportedStmt.step_state_sim
      (A_m := A_m)
      (cs0 := cs0)
      (prog := prog)
      (ρa := ρa)
      (ρt := ρt)
      (s_mir := s_mir)
      (s_mir_next := s_mir_next)
      (s_osea := s_osea)
      (stmt := stmt)
      h_stmt h_get h_inv h_alloc_base_any h_alloc_addrStart_any h_mir_step
  refine ⟨ρa', ρt', s_osea_next, h_steps, ?_⟩
  unfold CompilerInv
  rw [h_mir_pc_next]
  exact ⟨h_osea_pc_next, h_sim_next, h_closure_next, h_source_below_next, h_tag_fresh_next,
    h_absent_next, h_noninterference_next⟩

theorem CompilerInv.targetDone_of_sourceDone
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir : mirlite.State}
  {s_osea : oseair.State}
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (h_done : obseq.proof.MirDone prog s_mir) :
  obseq.proof.OseaDone (compileProgFrom cs0 prog) s_osea := by
  rcases h_inv with ⟨h_pc, _h_sim, _h_closure, _h_source_below, _h_tag_fresh, _h_absent, _h_noninterference⟩
  rcases h_done with h_oob | h_halt
  · left
    apply List.get?_eq_none_iff.mpr
    rw [h_pc]
    have h_suffix := compileProgFrom_suffix cs0 prog s_mir.pc
    have h_drop : prog.drop s_mir.pc = [] := by
      exact List.drop_eq_nil_of_le (List.get?_eq_none_iff.mp h_oob)
    have h_compiled :
        compileProgFrom cs0 prog = (prefixCompileState cs0 prog s_mir.pc).instrs := by
      have h_empty : (csAt cs0 prog s_mir.pc).instrs = [] := compilerEmpty_csAt cs0 prog s_mir.pc
      rw [h_suffix, h_drop, compileProgFrom_nil, h_empty]
      simp
    have h_len :
        (compileProgFrom cs0 prog).length = targetPcAt cs0 prog s_mir.pc := by
      rw [h_compiled]
      simp [targetPcAt]
    simpa [h_len]
  · right
    have h_start_full :=
      compileProgFrom_startsAt (cs0 := cs0) (prog := prog) (pc := s_mir.pc)
    rw [drop_eq_get_cons h_halt, compileProgFrom_cons] at h_start_full
    have h_start_halt :
        StartsAt (compileProgFrom cs0 prog) (targetPcAt cs0 prog s_mir.pc)
          (compileStmt (csAt cs0 prog s_mir.pc) mirlite.Stmt.Halt).instrs := by
      exact StartsAt.prefix h_start_full
    have h_compiled_halt :
        (compileStmt (csAt cs0 prog s_mir.pc) mirlite.Stmt.Halt).instrs = [oseair.Instr.Halt] := by
      have h_empty : (csAt cs0 prog s_mir.pc).instrs = [] := compilerEmpty_csAt cs0 prog s_mir.pc
      simp [compileStmt, emit, h_empty]
    have h_start_single :
        StartsAt (compileProgFrom cs0 prog) (targetPcAt cs0 prog s_mir.pc) [oseair.Instr.Halt] := by
      simpa [h_compiled_halt] using h_start_halt
    rw [h_pc]
    exact StartsAt.singleton h_start_single

theorem CompilerInv.stepStarWith
  {A_m : mirlite.AllocatorSpec}
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_final : mirlite.State}
  {s_osea : oseair.State}
  (h_supported : SupportedProgFrom cs0 prog)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (h_alloc_base_any : ∀ mem sz, (A_m.alloc mem sz).1 = mem.addrStart)
  (h_alloc_addrStart_any : ∀ mem sz, (A_m.alloc mem sz).2.addrStart = mem.addrStart + sz)
  (h_steps : MirStepStarWith A_m s_mir prog s_mir_final) :
  ∃ ρa' ρt' s_osea_final,
    StepStarWith oseair.bumpAllocator s_osea (compileProgFrom cs0 prog) s_osea_final ∧
    CompilerInv cs0 prog ρa' ρt' s_mir_final s_osea_final := by
  induction h_steps generalizing ρa ρt s_osea with
  | refl s prog =>
      exact ⟨ρa, ρt, s_osea,
        StepStarWith.refl s_osea (compileProgFrom cs0 prog), h_inv⟩
  | tail s1 s2 s3 prog h_step h_rest ih =>
      cases h_get : prog.get? s1.pc with
      | none =>
          have h_pc_ge : prog.length ≤ s1.pc := List.get?_eq_none_iff.mp h_get
          have h_not_pc : ¬ s1.pc < prog.length := Nat.not_lt.mpr h_pc_ge
          have h_step_done : mirlite.stepWith A_m s1 prog = mirlite.Result.Ok s1 := by
            simp [mirlite.stepWith, h_not_pc]
          rw [h_step_done] at h_step
          injection h_step with h_mid_eq
          subst h_mid_eq
          exact ih h_supported h_inv
      | some stmt =>
          cases stmt with
          | Halt =>
              cases h_supported s1.pc mirlite.Stmt.Halt h_get
          | Assgn lhs rhs =>
              obtain ⟨ρa_mid, ρt_mid, s_osea_mid, h_steps_mid, h_inv_mid⟩ :=
                CompilerInv.step
                  (A_m := A_m)
                  (cs0 := cs0)
                  (prog := prog)
                  (ρa := ρa)
                  (ρt := ρt)
                  (s_mir := s1)
                  (s_mir_next := s2)
                  (s_osea := s_osea)
                  (stmt := mirlite.Stmt.Assgn lhs rhs)
                  h_supported h_get h_inv h_alloc_base_any h_alloc_addrStart_any h_step
              obtain ⟨ρa_final, ρt_final, s_osea_final, h_steps_final, h_inv_final⟩ :=
                ih (ρa := ρa_mid) (ρt := ρt_mid) (s_osea := s_osea_mid)
                  h_supported h_inv_mid
              exact ⟨ρa_final, ρt_final, s_osea_final,
                StepStarWith.trans h_steps_mid h_steps_final, h_inv_final⟩

theorem CompilerInv.stepStar
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_final : mirlite.State}
  {s_osea : oseair.State}
  (h_supported : SupportedProgFrom cs0 prog)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (h_steps : MirStepStar s_mir prog s_mir_final) :
  ∃ ρa' ρt' s_osea_final,
    StepStarWith oseair.bumpAllocator s_osea (compileProgFrom cs0 prog) s_osea_final ∧
    CompilerInv cs0 prog ρa' ρt' s_mir_final s_osea_final := by
  exact CompilerInv.stepStarWith
    (A_m := mirlite.bumpAllocator)
    (cs0 := cs0)
    (prog := prog)
    (ρa := ρa)
    (ρt := ρt)
    (s_mir := s_mir)
    (s_mir_final := s_mir_final)
    (s_osea := s_osea)
    h_supported h_inv
    (by intro mem sz; simp [mirlite.bumpAllocator, mirlite.allocate])
    (by intro mem sz; simp [mirlite.bumpAllocator, mirlite.allocate])
    h_steps

theorem CompilerInv.stepStarDone
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_final : mirlite.State}
  {s_osea : oseair.State}
  (h_supported : SupportedProgFrom cs0 prog)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (h_steps : MirStepStar s_mir prog s_mir_final)
  (h_done : obseq.proof.MirDone prog s_mir_final) :
  ∃ ρa' ρt' s_osea_final,
    StepStarWith oseair.bumpAllocator s_osea (compileProgFrom cs0 prog) s_osea_final ∧
    CompilerInv cs0 prog ρa' ρt' s_mir_final s_osea_final ∧
    obseq.proof.OseaDone (compileProgFrom cs0 prog) s_osea_final := by
  obtain ⟨ρa', ρt', s_osea_final, h_target_steps, h_inv_final⟩ :=
    CompilerInv.stepStar
      (cs0 := cs0)
      (prog := prog)
      (ρa := ρa)
      (ρt := ρt)
      (s_mir := s_mir)
      (s_mir_final := s_mir_final)
      (s_osea := s_osea)
      h_supported h_inv h_steps
  exact ⟨ρa', ρt', s_osea_final, h_target_steps, h_inv_final,
    CompilerInv.targetDone_of_sourceDone h_inv_final h_done⟩

theorem CompilerInv.stepStarDoneFromStart
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {env0 : mirlite.Env}
  {mem0 : mirlite.Mem}
  {ap0 : AccessPerms}
  {s_mir_final : mirlite.State}
  {s_osea0 : oseair.State}
  (h_supported : SupportedProgFrom cs0 prog)
  (h_init :
    CompilerInv cs0 prog ρa ρt
      { pc := 0, env := env0, mem := mem0, ap := ap0 }
      s_osea0)
  (h_steps :
    MirStepStar { pc := 0, env := env0, mem := mem0, ap := ap0 } prog s_mir_final)
  (h_done : obseq.proof.MirDone prog s_mir_final) :
  ∃ ρa' ρt' s_osea_final,
    StepStarWith oseair.bumpAllocator s_osea0 (compileProgFrom cs0 prog) s_osea_final ∧
    CompilerInv cs0 prog ρa' ρt' s_mir_final s_osea_final ∧
    obseq.proof.OseaDone (compileProgFrom cs0 prog) s_osea_final := by
  exact CompilerInv.stepStarDone
    (cs0 := cs0)
    (prog := prog)
    (ρa := ρa)
    (ρt := ρt)
    (s_mir := { pc := 0, env := env0, mem := mem0, ap := ap0 })
    (s_mir_final := s_mir_final)
    (s_osea := s_osea0)
    h_supported h_init h_steps h_done

theorem CompilerInv.runNWith
  {A_m : mirlite.AllocatorSpec}
  {n : Nat}
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_final : mirlite.State}
  {s_osea : oseair.State}
  (h_supported : SupportedProgFrom cs0 prog)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (h_alloc_base_any : ∀ mem sz, (A_m.alloc mem sz).1 = mem.addrStart)
  (h_alloc_addrStart_any : ∀ mem sz, (A_m.alloc mem sz).2.addrStart = mem.addrStart + sz)
  (h_run : mirlite.runNWith A_m n s_mir prog = mirlite.Result.Ok s_mir_final) :
  ∃ ρa' ρt' s_osea_final,
    StepStarWith oseair.bumpAllocator s_osea (compileProgFrom cs0 prog) s_osea_final ∧
    CompilerInv cs0 prog ρa' ρt' s_mir_final s_osea_final := by
  exact CompilerInv.stepStarWith
    (A_m := A_m)
    (cs0 := cs0)
    (prog := prog)
    (ρa := ρa)
    (ρt := ρt)
    (s_mir := s_mir)
    (s_mir_final := s_mir_final)
    (s_osea := s_osea)
    h_supported h_inv h_alloc_base_any h_alloc_addrStart_any (MirStepStarWith.of_runN_ok h_run)

theorem CompilerInv.runN
  {n : Nat}
  {cs0 : CompilerState}
  {prog : mirlite.Prog}
  {ρa : AddrRenameMap}
  {ρt : TagRenameMap}
  {s_mir s_mir_final : mirlite.State}
  {s_osea : oseair.State}
  (h_supported : SupportedProgFrom cs0 prog)
  (h_inv : CompilerInv cs0 prog ρa ρt s_mir s_osea)
  (h_run : mirlite.runN n s_mir prog = mirlite.Result.Ok s_mir_final) :
  ∃ ρa' ρt' s_osea_final,
    StepStarWith oseair.bumpAllocator s_osea (compileProgFrom cs0 prog) s_osea_final ∧
    CompilerInv cs0 prog ρa' ρt' s_mir_final s_osea_final := by
  exact CompilerInv.stepStar
    (cs0 := cs0)
    (prog := prog)
    (ρa := ρa)
    (ρt := ρt)
    (s_mir := s_mir)
    (s_mir_final := s_mir_final)
    (s_osea := s_osea)
    h_supported h_inv (MirStepStar.of_runN_ok h_run)

end obseq.proof
