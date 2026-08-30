import obseq3.compile_tests
open obseq3 obseq3.CompileTests
open obseq3.mirlite obseq3.compile
open obseq3.Tests (M)

namespace obseq3.Trace
abbrev natL := obseq.LayoutTy.NatL
abbrev pN := obseq.LayoutTy.PtrL natL
abbrev ppN := obseq.LayoutTy.PtrL pN

def Γp : Ctx := [natL, pN, ppN, ppN, pN]
def x : Place Γp natL := .local ⟨⟨0, by decide⟩, rfl⟩
def p : Place Γp pN := .local ⟨⟨1, by decide⟩, rfl⟩
def q : Place Γp ppN := .local ⟨⟨2, by decide⟩, rfl⟩
def q2 : Place Γp ppN := .local ⟨⟨3, by decide⟩, rfl⟩
def r : Place Γp pN := .local ⟨⟨4, by decide⟩, rfl⟩

def prog : List (Stmt Γp) :=
  [.assign x (.constInit 5),
   .assign p (.ref .Mut false [] x),
   .assign q (.ref .Mut false [] p),
   .assign q2 (.ref .Mut false [] (.deref q)),
   .assign r (.ptrCast q2),
   .assign (.deref (.deref q)) (.copy (.deref r))]

/-- Instruction listing with the statement each label belongs to. -/
def listing : IO Unit := do
  match compileProg prog with
  | .error e => IO.println s!"compile error {reprStr e}"
  | .ok tp =>
      let ranges := stmtLabelRanges prog
      IO.println s!"statement label ranges: {reprStr ranges}"
      for i in [0:emittedLabels prog] do
        match tp i with
        | some instr => IO.println s!"  {i}: {reprStr instr}"
        | none => pure ()

/-- Step the target until it errors; print the pc and the error. -/
def traceTgt : IO Unit := do
  match compileProg prog with
  | .error e => IO.println s!"compile error {reprStr e}"
  | .ok tp =>
      let rec go : Nat → oseair.State M → IO Unit
        | 0, _ => IO.println "fuel out"
        | n + 1, st =>
            match tp st.pc with
            | none => IO.println s!"halted (fell off) at pc={st.pc}"
            | some .Halt => IO.println s!"Halt at pc={st.pc}"
            | some instr =>
                match oseair.step M st tp with
                | .Ok st' => go n st'
                | .Err msg => do
                    IO.println s!"TARGET TRAPS at pc={st.pc}"
                    IO.println s!"  instruction: {reprStr instr}"
                    IO.println s!"  error: {msg}"
      go 60 (oseair.State.initial M)

/-- Step the source until it errors (or finishes). -/
def traceSrc : IO Unit := do
  let rec go : Nat → mirlite.State M Γp → IO Unit
    | 0, _ => IO.println "fuel out"
    | n + 1, st =>
        match prog[st.pc]? with
        | none => IO.println s!"SOURCE finished ok at pc={st.pc}"
        | some stmt =>
            match mirlite.stepStmt M st stmt with
            | .ok st' => go n st'
            | .err msg => IO.println s!"SOURCE traps at stmt {st.pc}: {msg}"
  go 20 (mirlite.State.initial M Γp)

end obseq3.Trace

#eval! obseq3.Trace.listing
#eval! obseq3.Trace.traceSrc
#eval! obseq3.Trace.traceTgt
