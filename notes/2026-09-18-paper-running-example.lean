import obseq3.compile_tests
/-!
State-dumping trace of the paper's running example
(`pldi27/mirlite-oseair-correctness.typ`, the stepwise execution tables of §2).
Every address, tag, register and label printed in the paper comes from
this file's output. Run from the repo root:

    lake env lean notes/2026-09-18-paper-running-example.lean

The program is pinned in the witness corpus as `g14_paper_running_example`
and `d92_paper_running_example` (src/obseq3/compile_tests.lean).
-/
open obseq3 obseq3.CompileTests
open obseq3.mirlite obseq3.compile
open obseq3.Tests (M)

namespace obseq3.PaperTrace

def prog : List (Stmt ΓP) := paperProg

/-- Instruction listing with the statement each label belongs to. -/
def listing : IO Unit := do
  match compileProg prog with
  | .error e => IO.println s!"compile error {reprStr e}"
  | .ok tp =>
      IO.println s!"statement label ranges: {reprStr (stmtLabelRanges prog)}"
      for i in [0:emittedLabels prog] do
        match tp i with
        | some instr => IO.println s!"  {i}: {reprStr instr}"
        | none => pure ()

/-- Step the target, dumping the post-state of every instruction. -/
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
                | .Ok st' => do
                    IO.println s!"T after {st.pc}: {reprStr instr}"
                    IO.println s!"    reg   = {reprStr st'.reg}"
                    IO.println s!"    mem   = {reprStr st'.mem}"
                    IO.println s!"    perms = {reprStr (show obseq3.AccessPerms from st'.perms)}"
                    go n st'
                | .Err msg => IO.println s!"TARGET TRAPS at pc={st.pc}: {msg}"
      go 60 (oseair.State.initial M)

/-- Step the source, dumping the post-state of every statement. -/
def traceSrc : IO Unit := do
  let rec go : Nat → mirlite.State M ΓP → IO Unit
    | 0, _ => IO.println "fuel out"
    | n + 1, st =>
        match prog[st.pc]? with
        | none => IO.println s!"SOURCE finished ok at pc={st.pc}"
        | some .halt => IO.println s!"SOURCE halt at pc={st.pc}"
        | some stmt =>
            match mirlite.stepStmt M st stmt with
            | .ok st' => do
                IO.println s!"S after stmt {st.pc}:"
                IO.println s!"    env x = {reprStr (st'.env ⟨0, by decide⟩)}"
                IO.println s!"    env y = {reprStr (st'.env ⟨1, by decide⟩)}"
                IO.println s!"    mem   = {reprStr st'.mem}"
                IO.println s!"    perms = {reprStr (show obseq3.AccessPerms from st'.perms)}"
                go n st'
            | .err msg => IO.println s!"SOURCE traps at stmt {st.pc}: {msg}"
  go 20 (mirlite.State.initial M ΓP)

end obseq3.PaperTrace

#eval! obseq3.PaperTrace.listing
#eval! obseq3.PaperTrace.traceSrc
#eval! obseq3.PaperTrace.traceTgt
