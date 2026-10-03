import obseq3.compile_tests
/-!
State-dumping trace of the paper's running example
(`pldi27/mirlite-oseair-correctness.typ`, the stepwise execution tables of §2),
on the byte model at the uniform layout (every integer and pointer an
8-byte leaf). Every address, tag, register and label printed in the paper
comes from this file's output. Run from the repo root:

    lake env lean notes/2026-09-18-paper-running-example.lean

Memory is printed per allocation as its decoded 8-byte leaves; permission
stacks per byte, with runs of equal stacks grouped into ranges.

The program is pinned in the witness corpus as `g14_paper_running_example`
and `d92_paper_running_example` (src/obseq3/compile_tests.lean).
-/
open obseq3 obseq3.CompileTests obseq3.bytes
open obseq3.compile
open obseq3.Tests (M)

namespace obseq3.PaperTrace

def prog : List (Stmt ΓP) := paperProg
def L : mirlite.LayEnv ΓP := mirlite.uniformEnv ΓP

/-- An 8-byte leaf, decoded as a pointer when its first byte carries
    provenance, else as an integer. -/
def leafAt (m : bytes.Mem) (a : Nat) : mirlite.MemValue :=
  match m.bytes a with
  | .init _ (some _) => mirlite.decodeV .ptr (m.read a 8)
  | _ => mirlite.decodeV (.int 8) (m.read a 8)

def memDump (m : bytes.Mem) : String :=
  String.intercalate "; " <| m.allocs.reverse.map fun (base, size) =>
    let leaves := (List.range (size / 8)).map fun i => reprStr (leafAt m (base + 8 * i))
    s!"[{base}, {base + size}): {leaves}"

/-- Per-byte stacks, runs of equal stacks grouped as `[lo, hi)`. -/
def stacksDump (p : AccessPerms) : String :=
  let sorted := p.StackMap.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let groups := sorted.foldl (init := ([] : List (Nat × Nat × String))) fun acc (a, st) =>
    let s := reprStr st
    match acc with
    | (lo, hi, s') :: rest => if hi == a && s' == s then (lo, a + 1, s) :: rest
                              else (a, a + 1, s) :: acc
    | [] => [(a, a + 1, s)]
  String.intercalate "; " (groups.reverse.map fun (lo, hi, s) => s!"[{lo}, {hi}) {s}")

/-- Instruction listing with the statement each label belongs to. -/
def listing : IO Unit := do
  match compileProg L prog with
  | .error e => IO.println s!"compile error {reprStr e}"
  | .ok tp =>
      IO.println s!"statement label ranges: {reprStr (stmtLabelRanges L prog)}"
      for i in [0:emittedLabels L prog] do
        match tp i with
        | some instr => IO.println s!"  {i}: {reprStr instr}"
        | none => pure ()

/-- Step the target, dumping the post-state of every instruction. -/
def traceTgt : IO Unit := do
  match compileProg L prog with
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
                    IO.println s!"    reg    = {reprStr st'.reg}"
                    IO.println s!"    mem    = {memDump st'.mem}"
                    IO.println s!"    stacks = {stacksDump st'.perms}"
                    IO.println s!"    next tag = {(show AccessPerms from st'.perms).NextTag}"
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
            match mirlite.stepStmt M L st stmt with
            | .ok st' => do
                IO.println s!"S after stmt {st.pc}:"
                IO.println s!"    env x  = {reprStr (st'.env ⟨0, by decide⟩)}"
                IO.println s!"    env y  = {reprStr (st'.env ⟨1, by decide⟩)}"
                IO.println s!"    mem    = {memDump st'.mem}"
                IO.println s!"    stacks = {stacksDump st'.perms}"
                IO.println s!"    next tag = {(show AccessPerms from st'.perms).NextTag}"
                go n st'
            | .err msg => IO.println s!"SOURCE traps at stmt {st.pc}: {msg}"
  go 20 (mirlite.State.initial M ΓP)

end obseq3.PaperTrace

#eval! obseq3.PaperTrace.listing
#eval! obseq3.PaperTrace.traceSrc
#eval! obseq3.PaperTrace.traceTgt
