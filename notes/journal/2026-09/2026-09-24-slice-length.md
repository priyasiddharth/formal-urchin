# `sliceLen`: slice metadata is a word the program computes

2026-09-24 (same day as [[2026-09-24-binop-rvalue]], after it). "Now do
slice lengths" — the first half of the slice roadmap step.

## The shape: one read, then a register-only step

[FACT] `RExpr.sliceLen (p : Place Γ (PtrL σ)) : RExpr Γ NatL` reads the
fat pointer with copy's read (`evalCopy`) and yields
`extent / blockSize σ` — the length in ELEMENTS. `Rhs.SliceLen ty r` is
its register-only target form. The compiled shape is `readToReg p` plus
one instruction, exactly `binOp`'s minus an operand.

Two things make this the cheap design rather than the `exposeAddr`
design (which reads the cell inside its own instruction):
- the read is copy's, so `copy_readRegPkg_flat` supplies it, and the
  package is ~150 lines with no new read-family instances;
- `MemValSim`'s pointer clause carries the extent (`e' = e`, since
  2026-09-23), so the word the target computes is the word mirlite
  computed BY CONSTRUCTION — the proof never has to reason about how the
  extent got there.

`sliceLen_valuePkg` (proof/slice.lean) went through on the first build
after two type fixes. Audit unchanged: two roots, 3 axioms, 0 sorries.

[FACT] Where the length comes from in real code, both routes now
lowered: `<[T]>::len(&self)` is a bodyless std call (a seam shim), and
rustc ALSO reads it as a place projection `_p.PtrMetadata` when it emits
a bounds check. The latter is a new `UProj.ptrMetadata` that the seam
turns into `sliceLen` in a read position and every other position
rejects.

[FACT] Why `.len()` is not an access to the slice DATA: it reads the
local that holds the fat pointer. That is what `sliceLen` does (copy's
read of that one cell), so taking a length through a shared reborrow
does not disable a raw pointer derived from the slice earlier — the
content of the new local witness `slice_len_alias`.

## Validation: local witnesses, because the corpus cannot be rebuilt

[OBS 2026-09-24, SUPERSEDED → 2026-09-25-corpus-sources.md] The three
corpus tests this would help (zst_slice, buggy_split_at_mut,
buggy_as_mut_slice) are UNSUPPORTED, and unsupported entries' ULLBC
artifacts are not committed. Regenerating them needs the Miri corpus,
which `scripts/fetch_corpus.sh` exports from a local Miri checkout —
absent on this machine (`/home/siddharth/rustc/...` does not exist).
**The next day the corpus was simply cloned** (the remote is public and
this machine has network); what was missing was a checkout, not a
possibility. Why I was misled: the script hard-coded one path and I read
its failure as an environment constraint instead of a default. Charon (conformance/tools/) and the pinned Miri
(`cargo +nightly-2026-06-01 miri`) DO work, so new LOCAL tests are the
available validation, and that is what landed:

- `local/slice_len_alias` (verdict ok) — the aliasing witness above.
- `local/slice_len_value` (verdict ok, certified) — branches on
  `n != 4`, so the certificate's T2 check compares the lowering's own
  computed length against Miri's arm. Teeth: perturbing mirlite's
  `sliceLen` by one turns it into `certificate rejected at line 16`.
  This is the machinery from the binOp commit paying for itself — a
  value witness needs a branch, and a branch needs a real word.

Corpus: 98 supported / 0 fail / 40 unsupported (was 96/0/40), `--osea`
98 matched, certificates 24 entries, 43 checked, 0 unchecked. Units
18/18 and 124/124 (g16_slice_len, d101–d103).

[OPEN] Sub-slicing (`&s[lo..hi]`) is parked with a concrete plan: a
`subSlice` rvalue is the `binOp` package with three reads, plus a shim
for the std `Index<Range>` chain. See loose-ends/parked.md.
