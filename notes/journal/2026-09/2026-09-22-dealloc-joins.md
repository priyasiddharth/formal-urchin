# `dealloc` joins the theorem; the gate is empty

[FACT 2026-09-22, verified against f4d2b77+] See
durable/dealloc-is-copys-read-then-a-free.md for what landed. The
statement was cheap for the same reason `alloc`'s runtime length was:
once the pointer is read the way `copy` reads a place, the read is a
package that already exists (`copy_readRegPkg_flat`), and the
compiler's `readToReg` (generalising `guardRead` to any layout) makes
the lowering literally copy's read plus one instruction.

[FACT 2026-09-22] The semantics alignment: mirlite's `dealloc` used a
one-cell `M.read` with no bounds check where `evalCopy` checks the whole
range (Miri's dereferenceability of a typed access, 2026-08-28) and
initialisation (2026-09-21). Now it IS `evalCopy`. Verdicts unchanged
on the corpus (illegal_dealloc1 still fails for Miri's reason). Our
reading: a typed read of the pointer is what Miri does for
`dealloc`'s argument too, so the stricter form is the faithful one.

[OBS 2026-09-22] Proof idioms that paid off: name the fold's per-cell
op (`deallocCellOp`) and prove `sb_dealloc ap a n t = foldCells
(deallocCellOp t) ap a n` by `rfl`, so the fold's successor step can be
rewritten by the op's NAME — `rw` on the inlined lambda body failed to
find its own pattern. `List.lookup` through a key filter is the one
memory lemma both `removeRange`s need. `split at h` then `case h_2 =>`
handles a match on a constructor without `swap` (not in core).

[FACT 2026-09-22] `CoreProg.total` discharges the top-level theorems'
gate hypothesis; the predicate is kept as the deliberate admission
point for a future construct. Audit 3 axioms / 0 sorries; units 17/17 +
116/116; corpus 93/0/43; differential 93 matched.
