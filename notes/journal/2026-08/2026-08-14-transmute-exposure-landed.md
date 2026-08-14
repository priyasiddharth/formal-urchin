# Transmute + exposed provenance landed — 49/75, zero divergences

[OBS 2026-08-14] Fifth increment: transmute (incl. fn pointers) and
int-to-ptr exposed provenance. Suite: pass 62 | fail 0 | xfail 0 |
xpass 0 | unsupported 48 (110 entries); fail tests 49/75
verdict-conformant (41 line-accurate), 13 pass scenarios — counts
verified from the manifest (a dedup bug briefly double-counted two
pass scenarios; totals here are post-dedup).

[FACT] Int-to-ptr needs only ONE memory-model addition: `Mem.allocs`,
an allocation table making address→(base, offset, size) a *function* —
well-defined without angelic choice because addresses are concrete Nats
under the deterministic bump allocator (miri does the same range lookup
into its allocation map). Everything provenance-related lives in the SB
state: `AccessPerms.exposed`, the reserved `wildcardTag` (= 0, freshTag
now starts at 1 — so `MemValue.ptrVal` and the PermissionModel access
signatures are unchanged), and wildcard resolution in
readCell/writeCell/insertAboveCell.

[FACT] The ptr→int→ptr round trip destroys tag provenance by design:
the integer is a bare `word (base+offset)`; ptr-to-int *exposes* the
tag as a side effect; int-to-ptr rebuilds a wildcard pointer whose
authority is re-derived per access as "the topmost exposed item that
grants". This determinizes miri's angelic wildcard/"unknown bottom"
semantics — verdicts coincide on all covered tests
(unescaped_local: exposed-then-popped ⇒ "no exposed tags";
exposed_only_ro: read-only exposure blocks writes;
illegal_read/write_despite_exposed1: the wildcard wields the exposed
tag's invalidation power) — but a lower-exposed-item witness could in
principle differ: known approximation.

[FACT] Transmute lowering rules: to a RAW type = tag-preserving
reinterpret (ptrCast); to a REF type = a real retag via the value's tag
(illegal_write4 proves miri retags transmute-to-&mut results — "even
just creating it unfreezes"); `transmute_copy(&src) -> D` = a typed
load at D (the deref-load retag rule then fires exactly when D contains
refs). Fn-ptr transmutes/reifications are tracked statically
(`LowerSt.fnPtrs`, propagated through plain copies) and `callDyn`
resolves to the real callee — whose fn-entry seam retags then collide
exactly as miri's "protect" errors expect (aliasing_mut1/2/4) or pop
the sibling shared arg (aliasing_mut3).

[FACT] Charon encodes BOTH ptr↔ptr and ptr↔int casts as
`Cast RawPtr [srcTy, dstTy]` — disambiguate by parsing the types.
Fn reification is `Cast FnPtr` with a `Const FnDef` operand carrying
the fun id; indirect calls are `{"Dynamic": Move place}` FnOperands.
`expose_provenance`/`with_exposed_provenance_mut` are bodyless
(shimmed to the new `RExpr.exposeAddr`/`fromExposed`).

[OBS 2026-08-14] Line fidelity: 11 of the 13 new fail tests flag at
miri's exact line; aliasing_mut1-4 flag at the call-site seam vs miri's
callee-signature line (noted per-test). static_memory_modification
matches verdict+line via a different mechanism (no read-only memory in
the model: the transmute-to-&mut retag fails as a write through the
frozen shared ref).
