# 2026-08-28 (small hours) — Commutation meets the move-to-front list

## The finding
The disjoint-range die↔useMut commutation needed by the nonzero-offset
copy leaf is TRUE at the find?-level but UNSTATABLE at PermSim's level:
`PermSim`'s stacks conjunct is `ListRel (CellSim ρt)` over the
StackMap's LIST REPRESENTATION, and `SB.set` is move-to-front. The two
machines stay positionally aligned only because they perform the SAME
op sequence; the copy fragment's interleaved order (ref; read;
useMut(dst); die(src)) leaves src-range cells at the FRONT of the
target's list while the source (read(src); useMut(dst)) leaves
dst-range cells at the front. Same find? semantics, different lists —
`ListRel` positional alignment with the source is unprovable, and so
is literal StackMap equality for the commuted execution. This is the
`durable/sb-stackmap-assoclist-tradeoff.md` prediction coming due.

## The three routes (user decision)
(a) **find?-quotient PermSim** (proof-side only): stacks conjunct
    becomes `∀ a, OptionRel (StackSim ρt) (find? src a) (find? tgt a)`.
    Transports already consume via `SB.find?_transport` and can
    conclude via `setChain_chain_find?`; the keystones' literal
    equalities still imply it. Surgery: PermSim + ~8 ListRel sites in
    permsim_transport + conclusion rebuilds. Keeps semantics untouched.
(b) **stable SB.set** (semantics-representation): replace-in-place
    instead of move-to-front. Disjoint setChains then commute
    LITERALLY, and positional alignment becomes trivial (positions
    never change). Observable semantics unchanged (find? identical);
    every proof that peeks at the cons/filter structure needs repair.
(c) **PtrOffset lowering for place-to-register projections** (compiler
    change): `placeToRegChecked`'s proj arm emits
    `Assgn tmp (PtrOffset baseReg off)` — TAG-PRESERVING address
    arithmetic — instead of `Borrow`. The copy/write fragments then
    perform EXACTLY the source's events (mirlite never retags copy
    srcs or write dsts; the Borrow was a compiler phantom that BRIDGE
    1/1S existed to cancel). Removes the keystone obligation from
    every such leaf and shortens the closed proofs it re-proves — but
    it narrows the user's GEP-as-a-borrow decision (2026-08-27) to the
    contexts that genuinely reborrow (`&s.f`), so it is the user's
    call twice over.

## State
No code changed; finding recorded. The leaf itself remains UNBLOCKED
in principle (disjointness is supplied by the overlap guard) — the
block is purely the representation-level statement of commutation.
