# 2026-09-29 — stdlite: the std shims as a Lean module

[OBS] The user asked for a "libstdlite". Two readings were weighed: a Lean
module (refactor) or a Rust library of models compiled by Charon and
inlined. Probes for the Rust route: compiled with `--monomorphize` a
model crate yields NO bodies (nothing instantiates the generics); without
it, bodies are generic (TypeVar, `Box<T, Global>`, `ManuallyDrop<Box<T>>`)
and still call bodyless std (`ManuallyDrop::new`, `deref_mut`). It would
need loader-level generic instantiation, a second artifact, a Lean
primitive floor, and — decisive — models must be straight-line because
Miri's certificate has no frames for std, which excludes exactly the
branching functions (Vec::push, Option::unwrap) where Rust bodies would
pay off. A naive `write<T>(p, v) { *p = v }` also drops the old value,
which `ptr::write` must not do. Chose the Lean module.

[FACT] Now three files: `emit.lean` (LowerSt, emitAssign, seam retags;
moved verbatim), `stdlite.lean` (26 named shims, `abbrev Shim`, and
`stdlite.table` : path ↦ shim, 50 rows; `shimCall` = table lookup), and
`lowering.lean` (header, certificate checks, walker). The two shims that
read `f.path` for mutability (`sliceIndex`, `sliceAsPtr`) take
`(mutbl : Bool)`, one table row per path. Generated mechanically from the
old if-chain (a script split it and checked the table's 50 paths equal the
chain's).

[OBS] Behaviour identical to HEAD (4d9b207): all 145 `--dump`s, the full
`--record --osea` output on the committed artifacts and on the fresh
`.live` ones (which carry the unsupported entries' rejection messages).
Live 116/116, 0 drift; units unchanged.

## See also
2026-09-29-box-pointee-inference.md, loose-ends/parked.md § A′ j
