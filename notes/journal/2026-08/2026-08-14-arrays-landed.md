# Arrays + pointer arithmetic landed — 52/75, zero divergences

[OBS 2026-08-14] Seventh increment: fixed-size arrays and constant
pointer arithmetic. Suite: pass 72 | fail 0 | xfail 0 | xpass 0 |
unsupported 44 (116 entries); fail tests 52/75 (44 line-accurate),
20 pass scenarios. New: unescaped_static (ub at cell offset 1 — the
per-cell model verbatim), transmute-is-no-escape, and the array_casts
pass scenario.

[FACT] Arrays are homogeneous tuples: `[T; N]` parses to
`tup (replicate N T)` (charon: `{"Array": [elemTy, constGeneric]}`),
array aggregates and `[v; N]` Repeat rvalues desugar to per-element
writes. Charon Index projections carry an OPERAND (const indices flow
through temp locals), so the lowering tracks constant-valued plain
locals (`LowerSt.constVals`) and resolves `Index` to static field
projections; runtime indices stay unsupported.

[FACT] Built MIR guards every array index with a bounds check:
`_c = BinaryOp(Lt, i, N)` + an `Assert` terminator. Arithmetic is
supported ONLY in statically-foldable positions: `binOp` rvalues fold
through constOf (consts + tracked locals) and `Assert` terminators are
checked at lowering time (statically satisfied → goto target; dynamic
or failing → unsupported). This keeps real dynamic arithmetic out of
the IR while letting bounds checks vanish.

[FACT] `ptr.add/offset/wrapping_offset` (bodyless) shim to
`RExpr.ptrOffset` — a constant delta scaled by the POINTEE's blockSize,
preserving the tag (miri: ptr arithmetic keeps provenance). Signed
constants now parse (`UOperand.constNeg`); wrapping_offset(-1) in
transmute-is-no-escape moves cell1→cell0 where the transmuted tag does
not exist. Offsets below the allocation base error.

[OBS 2026-08-14] Slices proper (fat pointers, runtime-length retags,
from_raw_parts_mut, range indexing with dynamic bounds checks) remain
the honest boundary: zst_slice, buggy_as_mut_slice, buggy_split_at_mut,
fnentry_invalidation2 all need them (plus Vec/control flow).
