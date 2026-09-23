# Certificate-guided lowering: dynamic branches and loops without a CFG

[FACT 2026-09-23, verified against 3dd7ff0] Design landed (commit
3dd7ff0, plan ~/.claude/plans/harmonic-baking-panda.md): a certificate
`<name>.cert.json` records Miri's branch outcomes per user-frame instance
(switch arm, assert outcome); the seam follows it, unrolling loops, and
emits runtime checks from `uninit`/`assignIf`/`copy` only. Tiers: T1
folded + cross-checked, T2 runtime-checked (loaded word, enum slot 0,
`Eq/Ne(place, const)`), T3 unchecked pin (comparison on words Miri did
not log) — counted and reported. No model or proof change. User
decisions: existing instructions only; Miri as the source; count T3 now,
a word `binOp` rvalue later makes T3 checkable.

[FACT 2026-09-23] What Miri can emit on the pinned toolchain:
`MIRIFLAGS=-Zmir-opt-level=0 MIRI_LOG="rustc_const_eval::interpret::step=info,rustc_const_eval::interpret::stack=info"`
prints per frame the executed blocks and every statement/terminator as
MIR text; NO runtime values. The frame-pop line (`popping stack frame`)
lives in `interpret::call`, which that filter does not select even when
named — use the executed `return` terminator as the pop marker (410
frames = 410 returns in the probe). Block/local numbers differ from
charon's built MIR; the ORDER and KINDS of switch/assert events per user
frame agreed on every probe so far.

[OBS 2026-09-23] The checks earned their keep on the first non-trivial
probe: assigning a constant to ONE FIELD of a placeholder `(value,
overflowed)` tuple un-tainted the whole local, so the placeholder later
written through a raw pointer was trusted as exact, and the T2 check
`*y1 == 2` REJECTED the certificate at runtime (mirlite had 0 there).
Fixed (field assignments never clear taint). A silent wrong verdict was
impossible by construction; that is the property the design buys.

[FACT 2026-09-23] `assert_eq!(x, 2)` in built MIR is `_9 = const 2;
_8 = &_9; _6 = (move _7, move _8); right_val = copy _6.1; _14 = copy
(*right_val); _12 = Eq(move _13, move _14); if _12 …` — no promoted
constant, no global. Making it T1/T2 needs the constant reachable through
a reference stored in a tuple field: `refOf` is now keyed like
`constVals` by (local, field path) and points at a PLACE; `resolveKey`
follows deref chains (fuel 8). A write through a tracked pointer then
UPDATES the target's constant instead of killing everything.

[OBS 2026-09-23] `assert_eq!` on a TUPLE (`assert_eq!(*data, (1, 1))`)
calls `<(u8,u8) as PartialEq>::eq`, opaque in the artifact → "call to
bodyless function eq". Keep that one prep rewrite ("assert dropped").
`assert_eq!`'s never-walked panic arm declares `core::fmt::Arguments`
locals in the SAME body: elaboration now gives an un-layoutable local a
placeholder word and errors only on a USE of it.

[OBS 2026-09-23] A second bug the checks caught: `emitSeamCopy`'s
IN-PLACE retag (`dst == src`, a moved argument retagged where it sits)
recorded `refOf dst := *dst` — self-referential — so `self.0` in a method
could not resolve, `self.0 + n` became a placeholder, and the placeholder
flowed into `res` and into a checked `assert_eq!(res, 42)` →
"certificate rejected". Two fixes: an in-place retag keeps the old target;
`faithfulPlace` judges the RESOLVED local, not the reference local. After
that, two_phase_aliasing_violation is fully T1 (0 pins).

[OBS 2026-09-23] gen_cert.sh: argparse treats `-Zmiri-…` as an option
— pass `--flag=<v>`; and `"${arr[@]}"` on an empty array trips `set -u`.

[FACT 2026-09-23] Results: 96 pass / 0 fail / 40 unsupported; 23
certified entries, 27 checked, 14 unchecked; differential 96 matched;
units and audit unchanged (no model/proof change). `fnentry_invalidation`
needed no default-trait-method work: charon emits `Bad::do_bad`'s body.
