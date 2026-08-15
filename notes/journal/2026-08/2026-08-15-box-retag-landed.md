# Box unique retag landed — 56/75, claim unqualified

[OBS 2026-08-15] Tenth increment: the box unique retag, closing the
last SB-policy carve-out in the conformance claim. Suite:
pass 76 | fail 0 | xfail 0 | xpass 0 | unsupported 40; fail tests
56/75 (48 line-accurate), 20 pass scenarios. box_noalias_violation
conformant at miri's line 11 (`*y`), failing through the protected
Unique created by the Box argument's fn-entry retag — miri's error
category "weakly protected" exists solely for this rule.

[FACT] Implementation is a policy line, as predicted: UTy.boxT distinct
from raw; containsRef true; the seam case retags the pointee as a
protected Unique (`.ref .mut prot (pointee)`); Box::from_raw is a
tag-preserving value copy (the box retag happens at the next seam);
mem::forget is a no-op (protectors end at return regardless). All four
previously-passing Box tests held unchanged — box_exclusive_violation1
still fails at line 25 with the seam retag now in the chain.

[FACT] Remaining box nuances, documented not implemented: miri's box
protector is WEAK — pop-blocking identically to strong, differing only
in permitting deallocation during the call (no reachable test); plain
Box-typed assignments (`let b2 = b`) are retagged by miri's AddRetag
but not by us (no test).
