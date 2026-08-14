# obseq3 + conformance suite landed

[OBS 2026-08-14] The full pipeline from the morning's plan
(plans/sb_conformance_obseq3.md) landed in one session. Score against
miri @ 34d6a795: fail tests 23/75 verdict-conformant (19 line-accurate),
2 xfail-model (protectors), 50 unsupported with reasons; pass scenarios
9 clean. Suite: pass 30 | fail 0 | xfail 2 | xpass 0 | unsupported 77.
Run: `conformance/scripts/run_suite.sh`.

[FACT] Miri's raw-mut retag performs NO parent access and inserts the
SharedReadWrite item directly above the granting item — not on top of
the stack. This single placement rule is what makes sibling raws coexist
(pass/basic_aliasing_model::two_raw) while `&mut`-retag write-accesses
still invalidate them (fail/raw_tracking). First obseq3 draft did
write-access+push-on-top, which was strictly stronger than Miri and
wrongly flagged two_raw. Implementation: obseq3.sb.insertAboveCell,
src/obseq3/sb.lean.

[FACT] rustc's built MIR already lowers `&mut x as *mut T` to
Ref + RawPtr-of-deref rvalues (no cast fusion needed), and emits
TwoPhaseMut reborrows for by-value `&mut` call arguments. Ptr-to-ptr
`as` casts arrive as `UnaryOp [Cast RawPtr, op]` and are tag-preserving
(lowered as copies). Ref-typed returns get an explicit reborrow at the
`ret` expression — which is why our UB lines match miri's `//~ ERROR`
annotations on return_invalid_mut/shr; tuple-wrapped returns get no
such reborrow, so those two flag at the call-site seam instead (noted
in manifest).

[OBS 2026-08-14] The protector xfails behave as predicted:
invalidate_against_protector1/2 complete cleanly (our model pops
protected items without error). illegal_write6 however matches miri's
verdict AND line via a different mechanism (seam retag pops the raw
before the write; miri fails the same write via protector) — promoted
to supported with a mechanism note in the manifest.

[HYP] Highest-value Phase C item is protectors: it would convert 2
xfails + ~10 unsupported to supported, and it composes with the
existing seam-retag machinery (protector flag on seam-retagged items,
cleared at the inline return; "would pop protected" ⇒ UB in
sb_read/sb_write). Statics hoisting (~4 tests) is the cheapest.
