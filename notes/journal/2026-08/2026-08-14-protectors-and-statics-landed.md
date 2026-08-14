# Protectors + statics hoisting landed — zero divergences

[OBS 2026-08-14] Same-day follow-up to
[[2026-08-14-obseq3-conformance-landed]]: the [HYP] there ("highest-value
Phase C item is protectors ... composes with the seam-retag machinery")
is verified — implemented exactly as sketched and both protector xfails
flipped to line-accurate passes. Suite now:
pass 34 | fail 0 | xfail 0 | xpass 0 | unsupported 75. Fail tests
27/75 verdict-conformant (23 line-accurate); every test that loads
agrees with Miri's verdict.

[FACT] Protector design (src/obseq3/sb.lean): `AccessPerms.protFrames :
List (List Tag)` — a stack of tag sets, one frame per inlined call;
`pushProtectors`/`popProtectors` pseudo-statements bracket each inlined
call; `sb_ref ... (prot := true)` (emitted for reference-typed args at
inline seams, incl. tuple fields) registers the fresh tag in the top
frame; readCell/writeCell/sb_die error when a pop would remove a
protected item. Items themselves are unchanged — protection is
membership in an active frame, so popping the frame unprotects
automatically. Frame-exit runs BEFORE the return-value seam retag.

[FACT] Statics hoisting is loader-only (src/conformance/): ULLBC
represents static accesses as place-root `Global {id}` inside
`&raw mut` rvalues; the lowering appends one local per global,
materializes it with the new `RExpr.uninit` at pc 0, and rewrites
Global roots to those locals. Initializer bodies (separate const-fns in
the JSON) are not run — hoisted statics start undef. Both target tests
(pointer_smuggling, mut_exclusive_violation1) write the static before
any value-dependent use, so this is sound for them; a test that READS
a static's initial value would need initializer inlining first.

[OBS 2026-08-14] Protector error messages come out in Miri's own
phrasing ("not granting access ... would remove item ... which is
strongly protected") and at Miri's exact annotated lines (protector1@8,
protector2@9). The remaining ~10 protector-reason unsupported tests
stay unsupported for their OTHER blockers (Box, dealloc, drop glue,
control flow) — as predicted in the parked Phase C entry.
