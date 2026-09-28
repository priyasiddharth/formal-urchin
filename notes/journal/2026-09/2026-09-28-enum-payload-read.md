# 2026-09-28 — Enum variant field reads (survey item c)

[OBS] `parsePlace` turned `{"Field": [kind, i]}` into `.field i` whatever
the kind, so a variant field `(o as Some).0` read cell 0 — the
discriminant — although the enum layout (elab.lean `toLayout`) puts
variant field i at cell 1+i, where the aggregate and the seam retags
already write it. Charon's kinds across all artifacts: `{"Tuple": n}`
(286), a struct's `{"Adt": [decl, null]}` (74), an enum variant's
`{"Adt": [decl, v]}` (4). Fix: variant present ⇒ `1 + i`.

[OBS] The survey's "latent in return_invalid_{mut,shr}_option" is right
but weaker than it sounds: those reads are in `main`'s `Some(_x)` arm,
AFTER the UB, so the lowered program never contains them — their dumps
are unchanged by the fix.

[OBS] Two new entries exercise it, both failing on the pre-fix binary
(scratch worktree at d731852) and passing now:
- local/enum_payload_read — old: "type mismatch at line 12: dst PtrL NatL
  vs rhs NatL" (the binding typed as the discriminant word);
- interior_mutability::rust_issue_68303 (split; `as_ref().unwrap()` →
  `match &optional`, `is_some()` → `matches!`) — old: false positive
  "retag failed … tag 15 does not exist" at line 17, the one the survey
  saw.

Corpus 112/0/31, osea 112, certificates 38 / 52 checked; live Miri
112/112, 0 drift.

## See also
2026-09-28-impl-segments.md, loose-ends/parked.md § A′ c
