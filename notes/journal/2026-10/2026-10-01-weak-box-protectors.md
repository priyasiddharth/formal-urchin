# 2026-10-01 — Weak Box protectors (item p, step 1)

[FACT, vendor/miri/src/borrow_tracker/stacked_borrows/mod.rs] A Box's
fn-entry retag is Unique + WeakProtector (`from_box_ty`, :133); a
reference's is StrongProtector (:63). `Stack::dealloc` (:359) = a write
access (popping ANY protected item above the granting one is UB, even a
weak one) + a check of the remaining items: UB only if STRONGLY protected
(`item_invalidated`, :257).

[FACT] Encoding chosen for least proof churn (the `prot : Bool` in
RExpr.ref / Rhs.Borrow / PermissionModel.ref is untouched):
- `RefKind.BoxMut` — per cell exactly `Mut` (`refCellOp`, `toItem`);
- `AccessPerms.weakProt : List Tag` — `sb_ref` with `prot` and `BoxMut`
  adds the fresh tag (`if kind = .BoxMut`, the DecidableEq form: the
  derived-BEq `==` does not simp-reduce);
- `sb_dealloc` per cell: `firstProtected above` → UB; `(item :: below)`
  with a protected, non-weak item → UB ("strongly protected").
- `PermSim` gained a 5th conjunct `TagListSim ρt src.weakProt tgt.weakProt`.

[OBS] Proof repair: `BoxMut` arms share `Mut`'s (`| Mut | BoxMut =>`, 5
sites); 5 structure literals got `weakProt := _.weakProt`; ~15 PermSim
destructure/construct sites; `sb_ref_read_die_cancels` and
`sb_ref_use_die_cancels` return `s3.weakProt = sAcc.weakProt`; the
protected branch of the sb_ref transport splits on `kind = BoxMut`
(fresh pair via `h_newpair`); dealloc.lean: `deallocCellOp` mirrors the
new body, new `strongProt` + `firstProtectedIn_singleton_isSome` +
`strongProt_eq` (via existing `TagListSim.contains_eq`). Audit: 3 axioms,
0 sorries, same roots.

[OBS] Loader: `URefKind.boxMut` for the Box seam retag. Verdicts/lines/
osea of all 156 prior entries identical to HEAD (3 dumps differ only in
that label). Witness local/box_arg_dealloc_weak (Box arg freed via
into_raw + dealloc: ok as Miri; HEAD: false "strongly protected" UB).
Unit t19. Corpus 128/0/29, osea 128, live 128/128, units 19/19 + 129/129.

[OPEN] The paper (pldi27, ~l.420–436 retag kinds, ~l.1215 PermSim) now
lags: a retag kind and a fifth PermSim component. Its file carries
another session's uncommitted edits — not touched.

## Later: step 2 — Box drop glue

[FACT] Built MIR emits a `Drop` per place with drop glue at scope end or
before an overwrite; elaboration (later) skips moved-out places. The
loader now keeps `UTerm.drop place target`; the walker tracks moved
places on its one path (`markMoved` for `move` operands of statements and
call args, `markInit` for assignment and call destinations) and runs
`emitDropGlue` (emit.lean): a Box drops its contents, consumes the
certificate's next `drop` event, then `dealloc`s through its own pointer
unless the contents are zero-sized; tuples/structs recurse by field; an
enum holding a Box is unsupported. `mem::drop` (stdlite) = drop glue of
its argument. `checkDrops := true` at the cursor. A drop with no Miri
drop left, in a UB/panic certificate that is entirely consumed
(`CertCursor.allConsumed`), is past Miri's prefix: poison, not an error
(box-cell-alias's helper drops its Box after the UB line).

[OBS, a latent bug] miri_cert.py never classified a drop-flag switch: its
assignment regex ran on the text after `INFO`, which still starts with the
module path, so `_9 = const false` never matched; no committed certificate
had a `drop_flag`. Box drops create such switches (box_drop_conditional's
`switchInt(copy _9)` at scope end). Fixed (match after `interpret::step`);
all other certificates unchanged.

[OBS] Mutation checks on local/box_drop_conditional: `mem::drop` as a
no-op → "Miri dropped a Box<i32> in main after 1 branches; the lowering
did not drop it there"; ignoring moves → "the lowering drops a Box … that
Miri did not drop". 10 existing entries now contain Box deallocations,
all verdicts unchanged. Corpus 132/0/29, osea 132, certificates 40 / 55
checked; live 132/132, 0 drift; audit unchanged; units 19/19 + 129/129.

## See also
loose-ends/parked.md § B2 and A′ p
