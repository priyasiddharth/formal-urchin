# 2026-09-30 — Pointer-wrapper shims; what "the remaining shims" left open

[FACT] `NonNull<T>` and `ManuallyDrop<T>` are OPAQUE monomorphised decls
(like Box), so their `T` is inferred in the same prescan
(`collectBoxPointees`, now keyed by `wrapperDeclId name`): NonNull from
`new_unchecked`/`From::from`/`as_ptr`/`as_mut`, ManuallyDrop from
`new`/`deref`/`deref_mut`. `parseTy`: NonNull = `raw true T`
(repr(transparent) over `*const T`); ManuallyDrop = `T`, but only when
`T` has no reference anywhere (`containsRefTy`) — its field is a
`MaybeDangling`, whose inner references Miri does not retag.

[FACT] Shims, from std's bodies: `NonNull::from` = `from_mut(r)` =
`transmute(r as *mut T)` → two fn-entry retags then the raw retag (the
`into_raw` shape); both `From<&T>` and `From<&mut T>` render as
`<NonNull as From>::from`, so the argument type picks Unique/raw-mut or
SharedReadOnly/raw-const. `clone` = copy; `as_mut` = `&mut
*self.as_ptr()`; `as_ptr`/`cast`/`new_unchecked`/`UnsafeCell::raw_get` =
casts (`ptrCast`); `ManuallyDrop::new` = identity; `deref`/`deref_mut` =
shared/unique reborrow; `size_of` via `tyArgTable`.

[OBS] mut_exclusive_violation2 back to upstream NonNull code: UB line 18
(was 17 with the prep; the `use` line shifted it), same reason as Miri.
Witnesses local/std_wrappers_ok (ok) and local/nonnull_from_shared_write
(UB line 12; forcing the `&mut` path fails it at line 11). Old binary:
all three "call to bodyless function from"; 152 others byte-identical.
Corpus 126/0/29, osea 126, live 126/126, 0 drift.

[HYP → decision needed] Not done, each more than a shim:
- `Option::{as_ref, unwrap, is_some}`, `Result::unwrap`,
  `Layout::from_size_align` — a failure path. Miri's certificate records
  no std frames, so `unwrap` of `None` (a panic in Miri) needs a check of
  its own, reported as such; today's check machinery says "certificate
  rejected", lives after stdlite, and assumes a certificate.
- `null_mut`, `is_null`, `addr`, `without_provenance_mut` — a pointer
  without provenance and an address read that does NOT expose; mirlite
  and oseair have neither (item o; proof surface).
- `slice::from_raw_parts_mut` — item r.

## Later: user-written Option, and the enum freeze mask it exposed

[OBS] The user's proposal: rewrite preps to use a user-written Option so
Miri's certificate records the frames. A local `enum Option` + `use
Option::*` + an `impl` with std's bodies shadows the prelude; inherent
methods win, so call sites stay upstream. Needed one tooling fix:
`miri_cert.py` rejected `Option::<std::cell::RefCell<bool>>::as_ref`
because of the `std::` in its generic arguments — plain paths are now
judged with generics stripped (full live: 0 certificate drift).

[OBS] The pilot then gave a model false positive (UB at `*handle = true`):
`freezeMask` froze every enum, so `is_some(&self)`'s shared retag of
`&Option<RefCell<bool>>` did a read and popped `handle`. I first claimed
Miri decides per active variant — WRONG. [FACT, vendor/miri/src/helpers.rs
`visit_freeze_sensitive`] a non-`Freeze` `Variants::Multiple` value is
treated like a union: the whole value is UnsafeCell, with no read of the
variant ("Reading from memory would be subject to Stacked Borrows
rules"). `freezeMask (.enum e)` = all-true iff any variant holds a cell
(`containsCell`). No existing entry's lowering changed. Witness
local/enum_cell_shared_retag (frozen mask: false UB line 18 — checked).

[OBS] Pilot interior_mutability::rust_issue_68303: upstream body, 4 user
frames, 3 runtime-checked branches, ok as Miri. Corpus 127/0/29, osea 127,
certificates 39 / 54 checked; live 127/127, 0 drift.

## See also
2026-09-29-box-into-raw.md, 2026-09-29-stdlite-module.md
