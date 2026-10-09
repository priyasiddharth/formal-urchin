# 2026-10-08 — RefCell's borrow flag, modelled and checked

## Context
Two of the four `reason_known` entries (illegal_read5,
shared_rw_borrows_are_weak2) came from the elided flag: the model put
RefCell's value at offset 0, Miri at 8. The user chose the real flag
(parked option 2) WITH a flag check.

## What changed
- ullbc_ast: `RefCell<T>` = `structT [cell isize, cell T]` at Charon's
  layout for the opaque decl (fields in declaration order: borrow, value;
  `StructLay.refCell`). `Ref`/`RefMut` = `[raw value ptr (NonNull), &Cell<isize>
  (, ZST marker)]` with `StructLay.guard = some mutbl`. Opaque decls now
  keep Charon's layout (`parseDecls`).
- emit: `refCellFlagUpdate` — read the flag, optional `check` (an
  assumption-sentinel `check`, line 3×certLineBase), write `flag op 1`
  through a fresh `&mut isize` after reading the old value (std's
  Cell::get, Cell::set = mem::replace). `emitDropGlue` drops guards
  (Ref: −1, RefMut: +1) through the guard's `&Cell`.
- stdlite: `RefCell::new` writes flag 0 + value; `borrow` = `&Cell`, flag
  update with `check flag ∉ [-1]`, then the masked shared value reborrow;
  `borrow_mut` = `check flag ∈ [0]`, flag −1, unique value reborrow;
  `replace` = borrow_mut, read, write, give back; `get_mut` = unique
  reborrow of the value field; guard deref loads field 0.
- harness: the assumption-failure message names RefCell's flag.

## Evidence
[OBS] All 11 RefCell entries pass; illegal_read5 and
shared_rw_borrows_are_weak2 now fail at Miri's byte: reasons 105 as Miri
+ 2 known (static read-only memory; exposed-only int-to-ptr), was 103 + 4.
[OBS] Mutation test: with the guard drop disabled, the three new
witnesses (local/refcell_*) are rejected at exactly the next borrow's
line ("a lowering assumption failed") — the check catches missed drops.
[OBS] Corpus 201 / 0 / 17 of 218; --osea 201 (996 Dies); --layouts 201;
live.py: all 218 Miri verdicts equal the manifest, no drift.
[DEC] The guard's value pointer stays a MASKED shared reborrow for
`borrow` (as before).
[SUPERSEDED → correct as is, 2026-10-09] "Miri's `&*self.value.get()`
is `&T`, frozen for a Freeze `T`; not changed here — no test
distinguishes it" — wrong reading of std: `try_borrow` stores
`NonNull::new_unchecked(self.value.get())`, a RAW pointer from a
SharedReadWrite `&UnsafeCell<T>`; the freeze is at the deref's `&T`. A
test does distinguish it, and the model was already right; see
2026-10-09-refcell-guard-pointer.md.
[DEC] Borrow-conflict PANIC tests stay unsupported: the check rejects
the run rather than panicking.
