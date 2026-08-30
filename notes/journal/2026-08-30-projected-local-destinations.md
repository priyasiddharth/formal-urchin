# Projected destinations over a LOCAL base: mostly a generalization

[OBS 2026-08-30] `t.f := copy y` closes at both offsets and for both a
BOUND and an UNBOUND root (d66–d69). `copy_place_residual` now names
exactly ONE class.

**The bound half cost no new proof.** The parked note said to mirror
`const_write_proj_zero/offset_simulation` with the copy source
pre-phase in front — i.e. write two more ~600-line leaves. That was
unnecessary. `copy_projdst_zero/offset_chainsrc_simulation` were
written for a destination base `.deref P`, but nothing in either proof
uses the `deref` shape: the destination lowering goes through
`ptrChain_lowering_sim`, which is chain-generic, and a BOUND LOCAL is a
chain (`PtrChain.base`). Generalizing `.deref P` to `dbase` with
`h_dchain : PtrChain dbase` was mechanical.

[FACT] The one thing that genuinely differs is `preparePlaceAssign`.
For a deref-rooted place the `allocateRoot` branch is contradictory —
the old proofs closed it with `simp [mirlite.allocateRoot]`. For a
local root it is REACHABLE (that is the fresh case). So the
generalization takes a hypothesis

    h_bound : ∀ s, preparePlaceAssign MSB s_mir (.proj dbase path) = .ok s →
      s = s_mir ∧ ∃ r0, resolvePlace? s_mir (.proj dbase path) = some r0

which the deref call sites discharge with the old `simp`, and the local
call site discharges from `Env.lookup … = some bD`. A hypothesis
instead of a proof. The four `compileStmt_copy_projdst_*` fragments
generalized the same way (`h_np` instead of the inlined
`fun _ _ _ h => by cases h`), as did the source-flatten transfer, now
`compileStmt_copy_projdst_srcflatten_run/_value` — it was never
deref-specific, only deref-SPELLED.

**The fresh half is real work.** `copy_projlocal_fresh_zero_simulation`
and `..._offset_simulation` are regime B-proj for copy: the σ-sized
root `Alloc` from `ensurePlaceRoot`, then the source mother lemma at
the POST-allocation states under `ρa.extendBlock` and `ρt.extend`, then
the write — at `+ 0`, or through the fresh root register's own
`Borrow(Mut)`/`Die` (BRIDGE 1). Note the allocation is sized by the
BASE layout σ while the write is `blockSize τ` at `pathOffset path`;
`PathTo.offset_add_size_le` is what makes the write land inside.

## Potholes

[OBS] **`PtrRegisterEntry` is not a rewrite target.** Stating a
register fact as `PtrRegisterEntry m r base off size tag` and then
`rw [RegMap.lookup_insert_ne …]` fails — the goal is the abbreviation,
not the `lookup` equation. Either prefix with
`show oseair.RegMap.lookup _ _ = _`, or state the LOOKUP equation and
derive the `PtrRegisterEntry` from it by ascription. `simp only [… ,
h_entry]` has the same problem in reverse: to resolve a `match` on a
lookup, simp needs the lookup equation, not the entry. Keeping both
(`h_lookupTmp` and `h_entryTmp := h_lookupTmp`) is the cheapest fix.

[OBS] **Two spellings of the same address.** BRIDGE 1's borrow gives
`addrStart + (0 + pathOffset path)`; mirlite's resolution gives
`addrStart + PathTo.offset path`. They are defeq but not syntactically
equal, and `pathOffset` / `PathTo.offset` are distinct atoms. When one
appears on each side of a `SourceMemSim`, rewrite the GOAL into the
BRIDGE spelling (`rw [h_oe]` with `h_oe : … PathTo.offset … = … (0 +
pathOffset …)`) rather than rewriting the hypothesis — rewriting the
hypothesis hits both of its sides and breaks the half that already
matched.

[OBS] **`TagRenameBounded.mono` needs its bounds.** `refine
TagRenameBounded.mono ?_ h ?_` leaves the target tag bound `nT`
unsolved. Supply the whole thing as one `exact` so the first argument
pins it.

[OBS] The long-`StateIncr`-chain pothole recurred exactly as
[[transport-compiled-states-by-defeq]] predicts, twice, and the
prescribed fix (split at a nameable state, ground prefix + short tail)
worked both times without further thought. First real evidence the note
pays for itself.

## The class the parked note did not name

[FACT] `CompilerInv_step_copy`'s proj-dst arm reads

    by_cases h_sch : PtrChain (flattenPlace src)
    · exact copy_projdst_simulation …
    · exact copy_place_residual …

so a PROJ-TOPPED flattened source under ANY projected destination has
always gone to the residual, and the parked entry listed only the
local-base class. That is now the ONLY remaining copy class. Both
halves exist — the destination projection's BRIDGE 1 endgame (d63/d67)
and the source projection's BRIDGE 1S prefix (d65) — but they have not
been composed into a leaf that carries both.

## Teeth

Oversizing the projection's `Borrow` by one word, restricted to
`RefKind.Mut`, is discriminating for the fresh pair: d68 (offset zero,
which takes the no-borrow branch) passes, d69 flips to `target verdict
ub 1, source agrees ok`. Same shape as d65's tooth at `Shared`.

**Validation:** full build green; 17/17 + 82/82; corpus 82 pass / 0 fail
/ 123, osea matched 82; audit exact at 2 sorries, `[axioms]` untouched.
