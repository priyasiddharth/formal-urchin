# 2026-10-01 — Byte-addressing probe: what breaks in the proof

[OBS] A throwaway worktree of `conformance-drop-in-place` (4b1afea), build
cache seeded from the main tree. Nothing committed; the worktree is gone.
Question: if the memory unit became the byte (Miri's), how much of the
19,594-line obseq3 proof needs repair? Measured, not estimated.

## Stage 1 — byte size ≠ slot count

`src/obseq/types.lean`: `typeSize NatTy = 4`, `PTy = 8`; `layoutSize NatL
= 4`, `PtrL = 8`. One error, at the type level, before any proof is
reached: `EvalOutput.values_len : values.length = blockSize τ` — a one-cell
`ptrVal` list no longer has length `blockSize (PtrL σ)`. Every use of
`blockSize` as a COUNT OF VALUES is a type error from this point; every use
as a DISTANCE (offset, range, allocation size) is not.

## Stage 2 — split the two notions (C0: byte-sized cells, no partial access)

`slotCount : LayoutTy → Nat` / `slotCountTy : TyVal → Nat` (one per scalar
or pointer leaf) added in `src/obseq3/types.lean`. Definitions changed, 13
sites: `values_len`, `readWordSeq … (slotCount τ)` ×2 and the undef checks,
`List.replicate (slotCount τ) undef`, `writeResolvedPlace`'s length
hypothesis (mirlite); `Load`'s `readWordSeq`, `CStore`'s size check,
`Memcpy`'s read (oseair); the `uninit` fill (compile). Ranges, bounds,
`allocate`, `ptrOffset` scaling, slice extents keep `blockSize` (bytes).
`lake build Obseq3`: green, 4 s — the semantics and compiler accept the
split without further change. (Memory entries still sit at consecutive
addresses while offsets are in bytes: the probe does NOT make
`readWordSeq` layout-directed, so it under-counts; see caveat.)

### Mechanical restatements (sed, counted)

| kind | sites | files |
|---|---|---|
| `.length = blockSize/typeSize` → `slotCount`; `List.replicate (blockSize …)`; `readWordSeq … (blockSize τ)` in statements | 37 | spine 17, copy 11, common 5, const_write 2, alloc 1, ptrarith 1 |
| pointer-is-one-cell: `addr + 1 >/≤`, `read … 1`, `readWordSeq … 1`, `blockSize (PtrL σ) = 1 := rfl`, `typeSize PTy` | 31 lines | ptrarith 13, spine 11, casts 7 |

### Proof repairs (round-1 errors after the restatements, by module)

Build each module in import order; Lean's per-declaration recovery makes
the count one per broken theorem, not a cascade. Broken theorems were then
sorried so importers could be measured.

| module | lines | broken theorems | which |
|---|---|---|---|
| common | 3460 | 1 | `runN_Assgn_Load_ptr_step` |
| permsim_transport | 2251 | 0 | — (SB layer, unit-agnostic) |
| spine | 4752 | 6 | `ptrChain_lowering_sim`, `copy_{freshroot,freshproj,boundproj,boundplain,chain}_write_after_read` |
| copy | 1447 | 2 | `copy_chainsrc_read`, `copy_readpkg_projoffset` |
| const_write | 460 | 1 | `uninit_valuePkg` |
| ref | 1248 | 2 | `ref_valuePkg_chain`, `move_valuePkg_chain` |
| alloc | 391 | 1 | `alloc_step_bundle` |
| casts | 917 | 2 | `expose_readpkg_projoffset`, `fromexposed_readpkg_projoffset` |
| ptrarith | 1053 | 5 | `ptrcast_readpkg_{lowered,projoffset}`, `ptroffset_readpkg_projoffset`, `refslice_readpkg_{lowered,projoffset}` |
| keystone, dealloc, binop, slice, protectors, assign_if, compiler | 3,500 | 0 | — |
| **total** | 19,594 | **20 theorems** | **≈3,470 proof lines** (19,594 → 16,122 after sorrying them) |

`scripts/audit_axioms.sh` on the probe: `sorryAx` reachable from both roots
through exactly these theorems (plus 4 cascade-patched neighbours from a
mangled first patch: `LoweringSim.projZero`, `PtrChain.loweringSim`,
`copy_freshroot_prologue`, `copy_bound_write_after_read` — not counted).

### Classification of the breakages

1. **Mechanical (restate with the split)** — `runN_Assgn_Load_ptr_step`,
   `uninit_valuePkg`, `alloc_step_bundle`, the 7 `*_readpkg_*` lemmas in
   casts/ptrarith, `ptrChain_lowering_sim`: a pointer load's bound becomes
   `addr + 8 ≤ size` instead of `< size`; `read … 1` becomes
   `read … (blockSize (PtrL σ))`; `blockSize (PtrL σ) = 1 := rfl` goes.
   ~11 theorems; tedious, no new ideas.
2. **Design: the target's store width.** `copy_*_write_after_read` ×5 and
   `move/ref_valuePkg_chain`: oseair's `writeThroughPtr` (hence `RStore`,
   `CStore`) takes its SB range from `vals.length` — the number of values —
   while mirlite's `writeResolvedPlace` uses `blockSize τ` bytes. Under C0
   the store must carry a TYPE-DIRECTED byte width (`typeSize ty`), and
   the simulation lemmas relating the two ranges are re-proved. ~8
   theorems, the big ones (`spine.lean` `write_after_read` family is
   ~2,500 lines).
3. **Design: layout-directed memory access** — NOT exercised by the probe
   (caveat). With entries at byte addresses, `readWordSeq`/`writeWordSeq`
   must walk the layout (`NatL` at `a`, next leaf at `a + 4`, …), and the
   82 + 45 lemma references to them, `MemValSim`/`SourceMemSim`
   (common.lean:763, :1059), `readWordSeq_sim` (:1103) and the
   `copy`/`ref` composition lemmas over `PathTo.offset` change shape. Add
   `copy_freshproj_write_after_read`'s omega failure (offset arithmetic
   mixing the two units) to this bucket. Expect this to touch most of the
   `copy` and `spine` lemmas that stage 2 did not break: a realistic C0
   count is 20 theorems **plus** the `readWordSeq` family — order 40–60
   theorems, 5–7k lines.

## Revised estimate for C0 (byte-sized cells, no partial access)

- Definitions: ~13 sites + layout-directed read/write (~100 lines in
  mirlite and oseair) + a byte width on the store instructions.
- Loader: keep widths from Charon's `Literal` types and read `layout`
  (sizes, `field_offsets`, align) — a few hundred lines in
  `ullbc_ast.lean`/`elab.lean`; shims return bytes.
- Proof: 68 mechanical restatement sites; ~11 theorems restated; ~8
  store-width theorems re-proved; the `readWordSeq`-family rework
  (unmeasured, est. 20–40 theorems). Order 2–4 person-weeks of proof work
  if the `write_after_read` family survives in shape; the SB layer (keystone,
  permsim_transport, protectors — 3.4k lines) is untouched.
- Paper: §4–5 prose, the cell-column tables, the executed running example
  (`notes/2026-09-18-paper-running-example.lean`, witnesses g14/d92).
- Tests: 19 golden-instruction compiler tests pin cell offsets/lengths; 52
  `sb_*` unit calls use literal cell addresses.

C0 alone flips no Miri test file (see the plan's §2). C1 (partial access,
provenance fragments, bounded words) is a different project.

[HYP] The store-width item (bucket 2) is worth doing on its own even in the
cell model: `writeThroughPtr` deriving its SB range from `vals.length` is
what made the probe's two machines disagree; a type-directed width is the
Miri-faithful form and would make a later C0 cheaper.
