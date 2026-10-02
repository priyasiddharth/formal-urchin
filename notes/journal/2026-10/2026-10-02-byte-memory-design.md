# 2026-10-02 — Byte-addressed memory: design and stages

Branch `byteaddress` (from main 6c6dbca). Goal: replace the cell model
(one cell per scalar or pointer, unbounded `Nat` words) with byte-addressed
memory in the style of rustc's interpreter / Miri, as specified by MiniRust
(Ralf Jung's executable spec of Rust's operational semantics:
`AbstractByte = Uninit | Init(u8, Option<Provenance>)`, little-endian
encoding, provenance on every byte of a stored pointer).

Context: the cost was MEASURED on 2026-10-01
(journal/2026-10/2026-10-01-byte-probe.md, on `conformance-drop-in-place`):
splitting byte size from slot count breaks 20 theorems ≈ 3.5k proof lines
plus 68 mechanical sites; the SB layer (keystone, permsim_transport,
protectors) is untouched; layout-directed memory access is extra. Byte
memory is what the representation tests need (parked 12:
`ptr_int_transmute`, `provenance`, `transmute_ptr`, …), together with
other features (A/B/E/F/G in the 2026-10-01 plan).

## Decisions

- [FACT] **Reference model: MiniRust**, the formal reading of what rustc's
  interpreter does. Miri's extra machinery (per-byte `PointerFrag`
  indices, `DedupRangeMap`, lazy base addresses) is representation, not
  semantics, and is not copied.
- [FACT] **Provenance on every byte; a pointer read keeps it only when all
  bytes agree.** So a raw bytewise copy preserves a pointer and a copy
  through integers strips it (Miri tests `provenance::bytewise_*`,
  `ptr_int_transmute::transmute_strip_provenance`).
- [FACT] **Integer reads strip provenance** (MiniRust; Miri's default).
  Reading part of a pointer as `u8` is defined (`ptr_partial_read`).
- [FACT] **Bounded integers.** An `n`-byte integer is a bit pattern below
  `256 ^ n`; signedness is an interpretation. This retires "unbounded `Nat`
  words" (obseq3/types.lean `BinOp` doc) — arithmetic must wrap at the
  migration stage.
- [FACT] **Addresses**: bump allocation, aligned, never 0 (null is never a
  valid address). Concrete from the start (no lazy addresses: the
  compiler proof's identity address renaming depends on it).
- [FACT] **Pointer `extent` leaves the value.** The cell model's `ptrVal`
  carries how many cells it claims; byte memory stores only address +
  provenance. A thin pointer's extent is its pointee type's size; a slice's
  length becomes fat-pointer metadata (a second word). Layout stage.
- [FACT] **Per-byte borrow stacks need no change to `sb.lean`**: every SB
  operation already acts on `[addr, addr + len)` and never asks what a
  unit is. Lengths simply become byte counts.
- [FACT] **Build the new layer standalone first.** The audited theorem
  stays green on the branch while the foundation is built and proved;
  mirlite/oseair move onto it in later stages, one machine at a time.

## Stages

0. **Foundation — DONE 2026-10-02** (`src/obseq3/bytemem.lean`, ~330
   lines): `AbstractByte`, `Prov`, `Pointer`; LE encode/decode; scalar
   `encodeS`/`decodeS` for `int n` and `ptr`; total byte-map `Mem` with
   `read`/`write`/`copyBytes`, aligned `allocate`, `allocOf`; typed
   `load`/`store`. Proved: `decodeLE_encodeLE`, pointer/int round trips
   and the cross reads (pointer bytes read as an int = address; int bytes
   read as a pointer = no provenance), `read_write_same`,
   `read_write_disjoint`, `load_store_same`, `load_store_disjoint`,
   `allocate_wf`/`allocate_fresh`. Axioms: propext, Classical.choice,
   Quot.sound. Unit tests t20–t24 (round trip, partial read, bytewise copy
   keeps provenance, int copy strips it, mixed bytes / uninit).
1. **Layouts — DONE 2026-10-02** (`src/obseq3/bytelayout.lean`, ~330
   lines). `BLayout = int n | ptr pointee | tup fields offsets size align`
   (explicit offsets so Charon's `field_offsets` can be used verbatim);
   `reprC` computes the C layout (aligned fields, trailing padding);
   `leaves` gives the `(offset, scalar)` view; `Mem.loadL`/`storeL` move a
   whole value leaf by leaf. `ofLayoutTy` embeds the cell layouts (word =
   `usize`). Proved: `placeFields_good`/`reprC_good` (leaves pairwise
   separated, in address order, inside the size), `ofLayoutTy_good`,
   `ofLayoutTy_leaves_length` (**one leaf per cell**: the byte model
   produces exactly as many values as the cell model, so stage 2 changes
   addresses, not value counts), `storeLeaves_frame`,
   `loadLeaves_storeLeaves`, `loadL_storeL`. Unit tests t25–t27.
   Original plan text: obseq3 needs its own layout type:
   `obseq.LayoutTy` is shared with v1 (`src/obseq`) and obseq2, so do not
   widen it in place. `ByteLayout = int n | ptr pointee | tup [(offset,
   layout)] size align`; size/align/field offsets computed like rustc for
   tuples, or taken from Charon's `layout` field (present in 62/111
   artifacts) for user ADTs. A "leaf list" view (offset × scalar) gives
   the flat value shape the semantics already works with.
2. **mirlite on bytes — DONE 2026-10-02, as a PARALLEL semantics**
   (`src/obseq3/mirlite_bytes.lean`, namespace `obseq3.mirliteB`). Not an
   in-place edit: the compiler proof relates the cell mirlite to the cell
   oseair, so switching mirlite alone would break it until stages 3–4.
   Same syntax, permission model and evaluation order; values stay
   `List MemValue` (one per cell); each cell is an 8-byte leaf of
   `ofLayoutTy` (so addresses, offsets, sizes, SB ranges are `8 ×` cells;
   freeze masks expanded per byte); writes encode, reads decode at the
   leaf's scalar type — an integer read of pointer bytes yields the
   address without provenance (t29: the cell model returns the pointer
   cell), a pointer read without provenance gives a degenerate zero-size
   pointer. `extent` rides in the stored provenance
   (`bytes.Prov.extent`, TEMPORARY until fat pointers are two words).
   Harness `--bytes` runs both semantics and requires the same verdict at
   the same statement: **132/132 matched (52 ok, 80 UB)**. Unit tests
   t28–t29. Words above 2^64 error at the store (binOp does not wrap yet;
   no corpus program reaches it).
   Original plan text — concretely, from stage 1: a value of layout `τ`
   is the list of its `ofLayoutTy τ` leaves (same length as today's
   `List MemValue`, `ofLayoutTy_leaves_length`); `MemValue.word w` ↦
   `SVal.int w` (needs `w < 2^64`: the bounded-word decision bites here —
   `binOp` must wrap), `ptrVal b o e s t` ↦ `SVal.ptr ⟨b + o, some ⟨b, s, t⟩⟩`
   with `e` recovered from the pointee type; `undef` ↦ a failed leaf load.
   The one new lemma the place layer needs: the byte offset of a path is
   the offset of its first leaf (`PathTo.offset` in cells ↦ the leaf
   index; the byte offset is that leaf's `.1`). `Mem := bytes.Mem`; values become `List SVal`
   per leaf (or raw byte lists for copies); `evalCopy` = read the bytes,
   check initialization per leaf at the leaf's scalar type; a typed copy
   of a non-pointer leaf strips provenance, a raw copy keeps it; place
   resolution offsets in bytes; `ptrOffset` scales by the pointee size in
   bytes; SB ranges in bytes. Executable tests and the conformance corpus
   must still agree with Miri at every step (`--unit`, corpus, `--osea`
   cannot run until stage 3, so only the mirlite side is checked here).
3. **oseair on bytes — DONE 2026-10-02, as a PARALLEL target**
   (`src/obseq3/oseair_bytes.lean`, `obseq3.oseairB`). It runs the SAME
   compiled programs (`compileProg` unchanged) and, like the byte source,
   reads the compiler's cell-unit immediates as 8 bytes per cell (`Borrow`
   offsets/lengths, `Die` lengths, `PtrOffset` deltas, allocation sizes,
   masks); registers keep `List Val`; memory encodes/decodes through
   `mirliteB.encodeV`/`decodeV`; `Memcpy` is a raw byte copy (provenance
   travels). Checked on FOUR machines: every `expectDiff` compiler test
   (114) now requires cell source, cell target, byte source and byte
   target to reach the expected verdict; the harness's `--bytes` compares
   byte source with cell source AND byte target with byte source —
   133/133 on the corpus. Because the compiler still emits cell units,
   the store-width question (probe bucket 2) does not arise yet: it
   arrives with real widths (stage 5), when the compiler itself must emit
   byte offsets from `BLayout`. Original plan text: Same memory; `Load`/`Store` carry a
   scalar type; the store's SB width comes from the TYPE, not from the
   number of values (probe bucket 2: `writeThroughPtr` used
   `vals.length`); `Borrow`/`Die` lengths and offsets in bytes; the 19
   golden-instruction compiler tests re-pinned.
4. **Proof repair.** The probe's 20 theorems (spine ×6, ptrarith ×5, copy
   ×2, ref ×2, casts ×2, common/const_write/alloc ×1) plus the
   `readWordSeq` family (`MemValSim`, `SourceMemSim`, `readWordSeq_sim`)
   restated over byte ranges and leaf lists. The audit must be back to 0
   sorries before the branch merges.
5. **Loader.** Keep integer widths from Charon `Literal` types, read the
   `layout` field (sizes, `field_offsets`, align), fat pointers as (ptr,
   len); `size_of`/`Layout` shims return bytes (today
   `from_size_align_unchecked(4, 4)` is read as 4 CELLS).
6. **Tests that become reachable** (with the small rvalues A: `addr`, B:
   `with_addr`): `ptr_int_transmute`, `provenance::{basic,
   int_load_strip_provenance, bytewise_ptr_methods, bytewise_custom_memcpy,
   maybe_uninit_preserves_partial_provenance}`, `transmute_ptr::{t2,
   ptr_integer_array}`. `ptr_int_from_exposed` additionally needs E
   (angelic wildcard resolution).

## Open questions

- [HYP] Stage 2 value shape: per-leaf `SVal` lists keep the semantics
  close to today's `List MemValue` (smaller proof diff); raw byte lists
  are closer to MiniRust and make transmute a plain reinterpretation.
  Leaning per-leaf for typed copies plus a raw-bytes rvalue for
  `transmute`/`copy_nonoverlapping`.
- [HYP] Whether to keep the cell model alive behind a common interface
  during the migration (both machines parametric in the memory) or switch
  in one step per machine. The probe suggests one step: the breakage is
  concentrated, not spread.

## Integer arithmetic: MIR's wrapping and UB (2026-10-02, later)

[FACT] rustc's interpreter (`interpret/operator.rs`, `binary_int_op`;
`mir/syntax.rs` `BinOp`): `Add`/`Sub`/`Mul` WRAP at the type's width;
`*WithOverflow` return `(wrapped, overflowed)` — a debug build's panic is
a separate `Assert` on the flag; `*Unchecked` are UB on overflow; `Div`/
`Rem` are UB on a zero divisor and on signed `MIN / -1` (rustc inserts an
`Assert` before them); `Shl`/`Shr` mask the amount to the width,
`*Unchecked` shifts are UB out of range. Charon keeps these one to one
(`Add(Wrap|UB|Panic)`, `AddChecked`, `Div(UB)`, …).

Done: `obseq3.IntTy` (bits, signedness; words are bit patterns);
`BinOp` carries the type and covers all of the above plus bit ops and
comparisons by signedness; `evalBinOp` stays TOTAL (the proof treats it
as opaque) and `binOpUB` decides UB, consulted first by both mirlites and
oseair. Proof change: one `split` in `binop.lean`, one hypothesis on
`runN_Assgn_BinOp_step`. Loader: the operand's Charon integer type is
kept on `URvalue.binOp`; ops with modes render `Add.Wrap`…; a checked op
emits the wrapped value AND its real overflow flag (was: a hard-coded 0
relying on the certificate); folds use `evalBinOp` and do not fold an op
that would be UB, so the run raises it at its statement; negative
constant OPERANDS are two's complement at the op's type. The old
"`sub` truncates at 0" is gone (t18, d100 updated).

Negative numbers (later the same day): a negative constant is stored as
its two's-complement pattern at its OWN width (Charon's scalar carries it:
`{"Signed": ["I32", "-1"]}`); `Neg` is `0 - x` (wrapping, MIR `Neg`);
`Not` is `x ^ all-ones` (one bit for `bool`); integer casts (`Cast(Scalar)`,
rejected before) narrow by masking, sign-extend a signed source with
`(x ^ s) - s`, otherwise keep the pattern, and a cast of a constant is
computed while loading. All are existing typed ops — no model or proof
change. Witness local/negative_ints_ok: 12 value checks certified against
Miri, 11 at runtime.

Open: `Cmp` and `Offset` are still unsupported; a 128-bit value does not fit a
byte-model leaf (8 bytes) until leaves get widths (stage 5).

## Stage 5, byte machines first (2026-10-02, later)

Decision (user): widths go into the BYTE machines first; the typed syntax,
compiler, cell machines and proof stay on cell layouts, so the audit stays
green. The core-syntax switch is a separate later step.

Done:
- Loader: `UTy.int (t : UIntTy)` for Rust integers, `bool` (8 bits) and
  `char` (32); `.nat` stays the model word. `conformance.toBLayout`: each
  type's byte layout — integers at their width, 8-byte pointers (pointee
  kept), structs/tuples in C layout (DEVIATION: rustc may reorder
  `repr(Rust)`; Charon's `field_offsets` not read yet), enums as the
  model's own 8-byte discriminant + longest variant (cell shape, so leaves
  line up with values). `Loaded.blay`: one per local.
- Opaque std cells: `UnsafeCell<T>`/`Cell`/`RefCell`/`Atomic*` with no
  constructor call take `T` from the declaration's `Instantiated` type
  arguments (`DeclInfo.tyArgs`) — the old one-word fallback was harmless
  with cells but made `&UnsafeCell<i32>` an 8-byte (out-of-bounds) retag.
- `size_of`/`Layout::new`/`Layout::for_value` return BYTES; the cell
  machine allocates one cell per byte from them (more than it needs).
- `mirlite_bytes.lean` rewritten over a layout environment (`LayEnv`):
  a place's layout is static (local, field path, pointee); sizes, field
  offsets, strides, SB ranges and leaf widths come from it; writes encode
  each leaf at its width and make padding uninit; freeze masks per byte
  (padding takes the preceding leaf's bit). `uniformEnv` is stage 2's.
- The lowering's constant tracker no longer follows a pointer through a
  type-punning cast (`punsPointee`): a `u8` write through a cast `u32`
  pointer is not a write of the whole `u32`.
- Harness `--bytes`: the byte source on the REAL layouts vs the cell
  source; the byte target (still cell immediates) vs the byte source on
  the UNIFORM layout; for an `xfail-model` entry the byte source must match
  MIRI's verdict instead. live.py checks `xfail-model` entries against
  Miri like supported ones.
- Witnesses (`xfail-model` for cells, matched for bytes):
  local/narrow_ref_wide_write (`&mut s.a` as `*mut u16`: UB at line 21 —
  cells miss it) and local/narrow_fields_ok (repr(C) {u8,u32,u16}:
  `size_of` 12, a byte written into and read out of a u32, 6 checks
  certified, 5 at runtime — cells reject the certificate).

Result: corpus 133 pass + 2 xfail, osea 135, bytes 135, live 135/135.

Struct offsets from Charon (same day, later): `StructLay` (offsets in
declaration order, size, align) read from a struct decl's `layout`; the
loader's `UTy.structT` carries it and `toBLayout` uses it, so a
`repr(Rust)` struct sits at rustc's own offsets (`S { a: u8, b: u32,
c: u8 }` → b@0, a@4, c@5, size 8). Enums deliberately keep the MODEL's
shape (user decision): 8-byte tag, longest variant, no niches. Tuples are
Charon builtins without a layout, so they stay C layout. Leaves of a
reordered struct are in field order, not address order: `maskBytes`
picks the leaf starting closest at or below each byte. No committed
artifact had a reordered struct; witness local/rust_layout_ok (byte reads
at rustc's offsets, certified; xfail-model for cells).

Fixed on the way (both machines): `&arr[..]` on an ARRAY read the
RangeFull length from the array reference — its extent in ARRAYS, 1 —
instead of from the reinterpreted slice; the length is now read from the
destination, in elements.

Open: rustc's tuple reordering; the compiler emitting byte
offsets (core syntax switch) — then the byte target runs real layouts too.

## The byte model is the judged model (2026-10-02, later)

User decision: on this branch tests are judged by how they run on the
byte model. The harness's verdict is the byte source on the loader's real
layouts; `--cells` (was `--bytes`) runs the cell model against it
(statement-level agreement, except entries recorded
`"cell_model": "diverges"`) plus the byte target vs the uniform byte
source; `--osea` stays the cell pair. The three byte-level witnesses are
now plain `supported` entries with `cell_model: diverges`.

[OBS] Regression check against main (6c6dbca), all 161 pre-existing
entries: same outcome 161/161, same verdict (`ok` / UB line) 161/161; the
diagnostic text differs on 79 UB entries only because offsets are now in
bytes. Corpus 136 pass / 0 fail / 0 xfail / 29 unsupported; osea 136;
cells 133 matched + 3 diverging; live 136/136.

## UB reasons checked against Miri (2026-10-02, later)

[OBS] Until now a UB verdict matched Miri on verdict, line and (with a
certificate) path — not on the reason; `miri_error` in the manifest is a
hand-written regex (often covering both SB and TB revisions), never
matched. Now: live.py records Miri's actual error line + "occurs as part
of" label per UB entry (`charon/<artifact>.miri.txt`, 81 files,
deterministic, drift-checked); the harness classifies both sides into
(op, cause, byte offset in the allocation) and compares. First run: 72/81
agree. The 9: 4 classifier (Miri's protector message names no
operation — its span is the fn-entry retag), 2 a REAL mechanism
difference fixed in the byte model (use-after-free: Miri checks liveness
before SB; `bytes.Mem.freed` + `freedMsg` checks before every access,
retag and deref), 3 recorded as `reason_known` (RefCell flag elided →
offset 0 vs 8, ×2; immutable statics read-only in Miri vs a frozen SB
item here). Result: 78 as Miri, 3 known, 0 differ; an unrecorded
difference now fails the suite. Byte addressing is what makes the
offset comparable at all (Miri reports byte offsets).

## The byte-level proof: why A, and the spike (2026-10-02, later)

[FACT] A refinement of the byte machines into the proved cell machines
("option B") cannot cover sub-cell borrows: it needs every byte state to
have a cell image (8 bytes of a cell sharing one stack, one value per
cell), and a one-byte borrow, a byte written into a `u32`, or a reordered
struct has none — exactly the programs the byte model exists for. So the
byte proof is a direct compiler proof on the byte machines ("option A"),
built in PARALLEL (`obseq3/byteproof/`, library `Obseq3ByteProof`) so the
audited cell theorem stays green until the switch.

Spike — `src/obseq3/byteproof/memsim.lean`, sorry-free, axioms propext /
Quot.sound / Classical.choice only (`scripts/byteproof_axioms.lean`
fails on anything else, user instruction: stop and ask on a new axiom):
- the relation: `ByteSim` (same byte, provenance with its tag renamed;
  an uninit source byte refines anything), `ByteMemSim` (per address, NO
  address renaming: lockstep allocation), `ByteAllocLockstep`;
- memory: `ByteMemSim.read` / `.write` / `.copyBytes` / `.allocate` —
  any address, any length;
- values: `decodeV_sim` (related bytes decode to related values at ANY
  scalar type — the pointer case needs the tag renaming to be a function
  AND injective, which `TagRenameWF` already provides: renaming must not
  merge two provenances into one), `encodeAt_sim`;
- layouts: `readL_sim`, `writeL_sim` — any `BLayout`, padding included;
- steps: `store_step_sim` (sb_write + writeL), `load_step_sim` (sb_read
  + readL), `subcell_store_sim` (a one-byte store inside a wider value);
  the SB halves are the cell proof's `sb_*_respects_PermSim`, UNCHANGED.

[OBS] What the spike taught:
1. The per-byte relation makes sub-cell accesses free: no lemma mentions
   cells; a narrow store is `writeL_sim` at `.int 1`.
2. The SB layer needs nothing (per-byte stacks are stacks).
3. One asymmetry: the cell proof lets a source `undef` relate to ANY
   target value, but a byte STORE must encode the target value, which can
   fail (a word that does not fit). Stores therefore need `StoreSim`
   (undef ↔ undef, else related) — true of the compiler, whose `uninit`
   stores `Undef` on both sides; reads keep the weak relation.
4. Pointer decoding is where injectivity matters (mixed provenance must
   stay mixed under renaming).

Next for A, in order: (1) typed syntax with byte layouts and a compiler
that emits byte offsets/lengths and TYPE-directed store widths; (2) one
leaf end to end (const_write) restated over `ByteMemSim`; (3) the rest
of the port (measured: ~11 mechanical, ~8 store-width, ~20–40 memory-
relation theorems; SB layer unchanged).

## A step 1 — the byte compiler and its target (2026-10-02, late)

[DEC] A post-pass over the cell compiler's output cannot produce byte
code: a cell offset does not say which byte layout it came from. So
`src/obseq3/compile_bytes.lean` (`obseq3.compileB`) is a copy of
`compile.lean` parameterized by `L : mirliteB.LayEnv Γ` — same lowering,
same instruction order, same evidence inductives (now indexed by `L`),
same `StateIncr` monad — and `src/obseq3/oseair_layout.lean`
(`obseq3.oseairL`) is its target: OSEA-IR's instructions with
`BLayout` on `Load`/`Alloc`/`AllocN`/`AllocDyn`/`RStore`/`CStore`, byte
offsets and lengths on `Borrow`/`Die`/`PtrOffset`, element byte sizes on
`SliceLen`/`SubSlice`, memory `bytes.Mem`, registers holding one value
per leaf. No `Memcpy` (the cell compiler no longer emits it).

What the byte compiler emits differently (each mirrors the byte source):
- projection borrow offset `fieldOffset (placeLayout L base) path.indices`,
  every borrow/`Die` length `(placeLayout L p).size` (`placeSize`);
- loads at the SOURCE place's layout, stores at the DESTINATION's
  (`compileRExprPreChecked` takes `dstL`, as `evalRExpr` does), so a
  layout-mismatched copy fails at `writeL`'s leaf check on both sides;
- `ref`'s mask expanded by `maskBytes`; `move`'s stays `[]` — kept
  syntactically equal to the source's so the SB halves need no
  "[] ≡ all-false" lemma;
- the one-leaf reads (`exposeAddr`/`fromExposed`/`ptrOffset`/`ptrCast`/
  `refSlice`) carry the source's `leafKind`; `ptrOffset` is pre-scaled by
  the pointee's byte size; `uninit` stores one `Undef` per dst leaf;
- a deref loads one pointer leaf (`derefLoad`), as `resolvePlaceAcc`.
The target checks liveness (`freed`) before bounds and SB, as the byte
source does; the cell targets do not.

[OBS] Differential: `compile_tests` runs every program on a FIFTH machine
(byte compiler at the uniform layout, on `oseairL`) — 131/131; the
corpus `--osea` adds `osea bytes` (byte compiler at the REAL layouts vs
the judged byte verdict) — 146 matched / 0 mismatch / 0 skipped. Teeth:
mutating the projection offset to `8 * cell offset` gave ≥10 mismatches.
byteproof axioms unchanged; main audit unchanged (3 axioms, 0 sorries).

Next: step 2, the const_write leaf over `ByteMemSim` against these two
definitions.

## A step 2 — the first leaf: const_write, bound local (2026-10-02, late)

`src/obseq3/byteproof/const_write.lean`, sorry-free, axioms unchanged
(86 byteproof declarations; propext / Quot.sound / Classical.choice).

- `InvAtB L ρt s_mir s_osea cs`: the cell `InvAt` with `ByteMemSim` +
  `ByteAllocLockstep` for `SourceMemSim` + `AllocLockstep`; NO `ρa`, no
  `IdentityOnDomain`, no domain conjunct in the binding relation
  (`LocalBindingSimB`: the local's register holds `Ptr addr 0 _ (L x).size
  tag'`, same address). Permission and compiler-state halves unchanged.
- `compileStmt_constInit_local`: a bound local's `x := const v` compiles to
  exactly `emit cs [CStore (L x) [Dat v] reg]`.
- `constWrite_local_sim`: source step ok ⇒ target `runN 1` ok and
  `InvAtB` at the statement's compiled state. The body is the spike's
  `store_step_sim` plus bookkeeping (pc, liveness via lockstep `freed`,
  bounds, `sb_write_NextTag`); ~70 lines.

[OBS] What dropping ρa bought: the cell regime-A leaf goes through
`copy_bound_write_after_read`, a seam that also re-establishes ρa's
domain over the stored range; here nothing about addresses is carried,
and the leaf is one memory lemma and one permission lemma.

[OBS] Not yet general: the cell leaves are one per DESTINATION shape over a
value package (`ValuePkg`); this one is constInit-specific. Porting the
package abstraction is the next structural step (then fresh root,
projection, deref chains), before the remaining rvalues.

### Value packages (same day)

[DEC] Split as in the cell proof: `byteproof/spine.lean` holds `InvAtB`,
`StoreStepB` (`cstore`/`rstore`), `ValuePkgB` and the destination leaf
`storereg_local_simB` (any rvalue with a package, bound-local dst);
`byteproof/const_write.lean` holds the packages `constInit_pkg`,
`uninit_pkg` (via `pureCStore_pkg`) and the two one-line leaves. The
constInit-specific leaf is gone.

[DEC] `ValuePkgB` relates the stored values by `StoreSim`, not the read
relation (spike finding 3). `uninit` meets it with undef ↔ undef; every
reading rvalue errs on undef on both sides, so its values are defined.

[OBS] The leaf takes `CodeIncludedB` of the statement's run directly; the
cell leaf's conditional frame (`hF`, compile success ⇒ frame) is only
needed when the per-statement leaves are assembled into the program
theorem, and will come back then. 98 byteproof declarations, axioms
unchanged.

### Copy package, bound-local source (same day)

`byteproof/copy.lean`: `copy_local_pkg` (any destination layout `dstL`)
and the leaf `copy_local_local_sim`. The source's typed read is the
spike's `load_step_sim`; `readL_rel` turns the read relation into the
store relation, using that the source read erred on any undef leaf — so
every loaded target leaf is defined too (the target `Load`'s own undef
check passes) and `StoreSim` holds. The fresh temp register is above
every bound local's (`PlaceRegMapBoundB`), so the binding relation
survives the `Load`. 109 byteproof declarations, axioms unchanged.

Next: the byte place-lowering simulation (projection borrows at byte
offsets, deref loads) — the cell proof's `ptrChain_lowering_sim` — which
unlocks projected/deref sources and destinations for every package.
