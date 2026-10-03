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

### Place lowering (same day)

`byteproof/places.lean` (672 lines): `ptrChain_lowering_simB`, the byte
`ptrChain_lowering_sim`, for every `PtrChain` place (local; deref of a
chain; deref of a field of a chain), result packaged as `LoweredB`.
Pieces: `deref_lowering`/`proj_lowering`/`proj_eq` (compiled shapes),
`deref_level` (one Load level, shared by the deref and offset-zero
field cases), `load_level`, `runN_Load_ptr`/`runN_Borrow`/`runN_Die`,
`decode_ptr_sim`. The nonzero-offset field case is `Borrow(Shared);
Load; Die` against the source's one read, closed by keystone's
`sb_ref_read_die_cancels` at len = ptrSize — the SB layer unchanged, as
predicted. 148 byteproof declarations, axioms unchanged.

[DEC] New hypothesis `PtrPlacesWF L`: a pointer-typed place has a
pointer-sized layout. The compiler borrows the pointer FIELD at its
layout size and the Load reads 8 bytes through that borrow; the
cancellation needs the two lengths equal. A layout table violating it
is not a layout of the program's types.

[OBS] Two byte-SOURCE bugs found by the port (both fixed, commits
"mirliteB: a deref must find the whole pointer in bounds" and "mirliteB:
a one-leaf read decodes exactly the leaf's bytes"): the deref checked only
the pointer's first byte; `readCell` decoded 8 bytes for every leaf. The
differential corpus could not see either (no test straddles an
allocation end or casts a narrow int to a pointer); the proof could.
Witness t31 pins the second.

[OBS] Proof-engineering gotchas this file hit: structure-instance fields
on a continuation line must be indented past the `{` (colGt), else
"unexpected identifier; expected '}'"; `omega` does not see through
`Tag`, so NextTag chains use `Nat.le_trans`; an implicit machine state
that only appears as `s.pc` in a hypothesis must be given explicitly
(`(s := S1)`).

Next: use `LoweredB` for deref destinations (the cell `storereg_chaindst_simulation`)
and deref/projected sources (copy package beyond locals).

### Pointer destinations and chain sources (same day)

- `byteproof/derefdst.lean`: `storereg_chaindst_simB` — `*P := rhs` for any
  `PtrChain (.deref P)` destination and any rvalue with a package. Shape
  lemmas `ensurePlaceRoot_noop` (from the source's pure `resolvePlace?`,
  which `preparePlaceAssign` already established — the post-rvalue
  resolution can't be used, its env equality only arrives with the
  package's second half), `assign_dst_incr`, `compileStmt_storereg_dst`.
- `byteproof/copy_chain.lean`: `ptrChain_compiles` (compile-only: a chain
  with a bound root lowers with no cleanup and an unchanged place map —
  needed BEFORE code inclusion, for the package's ungated half),
  `readRhsPre_shape`, `copy_chain_pkg` (any chain source), and the leaves
  `copy_chain_local_sim`, `copy_chain_chaindst_sim`.
158 byteproof declarations, axioms unchanged.

Witness `local/deref_straddles_end` (commit 26a0956): Miri's partial-OOB
wording ("only N bytes from the end of the allocation") now classifies as
out-of-bounds; against the old deref check the verdict matched but the
reason check failed the suite.

Coverage now: destinations {bound local, pointer chain}; rvalues
{constInit, uninit, copy from any chain}. Remaining, in the cell proof's
order: fresh-root and projected destinations; the ref/move/cast/ptrarith/
binop/alloc/slice packages; dealloc, assignIf, protectors; the program
theorem (prefix states, frames).

### First assignments, fields, references (same day)

- `freshroot.lean`: a local's first assignment = the root `Alloc`
  (`freshroot_prologue`, `sb_own_respects_PermSim` growing ρt) followed by
  the bound-local leaf, via two equations: the compiler from the
  post-Alloc state emits the same code minus the Alloc
  (`compileStmt_fresh_eq`), the source from the post-allocation state steps
  the same (`stepStmt_fresh_eq`). No new simulation reasoning.
- `derefdst.lean` refactor: `storereg_lowered_simB` takes any destination
  meeting `LowersB` (the place-lowering contract); chains are an instance.
- `projdst.lean`: fields. Offset zero lowers as the base
  (`proj_zero_lowers`); nonzero offset is `Borrow(Mut); store; Die` closed by
  keystone's `sb_ref_use_die_cancels` at the field's BYTE length. Instances:
  `x.f` (x bound / first assignment), `(*P).f`.
- `ref.lean`: one core package `ref_pkg_core` from an anchor contract
  (`BorrowAnchorShape`, `BorrowAnchorRes`, `LowersB`, `CompilesB`) — every
  borrow is "lower the anchor, one Borrow at an offset"; instances `&x`,
  `&*chain`, `&chain.f`. The retag is `sb_ref_respects_PermSim` unchanged.
201 byteproof declarations, axioms unchanged.

Coverage: destinations {bound local, first assignment, field of a chain,
deref chain}; rvalues {constInit, uninit, copy from a chain, ref of a
chain/field}. Not yet: nested projections (reassociation) and derefs of
non-chain places (flatten); move, casts, ptrOffset, binOp, alloc, slices;
dealloc, assignIf, protectors; the program theorem.

### Move, one-leaf rvalues, register reads, arithmetic (same day)

- `move.lean`: `move_pkg_core` on the anchor contract; the three SB
  events (Mut retag, read via the fresh tag, die) transport one by one
  under the grown renaming — no cancellation needed, the source does the
  same three. `BorrowAnchorShape` now pins the borrow's cleanup too.
- `leafops.lean`: `leaf_pkg_core` + per-op `LeafOpB` for ptrCast,
  exposeAddr, fromExposed, ptrOffset (`readCell_inv`,
  `readCellThrough_sim`).
- `readreg.lean`: `readToReg_simB` with `InvAtB` at both ends, so reads
  chain. Needed `UnboundLocalsUnmappedB` in `ValuePkgB`'s hypotheses
  (mechanical, all packages/leaves updated).
- `binop.lean`: `binOp_pkg`.
238 byteproof declarations, axioms unchanged.

Remaining: sliceLen/subSlice (readToReg + register op — same pattern as
binOp), alloc (const/dyn: `sb_own` like the fresh root), refSlice (Load +
`Borrow … none`, the post-mint); statements dealloc, assignIf (SkipIf +
reserved label), push/pop protectors, halt; nested projections and
non-chain derefs (reassociation / flatten equations); then the program
theorem (prefix compile states, `StmtFrame`, the run induction).

### 2026-10-03: the remaining rvalues, statements, field reads

- `slice.lean` (sliceLen, subSlice), `alloc.lean` (const / runtime
  length; `allocPtr_sim`; `mirliteB.allocPointee` now names the element
  layout both source and compiler use), `refslice.lean` (Load + extent
  retag), `stmts.lean` (push/pop protectors, dealloc).
- `readsrc.lean`: `ReadSrcB` = chain or field of a chain; zero-offset
  fields via the lowering contract, nonzero via `Borrow(Shared); Load;
  Die` + `sb_ref_read_die_cancels`. All register-read consumers take
  `ReadSrcB`; `copy_pkgR` is derived from the register read.
270 byteproof declarations, axioms unchanged.

Still open, in order: one-leaf rvalues and refSlice from FIELD sources
(needs a leaf-size = field-size WF for the bracket); nested projections
(reassociation on both sides: `fieldOffset` over `PathTo.append`);
assignIf (root prologue, guard read, SkipIf over a reserved label, the
not-taken branch needs the body's compile facts) and halt; then the
program theorem (prefix compile states, per-statement code inclusion,
the run induction) with a dispatch that maps every statement shape to
its leaf.

### 2026-10-03: the program theorem

- `byteproof/program.lean`: `stepStmt_pc` (every successful non-halt step
  advances the source pc — needed because the leaves state `InvAtB` at the
  statement's compiled run, which must be the next prefix state);
  `csAtB` (prefix compile states) and `stmt_in_prog` (in a compiling
  program, statement i's run is the next prefix state and is code-included);
  `InvAtB_initial` (reusing the cell proof's initial permission facts);
  `StmtSimB` (a statement's simulation, the shape every leaf has);
  `compileB_run_sim` (the run induction) and `compileB_correct`.
- `byteproof/fragment.lean`: `BorrowSrcB`, `RhsB`, `DstB`, `StmtB` — the
  proved fragment as predicates — with `RhsB.pkg` and `StmtB.sim`
  dispatching to the leaves (bound vs first-assignment chosen by the
  source environment at the step), and
  **`compileB_correct_fragment`**: for a layout table with pointer-sized
  pointer places, a compiling program all of whose non-halt statements
  are in the fragment — every successful source run is matched by a
  successful target run from the initial state, related by `InvAtB`.
  Axioms: propext, Classical.choice, Quot.sound (334 byteproof
  declarations); main audit unchanged.

[DEC] Coverage is a hypothesis of the theorem (`h_frag`), not baked into
it: extending coverage is adding `StmtB` constructors and their cases in
`StmtB.sim`; the program theorem itself does not change.

Not in the fragment yet: assignIf; nested projections; derefs of non-chain
places; one-leaf rvalues and refSlice with a field operand.

### 2026-10-03: nested fields and assignIf

- `assoc.lean`: the source agrees with the compiler's reassociation:
  `(b.q).p` and `b.(q ++ p)` have the same byte layout, offset, access and
  pure resolution (`fieldLayout_append`, `fieldOffset_append` over index
  lists); the compiler's reassociation arms have the flattened place's
  run and result. Fragment closed under nesting: `StmtB0.nested`
  (`StmtSimB.congr`), `ReadSrcB.nested` (read lemmas by induction),
  `BorrowSrcB.nested` (`ValuePkgB.congr`).
- `prmpres.lean`: compile-only — only a root's `Alloc` changes the place
  map (`PrmPres`, closure tactic `prm_tac`); every place lowering, borrow,
  read and rvalue pre-phase preserves it.
- `assignif.lean`: root prologue (`ensureRoot_sim`), `assignIf_shape`
  (SkipIf over a reserved label), `assignIf_simB`. Taken: the assignment's
  own `StmtSimB` from the reserved label's successor. Not taken: the jump
  lands on the body's end label; the invariant moves there because the
  body's compile state has the guard's place map (`compileAssign_prm` +
  `ensurePlaceRoot_idem`) — the source never evaluated the body, so no
  value package could have said it.
- [DEC] The program theorem now takes `StmtSimBc` (a statement's
  simulation may use its own compile success — the skipped body must
  compile, which only whole-program compile success says); `StmtSimB.toC`
  lifts every other leaf. `correct.lean`: `StmtB` = `StmtB0` + assignIf,
  and `compileB_correct_fragment` (426 byteproof declarations; axioms the
  three whitelisted only).

Remaining outside the fragment: derefs of non-chain places (e.g.
`*(x.f.g)` as a pointer, `*((*p).f.g)`) and the one-leaf rvalues /
refSlice with a field operand.

### 2026-10-03: field operands; every program is in the fragment

- `leaffield.lean`: one-leaf rvalues (`ptrCast`, `ptrOffset`,
  `fromExposed`) with a field operand (`LeafSrcB` = chain | field of a
  chain | nested). Offset zero: the field lowers as its base
  (`proj_zero_lowers`), the chain skeleton applies. Nonzero offset:
  `leaf_pkg_projoff`, the bracket `Borrow(Shared); op; Die` cancelled by
  keystone's `sb_ref_read_die_cancels`, with the op given as a
  `ReadOnlyOpB` (source = one checked read; target = the op's value from
  the target read's outcome). Nested: `ValuePkgB.congr` +
  `readRhsPre_assoc`, well-founded on `Place.depth` (`cases` on the
  `LeafSrcB` at a fixed `PtrL` index; `induction` refuses it).
- [DEC] New layout hypothesis `LeafWF L`: integer- and pointer-typed places
  have a one-leaf layout (`leafKind` size = layout size). A nonzero-offset
  field's borrow covers the field's layout size while the op reads the
  leaf's; the keystone cancellation needs them equal.
- `refslicefield.lean`: the nonzero-offset bracket followed by the retag
  `Borrow … none` on the loaded pointer (`sb_ref_respects_PermSim` from the
  post-`Die` state). `exposefield.lean`: the exposure sits INSIDE the
  bracket; the cell proof's `sb_die_expose_comm` (a `die` never reads the
  exposed set) moves it past the `Die`, then the bracket cancels as before.
  Both are copies of `leaf_pkg_projoff`'s bracket (~200 lines each);
  factoring the bracket out is cleanup-pass item one.
- `coverage.lean`: [DEC] the place predicates are TOTAL. Every
  non-projection place is a `ChainB` (`ChainB.deref_all`: a deref of a
  deref recurses, a deref of a field flattens nesting by `derefNested`),
  every projection is a (nested) field of one. So "derefs of non-chain
  places" were never outside the fragment — `*(x.f.g)` and `*((*p).f.g)`
  are `derefNested`/`derefProj` chains since 9658d26 — and with field
  operands done every rvalue has an `RhsB` case: `StmtB.all` holds for
  every non-`halt` statement. `compileB_correct_all`: the byte-level
  theorem with no fragment hypothesis, assuming only `PtrPlacesWF L` and
  `LeafWF L`. Both are proved for `uniformEnv` (`placeLayout_uniform`:
  every place's layout is `ofLayoutTy` of its type), giving
  `compileB_correct_uniform` with no hypotheses beyond compilation.
  512 byteproof declarations, axioms the three whitelisted only; main
  audit unchanged (3 axioms, 0 sorries).

[Q] Do the LOADER's layouts (`conformance.toBLayout`) satisfy the two
conditions? Not proved: `toBLayout` is `partial` and maps `UTy`, not
`LayoutTy`, so a `NatL` place whose real layout is not an `.int` leaf
(an enum, a `Cell` wrapper flattened differently) would break `LeafWF`.
Cheap way to know: a decidable per-program check that each local's
`BLayout` has its `LayoutTy`'s shape (int ↔ NatL, ptr ↔ PtrL, tup ↔ TupL
fieldwise), which implies both conditions for every place; run it over
the corpus in the harness.

### 2026-10-03: the loader's layouts meet the two conditions

Answers the [Q] above. `bytes.Agrees τ l` (`obseq3/layout_agree.lean`,
decidable): `l` has `τ`'s shape — any-width int for `NatL`, a pointer to an
agreeing pointee for `PtrL`, fieldwise for `TupL` (offsets, size, align
free). `byteproof/layoutagree.lean`: if every LOCAL agrees, every PLACE
does (`placeLayout_agrees`; a field of an agreeing tuple, the pointee of an
agreeing pointer), hence `PtrPlacesWF` and `LeafWF`;
`compileB_correct_agrees` is the theorem under that decidable hypothesis.

`sb_conformance --layouts` checks the loader's layouts per program. First
run: 129 agree, 18 disagree, 26 do not load. All 29 disagreeing locals
were the same: `enum [[], [opaque core::fmt::Arguments]]` (a panic
message), a PLACEHOLDER local — `toLayout` fails, elaboration gives it
`NatL` and rejects any use — whose `toBLayout` was a 16-byte pair. [DEC]
Fixed in the loader, not the condition: a placeholder local gets the
placeholder's layout (`ofLayoutTy NatL`). It is never used, so no verdict
moves (corpus 147/0/26, osea 147, osea bytes 147, units 31 + 131,
unchanged). Now 147/147 loaded programs agree: the byte-level theorem
applies to every program the corpus compiles with its real layouts.
`--layouts` exits 1 on any disagreement; worth adding to the validation
list. 522 byteproof declarations, axioms unchanged.

### 2026-10-03: integer types carry their width (`IntL t`)

[DEC] obseq3 has its own `LayoutTy` (`types.lean`): `IntL (t : IntTy) |
PtrL | TupL` replaces v1's width-free `NatL` (v1 and obseq2 keep
`obseq.LayoutTy`). This is the static half of MiniRust's `Type::Int`;
offsets and padding stay in the per-local byte layout. Choices:
- cell model: `IntL _` is one cell (`layoutSize`, `layoutToTyVal ↦ NatTy`),
  so the cell semantics, compiled code and golden tests are unchanged;
- typing: integer-PRODUCING rvalues (`constInit`, `binOp`, `exposeAddr`,
  `sliceLen`) and integer OPERAND places (binOp operands, subSlice bounds,
  `fromExposed`, `alloc` length, `assignIf` discriminant) take any width
  (implicit `IntTy` indices); `copy`/`move`/`assign` are width-strict
  because they share one index. Tightening ops to their `BinOp`'s width is
  possible later, not needed by either proof;
- `ofLayoutTy` (the uniform layout) keeps 8-byte integers; `Agrees` now
  checks widths (`.int n` agrees with `IntL t` iff `n = t.bytes`), so
  `--layouts` checks the loader's widths against the types.
Loader: `toLayout` keeps `UIntTy` widths; integer rvalues are elaborated at
the destination's type (`elabRvalue … expected`). Corpus drift on the first
run (141/6): (a) enum tags were `usize` but MIR's `discriminant()` is
`isize` → the tag field is `IntL i64`; (b) a bit-pattern-preserving
`IntToInt` cast (widening unsigned, signedness change) was a plain copy,
now ill-typed → `x | 0` at the destination type; (c) `Ref`/`RefMut` guards
with an uninferred pointee fell back to `*usize`, which had unified with
`*i32` only because both were `NatL` → the pointee now comes from the type
arguments, as for cells. After: corpus 147/0/26, osea/osea bytes 147,
cells 144 + 3 recorded, `--layouts` 147/147 with widths, units 31 + 131.
Proof repair was signature-only: ~10 binders (`{t : IntTy}` /
`(t := t)`) in each proof; no proof body changed beyond naming a width.
Main audit unchanged (3 axioms, 0 sorries); byteproof 522 declarations,
axioms unchanged. Repair cost was far below the 2026-10-01 C0 estimate
because the cell SIZE did not change — only the type's name for it.

### 2026-10-03: the cell model is retired; the paper is about bytes

[DEC] (user) No cell model. Deleted: cell semantics, cell target, the
stage-2 byte target, cell compiler, cell proof (19.6k lines). Method: a
closure computation over the byte theorems, `conformance.realMain` and the
two unit suites listed every declaration still reached; the only cell
dependency of the byte proof was `InvAtB_initial` reusing
`CompilerInv_initial` (re-proved locally). Survivors moved to
`values.lean` (values, bindings, registers), `proof/basis.lean` (tag
renaming, PermSim, MemValSim, ListRel, PtrChain, initialTagRename) and
`proof/permsim_dealloc.lean`; `keystone.lean`/`permsim_transport.lean`
unchanged. Then the byte model took the plain names (`mirlite`, `oseair`,
`compile`, `proof/`, `compile_correct_*`). Tests ported: semantics tests
on bytes (30; t28 was the cell-vs-byte duplicate), compiler tests on
`compile` at the uniform layout (130; goldens re-pinned — same instruction
sequences, sizes ×8, masks per byte; d33, a forged cell state, dropped).
Harness: `--osea` is the one compiler; `--cells`, `"cell_model"` gone.

Paper (`pldi27/`): every section restated from HEAD — per-byte SB; MIRLite
with `Int θ` types, byte layouts, abstract bytes, leaf-wise rd/wr, move =
Mut retag/read/die, copy of an uninit leaf is UB; OSEA-IR with
layout-typed load/store/alloc and value-list registers; compiler offsets
and lengths in bytes, masks per byte, reassociation inline; correctness
with no address renaming, byte simulation, 9-clause invariant, layout
conditions as a definition, one-step `stmt_sim` (added to coverage.lean),
`compile_correct_all`, corollaries agrees/uniform; running example
regenerated from the trace (x at [8,32), y at [32,40), same tags as
before); appendix: full surface, `alloc` as an rvalue, no memcpy, error
classes with liveness/uninit, "outside the theorem" = layout hypothesis,
fat-pointer extent in provenance, determinized wildcard. Also fixed a
pre-existing numbering bug: references to Theorem/Definition took the
section number of the REFERENCE ("Theorem 3.7" for §2.5's theorem).
Built with typst 0.15.1 (musl release; typst is not installed system-wide).

### 2026-10-03: one bracket; `addr` (provenance-stripping read)

Dedup: `projoff_bracket` is the nonzero-offset `Borrow(Shared); op; Die`
argument once, parameterized by the op's target effect = the read then a
permission transform `g` commuting with `Die` (id; `sb_expose · t'`) and a
caller predicate `P vals g`; `projoff_compile` is the compile half.
`leaf_pkg_projoff`, `exposeAddr_projoff`, `refSlice_projoff` (bracket, then
its retag) use it. `leaf_pkgL` is the one chain/field/nested wrapper,
`ro_pkgL` its read-only instance. 1118 → 962 lines.

[DEC] `addr p` (Rust `ptr.addr()`, `transmute::<*T, usize>`): the source
decodes the place's leaf bytes at `int(|κ|)` (`readCellAs`), NOT "decode a
pointer then take base+offset" — those differ on mixed-provenance bytes,
and the byte decode is MiniRust's. Compiled to `Load (int |κ|)` (no new
target instruction); proof = `addr_leafop` + `addr_ro` + `ro_pkgL` (~170
lines). Loader: `URvalue.addr`; `Transmute` casts (ptr→int ↦ addr,
ptr→ptr ↦ copy); shims for `*const/*mut T::addr` and the `transmute`
intrinsic to an integer. Witnesses (Miri agrees 2/2): local/addr_ok (ok),
local/addr_strips_provenance (UB at the write; reason recorded as known —
Miri: dangling, no provenance, since it resolves addresses only to EXPOSED
allocations; ours: no exposed tag at the borrow stack, the determinized
wildcard). Corpus 149/0/26 of 175, --osea 149, --layouts 149, units
31 + 133; 779 proof declarations, axioms unchanged.

### 2026-10-03: three `pass/` scenarios (parked n, o)

box_into_raw_allows_interior_mutable_alias: split out, passes as-is.
raw_ref_to_part: split out with a certificate (its `assert!`), then the
expected false UB at line 22 — the loader retagged `&raw (*whole).part`
(4 bytes), so widening back to `Whole` (8 bytes) lacked the tag at byte
4. [DEC] rustc's `place_base_raw` rule in the loader: a raw borrow whose
last deref is through a raw pointer is a tag-preserving copy of that
pointer when the trailing fields sit at byte offset 0; nonzero offsets
stay unsupported. No verdict moved. zst: `without_provenance` shim (the
integer's bytes read back as a pointer, via scratch locals); `Layout::
from_size_align(..).unwrap()` rewritten to the unchecked form in the prep.
Remaining gap is model-level: a 0-byte retag must skip liveness and bounds
(Miri). Probed by editing the two machines only: zst passes, nothing else
moves. Kept as xfail-model pending the proof update.

### 2026-10-03: zero-sized retags adopted

[DEC] (user) A retag of 0 bytes needs no live, in-bounds memory (Miri:
zero-sized accesses are always allowed). Source `ref`: the liveness and
bounds checks are guarded by `lay.size != 0`; target `Borrow (some n)`: by
`n != 0`. `move` and route borrows keep their checks (the source is
stricter there, which a forward simulation tolerates). Proof: a new
`runN_Borrow'` takes the checks as `n ≠ 0 → …`; the old `runN_Borrow` is
derived from it, so moves, route borrows and refSlice needed nothing;
`ref_pkg_core` turns the source's conditional facts into the target's.
Tests d110 (zero-sized `&mut` 8 bytes past the end: ok on both) and d111
(the sized one: UB on both); d110 fails under the old semantics (teeth
checked — a first version at one-past-the-end had none). basic::zst
passes; corpus 152/0/23 of 175; units 31 + 135; 780 proof declarations.

### 2026-10-03: what Miri flags for `&raw (*p).f` (witnesses)

Probed with the pinned Miri: a raw-pointer field projection at byte offset
0 is never UB (freed base, too-small allocation, no provenance: all ok);
at a nonzero offset it is in-bounds pointer arithmetic — UB for a freed
base, no provenance, or a field starting past the end (exactly at the end
is fine). Our zero-offset lowering (a copy) matches; the three zero-offset
witnesses pass on the model. The nonzero ones are recorded unsupported.
[OBS] The same check exposes a missed UB the model already had: `p.add(k)`
past the end (Miri: UB) is lowered like `wrapping_add` (Miri: ok) to the
non-checking `ptrOffset`. Pinned as local/ptr_add_out_of_bounds
(xfail-model) beside local/ptr_wrapping_add_out_of_bounds (passes).
Proposed fix (parked n): an in-bounds flag on `ptrOffset`.
