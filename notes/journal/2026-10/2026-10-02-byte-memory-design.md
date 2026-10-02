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
3. **oseair + compiler on bytes.** Same memory; `Load`/`Store` carry a
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

Open: negative constants in plain value positions still clamp to 0 (the
destination's width is not on `UTy.nat` yet — stage 5); unary `Neg`/`Not`,
`Cmp` and `Offset` are still unsupported; a 128-bit value does not fit a
byte-model leaf (8 bytes) until leaves get widths (stage 5).
