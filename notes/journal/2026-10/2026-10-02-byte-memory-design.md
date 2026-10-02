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
2. **mirlite on bytes.** Concretely, from stage 1: a value of layout `τ`
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
