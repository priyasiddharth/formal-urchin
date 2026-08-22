// LOCAL conformance witness (NOT from the Miri corpus): a ZERO-SIZED field
// in the INTERIOR of a struct must retag an EMPTY range — it must not
// touch the cell that follows it.
//
// In the model's cell layout `(u64, (), u64)` puts `s.1` at offset 1 and,
// because the ZST occupies no cell, `s.2` at offset 1 as well. So a retag
// of `s.1` that wrongly used a length of 1 would take a write access on
// exactly the cell `b` points at, invalidating it and making `*b` UB.
// The test keeps `b` live across the ZST retag to catch that.
//
// (This is NOT a regression test for the one-past-the-end boundary —
// verified: it passes under the older point check `addr >= base + size`
// too, since an interior address is genuinely in bounds. `local/zst_ref`
// and `local/zst_tail_field` are the boundary witnesses.)
// Expected verdict is model-reasoned; pending real-Miri verification.
fn main() {
    let mut s: (u64, (), u64) = (7, (), 9);
    let b = &mut s.2;   // the cell after the ZST
    let z = &mut s.1;   // empty retag at the same offset -- must not disturb b
    *b = 10;            // UB if the ZST retag had taken a write access here
    let _ = z;
}
