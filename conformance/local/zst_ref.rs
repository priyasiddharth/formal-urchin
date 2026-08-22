// LOCAL conformance witness (NOT from the Miri corpus): taking a reference
// to a ZERO-SIZED place is legal Rust and performs no access, so it is OK
// under Stacked Borrows. mirlite agrees (`M.ref` over an empty range
// succeeds). The compiled OSEA target does NOT: its `Rhs.Borrow` bounds
// check `addr >= base + size` fires for `size = 0`, so the differential
// oracle is expected to report a MISMATCH here until that check is
// relaxed for empty ranges. Found 2026-08-22 while closing the ref leaf
// of the compiler-correctness proof (the closed regime carries
// `0 < blockSize τ`). Expected verdict is model-reasoned; pending
// verification against real Miri.
fn main() {
    let mut z = ();
    let r = &mut z;
    let _ = r;
    let mut x = 7u64;
    let p = &mut x;
    *p = 8;
}
