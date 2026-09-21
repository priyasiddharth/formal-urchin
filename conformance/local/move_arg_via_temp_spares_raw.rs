// LOCAL conformance witness (NOT from the Miri corpus): moving a named
// local into a call does NOT invalidate borrows of that local, because
// rustc moves it through a TEMPORARY first (`_4 = move _1; consume(move
// _4)`, an assignment move = a copy). Miri's in-place argument passing
// -- protected reborrow + uninit write, which the seam now emits too --
// hits `_4`, which nothing can observe; `s` keeps its bytes and its
// borrow stacks, and the read through `p` afterwards is fine. Miri's own
// in-place tests need custom MIR for this reason (fail/function_calls/
// arg_inplace_*, in the corpus). Real-Miri verified: OK (toolchain
// nightly-2026-06-01, miri 0.1.0 14210df0e2); the read prints 5.
struct S(u64);
fn consume(s: S) -> u64 {
    s.0
}
fn main() {
    let mut s = S(5);
    let p = &raw mut s.0;
    let _v = consume(s);
    let _w = unsafe { *p };
}
