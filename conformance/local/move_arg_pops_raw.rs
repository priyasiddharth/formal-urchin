// LOCAL conformance witness (NOT from the Miri corpus), DOCUMENTED MODEL
// DIVERGENCE (xfail-model): moving a local into a call clears the borrow
// stacks of the moved-from place in mirlite/oseair, so the read through
// the older raw pointer is UB at line 20 on both machines. Real Miri says
// OK: rustc moves a named place into a call through a TEMPORARY (`_4 =
// move _1; consume(move _4)`), evaluates the assignment move as a copy
// (rustc FIXME: "do some more logic on `move` to invalidate the old
// location"), and its in-place protection lands on `_4`. Our `move`
// clears on EVERY Move operand — the intended semantics of a move,
// which Miri does not yet implement. Real-Miri verified OK (toolchain
// nightly-2026-06-01, miri 0.1.0 14210df0e2); Miri's own in-place tests
// are custom MIR for this reason.
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
