// LOCAL conformance witness (NOT from the Miri corpus), DOCUMENTED MODEL
// DIVERGENCE (xfail-model): an assignment `let t = s;` is a `Move`
// operand, and mirlite's `move` clears the moved-from place's borrow
// stacks, so the read through the older raw pointer is UB at line 12 on
// both machines. Real Miri says OK: it evaluates `Copy` and `Move`
// operands identically (rustc FIXME to someday invalidate the old
// location). Real-Miri verified OK (toolchain nightly-2026-06-01, miri
// 0.1.0 14210df0e2).
struct S(u64);
fn main() {
    let mut s = S(5);
    let p = &raw mut s.0;
    let t = s;
    let _w = unsafe { *p };
    let _u = t.0;
}
