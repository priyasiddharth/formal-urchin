// LOCAL conformance witness (NOT from the Miri corpus): the positive
// side of `move` -- a non-Copy value moved into a call arrives, and a
// raw pointer into an UNRELATED local is untouched by the move. Both
// machines run clean. Real-Miri verified: OK (toolchain
// nightly-2026-06-01, miri 0.1.0 14210df0e2).
struct S(u64);
fn consume(s: S) -> u64 {
    s.0
}
fn main() {
    let mut other = 7u64;
    let q = &raw mut other;
    let s = S(5);
    let v = consume(s);
    let w = unsafe { *q };
    let _pair = (v, w);
}
