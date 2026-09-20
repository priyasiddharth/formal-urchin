// LOCAL conformance witness (NOT from the Miri corpus): moving ONE FIELD
// of a struct into a call -- through rustc's temporary, as every named
// place is -- leaves a raw pointer into the sibling field valid. Real-Miri
// verified: OK (toolchain nightly-2026-06-01, miri 0.1.0 14210df0e2).
struct S(u64);
struct Pair(S, S);
fn consume(s: S) -> u64 {
    s.0
}
fn main() {
    let mut pr = Pair(S(1), S(2));
    let q = &raw mut pr.0 .0;
    let _v = consume(pr.1);
    let _w = unsafe { *q };
}
