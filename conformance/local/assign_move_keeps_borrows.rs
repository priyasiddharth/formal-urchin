// LOCAL conformance witness (NOT from the Miri corpus): a `move` operand
// in an ASSIGNMENT is a copy -- rustc's interpreter evaluates `Copy` and
// `Move` operands identically (with a FIXME) -- so a raw pointer into the
// moved-from local survives `let t = s;`, and the read through it is
// fine. The seam lowers assignment moves as copies; the in-place
// protection applies to call arguments only. Real-Miri verified: OK
// (toolchain nightly-2026-06-01, miri 0.1.0 14210df0e2).
struct S(u64);
fn main() {
    let mut s = S(5);
    let p = &raw mut s.0;
    let t = s;
    let _w = unsafe { *p };
    let _u = t.0;
}
