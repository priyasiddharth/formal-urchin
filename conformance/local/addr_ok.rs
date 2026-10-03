// Local witness: `ptr.addr()` and a pointer-to-integer `transmute` read the
// pointer's address and strip its provenance without exposing it; the
// pointer itself stays usable. Both reads are plain reads of `p`'s bytes.
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut x = 7u64;
    let p = &raw mut x;
    let a: usize = p.addr();
    let b: usize = unsafe { std::mem::transmute::<*mut u64, usize>(p) };
    let _c = a ^ b;
    unsafe { *p = 8; }
    let _y = x;
}
