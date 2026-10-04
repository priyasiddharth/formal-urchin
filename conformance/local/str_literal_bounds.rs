// Local witness: a string literal's allocation is exactly its bytes, so
// in-bounds arithmetic past one-past-the-end leaves it.
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let s: &str = "hi";
    let p = s.as_ptr();
    let _q = unsafe { p.add(3) };
}
