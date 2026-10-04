// Local witness: the first push allocates exactly 4 elements (std's
// `min_non_zero_cap` for a 4-byte element), so in-bounds arithmetic to
// element 5 leaves the allocation.
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut v: Vec<u32> = Vec::new();
    v.push(1);
    let p = v.as_ptr();
    let _q = unsafe { p.add(5) };
}
