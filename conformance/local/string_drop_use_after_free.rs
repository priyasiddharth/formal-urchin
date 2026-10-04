// Local witness: dropping a String frees its buffer (`RawVec`'s drop), so
// a pointer into it taken before dangles.
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let s = String::from("hi");
    let p = s.as_ptr();
    drop(s);
    let _c = unsafe { *p };
}
