// Local witness: `push` past the capacity reallocates, and Miri's realloc
// frees the old buffer: a pointer taken before it dangles.
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut v: Vec<u32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    let p = v.as_ptr();
    v.push(5);
    let _x = unsafe { *p };
}
