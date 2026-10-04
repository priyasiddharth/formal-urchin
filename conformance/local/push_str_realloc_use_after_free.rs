// Local witness: `push_str` past the capacity reallocates (`reserve`), and
// Miri's realloc frees the old buffer: a pointer taken before it dangles.
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut s = String::from("ab");
    let p = s.as_ptr();
    s.push_str("c");
    let _c = unsafe { *p };
}
