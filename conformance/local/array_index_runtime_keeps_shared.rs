// Local witness: Miri's `a[i]` is a place projection, not a retag, so a
// read of `a[i]` at a run-time index leaves an earlier shared borrow of `a`
// valid. (A `&raw mut a` retag would not pop `s` either — Miri's mutable
// raw retag is no access — but it would add a stack item Miri does not.)
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let a = [1u32, 2, 3];
    let s = &a;
    let i = *Box::new(1usize);
    let _x = a[i];
    let _y = s[0];
}
