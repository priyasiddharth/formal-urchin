// Local witness: a fn pointer passed as a MOVED call argument and called
// in the callee. Charon passes `f` as `move _k`; the lowering tracks fn
// pointers statically, so the callee's parameter must inherit the
// caller's target (survey item e), or `f(x)` is an indirect call with an
// unknown target.
// expected: ok (checked against the pinned Miri by scripts/live.py)

fn set_two(x: &mut i32) {
    *x = 2;
}

fn apply(x: &mut i32, f: fn(&mut i32)) {
    f(x)
}

fn main() {
    let mut v = 1i32;
    apply(&mut v, set_two);
    let _w = v;
}
