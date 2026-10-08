// Local witness: a non-capturing closure coerced to a `fn` pointer and
// called through it (Charon: `as_fn` -> `call_once` -> `call_mut` ->
// `call`, the body; Miri: a shim, then the body frame).
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut a = 1u32;
    let g = |y: &mut u32| *y = 7;
    let h: fn(&mut u32) = g;
    h(&mut a);
    if a != 7 { panic!() }
}
