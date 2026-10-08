// Local witness: a closure capturing `&mut` state, passed by value to a
// generic `FnOnce` and called there. Charon translates the closure as its
// `call_once` method (the body); the certificate frame is `{closure#0}`.
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn apply<F: FnOnce(&mut u32)>(x: &mut u32, f: F) {
    f(x)
}
fn main() {
    let mut a = 1u32;
    let mut b = 2u32;
    let pb = &mut b;
    apply(&mut a, |x| {
        *x += 1;
        *pb += 1;
    });
    let s = a + b;
    if s != 5 { panic!() }
}
