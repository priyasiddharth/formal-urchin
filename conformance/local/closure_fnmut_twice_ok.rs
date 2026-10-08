// Local witness: an `FnMut` closure that captures `&mut` state, called
// twice through `&mut F` (`call_mut`).
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn twice<F: FnMut()>(f: &mut F) {
    f();
    f();
}
fn main() {
    let mut n = 0u32;
    let mut inc = || n += 1;
    twice(&mut inc);
    if n != 2 { panic!() }
}
