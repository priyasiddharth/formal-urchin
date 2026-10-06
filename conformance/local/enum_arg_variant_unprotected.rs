// Local witness: an enum argument is retagged at function entry for the
// variant it holds (Miri reads its discriminant). Variant `A` holds a raw
// pointer, which the entry retag does not protect, so a write through an
// aliasing raw pointer during the call is fine. The loader takes the variant from the
// certificate and checks it when the program runs.
// expected: ok (checked against the pinned Miri by scripts/live.py)
enum E<'a> { A(*mut u32), B(&'a mut u32) }
fn f(_e: E, p: *mut u32) {
    unsafe { *p = 5 };
}
fn main() {
    let mut x = 1u32;
    let p = &mut x as *mut u32;
    let k = *Box::new(0u8);
    let e = if k == 1 { E::B(unsafe { &mut *p }) } else { E::A(p) };
    f(e, p);
}
