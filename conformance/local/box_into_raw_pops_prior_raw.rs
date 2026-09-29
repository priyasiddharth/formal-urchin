// Local witness: a raw pointer taken from a Box BEFORE `Box::into_raw`
// does not survive it. `into_raw` takes the Box by value, and its
// fn-entry Unique retag of the Box writes through the Box's tag, popping
// every item above it — including `r`'s.
// expected: UB at the write through `r` (checked against the pinned Miri
// by scripts/live.py)

fn main() {
    let mut b = Box::new(5i32);
    let r = &mut *b as *mut i32;
    let p = Box::into_raw(b);
    unsafe {
        *r = 1;
        drop(Box::from_raw(p));
    }
}
