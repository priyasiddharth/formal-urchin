// Local witness: Boxes whose pointee type appears only at their
// constructor, never through a `*b` deref. Charon monomorphises each
// `Box<T>` into an OPAQUE decl, so the loader must read `T` off
// `Box::new(v: T)` and `Box::from_raw(p: *mut T)` (survey item f); before
// that, both locals were "Box with uninferred pointee".
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::alloc::{alloc, Layout};

fn main() {
    let b = Box::new(5i32);
    let c = b;
    drop(c);
    unsafe {
        let p = alloc(Layout::from_size_align_unchecked(8, 8)) as *mut u64;
        *p = 7;
        let d: Box<u64> = Box::from_raw(p);
        drop(d);
    }
}
