// Local witness: `Box::leak` returns a `&mut` that may be written and
// read (shim added 2026-09-29: `Box::into_raw`'s three retags, then the
// `&mut *ptr` reborrow). The memory is handed back to `Box::from_raw` at
// the end so that Miri's leak check stays quiet.
// expected: ok (checked against the pinned Miri by scripts/live.py)

fn main() {
    let r: &mut i32 = Box::leak(Box::new(5i32));
    *r = 6;
    let _v = *r;
    unsafe { drop(Box::from_raw(r as *mut i32)) };
}
