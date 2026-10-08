// Local witness, the counterpart of basic_aliasing_model::not_unpin_not_protected:
// the same program with an `Unpin` struct. Now `&mut Thing` is protected at
// `inner`'s entry, so the closure deallocating it through a `fn` pointer is
// UB (a strongly protected item).
// expected: ub (checked against the pinned Miri by scripts/live.py)
pub struct Thing(#[allow(dead_code)] i32);
fn inner(x: &mut Thing, f: fn(&mut Thing)) {
    f(x)
}
fn main() {
    inner(Box::leak(Box::new(Thing(0))), |x| {
        let raw = x as *mut _;
        drop(unsafe { Box::from_raw(raw) });
    });
}
