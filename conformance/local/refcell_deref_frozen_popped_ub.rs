// Local witness, the UB half of refcell_guard_ptr_survives_sibling_write_ok:
// the same sibling raw write (offset 8, after the isize flag) that the
// guard's SharedReadWrite pointer survives pops the frozen `&u32` that
// `&*g` makes (the reference `Ref::deref` returns, retagged as a shared
// reference to a Freeze type), so the read through it is UB.
// expected: ub (checked against the pinned Miri by scripts/live.py)
use std::cell::RefCell;
fn main() {
    let rc = RefCell::new(1u32);
    let g = rc.borrow();
    let x: *const u32 = &*g;
    let p = (&rc as *const RefCell<u32> as *mut u8).wrapping_add(8) as *mut u32;
    unsafe { *p = 2; }
    let _v = unsafe { *x };
    drop(g);
}
