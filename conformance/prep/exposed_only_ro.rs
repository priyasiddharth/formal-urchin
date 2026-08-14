// derived from miri tests/fail/stacked_borrows/exposed_only_ro.rs @ 34d6a7954
// expected: UB at `*ptr = 0` (only a read-only tag was exposed)
// rewrites: dropped error annotation

fn main() {
    let mut x = 0;
    let _fool = &mut x as *mut i32;
    let addr = (&x as *const i32).expose_provenance();
    let ptr = std::ptr::with_exposed_provenance_mut::<i32>(addr);
    unsafe { *ptr = 0 };
}
