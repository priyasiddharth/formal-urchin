// derived from miri tests/fail/both_borrows/box_noalias_violation.rs @ 34d6a7954
// (stack revision)
// expected: UB at `*y` (the read would disable the protected Unique from
// the Box argument's fn-entry retag; miri says "weakly protected", our
// protector blocks the pop identically)
// rewrites: dropped revisions and error annotations

unsafe fn test(mut x: Box<i32>, y: *const i32) -> i32 {
    *x = 5;
    std::mem::forget(x);
    *y
}

fn main() {
    unsafe {
        let mut v = 42;
        let ptr = &mut v as *mut i32;
        test(Box::from_raw(ptr), ptr);
    }
}
