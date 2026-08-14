// derived from miri tests/fail/stacked_borrows/raw_tracking.rs @ 34d6a7954
// expected: UB at `*raw1 = 13` (raw2's creation invalidated raw1)
// rewrites: dropped error annotation

fn main() {
    let mut l = 13;
    let raw1 = &mut l as *mut i32;
    let raw2 = &mut l as *mut i32;
    unsafe { *raw1 = 13 };
    unsafe { *raw2 = 13 };
}
