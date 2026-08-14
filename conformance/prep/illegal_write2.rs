// derived from miri tests/fail/stacked_borrows/illegal_write2.rs @ 34d6a7954
// expected: UB at `*target2 = 13` (raw's tag popped by the reborrow)
// rewrites: `drop(&mut *target)` -> `let _reborrow = &mut *target;`
//           (avoids std::mem::drop; the reborrow is the SB-relevant part);
//           dropped #![allow] and //~ ERROR annotation

fn main() {
    let target = &mut 42;
    let target2 = target as *mut i32;
    let _reborrow = &mut *target;
    unsafe { *target2 = 13 };
    let _val = *target;
}
