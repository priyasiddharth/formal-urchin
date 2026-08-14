// derived from miri tests/fail/both_borrows/outdated_local.rs @ 34d6a7954
// (stack revision)
// expected: UB at `*y` (write to x reactivated the base item, popping y)
// rewrites: assert_eq!(unsafe { *y }, 1) -> let _v = unsafe { *y };
//           assert_eq!(x, 1) -> let _w = x;
//           dropped //@revisions and //~ ERROR annotations

fn main() {
    let mut x = 0;
    let y: *const i32 = &x;
    x = 1;
    let _v = unsafe { *y };
    let _w = x;
}
