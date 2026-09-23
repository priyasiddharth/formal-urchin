// derived from miri tests/fail/both_borrows/outdated_local.rs @ 34d6a7954
// (stack revision)
// expected: UB at `*y` (write to x reactivated the base item, popping y)
// rewrites: dropped //@revisions and //~ ERROR annotations
//           [2026-09-23] restored upstream form under a certificate

fn main() {
    let mut x = 0;
    let y: *const i32 = &x;
    x = 1;
    assert_eq!(unsafe { *y }, 1);
    assert_eq!(x, 1);
}
