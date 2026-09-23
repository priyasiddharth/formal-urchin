// derived from miri tests/fail/stacked_borrows/illegal_read8.rs @ 34d6a7954
// expected: UB at the final `*y1` (raw write popped the laundered shared)
// rewrites: dropped error annotation
//           [2026-09-23] restored upstream form under a certificate

fn main() {
    unsafe {
        use std::mem;
        let x = &mut 0;
        let y1: &i32 = mem::transmute(&*x);
        let y2 = x as *mut i32;
        let _val = *y2;
        let _val = *y1;
        *y2 += 1;
        let _fail = *y1;
    }
}
