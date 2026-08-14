// derived from miri tests/fail/stacked_borrows/illegal_read8.rs @ 34d6a7954
// expected: UB at the final `*y1` (raw write popped the laundered shared)
// rewrites: `*y2 += 1` -> read then write; dropped error annotation

fn main() {
    unsafe {
        use std::mem;
        let x = &mut 0;
        let y1: &i32 = mem::transmute(&*x);
        let y2 = x as *mut i32;
        let _val = *y2;
        let _val = *y1;
        let _t = *y2;
        *y2 = 1;
        let _fail = *y1;
    }
}
