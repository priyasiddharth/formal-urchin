// derived from miri tests/fail/stacked_borrows/illegal_read6.rs @ 34d6a7954
// expected: UB at `*raw` (reborrow killed raw; shared reborrow must not revive it)
// rewrites: dropped error annotation

fn main() {
    unsafe {
        let x = &mut 0;
        let raw = x as *mut i32;
        let x = &mut *x;
        let _y = &*x;
        let _val = *raw;
    }
}
