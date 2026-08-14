// derived from miri tests/fail/stacked_borrows/disable_mut_does_not_merge_srw.rs @ 34d6a7954
// expected: UB at final `*raw` (write via base pops raw; the earlier read must not)
// rewrites: dropped comments/error annotation

fn main() {
    unsafe {
        let mut mem = 0;
        let base = &mut mem as *mut i32;
        let raw = {
            let mutref = &mut *base;
            mutref as *mut i32
        };
        let _val = *base;
        *base = 1;
        let _val = *raw;
    }
}
