// derived from miri tests/fail/both_borrows/shr_frozen_violation2.rs @ 34d6a7954
// (stack revision)
// expected: UB at the second `*frozen` read (direct write popped it)
// rewrites: dropped revisions and error annotations

fn main() {
    unsafe {
        let mut x = 0;
        let ptr = std::ptr::addr_of_mut!(x);
        let frozen = &*ptr;
        let _val = *frozen;
        x = 1;
        let _val = *frozen;
        let _val = x;
    }
}
