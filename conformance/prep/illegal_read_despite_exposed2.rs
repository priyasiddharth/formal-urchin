// derived from miri tests/fail/both_borrows/illegal_read_despite_exposed2.rs @ 34d6a7954
// (stack revision)
// expected: UB at the final `*root2 = 3` (the wildcard read disabled it)
// rewrites: dropped revisions and error annotations

fn main() {
    unsafe {
        let root = &mut 42;
        let addr = root as *mut i32 as usize;
        let exposed_ptr = addr as *mut i32;
        let root2 = &mut *exposed_ptr;
        *root2 = 42;
        let _val = *exposed_ptr;
        *root2 = 3;
    }
}
