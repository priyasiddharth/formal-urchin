// derived from miri tests/fail/both_borrows/illegal_read_despite_exposed1.rs @ 34d6a7954
// (stack revision)
// expected: UB at `*root2` (wildcard write via the exposed tag popped it)
// rewrites: dropped revisions and error annotations

fn main() {
    unsafe {
        let root = &mut 42;
        let addr = root as *mut i32 as usize;
        let exposed_ptr = addr as *mut i32;
        let root2 = &mut *exposed_ptr;
        let _fool = root2 as *mut i32;
        *exposed_ptr = 0;
        let _val = *root2;
    }
}
