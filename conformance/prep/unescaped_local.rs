// derived from miri tests/fail/stacked_borrows/unescaped_local.rs @ 34d6a7954
// expected: UB at `*raw = 13` (the exposed tag was popped; no exposed
// tags grant the wildcard write)
// rewrites: dropped error annotation

fn main() {
    let mut x = 42;
    let raw = &mut x as *mut i32 as usize as *mut i32;
    let _ptr = &mut x;
    unsafe {
        *raw = 13;
    }
}
