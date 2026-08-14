// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: array_casts — casting an array reference to a raw element
// pointer covers the whole array.
// expected: ok
// rewrites: scenario extracted; assert_eq! -> plain read

fn main() {
    let mut x: [usize; 2] = [0, 0];
    let p = &mut x as *mut usize;
    unsafe {
        *p.add(1) = 1;
    }

    let x: [usize; 2] = [0, 1];
    let p = &x as *const usize;
    let _v = unsafe { *p.add(1) };
}
