// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: mut_raw_mut — mut -> raw -> mut chain; reading through the
// original mut keeps the raw usable.
// expected: ok
// rewrites: scenario extracted; assert_eq! -> plain reads

fn main() {
    let mut x = 2;
    {
        let xref1 = &mut x;
        let xraw = xref1 as *mut i32;
        let _xref2 = unsafe { &mut *xraw };
        let _val = *xref1;
        unsafe {
            *xraw = 4;
        }
        let _v1 = *xref1;
        let _v2 = unsafe { *xraw };
        let _v3 = *xref1;
        let _v4 = unsafe { *xraw };
    }
    let _v5 = x;
}
