// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: mut_shr_then_mut_raw — share a mut, then create a raw from
// it and write through the raw. Must be OK.
// expected: ok
// rewrites: extracted scenario into its own main; assert_eq! -> plain read

fn main() {
    let xref = &mut 2;
    let _xshr = &*xref;
    let xraw = xref as *mut i32;
    unsafe {
        *xraw = 3;
    }
    let _v = *xref;
}
