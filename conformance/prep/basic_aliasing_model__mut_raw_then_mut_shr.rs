// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: mut_raw_then_mut_shr — escape a mut to raw, then share the
// same mut and use the share, then write through the raw. Must be OK
// (raw-mut items survive read accesses).
// expected: ok
// rewrites: extracted scenario into its own main; assert_eq! -> plain reads

fn main() {
    let mut x = 2;
    let xref = &mut x;
    let xraw = &mut *xref as *mut i32;
    let xshr = &*xref;
    let _v = *xshr;
    unsafe {
        *xraw = 4;
    }
    let _w = x;
}
