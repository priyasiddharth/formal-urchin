// derived from miri tests/fail/stacked_borrows/load_invalid_mut.rs @ 34d6a7954
// expected: UB at `*xref_in_mem` (retag of the loaded, invalidated &mut)
// rewrites: dropped error annotation

fn main() {
    let x = &mut 42;
    let xraw = x as *mut i32;
    let xref = unsafe { &mut *xraw };
    let xref_in_mem = Box::new(xref);
    let _val = unsafe { *xraw };
    let _val = *xref_in_mem;
}
