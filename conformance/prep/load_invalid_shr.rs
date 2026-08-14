// derived from miri tests/fail/both_borrows/load_invalid_shr.rs @ 34d6a7954
// (stack revision)
// expected: UB at `*xref_in_mem` (retag of the loaded, invalidated &)
// rewrites: dropped revisions and error annotations

fn main() {
    let x = &mut 42;
    let xraw = x as *mut i32;
    let xref = unsafe { &*xraw };
    let xref_in_mem = Box::new(xref);
    unsafe { *xraw = 42 };
    let _val = *xref_in_mem;
}
