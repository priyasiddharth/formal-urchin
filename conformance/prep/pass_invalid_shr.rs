// derived from miri tests/fail/both_borrows/pass_invalid_shr.rs @ 34d6a7954
// (stack revision)
// expected: UB at the seam retag of foo's argument (xref's tag was popped
// by the raw write) — requires inline-seam retag synthesis (B.6)
// rewrites: dropped //@revisions and //~ ERROR annotations

fn foo(_: &i32) {}

fn main() {
    let x = &mut 42;
    let xraw = x as *mut i32;
    let xref = unsafe { &*xraw };
    unsafe { *xraw = 42 };
    foo(xref);
}
