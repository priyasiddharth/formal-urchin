// derived from miri tests/fail/stacked_borrows/illegal_read3.rs @ 34d6a7954
// expected: UB at `*xref2` (callee's read with xref1's tag pops xref2)
// rewrites: union `HiddenRef { r: &i32 }` replaced by `*const i32` — the
// union's only job is to carry xref1's tag across the call WITHOUT a
// retag, which a raw pointer also does (raw args are not retagged, and
// `*p` reads with the carried tag); dropped //~ ERROR annotation

use std::mem;

fn main() {
    let mut x: i32 = 15;
    let xref1 = &mut x;
    let xref1_sneaky: *const i32 = unsafe { mem::transmute_copy(&xref1) };
    // Derived from `xref1`, so using raw value is still ok, ...
    let xref2 = &mut *xref1;
    callee(xref1_sneaky);
    // ... though any use of it will invalidate our ref.
    let _val = *xref2;
}

fn callee(xref1: *const i32) {
    let _val = unsafe { *xref1 };
}
