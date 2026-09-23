// derived from miri tests/fail/stacked_borrows/fnentry_invalidation.rs @ 34d6a7954
// expected: UB at `*z` (the method call's fn-entry retag of `&mut x`
// popped the raw)
// rewrites: dropped the //~ ERROR annotation; otherwise upstream (the
//           default trait method `Bad::do_bad` is inlined from charon's
//           monomorphized body), lowered under a certificate
// Test that spans displayed in diagnostics identify the function call, not the function
// definition, as the location of invalidation due to FnEntry retag. Technically the FnEntry retag
// occurs inside the function, but what the user wants to know is which call produced the
// invalidation.
fn main() {
    let mut x = 0i32;
    let z = &mut x as *mut i32;
    x.do_bad();
    unsafe {
        let _oof = *z;
    }
}

trait Bad {
    fn do_bad(&mut self) {
        // who knows
    }
}

impl Bad for i32 {}
