// derived from miri tests/fail/function_calls/return_pointer_aliasing_read.rs @ 34d6a7954
// expected: UB (Miri's in-place argument/return-place protection: a
// protected reborrow of the caller's slot for the call, uninit written
// through it). Custom MIR is the only way to name the in-place slot.
// rewrites: dropped //@revisions and //~ ERROR annotations; `ptr.read()`/
//           `ptr.write(v)` -> `(*ptr).0` / `(*ptr).0 = v` derefs; assert_eq! ->
//           a plain read
#![feature(core_intrinsics)]
#![feature(custom_mir)]
use std::intrinsics::mir::*;
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn main() {
    mir! {
        {
            let _x = 0;
            let ptr = &raw mut _x;
            Call(_x = myfun(ptr), ReturnTo(after_call), UnwindContinue())
        }
        after_call = {
            Return()
        }
    }
}
fn myfun(ptr: *mut i32) -> i32 {
    let _v = unsafe { *ptr };
    13
}
