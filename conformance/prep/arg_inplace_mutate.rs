// derived from miri tests/fail/function_calls/arg_inplace_mutate.rs @ 34d6a7954
// expected: UB (Miri's in-place argument/return-place protection: a
// protected reborrow of the caller's slot for the call, uninit written
// through it). Custom MIR is the only way to name the in-place slot.
// rewrites: dropped //@revisions and //~ ERROR annotations; upstream
//           `ptr.read()`/`ptr.write(v)` kept (restored 2026-09-29)
//           [2026-09-23] restored upstream form under a certificate
#![feature(custom_mir, core_intrinsics)]
use std::intrinsics::mir::*;
pub struct S(i32);
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn main() {
    mir! {
        let _unit: ();
        {
            let non_copy = S(42);
            let ptr = std::ptr::addr_of_mut!(non_copy);
            Call(_unit = callee(Move(*ptr), ptr), ReturnTo(after_call), UnwindContinue())
        }
        after_call = {
            Return()
        }
    }
}
fn callee(x: S, ptr: *mut S) {
    unsafe { ptr.write(S(0)) };
    assert_eq!(x.0, 42);
}
