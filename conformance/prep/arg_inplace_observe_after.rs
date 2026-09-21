// derived from miri tests/fail/function_calls/arg_inplace_observe_after.rs @ 34d6a7954
// expected: UB (Miri's in-place argument/return-place protection: a
// protected reborrow of the caller's slot for the call, uninit written
// through it). Custom MIR is the only way to name the in-place slot.
// rewrites: dropped //@revisions and //~ ERROR annotations; `ptr.read()`/
//           `ptr.write(v)` -> `(*ptr).0` / `(*ptr).0 = v` derefs; assert_eq! ->
//           a plain read
#![feature(custom_mir, core_intrinsics)]
use std::intrinsics::mir::*;
pub struct S(i32);
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn main() {
    mir! {
        let _unit: ();
        let _observe: i32;
        {
            let non_copy = S(42);
            Call(_unit = change_arg(Move(non_copy)), ReturnTo(after_call), UnwindContinue())
        }
        after_call = {
            _observe = non_copy.0;
            Return()
        }
    }
}
#[expect(unused_variables, unused_assignments)]
fn change_arg(mut x: S) {
    x.0 = 0;
}
