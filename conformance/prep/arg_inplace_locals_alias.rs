// derived from miri tests/fail/function_calls/arg_inplace_locals_alias.rs @ 34d6a7954
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
        {
            let staging = S(42);
            let non_copy = staging;
            Call(_unit = callee(Move(non_copy), Move(non_copy)), ReturnTo(after_call), UnwindContinue())
        }
        after_call = {
            Return()
        }
    }
}
#[expect(unused_variables, unused_assignments)]
fn callee(x: S, mut y: S) {
    y.0 = 0;
    let _v = x.0;
}
