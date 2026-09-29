// derived from miri tests/fail/both_borrows/mixed_mutability_static.rs @ 34d6a7954
// (stack revision)
// expected: UB at the write to the non-cell part of the static
// rewrites: dropped revisions and error annotations. The upstream
//           `ptr.cast_mut().write((1, AtomicI32::new(0)))` is kept
//           (restored 2026-09-29: the `cast_mut` and `ptr::write` shims,
//           and `Atomic::new` as the cell constructor it is in the
//           model)

use std::sync::atomic::*;

static X: (i32, AtomicI32) = (0, AtomicI32::new(1));

fn main() {
    let ptr = &raw const X;
    unsafe { ptr.cast_mut().write((1, AtomicI32::new(0))) };
}
