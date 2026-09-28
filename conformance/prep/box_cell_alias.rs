// derived from miri tests/fail/box-cell-alias.rs @ 34d6a7954
// expected: UB at the write through `ptr` inside `helper` (the moved Box
// is a protected fn-entry retag; the raw pointer's write would pop it)
// rewrites: dropped //@compile-flags and //~ ERROR annotation (the
//           upstream body is otherwise unchanged since 2026-09-28, when
//           `Cell::get` got its own shim — parked.md § A′ item b)

use std::cell::Cell;
fn helper(val: Box<Cell<u8>>, ptr: *const Cell<u8>) -> u8 {
    val.set(10);
    unsafe { (*ptr).set(20) };
    val.get()
}
fn main() {
    let val: Box<Cell<u8>> = Box::new(Cell::new(25));
    let ptr: *const Cell<u8> = &*val;
    let res = helper(val, ptr);
    assert_eq!(res, 20);
}
