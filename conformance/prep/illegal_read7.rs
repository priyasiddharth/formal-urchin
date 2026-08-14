// derived from miri tests/fail/stacked_borrows/illegal_read7.rs @ 34d6a7954
// expected: UB at the reborrow of x (raw read popped it)
// rewrites: *x.get_mut() -> &mut *x (same failing retag, avoids the
//           Cell::get_mut body); ptr::read(raw) kept (shimmed);
//           dropped error annotation

use std::cell::Cell;
use std::ptr;

fn main() {
    unsafe {
        let x = &mut Cell::new(0);
        let raw = x as *mut Cell<i32>;
        let x = &mut *raw;
        let _shr = &*x;
        let _val = ptr::read(raw);
        let _r = &mut *x;
    }
}
