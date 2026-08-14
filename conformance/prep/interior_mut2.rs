// derived from miri tests/fail/stacked_borrows/interior_mut2.rs @ 34d6a7954
// expected: UB at the final `*inner_shr.get()` (SRW tag popped)
// rewrites: dropped error annotation

use std::cell::UnsafeCell;
use std::mem;

#[allow(mutable_transmutes)]
unsafe fn unsafe_cell_get<T>(x: &UnsafeCell<T>) -> &'static mut T {
    mem::transmute(x)
}

fn main() {
    unsafe {
        let c = &UnsafeCell::new(UnsafeCell::new(0));
        let inner_uniq = &mut *c.get();
        let inner_shr = &*inner_uniq;
        let _val = c.get().read();
        let _val = *unsafe_cell_get(inner_shr);
        *c.get() = UnsafeCell::new(0);
        let _val = *inner_shr.get();
    }
}
