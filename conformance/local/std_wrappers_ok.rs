// Local witness for the pointer-wrapper shims (2026-09-30): NonNull
// (from(&mut T), from(&T), clone, as_ptr, cast, new_unchecked, as_mut),
// ManuallyDrop (new, deref, deref_mut), size_of (sizes an allocation: the
// second field's write is in bounds only if the size is right) and
// UnsafeCell::raw_get.
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::alloc::{alloc, dealloc, Layout};
use std::cell::UnsafeCell;
use std::mem::ManuallyDrop;
use std::ptr::NonNull;

fn main() {
    let mut x = 1i32;
    let mut a = NonNull::from(&mut x);
    let b = a.clone();
    unsafe { *a.as_mut() = 2 };
    let p: *mut i32 = b.as_ptr();
    let c: NonNull<u32> = b.cast();
    let d = unsafe { NonNull::new_unchecked(c.as_ptr()) };
    unsafe { *d.as_ptr() = 3 };
    unsafe { *p = 4 };
    let y = 5i32;
    let s = NonNull::from(&y);
    let _r = unsafe { *s.as_ptr() };

    let mut md = ManuallyDrop::new(6i32);
    *md = 7;
    let _m = *md;

    unsafe {
        let n = std::mem::size_of::<(i32, i32)>();
        let layout = Layout::from_size_align_unchecked(n, 4);
        let q = alloc(layout) as *mut (i32, i32);
        (*q).0 = 8;
        (*q).1 = 9;
        dealloc(q as *mut u8, layout);
    }

    let cell = UnsafeCell::new(10i32);
    let g = UnsafeCell::raw_get(&cell as *const UnsafeCell<i32>);
    unsafe { *g = 11 };
    let _h = unsafe { *cell.get() };
}
