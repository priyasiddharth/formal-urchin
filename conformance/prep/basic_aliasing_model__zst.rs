// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: zst — zero-sized retags perform no access: they are fine through
// an integer pointer, an out-of-bounds pointer and a dangling pointer, and a
// zero-sized protector does not block deallocation.
// expected: ok
// rewrites: scenario extracted
//           Layout::from_size_align(1, 1).unwrap() → from_size_align_unchecked(1, 1)
//           (same layout; the model has no `Result`)
use std::alloc::{Layout, alloc, dealloc};
use std::ptr;

fn main() {
    unsafe {
        // Integer pointer.
        let ptr = ptr::without_provenance_mut::<()>(15);
        let _ref = &mut *ptr;

        // Out-of-bounds pointer.
        let mut b = Box::new(0u8);
        let ptr = (&raw mut *b).wrapping_add(15) as *mut ();
        let _ref = &mut *ptr;

        // Deallocated pointer.
        let ptr = &raw mut *b as *mut ();
        drop(b);
        let _ref = &mut *ptr;

        // zero-sized protectors do not affect deallocation
        fn with_protector(_x: &mut (), ptr: *mut u8, l: Layout) {
            // `_x` here is strongly protected but covers zero bytes.
            unsafe { dealloc(ptr, l) };
        }
        let l = Layout::from_size_align_unchecked(1, 1);
        let ptr = alloc(l);
        with_protector(&mut *ptr.cast::<()>(), ptr, l);
    }
}
