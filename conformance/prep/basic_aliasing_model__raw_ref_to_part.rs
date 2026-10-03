// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: raw_ref_to_part — `&raw mut (*whole).part` through a raw pointer
// does not retag, so the part pointer may be widened back to the whole.
// expected: ok
// rewrites: scenario extracted
use std::ptr;

fn main() {
    struct Part {
        _lame: i32,
    }

    #[repr(C)]
    struct Whole {
        part: Part,
        extra: i32,
    }

    let it = Box::new(Whole { part: Part { _lame: 0 }, extra: 42 });
    let whole = ptr::addr_of_mut!(*Box::leak(it));
    let part = unsafe { ptr::addr_of_mut!((*whole).part) };
    let typed = unsafe { &mut *(part as *mut Whole) };
    assert!(typed.extra == 42);
    drop(unsafe { Box::from_raw(whole) });
}
