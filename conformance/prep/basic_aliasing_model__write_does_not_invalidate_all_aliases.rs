// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: write_does_not_invalidate_all_aliases — a type-punned read
// copies the `&mut`'s tag into a static; a later write through `x` does
// not invalidate that copy, so writing through the static is fine.
// expected: ok
// rewrites: scenario extracted; `(x as *const &mut i32).cast::<*mut i32>()`
//           -> `x as *const &mut i32 as *const *mut i32` (exactly what
//           `<*const T>::cast` does; raw args are not retagged)

fn main() {
    mod other {
        /// Some private memory to store stuff in.
        static mut S: *mut i32 = 0 as *mut i32;

        pub fn lib1(x: &&mut i32) {
            unsafe {
                S = (x as *const &mut i32 as *const *mut i32).read();
            }
        }

        pub fn lib2() {
            unsafe {
                *S = 1337;
            }
        }
    }

    let x = &mut 0;
    other::lib1(&x);
    *x = 42; // a write to x -- invalidates other pointers?
    other::lib2();
    assert_eq!(*x, 1337); // oops, the value changed! I guess not all pointers were invalidated
}
