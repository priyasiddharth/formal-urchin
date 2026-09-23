// derived from miri tests/pass/stacked_borrows/stacked-borrows.rs @ 34d6a7954
// scenario: two_phase_aliasing_violation — a two-phase borrow's receiver
// may be written through a raw pointer before activation; the method then
// reads the written value.
// expected: ok
// rewrites: scenario extracted into its own main; otherwise upstream
//           (upstream's -Zmir-opt-level=0 is what every certificate run uses)

fn main() {
    struct Foo(u64);
    impl Foo {
        fn add(&mut self, n: u64) -> u64 {
            self.0 + n
        }
    }

    let mut f = Foo(0);
    let alias = &mut f.0 as *mut u64;
    let res = f.add(unsafe {
        *alias = 42;
        0
    });
    assert_eq!(res, 42);
}
