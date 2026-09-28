// derived from miri tests/pass/both_borrows/interior_mutability.rs @ 34d6a7954
// scenario: two_phase — a two-phase `&mut x` for a method call on a Cell
// stays valid while the argument block writes and reads through both `x`
// and the shared `l`.
// expected: ok
// rewrites: scenario extracted (fn body -> main)

fn main() {
    use std::cell::Cell;

    trait Thing: Sized {
        fn do_the_thing(&mut self, _s: i32) {}
    }

    impl<T> Thing for Cell<T> {}

    let mut x = Cell::new(1);
    let l = &x;

    x.do_the_thing({
        // In TB terms:
        // Several Foreign accesses (both Reads and Writes) to the location
        // being reborrowed. Reserved + unprotected + interior mut
        // makes the pointer immune to everything as long as all accesses
        // are child accesses to its parent pointer x.
        x.set(3);
        l.set(4);
        x.get() + l.get()
    });
}
