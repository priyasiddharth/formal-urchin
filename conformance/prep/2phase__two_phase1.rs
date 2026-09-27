// derived from miri tests/pass/both_borrows/2phase.rs @ 34d6a7954
// scenario: two_phase1 — `x.tpb(x)`: the autoref `&mut x` is a two-phase
// borrow, so reading `x` for the argument before activation is fine.
// expected: ok
// rewrites: scenario extracted

trait S: Sized {
    fn tpb(&mut self, _s: Self) {}
}

impl S for i32 {}

fn main() {
    let mut x = 3;
    x.tpb(x);
}
