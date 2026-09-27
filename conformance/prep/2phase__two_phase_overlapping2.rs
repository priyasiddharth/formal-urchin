// derived from miri tests/pass/both_borrows/2phase.rs @ 34d6a7954
// scenario: two_phase_overlapping2 — a two-phase `&mut x` autoref while a
// shared `l = &x` is live and read for the argument.
// expected: ok
// rewrites: scenario extracted; std's `<i32 as AddAssign>::add_assign`
//           (no body under Charon) replaced by a local trait method with
//           std's body `*self += other` — same `&mut self` autoref (still
//           two-phase), same fn-entry retag of `self`

trait AddAssign {
    fn add_assign(&mut self, other: i32);
}

impl AddAssign for i32 {
    fn add_assign(&mut self, other: i32) {
        *self += other
    }
}

fn main() {
    let mut x = 1;
    let l = &x;
    x.add_assign(x + *l);
}
