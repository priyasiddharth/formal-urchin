// Local witness: two shared guards end at their scope's end; the later
// `borrow_mut` needs the flag back at 0. The loader checks the flag at every
// borrow (Miri's run did not panic), so a guard drop it missed would stop the
// run with "assumption rejected".
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::cell::RefCell;
fn main() {
    let rc = RefCell::new(1u32);
    {
        let a = rc.borrow();
        let b = rc.borrow();
        if *a + *b != 2 { panic!() }
    }
    *rc.borrow_mut() = 5;
    if *rc.borrow() != 5 { panic!() }
}
