// Local witness: a shared retag of a multi-variant enum that holds an
// UnsafeCell treats the WHOLE enum as interior-mutable — SharedReadWrite,
// no read access — without looking at the active variant (Miri's
// `visit_freeze_sensitive`, vendor/miri/src/helpers.rs). So a live `&mut`
// into the payload survives `&*op` and can still be used. A mask that
// froze the enum would do a read there and pop `r` (2026-09-30).
// expected: ok (checked against the pinned Miri by scripts/live.py)
use std::cell::Cell;

fn main() {
    let mut o: Option<Cell<i32>> = Some(Cell::new(1));
    let op = &raw mut o;
    let r: &mut Cell<i32> = match unsafe { &mut *op } {
        Some(c) => c,
        None => return,
    };
    let s: &Option<Cell<i32>> = unsafe { &*op };
    r.set(5);
    let _ = s;
}
