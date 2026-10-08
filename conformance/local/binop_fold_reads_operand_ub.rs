// Local witness: an arithmetic operand the lowering knows statically is
// still READ. `*pb += 1` after a write through `p` popped `pb`: Miri's add
// reads `*pb` through the popped tag (UB); a fold that skipped the read
// missed it (found 2026-10-08).
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut b = 2u32;
    let p = &mut b as *mut u32;
    let pb = unsafe { &mut *p };
    unsafe { *p = 5 };
    *pb += 1;
}
