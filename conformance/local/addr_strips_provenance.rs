// Local witness: `ptr.addr()` does NOT expose the pointer's provenance, so
// turning the address back into a pointer with `with_exposed_provenance_mut`
// gives a pointer that may not access `x` (nothing was exposed).
// expected: ub at `*q = 9;` (checked against the pinned Miri by
// scripts/live.py)
fn main() {
    let mut x = 7u64;
    let p = &raw mut x;
    let a: usize = p.addr();
    let q = std::ptr::with_exposed_provenance_mut::<u64>(a);
    unsafe { *q = 9; }
    let _y = x;
}
