// Local witness: `p.add(k)` with `k` known only when the program runs, past
// the end of the 12-byte array: in-bounds arithmetic fails (Miri: UB).
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let a = [1u32, 2, 3];
    let p = &a as *const [u32; 3] as *const u32;
    let k = *Box::new(4usize);
    let _q = unsafe { p.add(k) };
}
