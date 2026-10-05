// Local witness: `p.add(k)` with `k` known only when the program runs (read
// from a Box) is in-bounds arithmetic that succeeds; the branch makes the
// certificate check the element read through it.
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let a = [1u32, 2, 3];
    let p = &a as *const [u32; 3] as *const u32;
    let k = *Box::new(2usize);
    let x = unsafe { *p.add(k) };
    if x != 3 {
        unsafe { std::hint::unreachable_unchecked() }
    }
}
