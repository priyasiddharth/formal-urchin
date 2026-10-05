// Local witness: indexing slice data at a run-time index; the branch makes
// the certificate check the element read.
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let v = [1u32, 2, 3];
    let s: &[u32] = &v;
    let i = *Box::new(1usize);
    if s[i] != 2 {
        unsafe { std::hint::unreachable_unchecked() }
    }
}
