// Local witness: a local array read and written at an index known only when
// the program runs (from a Box). The loader dispatches over the possible
// indices; the branches make the certificate check the values.
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut a = [1u32, 2, 3];
    let i = *Box::new(2usize);
    a[i] = 7;
    let x = a[i];
    if x != 7 || a[0] != 1 {
        unsafe { std::hint::unreachable_unchecked() }
    }
}
