// Local witness: a string literal's bytes are readable through
// `str::as_ptr`; the branch makes the certificate check the byte read.
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let s: &str = "hello";
    let p = s.as_ptr();
    let c = unsafe { *p.add(1) };
    if c != b'e' {
        unsafe { std::hint::unreachable_unchecked() }
    }
}
