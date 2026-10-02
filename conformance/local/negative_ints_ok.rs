// Local witness (2026-10-02): negative numbers and integer casts compute
// the values MIR gives them. Every `check` is a certified branch: the
// lowering computes the condition word itself and CHECKS it against the
// arm Miri took, so a wrong value is reported as a rejected certificate,
// not hidden. `a` is derived from a slice LENGTH, which the lowering
// cannot know statically, so every value below is a runtime word in
// mirlite and every check is a runtime (T2) check.
// expected: ok (checked against the pinned Miri by scripts/live.py)

fn check(ok: bool) {
    if !ok {
        // only reachable if a value is wrong: a deliberate dangling read
        let x = 0u8;
        let p = &x as *const u8;
        unsafe {
            let _ = *p.wrapping_add(1000);
        }
    }
}

fn main() {
    let arr = [0u8; 5];
    let s: &[u8] = &arr;
    let a = -(s.len() as i32); // -5: a truncating cast, then Neg
    let b = -a; // Neg
    let c = !a; // Not: 4
    let d = a as i64; // sign extension
    let e = a as u8; // truncation: 251
    let f = a as u32 as u64; // zero extension of the bit pattern
    let g = b + c; // checked add: 9
    check(b == 5);
    check(c == 4);
    check(d == -5);
    check(e == 251);
    check(f == 4294967291);
    check(g == 9);
    check(a < 0); // signed comparison
    check(!(a > 0)); // `!` on a bool flips one bit
    check(-1i64 as u64 == 18446744073709551615);
}
