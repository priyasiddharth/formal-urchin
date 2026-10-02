// Local witness (2026-10-02, byte-addressed memory): rustc REORDERS a
// `repr(Rust)` struct. `S { a: u8, b: u32, c: u8 }` puts `b` at 0, `a` at
// 4 and `c` at 5 (size 8; C layout would be 12) — the offsets Charon
// reports and the byte model now uses. Each `check` is certified against
// the arm Miri took. The cell model lays fields out in declaration order,
// one cell each, so its byte reads land on the wrong fields
// (`xfail-model`).
// expected: ok (checked against the pinned Miri by scripts/live.py)

struct S {
    a: u8,
    b: u32,
    c: u8,
}

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
    let arr = [0u8; 7];
    let n = (&arr[..]).len() as u8; // 7: a runtime word
    let s = S { a: n, b: 0x01020304, c: n + 2 };
    check(std::mem::size_of::<S>() == 8);
    let p = &s as *const S as *const u8;
    check(unsafe { *p } == 0x04); // b's low byte, at offset 0
    check(unsafe { *p.add(4) } == 7); // a, at offset 4
    check(unsafe { *p.add(5) } == 9); // c, at offset 5
}
