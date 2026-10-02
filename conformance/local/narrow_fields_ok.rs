// Local witness (2026-10-02, byte-addressed memory): integer widths,
// padding and partial access. Each `check` is a certified branch: the
// lowering computes the condition itself and CHECKS it against the arm
// Miri took. The cell model has one cell per scalar, so a byte written
// into a u32 replaces the whole cell and its checks fail (`xfail-model`);
// the byte model computes Miri's values.
// expected: ok (checked against the pinned Miri by scripts/live.py)

#[repr(C)]
struct S {
    a: u8,
    b: u32,
    c: u16,
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
    let arr = [0u8; 3];
    let n = (&arr[..]).len() as u32; // 3: a runtime word
    let mut s = S { a: 1, b: 0x01020300 + n, c: 7 };
    check(std::mem::size_of::<S>() == 12); // a at 0, b at 4, c at 8
    let pb = &mut s.b as *mut u32 as *mut u8;
    unsafe {
        *pb = 0xFF; // the LOW byte of b (little-endian)
    }
    check(s.b == 0x010203FF);
    let second = unsafe { *(&s.b as *const u32 as *const u8).add(1) };
    check(second == 0x03);
    check(s.a == 1 && s.c == 7);
}
