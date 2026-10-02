// Local witness (2026-10-02, byte-addressed memory): a reference to a
// one-byte field, used through a WIDER pointer. `&mut s.a` retags exactly
// the byte of `a`; writing a u16 through a pointer derived from it also
// writes `b`'s byte, whose borrow stack has no item for that tag — UB in
// Miri. The cell model gives every scalar one cell, so the u16 write
// touches only `a`'s cell and the UB is missed; the byte model sees it.
// expected: UB at the write (checked against the pinned Miri by live.py)

#[repr(C)]
struct S {
    a: u8,
    b: u8,
    c: u16,
}

fn main() {
    let mut s = S { a: 1, b: 2, c: 3 };
    let pa = &mut s.a as *mut u8;
    let wide = pa as *mut u16;
    unsafe {
        *wide = 0;
    }
    let _ = s.c;
}
