// LOCAL conformance witness (NOT from the Miri corpus): a reference to a
// ZERO-SIZED field at the TAIL of a struct. Its address is one-past-the-end
// of the enclosing allocation (offset = size), so the retag range
// [addr, addr) sits exactly at the boundary — legal Rust, no access. This
// is the non-degenerate one-past-the-end case: unlike `local/zst_ref`
// (standalone ZST, base = addr, size = 0), here base != addr. It is
// admitted by the range-form Borrow check `addr + len > base + size` and
// was rejected by the older point check `addr >= base + size`.
// Expected verdict is model-reasoned; pending real-Miri verification.
fn main() {
    let mut s: (u64, ()) = (7, ());
    let r = &mut s.1;      // ZST field at offset 1 of a size-1 block
    let _ = r;
    let w = &mut s.0;      // the real field is still usable
    *w = 8;
}
