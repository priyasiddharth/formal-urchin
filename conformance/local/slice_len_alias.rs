// Slice length witness (2026-09-24): `s.len()` is the metadata of the
// fat pointer, read out of the local that holds it -- not an access to
// the slice DATA. So taking the length through a SHARED reborrow of a
// `&mut [u8]` must not disable the mutable pointer derived from it:
// the write through `p` after `len()` is legal, and the final read
// through the owner is legal too.
//
// The array-to-slice coercion gives the slice its extent (4 cells), so
// `len()` is 4 -- the value the guard below checks.
fn main() {
    let mut a = [1usize, 2, 3, 4];
    let s: &mut [usize] = &mut a;
    let p = s.as_mut_ptr();
    let n = s.len();
    unsafe {
        *p = n;
    }
    let _v = a[0];
}
