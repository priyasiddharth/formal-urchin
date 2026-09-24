// Slice length VALUE witness (2026-09-24): the length must be the
// element count the pointer's extent carries, not the rest of the
// allocation and not a placeholder. The branch below is certified: the
// lowering computes `n != 4` with `binOp` and CHECKS its own word
// against the arm Miri recorded, so a wrong length is reported as a
// rejected certificate rather than as a verdict.
//
// The slice is a sub-range of the array's allocation only in the sense
// that `&mut a` covers all of it; what makes this a real test is that
// the length is read at runtime out of the fat pointer.
fn main() {
    let mut a = [1usize, 2, 3, 4];
    let s: &mut [usize] = &mut a;
    let p = s.as_mut_ptr();
    let n = s.len();
    if n != 4 {
        // only reachable if the length is wrong; a deliberate OOB write
        unsafe {
            *p.add(9) = 0;
        }
    }
    unsafe {
        *p = n;
    }
    let _v = a[0];
}
