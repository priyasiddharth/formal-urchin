// derived from miri tests/fail/both_borrows/mut_exclusive_violation2.rs @ 34d6a7954
// expected: UB at `*raw1` (creating raw2 from the same raw provenance
// pops raw1's Unique)
// rewrites: dropped revisions and error annotations; `NonNull` replaced by
// `*mut i32` (NonNull is repr(transparent) over one): `NonNull::from(x)` ->
// `x as *mut`, `clone()` -> a copy, `as_mut()` -> `&mut *p`. Dropped with
// them: the fn-entry retags of the `&mut self`/`&self` locals those std
// methods take, which never touch the pointee.

fn main() {
    unsafe {
        let x = &mut 0;
        let ptr1: *mut i32 = x;
        let ptr2 = ptr1;
        let raw1 = &mut *ptr1;
        let raw2 = &mut *ptr2;
        let _val = *raw1;
        *raw2 = 2;
        *raw1 = 3;
    }
}
