// derived from miri tests/fail/both_borrows/mut_exclusive_violation2.rs @ 34d6a7954
// expected: UB at `*raw1` (creating raw2 from the same raw provenance
// pops raw1's Unique)
// rewrites: dropped revisions and error annotations. The upstream
// `NonNull` code is kept (restored 2026-09-30 with the NonNull shims:
// `from` = `from_mut`'s retags, `clone` = a copy, `as_mut` = a Unique
// reborrow through the stored pointer).

use std::ptr::NonNull;

fn main() {
    unsafe {
        let x = &mut 0;
        let mut ptr1 = NonNull::from(x);
        let mut ptr2 = ptr1.clone();
        let raw1 = ptr1.as_mut();
        let raw2 = ptr2.as_mut();
        let _val = *raw1;
        *raw2 = 2;
        *raw1 = 3;
    }
}
