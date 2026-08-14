// derived from miri tests/fail/stacked_borrows/fnentry_invalidation2.rs @ 34d6a7954
// expected: UB at `*ptr` in main (the fn-entry retag of as_mut_ptr's
// receiver popped the earlier as_ptr raw)
// rewrites: dropped error annotation

struct Thing<'a> {
    sli: &'a mut [i32],
}

fn main() {
    let mut t = Thing { sli: &mut [0, 1, 2] };
    let ptr = t.sli.as_ptr();
    inner(&mut t);
    unsafe {
        let _oof = *ptr;
    }
}

fn inner(t: &mut Thing) {
    let _ = t.sli.as_mut_ptr();
}
