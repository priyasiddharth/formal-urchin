// derived from miri tests/fail/both_borrows/alias_through_mutation.rs @ 34d6a7954
// (stack revision)
// expected: UB at `*target_alias` (write via target popped the alias)
// rewrites: dropped revisions and error annotations

fn retarget(x: &mut &u32, target: &mut u32) {
    unsafe {
        *x = &mut *(target as *mut _);
    }
}

fn main() {
    let target = &mut 42;
    let mut target_alias = &42;
    retarget(&mut target_alias, target);
    *target = 13;
    let _val = *target_alias;
}
