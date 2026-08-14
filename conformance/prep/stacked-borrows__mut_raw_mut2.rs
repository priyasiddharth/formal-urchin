// derived from miri tests/pass/stacked_borrows/stacked-borrows.rs @ 34d6a7954
// scenario: mut_raw_mut2 — raw from &mut survives a read of the base
// local (SB-specific; Tree Borrows rejects this).
// expected: ok
// rewrites: scenario extracted

fn main() {
    unsafe {
        let mut root = 0;
        let to = &mut root as *mut i32;
        *to = 0;
        let _val = root;
        *to = 0;
    }
}
