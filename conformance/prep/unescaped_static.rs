// derived from miri tests/fail/stacked_borrows/unescaped_static.rs @ 34d6a7954
// expected: UB at `*ptr_to_first.add(1)` (the element-0 tag does not
// exist at cell 1 — per-cell stacks)
// rewrites: dropped error annotation

static ARRAY: [u8; 2] = [0, 1];

fn main() {
    let ptr_to_first = &ARRAY[0] as *const u8;
    let _val = unsafe { *ptr_to_first.add(1) };
}
