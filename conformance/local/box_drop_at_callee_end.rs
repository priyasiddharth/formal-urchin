// Local witness: a Box moved into a function is dropped when that
// function returns (its `Drop` at scope end), so a pointer it hands back
// dangles. Before Box drops were modelled the read succeeded.
// expected: UB at the read (checked against the pinned Miri by
// scripts/live.py)

fn peek(b: Box<i32>) -> *const i32 {
    &*b as *const i32
}

fn main() {
    let p = peek(Box::new(7));
    let _v = unsafe { *p };
}
