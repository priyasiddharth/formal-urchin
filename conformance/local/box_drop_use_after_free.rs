// Local witness: `drop(b)` frees the Box's allocation (Box drop glue,
// 2026-10-01), so reading through a pointer taken from it afterwards is a
// use after free. Before Box drops were modelled the read succeeded.
// expected: UB at the read (checked against the pinned Miri by
// scripts/live.py)

fn main() {
    let b = Box::new(5i32);
    let p = &*b as *const i32;
    drop(b);
    let _v = unsafe { *p };
}
