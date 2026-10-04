// Local witness: `format!` reads its argument through the reference it is
// given (`<&mut String as Debug>::fmt` reborrows `**self`), so formatting
// through a `&mut` that a sibling `&mut` popped is UB.
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut s = String::from("hi");
    let p = &mut s as *mut String;
    let a = unsafe { &mut *p };
    let _b = unsafe { &mut *p };
    let _f = format!("{:?}", a);
}
