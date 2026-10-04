// Local witness: `&mut *v` (`DerefMut`) is a Unique retag of the elements,
// which pops a shared slice of them taken earlier.
// expected: ub (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut v: Vec<u32> = Vec::new();
    v.push(1);
    v.push(2);
    let s = &*v as *const [u32];
    let m: &mut [u32] = &mut *v;
    m[1] = 7;
    let _x = unsafe { (*s)[0] };
}
