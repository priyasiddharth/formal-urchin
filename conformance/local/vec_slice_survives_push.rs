// Local witness: `push` within the capacity writes only the new element
// (through the buffer pointer, no retag of the buffer), so a shared slice
// of the old elements stays valid.
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let mut v: Vec<u32> = Vec::new();
    v.push(1);
    v.push(2);
    let s = &*v as *const [u32];
    v.push(3);
    let _x = unsafe { (*s)[0] };
}
