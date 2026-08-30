// The witness shape: the copy's source cell is ALSO a pointer cell that the
// destination chain must read, and the source's tag is a reborrow ABOVE the
// chain's tag on that cell.
fn main() {
    let mut x: usize = 5;
    let mut p: *mut usize = &mut x;
    let q: *mut *mut usize = &mut p;
    unsafe {
        let q2: *mut *mut usize = &mut *q;   // Unique reborrow of p's cell
        let r: *mut usize = q2 as *mut usize; // same cell, viewed as usize
        **q = *r;                             // read via q2's tag, then chain-read via q's
    }
    println!("x = {}", x);
}
