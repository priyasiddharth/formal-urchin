// LOCAL conformance witness (NOT from the Miri corpus): evaluating `*p`
// reads `p` as an operand — once `p` is memory-resident (its address was
// taken), that read disables a `&mut` reborrow of the pointer variable
// itself. Expected verdict is model-reasoned; pending verification
// against real Miri (which performs the same operand read).
fn main() {
    unsafe {
        let mut x = 1u64;
        let mut p = &raw mut x;
        let qr = &raw mut p;
        let q = &mut *qr;
        *p = 5;
        let _v = **q; // UB: the read of `p` above disabled `q`
    }
}
