// LOCAL conformance witness (NOT from the Miri corpus): Rust's SPLIT
// BORROWS — all three fields of a struct mutably borrowed AT ONCE, with
// interleaved writes through the three references. Legal Rust (field
// borrows are disjoint places) and OK under Stacked Borrows with no
// special case: retags are per CELL, so the three Unique tags live on
// disjoint stacks and are never foreign to one another. A load-bearing
// idiom with no other coverage in the suite (the corpus aliasing tests
// exercise conflicts, not coexistence).
// Expected verdict is model-reasoned; pending real-Miri verification.
fn main() {
    let mut s: (u64, u64, u64) = (1, 2, 3);
    let p0 = &mut s.0;
    let p1 = &mut s.1;
    let p2 = &mut s.2;
    *p1 = 20;
    *p0 = 10;
    *p2 = 30;
    *p1 = 21;
    let _v = (*p0, *p1, *p2);
}
