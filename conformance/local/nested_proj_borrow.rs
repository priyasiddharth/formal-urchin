// LOCAL conformance witness (NOT from the Miri corpus): writing through a
// NESTED projection must not invalidate a live reference to a SIBLING
// field of the intermediate place.
//
// `s.1.1 = 9` writes exactly one cell. Miri/mirlite take a write access
// at that cell only, so `q = &mut s.1.0` survives. The OSEA compiler,
// however, lowers a nonzero-offset projection to an internal
// `Borrow(Mut)` over the WHOLE intermediate place -- here `s.1`, two
// cells -- and that retag performs a write access via the parent tag
// across both, invalidating `q`.
//
// Expected verdict is model-reasoned (this is legal Rust: the two field
// borrows are disjoint); pending real-Miri verification.
fn main() {
    let mut s: (u64, (u64, u64)) = (1, (2, 3));
    let q = &mut s.1.0;
    s.1.1 = 9;
    *q = 8;
    let _ = s.1.1;
}
