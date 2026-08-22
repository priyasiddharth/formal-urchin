// LOCAL conformance witness (NOT from the Miri corpus): borrowing a local
// whose contents were never WRITTEN is legal Rust and reads nothing, so it
// is OK under Stacked Borrows — Miri allocates the local at `StorageLive`,
// independently of any write. `let x: u64; &raw const x` is rejected by
// rustc (E0381), so the witness goes through `MaybeUninit`, whose
// `uninit()` is an empty union aggregate. The lowering drops
// `StorageLive`/`StorageDead` and relies on first-assignment for
// allocation; this probes whether that first assignment can be an
// access-free one. Expected verdict is model-reasoned; pending
// verification against real Miri.
use std::mem::MaybeUninit;
fn main() {
    let x: MaybeUninit<u64> = MaybeUninit::uninit();
    let p = &raw const x;
    let _q = p;
}
