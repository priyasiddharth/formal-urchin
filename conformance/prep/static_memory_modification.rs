// derived from miri tests/fail/stacked_borrows/static_memory_modification.rs @ 34d6a7954
// expected (miri): "mutable reference pointing to read-only memory" — a
// validity error. Our model has no read-only memory: the transmute-to-&mut
// retag fails as a write through the frozen shared ref (same line/verdict).
// rewrites: dropped error annotation

static X: usize = 5;

#[allow(mutable_transmutes)]
fn main() {
    let _x = unsafe { std::mem::transmute::<&usize, &mut usize>(&X) };
}
