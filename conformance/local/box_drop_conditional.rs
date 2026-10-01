// Local witness for drop matching against Miri's certificate: `b` is
// dropped on one branch only (by `drop`), so at the end of `main` only
// `c` is still owned and dropped. The certificate records both Box drops
// in `main`, each after the branch it follows; the lowering must make the
// same two drops at the same points — not three (b again at scope end),
// not one.
// expected: ok (checked against the pinned Miri by scripts/live.py)

fn pick(n: i32) -> i32 {
    n
}

fn main() {
    let b = Box::new(1i32);
    let c = Box::new(2i32);
    if pick(1) > 0 {
        drop(b);
    }
    let _v = *c;
}
