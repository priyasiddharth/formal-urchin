// Local witness: reading an enum variant's field through a place
// projection (`(o as Some).0`, what a `match` arm binding compiles to).
// The payload lives after the discriminant, so the binding must read
// cell 1, not cell 0; reading the discriminant word as the reference
// would make the write through `r` a wild access.
// expected: ok (checked against the pinned Miri by scripts/live.py)

fn main() {
    let mut v = 5i32;
    let o: Option<&mut i32> = Some(&mut v);
    match o {
        Some(r) => *r = 6,
        None => {}
    }
    let _w = v;
}
