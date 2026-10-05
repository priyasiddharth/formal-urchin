// Local witness: a local array of references read at an index known only
// when the program runs. The loader lowers `a[i]` as Miri's place
// projection: a pointer to `a[0]` with `a`'s own tag (`addrOf`, no retag),
// moved by `i`, then the load — whose reference value is retagged as any
// reference load is. The branch makes the certificate check the value.
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let x = 1u32;
    let y = 2u32;
    let a = [&x, &y];
    let i = *Box::new(1usize);
    let r = a[i];
    if *r != 2 {
        unsafe { std::hint::unreachable_unchecked() }
    }
}
