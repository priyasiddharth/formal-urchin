// Local witness: a branch inside a closure body, decided at run time; the
// certificate records it in the closure's own frame (`{closure#0}`).
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn call<F: Fn(u32) -> u32>(f: F, v: u32) -> u32 {
    f(v)
}
fn main() {
    let k = *Box::new(3u32);
    let r = call(|x| if x > k { x - k } else { k - x }, 5);
    if r != 2 { panic!() }
}
