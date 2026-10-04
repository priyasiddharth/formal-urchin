// Local witness: `format!` with Display and Debug placeholders of integers,
// `&str` and `String`, and literal pieces; `assert_eq!` makes the
// certificate check the model's output bytes.
// expected: ok (checked against the pinned Miri by scripts/live.py)
fn main() {
    let n: u8 = 7;
    let s = String::from("ab");
    let t = format!("{}-{:?}:{}{:?}", n, "x", s, s);
    assert_eq!(t, "7-\"x\":ab\"ab\"");
}
