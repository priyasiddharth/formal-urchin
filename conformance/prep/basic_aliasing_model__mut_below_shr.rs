// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: mut_below_shr — transmuting &&i32 to &&mut i32 is fine.
// expected: ok
// rewrites: scenario extracted

fn main() {
    let x = 0;
    let y = &x;
    let p = unsafe { core::mem::transmute::<&&i32, &&mut i32>(&y) };
    let r = &**p;
    let _val = *r;
}
