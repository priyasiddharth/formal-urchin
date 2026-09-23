// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: mut_derefer — nested derefs adjusted by the derefer pass;
// disjoint field borrows through them stay usable.
// expected: ok
// rewrites: scenario extracted
//           [2026-09-23] restored upstream form under a certificate

fn main() {
    let x = &mut &mut (1, 2);
    let l = &mut x.0;
    *l += 1;
    let _r = &mut x.1;
    *l += 1;
}
