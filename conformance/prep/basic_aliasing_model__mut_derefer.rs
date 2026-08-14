// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: mut_derefer — nested derefs adjusted by the derefer pass;
// disjoint field borrows through them stay usable.
// expected: ok
// rewrites: scenario extracted; `*l += 1` -> read then write

fn main() {
    let x = &mut &mut (1, 2);
    let l = &mut x.0;
    let _t = *l;
    *l = 2;
    let _r = &mut x.1;
    let _t2 = *l;
    *l = 3;
}
