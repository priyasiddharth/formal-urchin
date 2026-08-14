// derived from miri tests/fail/stacked_borrows/pointer_smuggling.rs @ 34d6a7954
// expected: UB at `*PTR` read in fun2 (direct write via val invalidated it)
// rewrites: dropped error annotation

static mut PTR: *mut u8 = 0 as *mut _;

fn fun1(x: &mut u8) {
    unsafe {
        PTR = x;
    }
}

fn fun2() {
    let _x = unsafe { *PTR };
}

fn main() {
    let mut val = 0;
    let val = &mut val;
    fun1(val);
    *val = 2;
    fun2();
}
