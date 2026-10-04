// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: drop_after_sharing — `x.len()` shares the String; dropping it
// afterwards (a Unique retag of the header, then freeing the buffer) is fine.
// expected: ok
// rewrites: scenario extracted (fn body -> main)

fn main() {
    let x = String::from("hello!");
    let _len = x.len();
}
