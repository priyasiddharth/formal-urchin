// derived from miri tests/pass/both_borrows/interior_mutability.rs @ 34d6a7954
// scenario: rust_issue_68303 — a RefMut into an Option's payload stays
// usable across a shared read of the Option.
// expected: ok
// rewrites: scenario extracted (fn body -> main); the body is upstream.
//           The prelude `Option` is shadowed by a user-written one whose
//           methods are std's bodies (core/src/option.rs; `unwrap_failed()`
//           -> `panic!`), so Charon translates them and Miri's certificate
//           records their frames and branches (2026-09-30).
use std::cell::RefCell;

enum Option<T> {
    None,
    Some(T),
}
use Option::*;

impl<T> Option<T> {
    fn as_ref(&self) -> Option<&T> {
        match *self {
            Some(ref x) => Some(x),
            None => None,
        }
    }
    fn unwrap(self) -> T {
        match self {
            Some(val) => val,
            None => panic!("called `Option::unwrap()` on a `None` value"),
        }
    }
    fn is_some(&self) -> bool {
        matches!(*self, Some(_))
    }
}

fn main() {
    let optional = Some(RefCell::new(false));
    let mut handle = optional.as_ref().unwrap().borrow_mut();
    assert!(optional.is_some());
    *handle = true;
}
