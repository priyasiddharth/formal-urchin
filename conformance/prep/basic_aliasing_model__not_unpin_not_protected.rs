// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: not_unpin_not_protected — `&mut !Unpin` gets no protector, so
// a closure passed as a `fn` pointer may deallocate the referent while the
// caller still holds the reference.
// expected: ok
// rewrites: scenario extracted (verbatim; the closure stays)

fn main() {
    // `&mut !Unpin`, at least for now, does not get `noalias` nor `dereferenceable`, so we also
    // don't add protectors. (We could, but until we have a better idea for where we want to go with
    // the self-referential-coroutine situation, it does not seem worth the potential trouble.)
    use std::marker::PhantomPinned;

    pub struct NotUnpin(#[allow(dead_code)] i32, PhantomPinned);

    fn inner(x: &mut NotUnpin, f: fn(&mut NotUnpin)) {
        // `f` is allowed to deallocate `x`.
        f(x)
    }

    inner(Box::leak(Box::new(NotUnpin(0, PhantomPinned))), |x| {
        let raw = x as *mut _;
        drop(unsafe { Box::from_raw(raw) });
    });
}
