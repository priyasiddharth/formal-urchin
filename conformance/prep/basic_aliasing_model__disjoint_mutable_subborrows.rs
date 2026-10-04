// derived from miri tests/pass/both_borrows/basic_aliasing_model.rs @ 34d6a7954
// scenario: disjoint_mutable_subborrows — two `&mut` to disjoint fields of
// one struct, both made through the same raw pointer, stay usable: a push
// through each, then both read by `format!`.
// expected: ok
// rewrites: scenario extracted (fn body -> main)

fn main() {
    struct Foo {
        a: String,
        b: Vec<u32>,
    }

    unsafe fn borrow_field_a<'a>(this: *mut Foo) -> &'a mut String {
        &mut (*this).a
    }

    unsafe fn borrow_field_b<'a>(this: *mut Foo) -> &'a mut Vec<u32> {
        &mut (*this).b
    }

    let mut foo = Foo { a: "hello".into(), b: vec![0, 1, 2] };

    let ptr = &mut foo as *mut Foo;

    let a = unsafe { borrow_field_a(ptr) };
    let b = unsafe { borrow_field_b(ptr) };
    b.push(4);
    a.push_str(" world");
    assert_eq!(format!("{:?} {:?}", a, b), r#""hello world" [0, 1, 2, 4]"#);
}
