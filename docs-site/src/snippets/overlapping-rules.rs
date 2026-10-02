k::rules! {
    for Object;
    use Syntax::*;

    first_foo : Foo() => Bar();
    second_foo: Foo() => Foo();
}
