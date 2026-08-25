use krs::{Term, cells, constructor, ml, rule, sort, term};

#[sort]
pub trait KItem {}

#[sort]
pub trait Expr: KItem {}

#[constructor(sort = Expr, syntax = "foo")]
pub struct Foo;

#[constructor(sort = Expr, syntax = "bar")]
pub struct Bar;

#[rule]
pub fn step(Foo: Term<dyn Expr>) -> Term<dyn Expr> {
    Bar
}

pub fn inspect_macro_payloads() -> (&'static str, &'static str, &'static str) {
    (term!(Foo), cells!((Foo, Bar)), ml!(true && true))
}

pub fn ordinary_reference() -> Foo {
    Foo
}
