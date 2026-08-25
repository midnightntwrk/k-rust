use krs::{Term, constructor, rule, sort};

#[sort]
pub trait KItem {}

#[sort]
pub trait Expr: KItem {}

#[sort]
pub trait KResult: KItem {}

// The ordinary Rust trait graph contains a diamond. KRS records both direct
// edges and computes path-independent semantic closure itself.
#[sort]
pub trait Value: Expr + KResult {}

#[constructor(sort = Expr, syntax = "foo")]
pub struct Foo;

#[constructor(sort = Expr, syntax = "bar")]
pub struct Bar;

#[rule]
pub fn step(Foo: Term<dyn Expr>) -> Term<dyn Expr> {
    Bar
}

pub mod nested {
    use krs::{constructor, rule, Term};

    use crate::Expr;

    #[constructor(sort = Expr, syntax = "nested")]
    pub struct Nested;

    #[rule]
    pub fn nested_step(Nested: Term<dyn Expr>) -> Term<dyn Expr> {
        Nested
    }
}

