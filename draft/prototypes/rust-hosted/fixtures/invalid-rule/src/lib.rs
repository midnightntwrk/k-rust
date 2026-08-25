#![allow(unused_imports)]

use krs::{rule, Term};

pub trait Expr {}

#[rule]
fn invalid(_: Term<dyn Expr>) -> Term<dyn Expr> {
    Unknown
}
