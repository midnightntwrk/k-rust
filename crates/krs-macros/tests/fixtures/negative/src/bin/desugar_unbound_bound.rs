use krs_macros::{constructor, desugar, sort};
use renamed_krs::Term;

#[sort]
pub trait Stmt {}

#[constructor(sort = Stmt, syntax = "twice {body}")]
#[renamed_krs::desugar]
pub struct Twice {
    pub body: Term<dyn Stmt>,
}

#[constructor(sort = Stmt, syntax = "{first} {second}")]
pub struct Seq {
    pub first: Term<dyn Stmt>,
    pub second: Term<dyn Stmt>,
}

#[desugar(unbound_variables = [body])] //~ ERROR `body` is bound by the pattern; `unbound_variables` lists only result names the pattern does not bind
fn twice(Twice { body }: Term<dyn Stmt>) -> Term<dyn Stmt> {
    Seq { first: body, second: body }
}

fn main() {}
