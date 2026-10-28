use renamed_krs as k;

#[k::sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = k::Term<dyn ExprSort>;

#[k::constructors(sort = Expr, result = k::KResult)]
#[k::precedence((False))]
pub enum Boolean {
    False,
}

use Boolean::False as No;

#[k::rule]
pub fn bad(No: k::Term<dyn ExprSort>) -> k::Term<dyn ExprSort> { //~ ERROR [krs::expand::not-a-declaration] `Boolean` is not a KRS declaration of this name
    No //~ ERROR [krs::expand::not-a-declaration] `Boolean` is not a KRS declaration of this name
}

fn main() {}
