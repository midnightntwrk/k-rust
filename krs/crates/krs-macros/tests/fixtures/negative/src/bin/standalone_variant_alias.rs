use renamed_krs as k;

#[k::sort(alias = Expr)]
pub trait ExprSort {} pub type Expr = k::Term<dyn ExprSort>;

#[k::constructors(sort = Expr, result = k::KResult)]
#[k::precedence((False))]
pub enum Boolean {
    False,
}

use Boolean::False as No;

#[k::rule] //~ ERROR the trait bound `Boolean: krs::__KrsRuleApplication<
pub fn bad(No: k::Term<dyn ExprSort>) -> k::Term<dyn ExprSort> {
    No
}

fn main() {}
