use renamed_krs as k;
use renamed_krs::Term;
use renamed_krs::builtin::{Bool, Int};

k::sorts! {
    Exp;
    impl Exp for Int;
}

#[k::function(total, sort = S, syntax = "choose({cond}, {then_branch}, {else_branch})")]
pub struct Choose<S: ?Sized> {
    pub cond: Term<Bool>,
    pub then_branch: Term<S>,
    pub else_branch: Term<S>,
}

#[k::equation]
fn choose_true(
    k::term![Choose::<Exp> { cond: true, then_branch: a, else_branch: _ }]: Term<Exp>, //~ ERROR not the alias `Exp`: write `Choose::<dyn ExpSort>`
) -> Term<Exp> {
    a
}

#[k::equation]
fn choose_true_marker(
    k::term![Choose::<dyn ExpSort> { cond: true, then_branch: a, else_branch: _ }]: Term<Exp>,
) -> Term<Exp> {
    a
}

#[k::equation]
fn choose_true_int(
    k::term![Choose::<Int> { cond: true, then_branch: a, else_branch: _ }]: Term<Int>,
) -> Term<Int> {
    a
}

fn main() {}
