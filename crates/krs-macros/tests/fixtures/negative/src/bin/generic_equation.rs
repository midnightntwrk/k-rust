use renamed_krs as k;
use renamed_krs::Term;
use renamed_krs::builtin::Bool;

#[k::function(total, sort = S, syntax = "choose({cond}, {then_branch}, {else_branch})")]
pub struct Choose<S: ?Sized> {
    pub cond: Term<Bool>,
    pub then_branch: Term<S>,
    pub else_branch: Term<S>,
}

#[k::equation]
fn choose_true<S: ?Sized>( //~ ERROR K rules never quantify over sorts
    k::term![Choose::<S> { cond: true, then_branch: a, else_branch: _ }]: Term<S>,
) -> Term<S> {
    a
}

fn main() {}
