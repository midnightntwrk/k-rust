use renamed_krs as k;
use renamed_krs::Term;
use renamed_krs::builtin::{Bool, Int};

#[k::function(total, sort = S, syntax = "choose({cond}, {then_branch}, {else_branch})")]
pub struct Choose<S: ?Sized> {
    pub cond: Term<Bool>,
    pub then_branch: Term<S>,
    pub else_branch: Term<S>,
}

#[k::equation]
fn choose_true(
    k::term![Choose::<'static> { cond: true, then_branch: a, else_branch: _ }]: Term<Int>, //~ ERROR a turbofish on a term head lists sort markers only
) -> Term<Int> {
    a
}

fn main() {}
