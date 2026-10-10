use renamed_krs as k;
use renamed_krs::Term;
use renamed_krs::builtin::{Bool, Int};

k::sorts! {
    Exp;
    impl Exp for Int;
}

#[k::constructors(sort = Exp)]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("pick({cond}, {first}, {second})")]
    Pick { cond: Bool, first: Exp, second: Exp },
}

#[k::function(total, sort = S, syntax = "choose({cond}, {then_branch}, {else_branch})")]
pub struct Choose<S: ?Sized> {
    pub cond: Term<Bool>,
    pub then_branch: Term<S>,
    pub else_branch: Term<S>,
}

k::rules! {
    for Exp;
    use ExpSyntax::*;

    pick: Pick(c, x, y) => crate::Choose::<dyn ExpSort> { cond: c, then_branch: x, else_branch: y }; //~ ERROR write `crate::Choose::<Exp>`
}

fn main() {}
