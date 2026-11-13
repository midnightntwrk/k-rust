//! `k::is!` in a rule subject: a sort predicate is a function call, so it cannot be matched.

use k::KResult;
use k::Term;
use k::builtin::{Bool, Int, KSequence, int};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bool, Int;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Chk, Prj))]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("chk({value})")]
    Chk { value: Exp },
    #[k::syntax("prj({e})")]
    Prj { e: Exp },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

#[k::rule]
fn chk(
    k::term![ExpSyntax::Chk {
        value: k::is!(Int, x)
    }]: Term<Exp>,
) -> Term<Exp> {
    x
}

#[k::rule]
fn prj(k::term![ExpSyntax::Prj { e }]: Term<Exp>) -> Term<Exp> {
    int::add(k::project!(Int, e), 1)
}
