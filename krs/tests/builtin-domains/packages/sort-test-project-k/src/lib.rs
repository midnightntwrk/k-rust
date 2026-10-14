//! `k::project!(K, ..)`: K generates no projection into `K`.

use k::KResult;
use k::Term;
use k::builtin::{Bool, Int, KSequence};

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
fn chk(k::term![ExpSyntax::Chk { value }]: Term<Exp>) -> Term<Exp> {
    k::is!(Int, value)
}

#[k::rule]
fn prj(k::term![ExpSyntax::Prj { e }]: Term<Exp>) -> Term<Exp> {
    k::project!(KSequence, e)
}
