//! `k::rewrite!` is a term island of a single-body rule's subject; in
//! ordinary Rust code it is a compile error.

use k::builtin::{Id, Int, KSequence, Map};
use k::{Term, map};

k::sorts! {
    Stmt;
}

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Assign))]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("{name} = {value};")]
    Assign { name: Id, value: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map<Id, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: k::map![],
        }
    }
}

/// Not a rule: the island has no subject to rewrite.
pub fn outside() {
    k::rewrite!(StmtSyntax::Assign(name, value) => ());
}
