//! `k::rewrite!` belongs to a single-body rule; a rule with a result already
//! states the after-state.

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

#[k::rule]
fn assign(
    name: Term<Id>,
    value: Term<Int>,
    environment: Term<Map>,
    k::cells! {
        k: k::configuration::KCell(k::rewrite!(StmtSyntax::Assign(name, value) => ()), tail @ ..),
        env: k::configuration::Cell(environment),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![environment [ name <- value ]]),
        ..state
    }
}
