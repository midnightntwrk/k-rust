//! Assignment language whose claims name `$`-prefixed program identifiers.
//!
//! K's rule grammar has no lexical syntax for `Id` under `ID-SYNTAX`, so the emitted claims must
//! spell `k::id!("$x")` as `#token("$x","Id")` for `kprove` to read them back.

use krs::KResult;
use krs::builtin::{Id, Int, KSequence, Map, map};

krs::sorts! {
    Expr;
    impl Expr for Id;

    Value: Expr + KResult;
    impl Value for Int;

    Stmt;
}

#[krs::constructors(sort = Stmt, result = KResult)]
#[krs::precedence((Assign))]
pub enum StmtSyntax {
    #[krs::syntax("{name} = {value};")]
    #[krs::strict(value)]
    Assign { name: Id, value: Expr },
}

#[krs::configuration]
pub struct Machine {
    #[krs::cell]
    pub k: KSequence,
    #[krs::cell]
    pub env: Map<Id, Value>,
}

impl Machine {
    #[krs::init]
    pub fn init(pgm: Stmt, env: Map<Id, Value>) -> Self {
        Self {
            k: krs::k![pgm],
            env,
        }
    }
}

krs::rules! {
    for Machine;
    use StmtSyntax::Assign;

    /// Replace an identifier at the head of `k` with its mapped value.
    lookup: {
        k: [name, ..],
        env: { name -> value, .. },
    } => {
        k: [value, ..],
    }
    where name: Id;

    /// Consume a value assignment and update the environment map.
    assign: {
        k: [Assign(name, value), ..],
        env: old_env,
    } => {
        k: [..],
        env: map::update(old_env, name, value),
    }
    where value: Value;
}

mod claims {
    use crate::{Machine, StmtSyntax};
    use krs::map;

    #[krs::claim(all_paths, label = "assign-x")]
    fn assign_x(
        krs::cells! {
            k: krs::configuration::KCell(StmtSyntax::Assign(krs::id!("$x"), 1), tail @ ..),
            env: krs::configuration::Cell(map![.Map]),
            state @ ..
        }: Machine,
    ) -> Machine {
        krs::cells! {
            k: krs::configuration::KCell(..tail),
            env: krs::configuration::Cell(map![krs::id!("$x") -> 1]),
            ..state
        }
    }
}
