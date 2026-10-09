use k::builtin::KSequence;

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self {
            k: k::k![],
        }
    }
}

mod plain {
    pub fn f() {}
}

pub fn helper() -> KSequence {
    k::k![]
}

#[k::spec_module(name = "ORG-PROOFS", imports = [crate])]
mod proofs {
    use k::Term;
    use k::builtin::{Bool, int};

    #[k::simplification]
    fn lt_irreflexive(k::term![int::lt(value, value)]: Term<Bool>) -> Term<Bool> {
        false
    }
}
