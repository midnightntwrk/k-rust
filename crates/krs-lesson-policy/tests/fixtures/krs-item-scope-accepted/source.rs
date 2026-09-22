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
