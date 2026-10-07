//! An unsigned package whose program syntax imports the signed package's.

use k::Term;
use k::builtin::KSequence;

#[k::sort]
pub trait Top {}

#[k::constructor(sort = Top, syntax = "top {value}")]
pub struct Wrap {
    pub value: Term<dyn signed_base::Num>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![] }
    }
}
