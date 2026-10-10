//! An unsigned package whose program syntax imports the signed package's.

use k::Term;
use k::builtin::KSequence;

#[k::sort(alias = Top)]
pub trait TopSort {} pub type Top = k::Term<dyn TopSort>;

#[k::constructor(sort = Top, syntax = "top {value}")]
pub struct Wrap {
    pub value: Term<dyn signed_base::NumSort>,
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
