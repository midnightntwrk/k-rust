//! The configured package over `krs-grammar-dependency-rules-base`, whose
//! `double` rule needs this package's configuration: `double 21` is `42`.

use base::Exp;
use k::builtin::KSequence;

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
