//! `internal` on a production whose item is not `pub`: non-pub productions are
//! already private to the package's rules.

use k::KResult;
use k::builtin::KSequence;

k::sorts! {
    Exp: KResult;
}

#[k::constructors(sort = Exp, result = KResult, internal)]
#[k::precedence((Hidden))]
enum Aux {
    #[k::syntax("hidden")]
    Hidden(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![Aux::Hidden()] }
    }
}
