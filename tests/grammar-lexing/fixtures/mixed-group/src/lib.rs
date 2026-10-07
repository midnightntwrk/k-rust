//! One precedence group holds an `internal` production and a program-syntax
//! production; K priorities apply per module, so KRS rejects the mix.

use k::KResult;
use k::builtin::KSequence;

k::sorts! {
    Exp: KResult;
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence((Visible, Hidden))]
pub enum Ops {
    #[k::syntax("visible")]
    Visible(),
    #[k::syntax("hidden", internal)]
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
        Self { k: k::k![Ops::Visible()] }
    }
}
