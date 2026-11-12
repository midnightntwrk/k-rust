//! The configuration initializes `<mode>` with the non-`pub` `ready`, whose
//! precedence group a sentence of this package orders above `after`'s. The
//! sentence stays in `KRS-CONFIGURATION-VISIBILITY` with `after`, a module
//! above the configuration's, so the configuration module cannot declare
//! `ready`: `krs::partition::configuration-visibility`. Without the order,
//! the configuration module declares `ready` and the definition is accepted
//! (`krs-cli --test initializer_calls`).

use base::Exp;
use k::KResult;
use k::builtin::KSequence;

k::sorts! {
    Mode;
}

#[k::constructors(sort = Mode, result = KResult)]
#[k::precedence((Ready) > (After))]
#[rustfmt::skip]
enum ModeSyntax {
    #[k::syntax("ready")]
    Ready(),
    #[k::syntax("after {mode}")]
    After { mode: Mode },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub mode: Mode,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            mode: ModeSyntax::Ready(),
        }
    }
}
