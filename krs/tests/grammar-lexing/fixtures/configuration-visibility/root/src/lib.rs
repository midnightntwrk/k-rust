//! The configuration initializes `<mode>` with the non-`pub` `ready`, which
//! lives in `KRS-CONFIGURATION-VISIBILITY`, a module the configuration module
//! cannot import: `krs::partition::configuration-visibility`.

use base::Exp;
use k::KResult;
use k::builtin::KSequence;

k::sorts! {
    Mode;
}

#[k::constructors(sort = Mode, result = KResult)]
#[k::precedence((Ready))]
#[rustfmt::skip]
enum ModeSyntax {
    #[k::syntax("ready")]
    Ready(),
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
