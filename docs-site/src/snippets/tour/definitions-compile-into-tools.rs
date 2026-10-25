//! A light that shows red or green, and one transition: red becomes green.

// [!region definition]
use k::KItem;
use k::builtin::KSequence;

k::sorts! {
    Light: KItem;
}

#[k::constructors(sort = Light, result = KResult)]
pub enum LightSyntax {
    #[k::syntax("red")]
    Red(),
    #[k::syntax("green")]
    Green(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Light) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::rules! {
    for Light;
    use LightSyntax::*;

    // [!region rule]
    red_to_green: Red() => Green();
    // [!endregion rule]
}
// [!endregion definition]
