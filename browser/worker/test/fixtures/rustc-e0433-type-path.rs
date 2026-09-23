//! The smallest complete idiomatic KRS definition used by the language tour.
//!
//! `Foo` and `Bar` are symbolic object-language terms.
//! The sole transition rewrites `foo` at the head of the computation to `bar`.

// [!region definition]
use k::KResult;
use k::builtin::KSequence;

k::sorts! {
    M2Obj: KResult;
}

#[k::constructors(sort = missing::M2Obj, result = KResult)]
#[k::precedence((Foo, Bar))]
pub enum Object {
    #[k::syntax("foo")]
    Foo(),
    #[k::syntax("bar")]
    Bar(),
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self {
            k: k::k![Object::Foo()],
        }
    }
}

k::rules! {
    for M2Obj;
    use Object::*;

    // [!region orientation-rule]
    foo_to_bar: Foo() => Bar();
    // [!endregion orientation-rule]
}
// [!endregion definition]
