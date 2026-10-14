//! Two individually valid rules whose computation heads overlap.

use k::KResult;
use k::builtin::KSequence;

k::sorts! {
    Object: KResult;
}

#[k::constructors(sort = Object, result = KResult)]
#[k::precedence((Foo, Bar))]
pub enum Syntax {
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
            k: k::k![Syntax::Foo()],
        }
    }
}

k::rules! {
    for Object;
    use Syntax::*;

    first_foo : Foo() => Bar();
    second_foo: Foo() => Foo();
}
