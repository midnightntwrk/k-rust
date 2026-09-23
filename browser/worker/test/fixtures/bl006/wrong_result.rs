use k::KResult;
use k::builtin::KSequence;

k::sorts! {
    Object: KResult;
}

#[k::constructors(sort = Object, result = KResult)]
#[k::precedence((Foo))]
pub enum Syntax {
    #[k::syntax("foo")]
    Foo(),
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

    // The rule declares Object but returns a builtin Int literal.
    wrong_result: Foo() => 1;
}
