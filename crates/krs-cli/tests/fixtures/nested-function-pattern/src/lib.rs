//! The foo-bar language plus one equation that k-rust rejects on every backend.

#[krs::sort]
pub trait KItem {}

#[krs::sort]
pub trait KResult: KItem {}

#[krs::sort]
pub trait Obj: KResult {}

#[krs::constructor(sort = Obj, syntax = "foo")]
pub struct Foo;

#[krs::constructor(sort = Obj, syntax = "bar")]
pub struct Bar;

#[krs::configuration(root = "machine")]
pub struct Machine {
    pub k: krs::configuration::KCell<krs::builtin::KSequence>,
}

impl Machine {
    #[krs::init]
    pub fn init() -> Self {
        Self {
            k: krs::configuration::KCell::new(krs::k![Foo]),
        }
    }
}

#[krs::rule]
pub fn foo_to_bar(Foo: krs::Term<dyn Obj>) -> krs::Term<dyn Obj> {
    Bar
}

#[krs::function(total, sort = krs::builtin::Int, syntax = "#twist({value})")]
pub struct Twist {
    pub value: krs::Term<krs::builtin::Int>,
}

#[krs::equation]
fn twist(krs::term![Twist(value)]: krs::Term<krs::builtin::Int>) -> krs::Term<krs::builtin::Int> {
    value
}

// K forbids a function symbol under the defining symbol of an equation's
// left side unless the sentence is a simplification.
#[krs::equation]
fn twist_twice(
    krs::term![Twist(Twist(value))]: krs::Term<krs::builtin::Int>,
) -> krs::Term<krs::builtin::Int> {
    value
}
