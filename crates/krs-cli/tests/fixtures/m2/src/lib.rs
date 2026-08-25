//! Minimal authored language used by the crate-local CLI integration test.

#[krs::sort]
pub trait KItem {}

#[krs::sort]
pub trait KResult: KItem {}

#[krs::sort]
pub trait M2Obj: KResult {}

#[krs::constructor(sort = M2Obj, syntax = "foo")]
pub struct Foo;

#[krs::constructor(sort = M2Obj, syntax = "bar")]
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
pub fn foo_to_bar(Foo: krs::Term<dyn M2Obj>) -> krs::Term<dyn M2Obj> {
    Bar
}
