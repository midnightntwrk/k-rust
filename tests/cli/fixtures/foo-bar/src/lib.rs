//! Standalone authored foo-to-bar language used only by the external CLI oracle.

#[krs::sort(alias = ObjectTerm, parents = [krs::KResult])]
pub trait ObjectTermSort: krs::KResultSort {}
pub type ObjectTerm = krs::Term<dyn ObjectTermSort>;

#[krs::constructor(sort = ObjectTerm, syntax = "foo")]
pub struct Foo;

#[krs::constructor(sort = ObjectTerm, syntax = "bar")]
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
pub fn foo_to_bar(Foo: krs::Term<dyn ObjectTermSort>) -> krs::Term<dyn ObjectTermSort> {
    Bar
}
