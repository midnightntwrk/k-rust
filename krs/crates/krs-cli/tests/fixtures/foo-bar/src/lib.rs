//! Minimal authored language used by the crate-local CLI integration test.

#[krs::sort(alias = Obj, parents = [krs::KResult])]
pub trait ObjSort: krs::KResultSort {}
pub type Obj = krs::Term<dyn ObjSort>;

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
pub fn foo_to_bar(Foo: krs::Term<dyn ObjSort>) -> krs::Term<dyn ObjSort> {
    Bar
}
