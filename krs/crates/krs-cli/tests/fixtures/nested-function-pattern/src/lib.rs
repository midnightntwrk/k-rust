//! The foo-bar language plus a function, its equation, and one `raw_k!` equation that applies the
//! function below the root of its pattern.
//!
//! KRS does not read a `raw_k!` sentence: its text is K the native frontend judges, so KRS accepts
//! this package, and the native frontend refuses the raw equation on every backend. An equation
//! matches its argument patterns as written, and an application of `#twist` is evaluated wherever
//! it occurs, so the raw pattern describes a term that never occurs.

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

#[krs::function(total, sort = krs::builtin::Int, syntax = "#twist({value})")]
pub struct Twist {
    pub value: krs::Term<krs::builtin::Int>,
}

#[krs::equation]
fn twist(krs::term![Twist(value)]: krs::Term<krs::builtin::Int>) -> krs::Term<krs::builtin::Int> {
    value
}

krs::raw_k!(r"rule # twist ( # twist ( V:Int ) ) => V:Int");
