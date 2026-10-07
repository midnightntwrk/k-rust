//! Foo-to-bar language with one claim that holds and one that does not, for `krs prove`.

use krs::KResult;
use krs::builtin::KSequence;

krs::sorts! {
    ObjectTerm: KResult;
}

#[krs::constructors(sort = ObjectTerm, result = KResult)]
#[krs::precedence((Foo, Bar))]
pub enum Object {
    #[krs::syntax("foo")]
    Foo(),
    #[krs::syntax("bar")]
    Bar(),
}

#[krs::configuration]
pub struct Machine {
    #[krs::cell]
    pub k: KSequence,
}

impl Machine {
    #[krs::init]
    pub fn init(pgm: ObjectTerm) -> Self {
        Self { k: krs::k![pgm] }
    }
}

krs::rules! {
    for ObjectTerm;
    use Object::*;

    foo_to_bar: Foo() => Bar();
}

mod claims {
    use crate::{Machine, Object};

    /// Holds: the only rule rewrites `foo` to `bar`.
    #[krs::claim(all_paths, label = "foo-reaches-bar")]
    fn foo_reaches_bar(
        krs::cells! {
            k: krs::configuration::KCell(Object::Foo(), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        krs::cells! {
            k: krs::configuration::KCell(Object::Bar(), ..tail),
            ..state
        }
    }

    /// Fails: `bar` is stuck and is not `foo`.
    #[krs::claim(all_paths, label = "bar-reaches-foo")]
    fn bar_reaches_foo(
        krs::cells! {
            k: krs::configuration::KCell(Object::Bar(), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        krs::cells! {
            k: krs::configuration::KCell(Object::Foo(), ..tail),
            ..state
        }
    }
}
