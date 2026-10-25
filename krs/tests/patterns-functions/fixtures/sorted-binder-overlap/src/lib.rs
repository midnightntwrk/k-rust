//! A type lookup whose known-type equation binds its argument at the
//! field's sort, `MaybeTy`, so it also matches `TyUnknown`, which the
//! unknown-type equation answers: both define `Lookup(_, TyUnknown)` at one
//! priority with different results. Declaring the binder `Term<Ty>` makes
//! the patterns disjoint.

use k::Term;
use k::builtin::{Int, KSequence, Map, map};

k::sorts! {
    MaybeTy: k::KItem;
    Ty: MaybeTy;
    Info: k::KItem;
}

#[k::constructors(sort = Ty, result = k::KResult)]
pub enum Type {
    #[k::syntax("ty({id})")]
    Id { id: Int },
}

#[k::constructors(sort = MaybeTy, result = k::KResult)]
pub enum Maybe {
    #[k::syntax("tyUnknown")]
    TyUnknown,
}

#[k::constructors(sort = Info, result = k::KResult)]
pub enum TypeInfo {
    #[k::syntax("voidType")]
    Void,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::k![] }
    }
}

/// The type information of a possibly unknown type.
#[k::function(total, internal)]
pub fn Lookup(types: Term<Map>, ty: Term<MaybeTy>) -> Term<Info>;

#[k::equation]
fn lookup_known(k::term![Lookup(types, ty)]: Term<Info>) -> Term<Info> {
    k::term![map::get(types, ty)]
}

#[k::equation]
fn lookup_unknown(k::term![Lookup(_, Maybe::TyUnknown())]: Term<Info>) -> Term<Info> {
    TypeInfo::Void()
}
