//! The four exact, unprioritized simplification lemmas from `IMP-VERIFICATION`.

use k::Term;
use k::builtin::{Bool, bool, int};

#[k::simplification]
fn normalize_gt(k::term![int::gt(lhs, rhs)]: Term<Bool>) -> Term<Bool> {
    int::lt(rhs, lhs)
}

#[k::simplification]
fn normalize_ge(k::term![int::ge(lhs, rhs)]: Term<Bool>) -> Term<Bool> {
    int::le(rhs, lhs)
}

#[k::simplification]
fn normalize_not_lt(k::term![bool::not(int::lt(lhs, rhs))]: Term<Bool>) -> Term<Bool> {
    int::le(rhs, lhs)
}

#[k::simplification]
fn normalize_not_le(k::term![bool::not(int::le(lhs, rhs))]: Term<Bool>) -> Term<Bool> {
    int::lt(rhs, lhs)
}
