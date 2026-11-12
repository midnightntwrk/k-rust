//! K tutorial lesson 1.22: matching-logic predicates (KF-039).
//!
//! K has two kinds of truth. `int::eq(a, b)` is an object `Bool`, a value a
//! rule computes; `ml::equals(a, b)` is K's `{ A #Equals B }`, a statement
//! about what two patterns denote, which only the prover reads. Claim
//! conditions and simplification lemmas may be such predicates.
//!
//! The package depends on the lesson's language. Its own definition module
//! adds only a regex token for `$`-prefixed identifiers to `Id`, as the
//! lesson's `LESSON-22-SPEC-SYNTAX` does, so the claims print `$a` bare.
//!
//! - `KRS-L22-LEMMAS` holds two predicate simplifications: `update-injective`,
//!   the lesson's map lemma `{ M[K <- V] #Equals M[K <- W] } => { V #Equals W }`,
//!   and `pf-defined`, the definedness lemma `#Ceil(pf(X)) => { true #Equals
//!   X >Int 0 }`.
//! - `KRS-L22-CLAIMS` imports them and states the lesson's `branch` claim (both
//!   branches of an `if` on symbolic `$a < $b` store some `?C` that equals `A`
//!   or `B`), `div-eq` (an ML precondition `#Not({ B #Equals 0 })` and an ML
//!   postcondition `{ ?R #Equals A /Int B }`), `div-small`, whose
//!   postcondition quantifies with `#Exists`, and `equals-two-joins`, an
//!   equality of operands whose sorts `Left` and `Right` have two least common
//!   supersorts, `Both1` and `Both2`.
//! - `KRS-L22-ABLATION` states `branch` again without the lemmas. It still
//!   holds: a prover that matches the two stores key by key finds `?C` without
//!   `update-injective`, while one that needs the lemma to equate the stores
//!   cannot close it.

use k::builtin::{Int, Map, bool, int, map};
use k::ml::{self, Predicate};
use k::{KItem, Term};
use krs_verification_surface_l22::{Machine, Op, Pf, StmtSyntax};

/// Every `$`-prefixed identifier, as the lesson's spec syntax declares them.
#[k::token(regex = r"\$[a-zA-Z0-9_]+")]
pub type DollarId = k::builtin::Id;

// `Left` and `Right` are both below `Both1` and `Both2`, so they have two least common
// supersorts and no one least; they meet at their common subsort `Mid`.
k::sorts! {
    Both1;
    Both2;
    Left: Both1 + Both2;
    Right: Both1 + Both2;
    Mid: Left + Right;
}

/// Lemmas: predicate simplifications, which the prover trusts. A
/// simplification is an unchecked axiom, not a match arm.
#[k::spec_module(name = "KRS-L22-LEMMAS", imports = [crate])]
pub mod lemmas {
    use super::{KItem, Map, Pf, Predicate, int, map, ml};

    /// Definedness: `pf(x)` denotes a value exactly when `x` is positive.
    #[k::simplification]
    fn pf_defined(k::term![ml::ceil(Pf(x))]: Predicate) -> Predicate {
        ml::equals(true, int::gt(x, 0))
    }

    /// Lesson 1.22's lemma: updating one key of one map to two values gives
    /// equal maps only if the values are equal.
    #[k::simplification]
    fn update_injective(
        m: k::Term<Map>,
        key: k::Term<KItem>,
        v: k::Term<KItem>,
        w: k::Term<KItem>,
        k::term![ml::equals(map::update(m, key, v), map::update(m, key, w))]: Predicate,
    ) -> Predicate {
        ml::equals(v, w)
    }
}

/// The lesson's claims, proved with the lemmas.
#[k::spec_module(name = "KRS-L22-CLAIMS", imports = [lemmas])]
mod spec {
    use super::{Int, Left, Machine, Map, Op, Right, StmtSyntax, Term, bool, int, map, ml};

    /// Lesson 1.22 claim 3: both branches of an `if` on a symbolic condition
    /// store some `c` that is `a` or `b`. Only `update-injective` lets the
    /// prover see that the stores agree exactly when `c` is `b`.
    #[k::claim(all_paths, label = "branch")]
    #[k::exists(c: Int)]
    #[k::ensures(ml::equals(true, bool::or(int::eq(c, a), int::eq(c, b))))]
    fn branch(
        a: Term<Int>,
        b: Term<Int>,
        s: Term<Map>,
        k::cells! {
            k: k::configuration::KCell(
                StmtSyntax::Seq(
                    StmtSyntax::Assign(k::id!("$a"), a),
                    StmtSyntax::Seq(
                        StmtSyntax::Assign(k::id!("$b"), b),
                        StmtSyntax::If(
                            Op::Lt(k::id!("$a"), k::id!("$b")),
                            StmtSyntax::Assign(k::id!("$c"), k::id!("$b")),
                            StmtSyntax::Assign(k::id!("$c"), k::id!("$a")),
                        ),
                    ),
                ),
                tail @ ..
            ),
            store: k::configuration::Cell(s),
            state @ ..
        }: Machine,
    ) -> Machine {
        k::cells! {
            k: k::configuration::KCell(..tail),
            store: k::configuration::Cell(map::update(
                map::update(map::update(s, k::id!("$a"), a), k::id!("$b"), b),
                k::id!("$c"),
                c,
            )),
            ..state
        }
    }

    /// An ML precondition and an ML postcondition: `div` rewrites to the
    /// quotient whenever the divisor does not denote zero.
    #[k::claim(all_paths, label = "div-eq")]
    #[k::exists(r: Int)]
    #[k::requires(ml::not(ml::equals(b, 0)))]
    #[k::ensures(ml::equals(r, int::div(a, b)))]
    fn div_eq(
        a: Term<Int>,
        b: Term<Int>,
        k::cells! { k: k::configuration::KCell(Op::Div(a, b), tail @ ..), state @ .. }: Machine,
    ) -> Machine {
        k::cells! { k: k::configuration::KCell(r, ..tail), ..state }
    }

    /// A quantified postcondition: halving a number below ten gives some `q`
    /// below five.
    #[k::claim(all_paths, label = "div-small")]
    #[k::exists(r: Int)]
    #[k::requires(ml::and(ml::equals(true, int::le(0, a)), ml::equals(true, int::lt(a, 10))))]
    #[k::ensures(ml::exists(|q: Int| ml::and(ml::equals(r, q), ml::equals(true, int::lt(q, 5)))))]
    fn div_small(
        a: Term<Int>,
        k::cells! { k: k::configuration::KCell(Op::Div(a, 2), tail @ ..), state @ .. }: Machine,
    ) -> Machine {
        k::cells! { k: k::configuration::KCell(r, ..tail), ..state }
    }

    /// An equality of operands of sorts `Left` and `Right`, which have two least common
    /// supersorts, `Both1` and `Both2`. It has one meaning at either: sort injections are
    /// injective and compose, so the injected operands are equal at one common supersort
    /// exactly when they are at every other, which is where both are the same value of their
    /// common subsort `Mid`. The claim's end state is its start, which the condition narrows to
    /// such values.
    #[k::claim(all_paths, label = "equals-two-joins")]
    #[k::requires(ml::equals(l, r))]
    fn equals_two_joins(
        l: Term<Left>,
        r: Term<Right>,
        k::cells! { k: k::configuration::KCell(l, r, tail @ ..), state @ .. }: Machine,
    ) -> Machine {
        k::cells! { k: k::configuration::KCell(l, r, ..tail), ..state }
    }
}

/// The ablation: `branch` without the lemmas, which holds all the same.
#[k::spec_module(name = "KRS-L22-ABLATION", imports = [crate])]
mod ablation {
    use super::{Int, Machine, Map, Op, StmtSyntax, Term, bool, int, map, ml};

    #[k::claim(all_paths, label = "branch-ablation")]
    #[k::exists(c: Int)]
    #[k::ensures(ml::equals(true, bool::or(int::eq(c, a), int::eq(c, b))))]
    fn branch_ablation(
        a: Term<Int>,
        b: Term<Int>,
        s: Term<Map>,
        k::cells! {
            k: k::configuration::KCell(
                StmtSyntax::Seq(
                    StmtSyntax::Assign(k::id!("$a"), a),
                    StmtSyntax::Seq(
                        StmtSyntax::Assign(k::id!("$b"), b),
                        StmtSyntax::If(
                            Op::Lt(k::id!("$a"), k::id!("$b")),
                            StmtSyntax::Assign(k::id!("$c"), k::id!("$b")),
                            StmtSyntax::Assign(k::id!("$c"), k::id!("$a")),
                        ),
                    ),
                ),
                tail @ ..
            ),
            store: k::configuration::Cell(s),
            state @ ..
        }: Machine,
    ) -> Machine {
        k::cells! {
            k: k::configuration::KCell(..tail),
            store: k::configuration::Cell(map::update(
                map::update(map::update(s, k::id!("$a"), a), k::id!("$b"), b),
                k::id!("$c"),
                c,
            )),
            ..state
        }
    }
}
