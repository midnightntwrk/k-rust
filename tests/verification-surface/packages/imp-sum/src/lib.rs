//! IMP's `sum-spec` loop in an author spec module (KF-041), as upstream
//! `imp-verification.k` writes it: the definition adds a `$`-identifier
//! token to `Id`, and the spec modules import the definition explicitly.
//!
//! The package depends on the IMP language. Its own definition module,
//! `IMP-VERIFICATION`, adds only the regex token, so the claim can write
//! `$n` where IMP's loose claims need `#token("$n","Id")`. `LEMMAS` adds a
//! simplification lemma, and `IMP-SUM-SPEC` imports it and proves the loop.

use k::Term;
use k::builtin::{Bool, Int, int};
#[allow(unused_imports)]
use k::map;
use krs_imp_definition::{Machine, Op, StmtSyntax};

/// Every `$`-prefixed identifier, as upstream IMP-VERIFICATION declares it.
#[k::token(regex = r"\$[a-zA-Z0-9_]+")]
pub type DollarId = k::builtin::Id;

/// A lemma module: imports the definition and adds one simplification.
#[k::spec_module(name = "IMP-VERIFICATION-LEMMAS", imports = [crate])]
pub mod lemmas {
    use super::{Bool, Term, int};

    #[k::simplification]
    fn lt_irreflexive(k::term![int::lt(value, value)]: Term<Bool>) -> Term<Bool> {
        false
    }
}

/// The sum loop's circularity, upstream's `sum-spec`. The label differs from
/// IMP's own loose `sum-spec` claim, which this definition also contains:
/// claim labels are unique across a definition.
#[k::spec_module(name = "IMP-SUM-SPEC", imports = [lemmas])]
mod sum_spec {
    #[allow(unused_imports)]
    use super::map;
    use super::{Int, Machine, Op, StmtSyntax, Term, int};

    #[k::claim(all_paths, label = "dollar-sum-spec", circularity)]
    #[k::requires(int::ge(n, 0))]
    fn dollar_sum_spec(
        n: Term<Int>,
        s: Term<Int>,
        k::cells! {
            k: k::configuration::KCell(
                StmtSyntax::While(
                    Op::Not(Op::Le(k::id!("$n"), 0)),
                    StmtSyntax::Block(StmtSyntax::Sequence(
                        StmtSyntax::Assign(k::id!("$s"), Op::Add(k::id!("$s"), k::id!("$n"))),
                        StmtSyntax::Assign(k::id!("$n"), Op::Add(k::id!("$n"), Op::Neg(1))),
                    )),
                ),
                tail @ ..
            ),
            env: k::configuration::Cell(map![
                k::id!("$n") -> n,
                k::id!("$s") -> s,
            ]),
            state @ ..
        }: Machine,
    ) -> Machine {
        k::cells! {
            k: k::configuration::KCell(..tail),
            env: k::configuration::Cell(map![
                k::id!("$n") -> 0,
                k::id!("$s") -> int::add(
                    s,
                    int::div(int::mul(int::add(n, 1), n), 2),
                ),
            ]),
            ..state
        }
    }
}
