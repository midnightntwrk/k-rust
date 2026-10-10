//! A lesson package whose only content is a spec module: it depends on
//! lesson 1.22's language and adds claims, as a K lesson's `-spec.k` file
//! adds claims to a kompiled language. The package has no definition of its
//! own; its definition module `KRS-L22-LESSON` is empty and imports the
//! language, so `kompile` sees exactly the language.
//!
//! `LESSON-SPEC` declares the `$`-identifier token itself, so the token is
//! part of the proof input only and its claim writes `$n` bare.

use k::Term;
use k::builtin::{Int, Map, map};
use krs_verification_surface_l22::{Machine, StmtSyntax};

/// A lesson's proof module that needs `$` identifiers only in its claims.
#[k::spec_module(name = "LESSON-SPEC", imports = [crate])]
mod lesson_spec {
    use super::{Int, Machine, Map, StmtSyntax, Term, map};

    /// Every `$`-prefixed identifier, for this module's claims only.
    #[k::token(regex = r"\$[a-zA-Z0-9_]+")]
    pub type DollarId = k::builtin::Id;

    /// `$n = n; $m = m;` stores both values under their names.
    #[k::claim(all_paths, label = "dollar-assign")]
    fn dollar_assign(
        n: Term<Int>,
        m: Term<Int>,
        s: Term<Map>,
        k::cells! {
            k: k::configuration::KCell(
                StmtSyntax::Seq(
                    StmtSyntax::Assign(k::id!("$n"), n),
                    StmtSyntax::Assign(k::id!("$m"), m),
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
                map::update(s, k::id!("$n"), n),
                k::id!("$m"),
                m,
            )),
            ..state
        }
    }
}
