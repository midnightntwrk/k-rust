//! Anywhere rules.
//!
//! Most rules act at the head of the computation cell, and equations act
//! wherever their function appears. `#[k::rule(anywhere)]` gives a
//! constructor that behaviour while it stays a constructor: `drop_a` removes
//! a leading `a` from a sequence at the top, inside `wrap(..)`, or repeatedly,
//! and `reassociate` rewrites a left-nested sequence to the right-nested form.
//! `;` is right-associative, so the emitted K writes the left-nested
//! `(S1 ; S2) ; S3` with parentheses and the right-nested one without.
//! K's Haskell backend does not support anywhere rules, so the Java Haskell
//! reference route refuses this definition.

use k::Term;
use k::builtin::KSequence;

k::sorts! {
    #[k::bracket("(", ")")]
    Stmt;
}

#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence(
    (A, B, C, D, Wrap)
    > right (Seq)
)]
#[rustfmt::skip]
pub enum StmtSyntax {
    #[k::syntax("a")] A(),
    #[k::syntax("b")] B(),
    #[k::syntax("c")] C(),
    #[k::syntax("d")] D(),
    #[k::syntax("wrap({inner})")] Wrap { inner: Stmt },
    #[k::syntax("{lhs} ; {rhs}")] Seq { lhs: Stmt, rhs: Stmt },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm] }
    }
}

#[k::rule(anywhere, label = "reassociate")]
fn reassociate(
    k::term![StmtSyntax::Seq {
        lhs: StmtSyntax::Seq { lhs: s1, rhs: s2 },
        rhs: s3
    }]: Term<Stmt>,
) -> Term<Stmt> {
    k::term![StmtSyntax::Seq {
        lhs: s1,
        rhs: StmtSyntax::Seq { lhs: s2, rhs: s3 }
    }]
}

#[k::rule(anywhere, label = "drop-a")]
fn drop_a(
    k::term![StmtSyntax::Seq {
        lhs: StmtSyntax::A(),
        rhs: s
    }]: Term<Stmt>,
) -> Term<Stmt> {
    s
}
