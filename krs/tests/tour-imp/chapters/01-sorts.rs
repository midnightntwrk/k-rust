//! Readable Rust-authored definition of the complete IMP language.
//!
//! This is the production form of the semantics in the upstream `expr.k`,
//! `calc.k`, and `imp.k` modules. The object-language declarations stay visible
//! to rustc and rust-analyzer while KRS owns the symbolic rule bodies.

use k::KResult;
use k::builtin::{Bool, Id, Int, KSequence, Map, bool, int, map};

k::sorts! {
    #[k::bracket("(", ")")]
    Expr;
    impl Expr for Id;

    Value: Expr + KResult;
    impl Value for Int, Bool;

    Stmt;
}
