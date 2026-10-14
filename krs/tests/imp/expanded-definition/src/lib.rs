//! Replacement crate for the reviewed deterministic layer-2 IMP surface.

// The module is the reviewed expansion golden, which the IMP gate compares byte for byte.
#[rustfmt::skip]
pub mod imp;

pub use imp::{Expr, ExprSort, Machine, Op, Stmt, StmtSort, StmtSyntax, Value, ValueSort};
