//! Replacement crate for the reviewed deterministic layer-2 IMP surface.

pub mod imp;

pub use imp::{Expr, ExprSort, Machine, Op, Stmt, StmtSort, StmtSyntax, Value, ValueSort};
