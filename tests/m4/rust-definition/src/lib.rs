//! Complete Rust-authored IMP package for the M4 differential gate.
//!
//! The operational language is public so ordinary Rust tooling and downstream
//! authored claims can name its object-language sorts and constructors. Static
//! equations, simplifiers, and proof sentences remain implementation details.

mod claims;
pub mod imp;
#[cfg(test)]
mod parity;
mod static_adjunct;
mod verification;

pub use imp::{Expr, ExprSort, Machine, Op, Stmt, StmtSort, StmtSyntax, Value, ValueSort};
pub use static_adjunct::{M3dPositive, M3dPriority, M3dTotal, StaticExpr};
