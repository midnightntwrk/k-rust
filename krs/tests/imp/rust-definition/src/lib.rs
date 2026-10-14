//! Complete Rust-authored IMP package for the IMP differential gate.
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
pub use static_adjunct::{AddOne, NonnegativeIdentity, PriorityChoice, StaticExpr};
