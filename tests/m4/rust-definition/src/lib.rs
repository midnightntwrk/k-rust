//! Complete Rust-authored IMP package for the M4 differential gate.
//!
//! The operational language is public so ordinary Rust tooling and downstream
//! authored claims can name its object-language sorts and constructors. Static
//! equations, simplifiers, and proof sentences remain implementation details.

pub mod imp;
mod static_adjunct;
mod verification;
mod claims;

pub use imp::{
    Add, And, Assign, Block, Div, EmptyBlock, Eq, Expr, Ge, Gt, IfThen, IfThenElse, KItem,
    KResult, Le, Lt, Machine, Mul, Ne, Neg, Not, Or, Sequence, Stmt, Sub, Value, While,
};
pub use static_adjunct::{M3dPositive, M3dPriority, M3dTotal, M3dTwice, M3dZero};
