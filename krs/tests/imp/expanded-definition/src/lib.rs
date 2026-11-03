//! Replacement crate for the reviewed deterministic layer-2 IMP surface.

// Each module is the reviewed expansion golden of the authored module file of its name, which
// the IMP gate compares byte for byte.
#[rustfmt::skip]
pub mod imp;
#[rustfmt::skip]
mod static_adjunct;

pub use imp::{Expr, ExprSort, Machine, Op, Stmt, StmtSort, StmtSyntax, Value, ValueSort};
pub use static_adjunct::{AddOne, NonnegativeIdentity, PriorityChoice, StaticExpr};
