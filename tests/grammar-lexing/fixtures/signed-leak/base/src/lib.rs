//! A signed package whose program syntax uses integers.

use k::Term;
use k::builtin::Int;

#[k::sort]
pub trait Num {}

#[k::constructor(sort = Num, syntax = "num {value}")]
pub struct Literal {
    pub value: Term<Int>,
}
