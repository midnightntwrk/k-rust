//! A signed package whose program syntax uses integers.

use k::Term;
use k::builtin::Int;

#[k::sort(alias = Num)]
pub trait NumSort {} pub type Num = k::Term<dyn NumSort>;

#[k::constructor(sort = Num, syntax = "num {value}")]
pub struct Literal {
    pub value: Term<Int>,
}
