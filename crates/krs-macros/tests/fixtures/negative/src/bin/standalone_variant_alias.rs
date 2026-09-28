use renamed_krs as k;

#[k::sort]
pub trait Expr {}

#[k::constructors(sort = Expr)]
pub enum Boolean {
    False,
}

use Boolean::False as No;

#[k::rule]
pub fn bad(No: k::Term<Boolean>) -> k::Term<Boolean> { //~ ERROR expected type, found variant
    No
}

fn main() {}
