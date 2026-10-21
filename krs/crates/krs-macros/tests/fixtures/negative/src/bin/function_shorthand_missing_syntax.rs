use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total)]
pub fn Byte(value: k::Term<Int>) -> k::Term<Int> { //~ ERROR needs an explicit `syntax
    value
}

#[k::function(total, program)]
pub fn Word(value: k::Term<Int>) -> k::Term<Int>; //~ ERROR needs an explicit `syntax

#[k::function(total, sort = Int)]
pub struct Half { //~ ERROR needs an explicit `syntax
    pub value: k::Term<Int>,
}

fn main() {}
