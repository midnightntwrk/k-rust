use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::syntax_list(separator = ",")]
pub enum Ints {
    Cons { head: Int, tail: Ints },
    Nil, //~ ERROR a zero-field tuple terminator `Nil()`
}

fn main() {}
