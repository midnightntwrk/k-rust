use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::syntax_list(separator = ",")]
pub enum Ints { //~ ERROR a syntactic list has exactly two variants
    Cons { head: Int, tail: Ints },
    Nil(),
    Empty(),
}

fn main() {}
