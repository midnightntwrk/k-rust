use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::syntax_list(separator = ",")]
pub enum Ints<T> { //~ ERROR a syntactic list cannot have generic parameters
    Cons { head: Int, tail: Ints<T> },
    Nil(),
}

fn main() {}
