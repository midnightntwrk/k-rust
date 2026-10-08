use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::syntax_list(separator = "a+")] //~ ERROR a list separator is empty or exactly one K terminal
pub enum Ints {
    Cons { head: Int, tail: Ints },
    Nil(),
}

fn main() {}
