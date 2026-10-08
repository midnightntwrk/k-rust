use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::syntax_list(separator = ",")]
pub enum Ints {
    Cons { head: Int, tail: Int }, //~ ERROR the second field of the cons variant is the list itself
    Nil(),
}

fn main() {}
