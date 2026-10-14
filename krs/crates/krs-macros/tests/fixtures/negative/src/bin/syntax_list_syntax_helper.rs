use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::syntax_list(separator = ",")]
pub enum Ints {
    #[k::syntax("{head} :: {tail}")] //~ ERROR syntactic-list variants take no `#[k::syntax]`
    Cons { head: Int, tail: Ints },
    Nil(),
}

fn main() {}
