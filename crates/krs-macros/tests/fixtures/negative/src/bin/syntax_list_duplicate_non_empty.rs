use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::syntax_list(separator = ",", non_empty, non_empty)] //~ ERROR `non_empty` is written once
pub enum Ints {
    Cons { head: Int, tail: Ints },
    Nil(),
}

fn main() {}
