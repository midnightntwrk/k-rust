use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::syntax_list(separator = ",")]
pub enum Ints {
    Cons { head: Int, tail: Ints },
    Nil(),
}

// A type joins `Below` only together with the list sort above it, which
// `Other` is not a member of.
k::sorts! {
    Below: Ints;
}

pub struct Other;
impl BelowSort for Other {} //~ ERROR [krs::expand::sort-membership] `Other` is not a member of the syntactic list sort `Ints`

fn main() {}
