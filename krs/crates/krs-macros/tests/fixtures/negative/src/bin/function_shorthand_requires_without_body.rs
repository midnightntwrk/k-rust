use renamed_krs as k;
use renamed_krs::builtin::{Int, int};

#[k::function(partial, internal)]
#[k::requires(int::gt(value, 0))] //~ ERROR a declaration ending with `;` has none
pub fn Pred(value: k::Term<Int>) -> k::Term<Int>;

fn main() {}
