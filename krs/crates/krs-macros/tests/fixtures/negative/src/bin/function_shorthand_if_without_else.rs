use renamed_krs as k;
use renamed_krs::builtin::{Int, int};

#[k::function(partial, internal)]
pub fn Negative(value: k::Term<Int>) -> k::Term<Int> {
    if int::lt(value, 0) { //~ ERROR an `if` that defines a function needs an `else`
        1
    }
}

fn main() {}
