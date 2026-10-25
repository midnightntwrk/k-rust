use renamed_krs as k;
use renamed_krs::builtin::{Int, int};

#[k::function(total, internal)]
pub fn Twice(value: k::Term<Int>) -> k::Term<Int> {
    match int::add(value, value) {
        0 => 0,
        sum => sum, //~ ERROR `sum` binds a name, but this component of the scrutinee is not a parameter
    }
}

fn main() {}
