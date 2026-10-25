use renamed_krs as k;
use renamed_krs::builtin::{Int, int};

#[k::function(total, internal)]
pub fn Shift(value: k::Term<Int>) -> k::Term<Int> {
    int::add(
        1,
        if int::lt(value, 0) { 0 } else { value }, //~ ERROR an `if` or `match` inside a term cannot define equations
    )
}

fn main() {}
