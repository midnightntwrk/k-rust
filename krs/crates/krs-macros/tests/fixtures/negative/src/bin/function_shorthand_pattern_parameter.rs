use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Byte(
    mut value: k::Term<Int>, //~ ERROR a function parameter is a plain name
) -> k::Term<Int> {
    value
}

fn main() {}
