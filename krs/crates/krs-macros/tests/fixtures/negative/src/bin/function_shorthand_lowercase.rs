use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn byte(value: k::Term<Int>) -> k::Term<Int> { //~ ERROR UpperCamelCase (`fn Byte`)
    value
}

fn main() {}
