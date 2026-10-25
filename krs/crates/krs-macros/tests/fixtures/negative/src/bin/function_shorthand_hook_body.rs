use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal, hook = "INT.abs")] //~ ERROR a hooked function takes its values from the backend
pub fn Abs(value: k::Term<Int>) -> k::Term<Int> {
    value
}

fn main() {}
