use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal, sort = Int)] //~ ERROR takes its sort from the return type
pub fn Byte(value: k::Term<Int>) -> k::Term<Int> {
    value
}

fn main() {}
