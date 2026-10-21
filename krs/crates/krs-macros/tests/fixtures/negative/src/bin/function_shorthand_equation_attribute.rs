use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
#[k::equation(owise)] //~ ERROR `#[k::equation]` does not apply to a function declared by a `fn`
pub fn Byte(value: k::Term<Int>) -> k::Term<Int> {
    value
}

fn main() {}
