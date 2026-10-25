use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Zero(value: k::Term<Int>) -> k::Term<Int> {
    match value {
        _ => 1, //~ ERROR this arm matches every value, so the arms after it could never apply
        0 => 0,
    }
}

fn main() {}
