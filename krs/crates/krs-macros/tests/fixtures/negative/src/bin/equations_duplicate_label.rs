use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code: 0 => 1;
    code: 1 => 2; //~ ERROR duplicate row label `code`
}

fn main() {}
