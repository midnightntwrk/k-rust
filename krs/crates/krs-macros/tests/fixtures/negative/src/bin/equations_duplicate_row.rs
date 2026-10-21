use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code_zero: 0 => 1;
    code_again: 00 => 2; //~ ERROR rows `code_zero` and `code_again` give one application two results
}

fn main() {}
