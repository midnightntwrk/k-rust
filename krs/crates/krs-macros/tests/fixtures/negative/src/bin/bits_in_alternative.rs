use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code_or: k::bits!("1_") | 0 => 1; //~ ERROR a bit template cannot be an alternative of `|`
}

fn main() {}
