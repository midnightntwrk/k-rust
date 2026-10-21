use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code_empty: k::bits!("  ") => 0; //~ ERROR a bit template needs at least one bit
}

fn main() {}
