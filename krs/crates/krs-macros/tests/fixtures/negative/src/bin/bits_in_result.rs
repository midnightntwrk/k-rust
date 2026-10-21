use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code_result: 0 => k::bits!("01"); //~ ERROR `k::bits!` is a pattern
}

fn main() {}
