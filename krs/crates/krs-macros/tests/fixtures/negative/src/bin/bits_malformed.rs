use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code_inc: k::bits!("00 Y 100") => 1; //~ ERROR character 3 of the bit template, `Y`, is not a bit
}

fn main() {}
