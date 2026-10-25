use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code_split: k::bits!("aa 0 aa") => a; //~ ERROR field `a` is split
}

fn main() {}
