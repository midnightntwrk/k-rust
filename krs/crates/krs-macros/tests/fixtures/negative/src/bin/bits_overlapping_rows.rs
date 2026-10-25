use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code_inc: k::bits!("00 yyy 100") => y;
    code_jump: k::bits!("00 1cc 100") => c; //~ ERROR rows `code_inc` and `code_jump` both apply to the arguments (36)
}

fn main() {}
