use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code_any: k::bits!("01 yyy zzz") => y;
    code_halt: 118 => 0; //~ ERROR rows `code_any` and `code_halt` both apply to the arguments (118)
}

fn main() {}
