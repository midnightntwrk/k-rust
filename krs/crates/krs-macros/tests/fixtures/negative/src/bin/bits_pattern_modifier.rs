use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code_modified: k::bits!("aa", signed) => a; //~ ERROR `signed` is no field letter; a modifier starts with the field's letter, as in `i: signed`
    #[k::equation(owise)]
    code_other: n => 1;
}

fn main() {}
