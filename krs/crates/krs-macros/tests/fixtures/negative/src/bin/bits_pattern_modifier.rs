use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    code_modified: k::bits!("aa", signed) => a; //~ ERROR a second argument is reserved for modifiers such as signed fields
    #[k::equation(owise)]
    code_other: n => 1;
}

fn main() {}
