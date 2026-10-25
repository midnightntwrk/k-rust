use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    #[k::rule(owise)] //~ ERROR not `#[k::rule]`
    code_zero: 0 => 1;
}

fn main() {}
