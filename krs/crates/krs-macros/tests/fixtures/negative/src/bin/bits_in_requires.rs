use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    #[k::requires(k::bits!("01"))] //~ ERROR To test a value against a template in a condition or a claim, write `k::bits!(value, "..")`
    code_tested: n => 0;
    #[k::equation(owise)]
    code_other: n => 1;
}

fn main() {}
