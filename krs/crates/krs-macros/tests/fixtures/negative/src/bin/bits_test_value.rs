use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

k::equations! {
    for Code;
    #[k::requires(k::bits!(n.add::<Int>(1), "01"))] //~ ERROR the value a `k::bits!` test reads is a variable
    code_tested: n => 0;
    #[k::equation(owise)]
    code_other: n => 1;
}

fn main() {}
