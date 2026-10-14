use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::Int,
    syntax = "myAbs({value})",
    smtlib = "absProbe",
    smt_hook = "(ite (< {value} 0) (- 0 {value}) {value})", //~ ERROR `smtlib` and `smt_hook` are mutually exclusive
)]
pub struct MyAbs {
    pub value: k::Term<k::builtin::Int>,
}

fn main() {}
