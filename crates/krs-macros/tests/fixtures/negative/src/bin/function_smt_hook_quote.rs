use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::Int,
    syntax = "myAbs({value})",
    smt_hook = "(str.++ {value} \"!\")", //~ ERROR an `smt_hook` template cannot contain `"`
)]
pub struct MyAbs {
    pub value: k::Term<k::builtin::Int>,
}

fn main() {}
