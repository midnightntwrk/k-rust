use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::Int,
    syntax = "myAbs({value})",
    smt_hook = "(ite (< {value} 0) (- 0 {value}) {value}", //~ ERROR the `smt_hook` template has an unclosed `(`
)]
pub struct MyAbs {
    pub value: k::Term<k::builtin::Int>,
}

fn main() {}
