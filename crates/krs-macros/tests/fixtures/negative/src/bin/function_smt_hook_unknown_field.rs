use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::Int,
    syntax = "myAbs({value})",
    smt_hook = "(ite (< {valeu} 0) (- 0 {value}) {value})", //~ ERROR `smt_hook` placeholder `{valeu}` names no field of this function; did you mean `{value}`?
)]
pub struct MyAbs {
    pub value: k::Term<k::builtin::Int>,
}

fn main() {}
