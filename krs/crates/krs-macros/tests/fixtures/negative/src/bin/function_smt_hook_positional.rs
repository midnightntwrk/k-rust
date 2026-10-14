use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::Int,
    syntax = "myAbs({value})",
    smt_hook = "(ite (< #1 0) (- 0 #1) #1)", //~ ERROR `#1` is K's positional placeholder; name the field instead: did you mean `{value}`?
)]
pub struct MyAbs {
    pub value: k::Term<k::builtin::Int>,
}

fn main() {}
