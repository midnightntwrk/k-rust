use renamed_krs as k;

#[k::function(
    partial,
    sort = k::builtin::Int,
    syntax = "half({value})",
    assumed = "odd values never arise", //~ ERROR `assumed` states that a `total` function has a value on every argument
)]
pub struct Half {
    pub value: k::Term<k::builtin::Int>,
}

fn main() {}
