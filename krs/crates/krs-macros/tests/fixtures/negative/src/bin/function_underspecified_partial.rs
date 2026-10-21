use renamed_krs as k;

#[k::function(
    partial,
    sort = k::builtin::Int,
    syntax = "half({value})",
    underspecified = "odd values", //~ ERROR `underspecified` states a gap in a `total` function's equations
)]
pub struct Half {
    pub value: k::Term<k::builtin::Int>,
}

fn main() {}
