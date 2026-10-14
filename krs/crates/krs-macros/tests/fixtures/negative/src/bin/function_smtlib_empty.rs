use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::Int,
    syntax = "h({value})",
    smtlib = "", //~ ERROR an `smtlib` symbol must not be empty
)]
pub struct ProbeH {
    pub value: k::Term<k::builtin::Int>,
}

fn main() {}
