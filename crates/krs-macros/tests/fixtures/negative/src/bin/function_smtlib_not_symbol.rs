use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::Int,
    syntax = "h({value})",
    smtlib = "probe h", //~ ERROR `probe h` is not an SMT-LIB simple symbol
)]
pub struct ProbeH {
    pub value: k::Term<k::builtin::Int>,
}

fn main() {}
