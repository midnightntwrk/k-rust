use renamed_krs as k;

#[k::function(total, internal, underspecified = true)] //~ ERROR string literal
pub fn Index(value: k::Term<k::builtin::Int>) -> k::Term<k::builtin::Int>;

fn main() {}
