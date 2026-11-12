use renamed_krs as k;

#[k::function(total, internal, assumed = " ")] //~ ERROR an `assumed` reason must not be empty
pub fn Index(value: k::Term<k::builtin::Int>) -> k::Term<k::builtin::Int>;

fn main() {}
