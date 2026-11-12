use renamed_krs as k;

#[k::function(total, internal, assumed = "one", assumed = "two")] //~ ERROR duplicate
pub fn Index(value: k::Term<k::builtin::Int>) -> k::Term<k::builtin::Int>;

fn main() {}
