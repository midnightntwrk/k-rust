use renamed_krs as k;

#[k::function(total, internal, assumed)] //~ ERROR `assumed` takes a reason
pub fn Index(value: k::Term<k::builtin::Int>) -> k::Term<k::builtin::Int>;

fn main() {}
