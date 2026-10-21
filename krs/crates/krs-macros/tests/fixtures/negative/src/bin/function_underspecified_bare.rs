use renamed_krs as k;

#[k::function(total, internal, underspecified)] //~ ERROR `underspecified` takes a reason
pub fn Index(value: k::Term<k::builtin::Int>) -> k::Term<k::builtin::Int>;

fn main() {}
