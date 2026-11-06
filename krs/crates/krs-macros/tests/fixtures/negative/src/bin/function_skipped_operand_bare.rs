use renamed_krs as k;

#[k::function(total, internal, skipped_operand)] //~ ERROR `skipped_operand` takes a reason
pub fn Index(value: k::Term<k::builtin::Int>) -> k::Term<k::builtin::Int>;

fn main() {}
