use renamed_krs as k;

#[k::function(total, internal, skipped_operand = "one", skipped_operand = "two")] //~ ERROR `skipped_operand` is given twice
pub fn Index(value: k::Term<k::builtin::Int>) -> k::Term<k::builtin::Int>;

fn main() {}
