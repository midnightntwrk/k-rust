use renamed_krs as k;

#[k::function(total, internal, skipped_operand = " ")] //~ ERROR a `skipped_operand` reason must not be empty
pub fn Index(value: k::Term<k::builtin::Int>) -> k::Term<k::builtin::Int>;

fn main() {}
