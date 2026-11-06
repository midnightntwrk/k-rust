use renamed_krs as k;

#[k::constant(skipped_operand = "a constant is no function")] //~ ERROR unknown argument `skipped_operand`
const ONE: k::builtin::Int = 1;

fn main() {}
