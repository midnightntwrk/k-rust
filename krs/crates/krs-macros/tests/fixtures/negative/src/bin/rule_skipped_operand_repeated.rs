use renamed_krs as k;

#[k::rule(skipped_operand = "one", skipped_operand = "two")] //~ ERROR `skipped_operand` is given twice
fn transition() {}

fn main() {}
