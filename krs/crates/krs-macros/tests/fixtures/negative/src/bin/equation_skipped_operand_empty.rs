use renamed_krs as k;

#[k::equation(skipped_operand = " ")] //~ ERROR a `skipped_operand` reason must not be empty
fn equation() {}

fn main() {}
