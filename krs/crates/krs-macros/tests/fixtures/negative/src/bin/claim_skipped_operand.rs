use renamed_krs as k;

#[k::claim(all_paths, label = "proved", skipped_operand = "a claim is proved")] //~ ERROR unknown argument `skipped_operand`
fn claim() {}

fn main() {}
