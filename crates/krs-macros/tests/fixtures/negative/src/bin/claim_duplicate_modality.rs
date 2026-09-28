use krs_macros::claim;

#[claim(all_paths, one_path, label = "duplicate-modality")] //~ ERROR a claim requires exactly one modality
fn invalid() {}

fn main() {}
