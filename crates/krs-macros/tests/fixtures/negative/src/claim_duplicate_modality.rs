use krs_macros::claim;

#[claim(all_paths, one_path, label = "duplicate-modality")]
fn invalid() {}

fn main() {}
