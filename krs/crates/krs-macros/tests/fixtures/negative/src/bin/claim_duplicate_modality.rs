use krs_macros::claim;

#[claim(all_paths, one_path, label = "duplicate-modality")] //~ ERROR `all_paths` and `one_path` cannot stand together
fn invalid() {}

fn main() {}
