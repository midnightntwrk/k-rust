use krs_macros::claim;

#[claim(all_paths, label = "duplicate-exists")]
#[renamed_krs::exists(n: renamed_krs::builtin::Int)]
#[renamed_krs::exists(m: renamed_krs::builtin::Int)] //~ ERROR a claim may declare only one `exists` helper
fn invalid() {}

fn main() {}
