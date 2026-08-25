use krs_macros::claim;

#[claim(all_paths, label = "duplicate-exists")]
#[renamed_krs::exists(n: renamed_krs::builtin::Int)]
#[renamed_krs::exists(m: renamed_krs::builtin::Int)]
fn invalid() {}

fn main() {}
