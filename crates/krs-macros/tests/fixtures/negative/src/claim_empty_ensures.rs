use krs_macros::claim;

#[claim(all_paths, label = "empty-ensures")]
#[renamed_krs::ensures()]
fn invalid() {}

fn main() {}
