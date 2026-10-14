use krs_macros::claim;

#[claim(all_paths, label = "empty-ensures")]
#[renamed_krs::ensures()] //~ ERROR claim helper payload must not be empty
fn invalid() {}

fn main() {}
