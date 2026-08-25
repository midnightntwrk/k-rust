use krs_macros::claim;

#[claim(all_paths, label = "duplicate-ensures")]
#[renamed_krs::ensures(check(0))]
#[renamed_krs::ensures(check(1))]
fn invalid() {}

fn main() {}
