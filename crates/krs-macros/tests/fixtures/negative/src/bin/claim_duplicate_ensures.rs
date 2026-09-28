use krs_macros::claim;

#[claim(all_paths, label = "duplicate-ensures")]
#[renamed_krs::ensures(check(0))]
#[renamed_krs::ensures(check(1))] //~ ERROR a claim may declare only one `ensures` helper
fn invalid() {}

fn main() {}
