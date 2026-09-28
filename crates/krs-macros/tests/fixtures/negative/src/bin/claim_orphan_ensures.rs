#[renamed_krs::ensures(check(0))] //~ ERROR `#[k::ensures]` is a claim helper; place `#[k::claim(...)]` before it
fn orphan() {}

fn main() {}
