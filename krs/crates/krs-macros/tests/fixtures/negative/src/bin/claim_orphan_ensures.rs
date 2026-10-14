#[renamed_krs::ensures(check(0))] //~ ERROR `#[k::ensures]` is a rule or claim helper; place `#[k::rule(...)]` or `#[k::claim(...)]` before it
fn orphan() {}

fn main() {}
