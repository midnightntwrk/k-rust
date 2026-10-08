#[renamed_krs::exists(n: renamed_krs::builtin::Int)] //~ ERROR `#[k::exists]` is a rule or claim helper; place `#[k::rule(...)]` or `#[k::claim(...)]` before it
fn orphan() {}

fn main() {}
