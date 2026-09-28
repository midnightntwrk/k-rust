#[renamed_krs::exists(n: renamed_krs::builtin::Int)] //~ ERROR `#[k::exists]` is a claim helper; place `#[k::claim(...)]` before it
fn orphan() {}

fn main() {}
