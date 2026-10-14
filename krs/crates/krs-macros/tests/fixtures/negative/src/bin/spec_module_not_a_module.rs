use renamed_krs as k;

#[k::spec_module(imports = [crate])]
fn proofs() {} //~ ERROR `#[k::spec_module]` applies to an inline `mod name { .. }`

fn main() {}
