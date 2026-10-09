use renamed_krs as k;

#[k::spec_module(name = "ORG-SYNTAX", imports = [crate])] //~ ERROR reserves for program-syntax modules
mod proofs {}

fn main() {}
