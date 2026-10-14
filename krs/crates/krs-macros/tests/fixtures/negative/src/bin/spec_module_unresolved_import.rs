use renamed_krs as k;

#[k::spec_module(imports = [missing_lemmas])] //~ ERROR unresolved import `missing_lemmas`
mod proofs {}

fn main() {}
