use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::string::String,
    syntax = "#keccak({value}, {salt})",
    hook = "KRYPTO.keccak256", //~ ERROR `KRYPTO.keccak256` takes 1 argument, but the production has 2 fields
)]
pub struct KeccakHex {
    pub value: k::Term<k::builtin::string::String>,
    pub salt: k::Term<k::builtin::string::String>,
}

fn main() {}
