use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::string::String,
    syntax = "#keccak({value})",
    hook = "keccak256", //~ ERROR invalid hook string `keccak256`; expected NAMESPACE.name, such as "KRYPTO.keccak256"
)]
pub struct KeccakHex {
    pub value: k::Term<k::builtin::string::String>,
}

fn main() {}
