use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::string::String,
    syntax = "#keccak({value})",
    hook = "KRYPTO.keccak", //~ ERROR `KRYPTO.keccak` is not a hook of the pinned K and k-rust; check its spelling
)]
pub struct KeccakHex {
    pub value: k::Term<k::builtin::string::String>,
}

fn main() {}
