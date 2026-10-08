use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::Bytes,
    syntax = "#keccakRaw({value})",
    hook = "KRYPTO.keccak256raw", //~ ERROR `KRYPTO.keccak256raw` is in the typed hook catalog; use hook = krypto::keccak256_raw
)]
pub struct KeccakRaw {
    pub value: k::Term<k::builtin::Bytes>,
}

fn main() {}
