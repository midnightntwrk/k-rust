use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::Bytes,
    syntax = "Digest({value})",
    hook = krypto::sha256_hex, //~ ERROR unknown KRS hook; expected `krypto::keccak256_raw`, `krypto::sha256_raw`, `krypto::ripemd160_raw`, `krypto::ecdsa_recover`, `krypto::bn128_valid`, `krypto::bn128_add`, `krypto::bn128_mul`, `krypto::bn128_g2_valid`, or `krypto::bn128_ate`
)]
pub struct Digest {
    pub value: k::Term<k::builtin::Bytes>,
}

fn main() {}
