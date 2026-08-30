use renamed_krs as k;

#[k::function(
    total,
    sort = k::builtin::Bytes,
    syntax = "Digest({value})",
    hook = krypto::sha256_hex,
)]
pub struct Digest {
    pub value: k::Term<k::builtin::Bytes>,
}

fn main() {}
