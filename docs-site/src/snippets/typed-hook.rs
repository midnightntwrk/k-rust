#[language_host::function(
    total,
    sort = language_host::builtin::Bytes,
    syntax = "Keccak256raw({value})",
    hook = krypto::keccak256_raw,
)]
pub struct Keccak256Raw {
    pub value: Term<language_host::builtin::Bytes>,
}
