//! Raw K under `profile = "strict"` (KF-037): both uses are errors even with
//! `allow-raw-k = true`.

use k::builtin::{Bytes, Int, KSequence, string};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bytes, Int, string::String;
}

/// A quoted hook, which needs the opt-in.
#[k::function(total, sort = string::String, syntax = "keccak({value})", hook = "KRYPTO.keccak256")]
pub struct KeccakHex {
    pub value: Term<Bytes>,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::raw_k!("rule <k> 0 => 1 ... </k>");
