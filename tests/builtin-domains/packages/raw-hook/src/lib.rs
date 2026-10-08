//! A quoted hook outside the typed catalog (KF-037).
//!
//! `KRYPTO.keccak256` returns the hexadecimal Keccak-256 digest of Bytes as a
//! String.
//! The typed catalog covers only the raw-bytes forms, so the hook is named by
//! its exact K spelling, which KRS checks against the pinned hook registry but
//! whose signature it cannot check; the package opts in with `allow-raw-k`.
//! k-rust and K's Haskell backend evaluate the hook; K's LLVM backend needs
//! the blockchain plugin.

use k::builtin::{Bytes, KSequence, string};
use k::{KResult, Term};

k::sorts! {
    Exp;
    Value: Exp + KResult;
    impl Value for Bytes, string::String;
}

/// The hexadecimal Keccak-256 digest of a byte string.
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
