pub const TEXT: &str = include_str!("secret.txt");

pub const BYTES: &[u8] = ::core::include_bytes!("blob.bin");

include!("more.rs");

#[doc = include_str!("doc.md")]
pub struct Documented;
