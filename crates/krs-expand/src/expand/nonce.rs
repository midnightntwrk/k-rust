//! Expansion nonces and rule-application selectors.

use std::hash::{Hash, Hasher};

use syn::Ident;
use syn::ext::IdentExt;

use crate::environment::{MacroEnvironment, SourcePosition};

pub(super) fn expansion_nonce(
    env: &dyn MacroEnvironment,
    kind: &str,
    ident: &Ident,
    range: krs_syntax::TokenRange,
) -> u64 {
    let mut hasher = StableHasher::default();
    kind.hash(&mut hasher);
    ident.to_string().hash(&mut hasher);
    env.span_file(range.first()).hash(&mut hasher);
    let (start_line, start_column) = nonce_position(env.span_start(range.first()));
    let (end_line, end_column) = nonce_position(env.span_end(range.last()));
    start_line.hash(&mut hasher);
    start_column.hash(&mut hasher);
    end_line.hash(&mut hasher);
    end_column.hash(&mut hasher);
    hasher.finish()
}

/// The nonce's view of an environment position: the 1-based line and the
/// 0-based column that `proc_macro2::Span::start`/`end` report for a rustc
/// span, and `(0, 0)` where `proc_macro2` has no location.
///
/// The environment, not `proc_macro2`, resolves the span, so a host outside a
/// procedural macro can resolve synthesized spans (such as `Span::call_site()`
/// tokens re-quoted by `krs-syntax`) to the invocation, as rustc does. The
/// values are hashed as `u64`, which is what `usize` hashed on the 64-bit
/// hosts that run `krs-macros`, so the nonce does not depend on the pointer
/// width of the expanding host.
fn nonce_position(position: Option<SourcePosition>) -> (u64, u64) {
    position.map_or((0, 0), |position| {
        (
            u64::from(position.line),
            u64::from(position.column.saturating_sub(1)),
        )
    })
}

pub(super) fn rule_application_selector(ident: &Ident) -> u64 {
    let mut selector = 0xcbf2_9ce4_8422_2325_u64;
    for byte in ident.unraw().to_string().bytes() {
        selector ^= u64::from(byte);
        selector = selector.wrapping_mul(0x0000_0100_0000_01b3);
    }
    selector
}

struct StableHasher(u64);

impl Default for StableHasher {
    fn default() -> Self {
        Self(0xcbf2_9ce4_8422_2325)
    }
}

impl Hasher for StableHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::expansion_nonce;
    use crate::environment::FixedEnvironment;

    #[test]
    fn expansion_nonce_depends_on_the_environment_display_file() {
        let ident: syn::Ident = syn::parse_str("Exp").unwrap();
        let tokens: proc_macro2::TokenStream = "Exp;".parse().unwrap();
        let range = krs_syntax::TokenRange::for_tokens(&tokens).unwrap();
        let first = FixedEnvironment::new("src/first.rs", "::k");
        let second = FixedEnvironment::new("src/second.rs", "::k");
        assert_eq!(
            expansion_nonce(&first, "sort", &ident, range),
            expansion_nonce(&first, "sort", &ident, range)
        );
        assert_ne!(
            expansion_nonce(&first, "sort", &ident, range),
            expansion_nonce(&second, "sort", &ident, range)
        );
    }
}
