//! K sources embedded for hosts without a K installation or filesystem.

use crate::outer::ResolvedSource;

/// Normalize legacy `.k` builtin names to the current literate source names.
pub fn source_name(required: &str) -> &str {
    match required {
        "ffi.k" => "ffi.md",
        "json.k" => "json.md",
        "rat.k" => "rat.md",
        "substitution.k" => "substitution.md",
        "domains.k" => "domains.md",
        "kast.k" => "kast.md",
        required => required,
    }
}

/// Return one of the K sources embedded in `k-rust`.
///
/// Native hosts such as the CLI and Node bindings use this as the final fallback in their own
/// [`crate::outer::SourceResolver`] implementations.
pub fn embedded(required: &str) -> Option<ResolvedSource> {
    let name = source_name(required);
    let text = match name {
        "domains.md" => include_str!("../builtin/domains.md"),
        "ffi.md" => include_str!("../builtin/ffi.md"),
        "json.md" => include_str!("../builtin/json.md"),
        "kast.md" => include_str!("../builtin/kast.md"),
        "prelude.md" => include_str!("../builtin/prelude.md"),
        "rat.md" => include_str!("../builtin/rat.md"),
        "substitution.md" => include_str!("../builtin/substitution.md"),
        "timer.md" => include_str!("../builtin/timer.md"),
        "unification.k" => include_str!("../builtin/unification.k"),
        _ => return None,
    };
    Some(ResolvedSource::new(format!("krust-builtin://{name}"), text))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolves_current_and_legacy_builtin_names() {
        assert_eq!(
            embedded("domains.md").unwrap(),
            embedded("domains.k").unwrap()
        );
        assert!(
            embedded("prelude.md")
                .unwrap()
                .text
                .contains("requires \"kast.md\"")
        );
        assert!(embedded("not-a-builtin.k").is_none());
    }
}
