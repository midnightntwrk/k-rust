//! Rust keywords used when validating authored and generated identifiers.

const KEYWORDS: &[&str] = &[
    "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum", "extern",
    "false", "fn", "for", "gen", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut",
    "pub", "ref", "return", "self", "Self", "static", "struct", "super", "trait", "true", "try",
    "type", "unsafe", "use", "where", "while", "yield", "abstract", "become", "box", "do", "final",
    "macro", "override", "priv", "typeof", "unsized", "virtual",
];

/// Return whether `identifier` is a strict or reserved Rust keyword.
#[must_use]
pub fn is_keyword(identifier: &str) -> bool {
    KEYWORDS.contains(&identifier)
}
