k::lexical! {
    /// One ASCII letter.
    Alpha = r"[a-zA-Z]";
    AlphaNum = r"[a-zA-Z0-9_]";
}

k::layout! {
    r"(;[^\n\r]*)",     // `;` starts a comment to the end of the line
    r"([\ \n\r\t])",    // whitespace: declaring any layout replaces K's default
}

/// Identifiers, built from the named lexicals.
#[k::token(regex = r"{Alpha}{AlphaNum}*")]
pub struct Name(pub String);
