//! KORE name demangling and Lean identifiers.

/// The KORE escape table: K writes characters outside `[A-Za-z0-9-]` of a symbol name as
/// four-letter codes inside `'...'` blocks.
const CODES: &[(&str, char)] = &[
    ("Spce", ' '),
    ("Bang", '!'),
    ("Quot", '"'),
    ("Hash", '#'),
    ("Dolr", '$'),
    ("Perc", '%'),
    ("And-", '&'),
    ("Apos", '\''),
    ("LPar", '('),
    ("RPar", ')'),
    ("Star", '*'),
    ("Plus", '+'),
    ("Comm", ','),
    ("Hyph", '-'),
    ("Stop", '.'),
    ("Slsh", '/'),
    ("Coln", ':'),
    ("SCln", ';'),
    ("-LT-", '<'),
    ("Eqls", '='),
    ("-GT-", '>'),
    ("Ques", '?'),
    ("-AT-", '@'),
    ("LSqB", '['),
    ("Bash", '\\'),
    ("RSqB", ']'),
    ("Xor-", '^'),
    ("Unds", '_'),
    ("BQuo", '`'),
    ("LBra", '{'),
    ("Pipe", '|'),
    ("RBra", '}'),
    ("Tild", '~'),
];

/// Decodes a KORE identifier (without the `Lbl` prefix) into the K label it encodes.
/// Returns the input unchanged when it is not a well-formed encoding.
pub fn demangle(name: &str) -> String {
    let body = name.strip_prefix("Lbl").unwrap_or(name);
    let mut out = String::new();
    let mut quoted = false;
    let bytes: Vec<char> = body.chars().collect();
    let mut i = 0;
    while i < bytes.len() {
        let ch = bytes[i];
        if ch == '\'' {
            quoted = !quoted;
            i += 1;
            continue;
        }
        if quoted {
            if i + 4 > bytes.len() {
                return name.to_string();
            }
            let code: String = bytes[i..i + 4].iter().collect();
            match CODES.iter().find(|(c, _)| *c == code) {
                Some((_, c)) => out.push(*c),
                None => return name.to_string(),
            }
            i += 4;
        } else {
            out.push(ch);
            i += 1;
        }
    }
    if quoted {
        return name.to_string();
    }
    out
}

/// The sort name without KORE's `Sort` prefix.
pub fn short_sort(sort: &str) -> &str {
    sort.strip_prefix("Sort").unwrap_or(sort)
}

/// A shorter label for a production: K's generated labels are
/// `<syntax>_<MODULE>_<Result>_<Arg>...`; strip the sort and module suffix when present.
pub fn short_label(label: &str, result: &str, args: &[String]) -> Option<String> {
    let mut suffix = format!("_{}", short_sort(result));
    for a in args {
        suffix.push('_');
        suffix.push_str(short_sort(a));
    }
    let rest = label.strip_suffix(&suffix)?;
    // `_MODULE-NAME`: upper case, digits and dashes
    let idx = rest.rfind('_')?;
    let module = &rest[idx + 1..];
    if module.is_empty()
        || !module
            .chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '-')
    {
        return None;
    }
    let short = &rest[..idx];
    if short.is_empty() {
        return None;
    }
    Some(short.to_string())
}

/// A Lean identifier component for an arbitrary string: plain when it is a valid identifier
/// that is not a keyword, otherwise quoted with `«»`.
pub fn ident(s: &str) -> String {
    let plain = !s.is_empty()
        && s.chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !LEAN_KEYWORDS.contains(&s);
    if plain {
        s.to_string()
    } else {
        assert!(
            !s.contains('»') && !s.contains('«') && !s.contains('\n'),
            "unquotable name {s:?}"
        );
        format!("«{s}»")
    }
}

const LEAN_KEYWORDS: &[&str] = &[
    "fun",
    "let",
    "in",
    "if",
    "then",
    "else",
    "match",
    "with",
    "do",
    "for",
    "where",
    "end",
    "at",
    "by",
    "have",
    "show",
    "from",
    "open",
    "namespace",
    "section",
    "theorem",
    "def",
    "inductive",
    "structure",
    "class",
    "instance",
    "mutual",
    "import",
    "return",
    "true",
    "false",
    "Type",
    "Prop",
    "Sort",
    "deriving",
    "variable",
    "universe",
    "axiom",
    "example",
    "abbrev",
    "notation",
    "macro",
    "syntax",
    "local",
    "private",
    "protected",
    "partial",
    "unsafe",
    "noncomputable",
    "calc",
    "suffices",
    "this",
    "try",
    "catch",
    "finally",
    "unless",
    "mut",
    "break",
    "continue",
    "nomatch",
    "nofun",
    "forall",
    "exists",
    "Exists",
];

/// A Lean string literal.
pub fn string_lit(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                out.push_str(&format!("\\x{:02x}", c as u32))
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn demangles() {
        assert_eq!(demangle("Lbl'UndsPlus'Int'Unds'"), "_+Int_");
        assert_eq!(demangle("Lbl'-LT-'k'-GT-'"), "<k>");
        assert_eq!(
            demangle("Lbl-'UndsUnds'EXPR-SYNTAX'Unds'Expr'Unds'Expr"),
            "-__EXPR-SYNTAX_Expr_Expr"
        );
        assert_eq!(
            short_label(
                "_+__EXPR-SYNTAX_Expr_Expr_Expr",
                "SortExpr",
                &["SortExpr".into(), "SortExpr".into()]
            ),
            Some("_+_".into())
        );
    }
}
