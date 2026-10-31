//! String and quoted-label codecs used by textual KAST.

pub use k_rust_domain::string::{HEX_ESCAPES, NAMED_ESCAPES, quote, quote_bytes, unquote};

pub fn quote_label(value: &str) -> String {
    format!("`{}`", value.replace('\\', "\\\\").replace('`', "\\`"))
}

pub fn unquote_label(input: &str) -> Result<String, String> {
    if !input.starts_with('`') || !input.ends_with('`') || input.len() < 2 {
        return Err("expected a backtick-quoted label".into());
    }
    let mut output = String::new();
    let mut characters = input[1..input.len() - 1].chars();
    while let Some(character) = characters.next() {
        if character == '\\' {
            match characters.next().ok_or("truncated label escape")? {
                '\\' => output.push('\\'),
                '`' => output.push('`'),
                _ => return Err("unsupported label escape".into()),
            }
        } else if character.is_control() {
            return Err("control character in label".into());
        } else {
            output.push(character);
        }
    }
    Ok(output)
}
