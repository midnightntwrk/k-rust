//! K3's comparison: a case's own K sentences, as its source emits them and as the source
//! `krs expand` prints for it emits them, compared raw and after the normalization that equates
//! spellings with one meaning in K:
//!
//! - alpha-renaming: variables are renamed `V0`, `V1`, ... in order of first appearance;
//! - `<k> A => B ... </k>` ≡ `<k> A ~> T:K => B ~> T:K </k>`, and `<k> A ... </k>` ≡
//!   `<k> A ~> T:K </k>`, when `T` occurs nowhere else in the sentence;
//! - an anonymous frame `...` ≡ a named frame variable that occurs once, at the end of its cell.

use std::collections::BTreeMap;

/// What K3 found for one case.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Closure {
    /// The printed source emits the case's sentences byte for byte.
    Identical,
    /// The sentences are equal after normalization.
    Normalized,
    /// The sentences differ after normalization: the original and the printed ones, normalized.
    Different {
        /// The case's own sentences, normalized.
        original: Vec<String>,
        /// The printed source's sentences for the case, normalized.
        printed: Vec<String>,
    },
    /// The printed source, or `krs expand` itself, refuses the case: what it reported.
    Refused(String),
}

impl Closure {
    /// The form's column in K3's counts.
    #[must_use]
    pub const fn column(&self) -> &'static str {
        match self {
            Self::Identical => "byte-identical",
            Self::Normalized => "equal after normalization",
            Self::Different { .. } => "different",
            Self::Refused(_) => "printed surface refused",
        }
    }

    /// Whether the case meets K3.
    #[must_use]
    pub const fn conforms(&self) -> bool {
        matches!(self, Self::Identical | Self::Normalized)
    }

    /// The signature `pending.toml` records for a deviation.
    #[must_use]
    pub fn signature(&self) -> String {
        match self {
            Self::Refused(reported) => format!("printed surface refused: {reported}"),
            other => other.column().to_owned(),
        }
    }
}

/// The sentences of emitted K text: each line indented at most two spaces starts one, and the
/// more deeply indented lines after it continue it. Module headers, imports, and `endmodule`
/// are left out.
#[must_use]
pub fn sentences(text: &str) -> Vec<String> {
    let mut sentences = Vec::<String>::new();
    let mut open = false;
    for line in text.lines() {
        let indent = line.len() - line.trim_start().len();
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if indent <= 2 {
            open = !(trimmed.starts_with("module ")
                || trimmed == "endmodule"
                || trimmed.starts_with("imports ")
                || trimmed.starts_with("requires "));
            if open {
                sentences.push(trimmed.to_owned());
            }
        } else if open && let Some(last) = sentences.last_mut() {
            last.push('\n');
            last.push_str(trimmed);
        }
    }
    sentences
}

/// The sentences of `definition` that `base` lacks, counted as a multiset, in order.
#[must_use]
pub fn additions(definition: &[String], base: &[String]) -> Vec<String> {
    let mut remaining = BTreeMap::<&str, usize>::new();
    for sentence in base {
        *remaining.entry(sentence.as_str()).or_default() += 1;
    }
    definition
        .iter()
        .filter(|sentence| match remaining.get_mut(sentence.as_str()) {
            Some(count) if *count > 0 => {
                *count -= 1;
                false
            }
            _ => true,
        })
        .cloned()
        .collect()
}

/// Compare a case's own sentences with the printed source's.
#[must_use]
pub fn compare(original: &[String], printed: &[String]) -> Closure {
    let sorted = |sentences: &[String]| {
        let mut sentences = sentences.to_vec();
        sentences.sort();
        sentences
    };
    if sorted(original) == sorted(printed) {
        return Closure::Identical;
    }
    let normalized = |sentences: &[String]| {
        let mut sentences = sentences
            .iter()
            .map(|text| normalize(text))
            .collect::<Vec<_>>();
        sentences.sort();
        sentences
    };
    let (original, printed) = (normalized(original), normalized(printed));
    if original == printed {
        Closure::Normalized
    } else {
        Closure::Different { original, printed }
    }
}

/// The tokens of a sentence: runs of identifier characters, and every other character alone.
fn tokens(text: &str) -> Vec<&str> {
    let mut tokens = Vec::new();
    let mut start = None;
    for (index, character) in text.char_indices() {
        let word = character.is_alphanumeric() || character == '_' || character == '\'';
        match (word, start) {
            (true, None) => start = Some(index),
            (false, Some(begin)) => {
                tokens.push(&text[begin..index]);
                start = None;
            }
            _ => {}
        }
        if !word {
            tokens.push(&text[index..index + character.len_utf8()]);
        }
    }
    if let Some(begin) = start {
        tokens.push(&text[begin..]);
    }
    tokens
}

/// The variables of a sentence: every name written `Name:Sort`, capitalized or starting with `_`.
fn variables<'a>(tokens: &[&'a str]) -> Vec<&'a str> {
    let mut found = Vec::new();
    for window in tokens.windows(2) {
        let (name, colon) = (window[0], window[1]);
        let starts = name
            .chars()
            .next()
            .is_some_and(|first| first.is_uppercase() || first == '_');
        if colon == ":" && starts && !found.contains(&name) {
            found.push(name);
        }
    }
    found
}

/// One sentence normalized as the module documentation says.
#[must_use]
pub fn normalize(sentence: &str) -> String {
    let mut text = sentence.to_owned();
    let all = tokens(sentence);
    let occurrences = |name: &str| all.iter().filter(|token| **token == name).count();
    for variable in variables(&all) {
        let annotated = |sort: &str| format!(" ~> {variable}:{sort}");
        // An explicit computation rest on both sides of the cell's rewrite, or alone.
        let rest = annotated("K");
        if occurrences(variable) == 2 && text.matches(&rest).count() == 2 {
            text = text.replacen(&format!("{rest} => "), " => ", 1);
            text = text.replacen(&format!("{rest} </k>"), " ... </k>", 1);
        } else if occurrences(variable) == 1 && text.contains(&format!("{rest} </k>")) {
            text = text.replacen(&format!("{rest} </k>"), " ... </k>", 1);
        }
        // A named frame used once, at the end of its cell.
        if occurrences(variable) == 1 {
            for sort in ["Map", "List", "Set", "Bag"] {
                let frame = format!(" {variable}:{sort} </");
                if text.contains(&frame) {
                    text = text.replacen(&frame, " ... </", 1);
                }
            }
        }
    }
    let all = tokens(&text);
    let renamed = variables(&all)
        .into_iter()
        .enumerate()
        .map(|(index, name)| (name, format!("V{index}")))
        .collect::<BTreeMap<_, _>>();
    all.iter()
        .map(|token| renamed.get(token).map_or(*token, String::as_str))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_computation_rest_and_alpha_renaming_are_normalized() {
        let original = "rule [case-2]:\n<k> c2 => .K ... </k>\n<stack> ListItem(X:KItem) Krs_RestStack:List </stack>";
        let printed = "rule [case-2]:\n<k> c2 ~> Tail:K => .K ~> Tail:K </k>\n<stack> ListItem(X:KItem) Rest:List </stack>";
        assert_eq!(normalize(original), normalize(printed));
        assert_eq!(
            compare(&[original.to_owned()], &[printed.to_owned()]),
            Closure::Normalized
        );
    }

    #[test]
    fn a_frame_used_twice_is_kept() {
        let used = "rule [r]:\n<env> M:Map </env>\n<pc> 0 => size(M:Map) </pc>";
        assert!(normalize(used).contains("V0:Map </env>"));
        let once = "rule [r]:\n<env> (K:Int |-> V:Int) M:Map </env>";
        assert_eq!(
            normalize(once),
            normalize("rule [r]:\n<env> (A:Int |-> B:Int) ... </env>")
        );
    }

    #[test]
    fn sentences_split_at_shallow_lines_and_additions_subtract_the_base() {
        let text =
            "module M\n  imports N\n  syntax A ::= \"a\"\n  rule [x]:\n    <k> a </k>\nendmodule\n";
        let all = sentences(text);
        assert_eq!(all, ["syntax A ::= \"a\"", "rule [x]:\n<k> a </k>"]);
        assert_eq!(additions(&all, &all[..1]), ["rule [x]:\n<k> a </k>"]);
    }
}
