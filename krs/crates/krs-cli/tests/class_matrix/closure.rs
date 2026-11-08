//! K3's comparison: a case's own K sentences, as its source emits them and as the source
//! `krs expand` prints for it emits them, compared raw and after the normalization that equates
//! spellings with one meaning in K:
//!
//! - alpha-renaming: variables are renamed `V0`, `V1`, ... in order of first appearance;
//! - `<k> A => B ... </k>` ≡ `<k> A ~> T:K => B ~> T:K </k>`, and `<k> A ... </k>` ≡
//!   `<k> A ~> T:K </k>`, when `T` occurs nowhere else in the sentence;
//! - an anonymous frame `...` ≡ a named frame variable that occurs once, at the end of its cell,
//!   and ≡ the anonymous variable `_` there, which is such a variable;
//! - a generated sentence label, the item path `label(<namespace>--…--<item>)` or the digest
//!   `label(krsRule_<digest>)`, is `label(krsRule_DIGEST)`, and a lifted local function's symbol,
//!   `krsLocal_<digest>`, is `krsLocal_DIGEST`: both name the sentence's source, not its
//!   meaning;
//! - a variable that occurs once in its sentence is the anonymous variable: `X:Int` ≡ `_:Int`
//!   ([`once_used_as_anonymous`]).
//!
//! [`case_k`], the K the table records, is the emitted K under every rule but the last: it keeps
//! each variable the emitter names, so a table entry shows the K as written.

use std::collections::{BTreeMap, BTreeSet};

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
/// are left out, and so are the comments that name the Rust source rather than the K
/// ([`krs_test_support::without_source_comments`]): the artifact's header (the comment lines
/// that open it) and the `// KRS` line above a sentence, which a case and its printed source
/// spell differently for one sentence (a shorthand branch and the equation fn `krs expand`
/// prints for it). Rustdoc, capability lines and any other comment stay sentences.
#[must_use]
pub fn sentences(text: &str) -> Vec<String> {
    let mut sentences = Vec::<String>::new();
    let mut open = false;
    for line in krs_test_support::without_source_comments(text).lines() {
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

/// A case's K as `expected.toml` records it: the sentences it adds to its base, each
/// normalized, with the case's tag (which names its command, its label, and its other items)
/// written `TAG`, in sorted order, one sentence per paragraph. The tag is spelled as written, in
/// upper case, and capitalized, as a label derived from a fn `case_<tag>` writes it
/// (`caseD3ff6113` for the tag `d3ff6113`).
#[must_use]
pub fn case_k(additions: &[String], tag: &str) -> String {
    let upper = tag.to_uppercase();
    let mut characters = tag.chars();
    let capitalized = characters
        .next()
        .map(|first| first.to_uppercase().chain(characters).collect::<String>())
        .unwrap_or_default();
    let mut sentences = additions
        .iter()
        .map(|sentence| {
            recorded(sentence)
                .replace(tag, "TAG")
                .replace(&upper, "TAG")
                .replace(&capitalized, "TAG")
        })
        .collect::<Vec<_>>();
    sentences.sort();
    let mut text = sentences.join("\n\n");
    text.push('\n');
    text
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
/// A configuration variable, `$PGM:Stmt`, is named by the program's input and keeps its name, and
/// the anonymous variable `_`, written with its sort or without, names none: each occurrence is
/// a variable of its own, which one name for all of them would equate.
fn variables<'a>(tokens: &[&'a str]) -> Vec<&'a str> {
    let mut found = Vec::new();
    for (index, window) in tokens.windows(2).enumerate() {
        let (name, colon) = (window[0], window[1]);
        if index > 0 && tokens[index - 1] == "$" {
            continue;
        }
        let starts = name
            .chars()
            .next()
            .is_some_and(|first| first.is_uppercase() || first == '_');
        if colon == ":" && starts && name != "_" && !found.contains(&name) {
            found.push(name);
        }
    }
    found
}

/// One sentence normalized as the module documentation says.
#[must_use]
pub fn normalize(sentence: &str) -> String {
    renamed(&once_used_as_anonymous(&spelled(sentence)))
}

/// One sentence as [`case_k`] records it: [`normalize`] without its reading of a variable used
/// once as `_`.
fn recorded(sentence: &str) -> String {
    renamed(&spelled(sentence))
}

/// The sentence with its frames and generated labels normalized, its variables as written.
fn spelled(sentence: &str) -> String {
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
    // The anonymous variable as a frame: after an item, at the end of its cell.
    let mut framed = String::with_capacity(text.len());
    let mut rest = text.as_str();
    while let Some(index) = rest.find(" _ </") {
        let before = &rest[..index];
        framed.push_str(before);
        framed.push_str(if before.ends_with('>') {
            " _ </"
        } else {
            " ... </"
        });
        rest = &rest[index + " _ </".len()..];
    }
    framed.push_str(rest);
    generated_labels(&framed)
}

/// The variables K reserves, whose name is their meaning: a context's hole and a context alias's
/// place.
const RESERVED_VARIABLES: &[&str] = &["HOLE", "HERE"];

/// `text` with each variable that occurs once in it written `_`, its sort kept: `X:Int` is
/// `_:Int`.
///
/// A rule's variable that occurs once is matched and never used: no other occurrence equates it
/// with another part of the subject, and nothing on the right-hand side or in a condition reads
/// it. It constrains the match by its sort only, which is what the anonymous variable of that
/// sort does, so the two spell one rule. A claim's or an equation's left-hand variable is the
/// same: it is quantified over every term of its sort, as `_` is. The emitted K has no other
/// once-used variable that this would change:
/// - an existential `?X` (`#[k::exists]`, a claim's) and a fresh `!X` are no anonymous
///   variables, so a variable written after `?` or `!` is kept, and so is a configuration
///   variable `$X` ([`variables`]);
/// - a context's `HOLE` and an alias's `HERE` name the hole by their name, and are kept;
/// - a variable written only on a rule's right-hand side, which `_` would not mean, is refused
///   before any K is emitted, and a claim's right-hand side writes its unknowns `?X`; a desugar
///   clause's right-hand variable (KF-046) is listed again in its `unboundVariables(X)`, so it
///   occurs twice, and a `_` there means what a variable used once there does.
///
/// A variable's occurrences are the tokens that spell it outside a sort position (after `:` or
/// `:>`), where a sort of the same name is written, so the count does not change when the
/// variables are renamed.
fn once_used_as_anonymous(text: &str) -> String {
    let all = tokens(text);
    let sort_position = |index: usize| {
        (index > 0 && all[index - 1] == ":")
            || (index > 1 && all[index - 1] == ">" && all[index - 2] == ":")
    };
    let once = variables(&all)
        .into_iter()
        .filter(|name| !RESERVED_VARIABLES.contains(name))
        .filter(|name| {
            let mut at = all
                .iter()
                .enumerate()
                .filter(|(index, token)| *token == name && !sort_position(*index))
                .map(|(index, _)| index);
            match (at.next(), at.next()) {
                (Some(index), None) => index == 0 || !matches!(all[index - 1], "?" | "!" | "$"),
                _ => false,
            }
        })
        .collect::<BTreeSet<_>>();
    all.iter()
        .enumerate()
        .map(|(index, token)| {
            if once.contains(token) && !sort_position(index) {
                "_"
            } else {
                token
            }
        })
        .collect()
}

/// `text` with its variables renamed `V0`, `V1`, .. in order of first appearance.
fn renamed(text: &str) -> String {
    let all = tokens(text);
    let renamed = variables(&all)
        .into_iter()
        .enumerate()
        .map(|(index, name)| (name, format!("V{index}")))
        .collect::<BTreeMap<_, _>>();
    all.iter()
        .map(|token| renamed.get(token).map_or(*token, String::as_str))
        .collect()
}

/// `text` with the digest of every generated sentence label, `krsRule_<hex>`, and of every lifted
/// local function's symbol, `krsLocal_<hex>`, written `DIGEST`, and every item-path label,
/// `<namespace>--…--<item>`, written `krsRule_DIGEST`.
fn generated_labels(text: &str) -> String {
    // The digests first: `digests` would read the `D` of a written `krsRule_DIGEST` as a digit.
    let text = ["krsRule_", "krsLocal_"]
        .into_iter()
        .fold(text.to_owned(), |text, prefix| digests(&text, prefix));
    item_path_labels(&text)
}

/// `text` with every item-path label written `krsRule_DIGEST`: a maximal run of label characters
/// (ASCII letters, digits, `_`, `-`) that is a lowercase namespace and one or more identifiers,
/// each after `--`. K syntax writes no such run otherwise: its operators are spaced from their
/// operands, and a variable or a sort starts with an uppercase letter.
fn item_path_labels(text: &str) -> String {
    let label_character =
        |character: char| character.is_ascii_alphanumeric() || "_-".contains(character);
    let identifier = |part: &str| {
        part.chars()
            .next()
            .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
            && part
                .chars()
                .all(|character| character.is_ascii_alphanumeric() || character == '_')
    };
    let item_path = |run: &str| {
        let mut parts = run.split("--");
        let namespace = parts.next().unwrap_or_default();
        namespace
            .chars()
            .next()
            .is_some_and(|first| first.is_ascii_lowercase())
            && namespace.chars().all(|character| {
                character.is_ascii_lowercase() || character.is_ascii_digit() || character == '_'
            })
            && run.contains("--")
            && parts.all(identifier)
    };
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find(label_character) {
        let (before, from) = rest.split_at(start);
        out.push_str(before);
        let end = from
            .find(|character| !label_character(character))
            .unwrap_or(from.len());
        let (run, after) = from.split_at(end);
        out.push_str(if item_path(run) {
            "krsRule_DIGEST"
        } else {
            run
        });
        rest = after;
    }
    out.push_str(rest);
    out
}

/// `text` with the hex digits after each `prefix` written `DIGEST`.
fn digests(text: &str, prefix: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(index) = rest.find(prefix) {
        let (before, after) = rest.split_at(index + prefix.len());
        out.push_str(before);
        let digits = after
            .find(|character: char| !character.is_ascii_hexdigit())
            .unwrap_or(after.len());
        out.push_str(if digits > 0 { "DIGEST" } else { "" });
        rest = &after[digits..];
    }
    out.push_str(rest);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_anonymous_variable_keeps_its_name_at_every_occurrence() {
        assert_eq!(
            normalize("<k> _:KItem ~> c ( X:KItem , _ ) => X:KItem ... </k>"),
            "<k> _:KItem ~> c ( V0:KItem , _ ) => V0:KItem ... </k>"
        );
    }

    #[test]
    fn a_variable_used_once_is_the_anonymous_variable() {
        // A head `_` of a `for Stmt` clause and the binder of its sort its print writes.
        assert_eq!(
            normalize("rule [drop]:\n<k> _Stmt:Stmt => .K ... </k>"),
            normalize("rule [drop]:\n<k> _:Stmt => .K ... </k>")
        );
        assert_eq!(
            normalize("rule f ( X:Int , Y:Int ) => Y:Int"),
            "rule f ( _:Int , V0:Int ) => V0:Int"
        );
        // A claim's left-hand variable is quantified over its sort, as `_` is.
        assert_eq!(
            normalize("claim <k> run ( N:Int ) => .K ... </k>"),
            normalize("claim <k> run ( _:Int ) => .K ... </k>")
        );
        // A variable named as its sort is counted where it is written, not where its sort is.
        assert_eq!(
            normalize("rule <k> Stmt:Stmt => .K ... </k>"),
            normalize("rule <k> X:Stmt => .K ... </k>")
        );
        assert_eq!(
            normalize("rule <k> Stmt:Stmt => .K ... </k>"),
            "rule <k> _:Stmt => .K ... </k>"
        );
        // Kept: an existential, a fresh variable, a configuration variable, the hole of a
        // context, and a variable used twice.
        for kept in [
            "rule <k> a => ?X:Int ... </k>",
            "claim <k> a => b ... </k> ensures ?X:Int ==Int 1",
            "rule <k> a => !X:Int ... </k>",
            "configuration <k> $PGM:Stmt </k>",
            "context f ( HOLE:Exp , _:Exp )",
            "rule <k> X:Int => X:Int ... </k>",
        ] {
            assert!(!normalize(kept).contains("_:Int"), "{kept}");
            assert!(!normalize(kept).contains("_:Stmt"), "{kept}");
            assert!(!normalize(kept).contains("( _:Exp , _:Exp )"), "{kept}");
        }
        // The table records each variable as the emitter names it.
        assert_eq!(
            case_k(&["rule f ( X:Int ) => 0".to_owned()], "d3ff6113"),
            "rule f ( V0:Int ) => 0\n"
        );
    }

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
    fn an_anonymous_frame_and_a_generated_label_are_normalized() {
        assert_eq!(
            normalize("rule [r]:\n<stack> ListItem(X:KItem) _ </stack>\n<pc> _ </pc>"),
            normalize("rule [r]:\n<stack> ListItem(Y:KItem) ... </stack>\n<pc> _ </pc>")
        );
        assert_eq!(
            normalize("rule f ( 1 ) => 0 [label(krsRule_0123abcd)]"),
            normalize("rule f ( 1 ) => 0 [label(krsRule_ffff0000)]")
        );
        assert_eq!(
            normalize("rule f ( 1 ) => 0 [label(nat--case_x)]"),
            "rule f ( 1 ) => 0 [label(krsRule_DIGEST)]"
        );
        assert_eq!(
            normalize("rule f ( 1 ) => 0 [label(org_krs_class_9--cases--case_x_2)]"),
            normalize("rule f ( 1 ) => 0 [label(krsRule_0123abcd)]")
        );
        assert_eq!(
            normalize(
                "// krs-capability: AnywhereRule nat--case_x\nrule f ( 1 ) => 0 [anywhere, label(nat--case_x)]"
            ),
            "// krs-capability: AnywhereRule krsRule_DIGEST\nrule f ( 1 ) => 0 [anywhere, label(krsRule_DIGEST)]"
        );
        // An authored label, a K operator, and a variable keep their spelling.
        for kept in [
            "rule [case-TAG]:\n<k> a => b ... </k>",
            "rule f ( X:Int ) => X:Int -Int 1 [label(go-on)]",
            "rule f ( X:Int ) => --X:Int [label(case_x)]",
        ] {
            assert!(!normalize(kept).contains("krsRule_DIGEST"), "{kept}");
        }
        assert!(normalize("rule [r]:\n<pc> _ </pc>").contains("<pc> _ </pc>"));
    }

    #[test]
    fn sentences_skip_the_header_and_source_lines_and_keep_other_comments() {
        let text = "// Generated by `krs emit-k` from p. Do not edit; edit the Rust sources and emit again.\n\
            // The `// KRS <package>/<file>: <item>` line above a sentence names the Rust item it comes from.\n\n\
            module M\n  // KRS p/src/lib.rs: Machine\n  configuration\n    <k> $PGM:K </k>\n\n\
            \x20 // KRS p/src/lib.rs: F, branch 2\n  // krs-capability: AnywhereRule m--f_2\n\
            \x20 rule f ( 2 ) => 0 [anywhere, label(m--f_2)]\n  // Rustdoc of a production.\n\
            \x20 syntax A ::= \"a\"\n// An unindented comment after the header.\nendmodule\n";
        assert_eq!(
            sentences(text),
            [
                "configuration\n<k> $PGM:K </k>",
                "// krs-capability: AnywhereRule m--f_2",
                "rule f ( 2 ) => 0 [anywhere, label(m--f_2)]",
                "// Rustdoc of a production.",
                "syntax A ::= \"a\"",
                "// An unindented comment after the header.",
            ]
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
