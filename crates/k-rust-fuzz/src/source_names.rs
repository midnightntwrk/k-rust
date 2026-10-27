//! The location-independent names under which a campaign's identity digests a definition's
//! sources, and under which its report names them (ARCHITECTURE 5.4, FZ-SETUP fix round,
//! FZ-REPLAY-WHOLE S1).
//!
//! `krust kcompile` records each source under its canonical absolute path, an in-process host
//! under whatever name it gave (the bindings default to `definition.k`). Where the sources sit
//! is not part of what a campaign does: what it does depends on the sources' contents, the
//! sentences they hold, their positions and which source requires which. A source location is
//! therefore named by the source's path relative to the directory of the main module's file
//! (that file by its own name, `./imp.k`), which is the same wherever the checkout lies, and an
//! unrelated name (a `krust-builtin://` URI) as it is. The identity digests every source
//! reference so, and the report writes every source location so ([`SourceNames::location`]):
//! the report's rule locations and finding positions are then functions of what the identity
//! digests. The main file's own name is part of both, since the report and rule references name
//! rules by it. Relative names are injective on the sources of one definition, so the inclusion
//! structure is kept; the contents stay digested through each source's content hash and the
//! definitions' sentences, positions and provenance.

use std::borrow::Cow;

use k_rust::definition::Definition;
use k_rust::kore::{ast::KoreString, string};

/// The JSON keys of `KRUST-PROVENANCE` whose string values name a source: the `Source`
/// attribute of a sentence or module, and a source-table entry's logical name.
const JSON_KEYS: [&str; 2] = ["\"org.kframework.attributes.Source\":", "\"logical\":"];

/// The KORE attribute whose argument names a source, as `"Source(<name>)"`.
const KORE_SOURCE: &str = "attributes'Stop'Source{}(";

/// A lexically normalized path: absolute or relative, its components without `.` and with each
/// `..` that follows a name resolved.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LexicalPath {
    absolute: bool,
    parts: Vec<String>,
}

impl LexicalPath {
    /// `name` as a path, `None` for a name that is a URI (`scheme://…`).
    fn parse(name: &str) -> Option<Self> {
        if name.contains("://") {
            return None;
        }
        let absolute = name.starts_with('/');
        let mut parts: Vec<String> = Vec::new();
        for part in name.split('/') {
            match part {
                "" | "." => {}
                ".." => {
                    if parts.last().is_some_and(|last| last != "..") {
                        parts.pop();
                    } else if !absolute {
                        parts.push("..".to_owned());
                    }
                }
                _ => parts.push(part.to_owned()),
            }
        }
        Some(Self { absolute, parts })
    }
}

/// How one definition's source names are written into its identity.
#[derive(Clone, Debug)]
pub(crate) struct SourceNames {
    /// The directory of the main module's file, when its recorded name is a path.
    base: Option<LexicalPath>,
}

impl SourceNames {
    /// The names of `frontend`'s sources, relative to the file its main module is written in
    /// (its `Source` attribute). Without one, every name is kept as it is.
    pub(crate) fn of(frontend: &Definition) -> Self {
        let base = frontend
            .main_module()
            .and_then(|module| module.attributes.source())
            .and_then(LexicalPath::parse)
            .map(|mut path| {
                path.parts.pop();
                path
            });
        Self { base }
    }

    /// The identity's name of the source recorded as `name`: `./` and its path relative to the
    /// directory of the main module's file (with `..` steps for a source outside it; the main
    /// module's file is `./` and its own name); the name itself for a URI, or for a path that
    /// cannot be made relative to the base (an absolute path under a relative base, or the
    /// reverse).
    pub(crate) fn name<'a>(&self, name: &'a str) -> Cow<'a, str> {
        let (Some(base), Some(path)) = (&self.base, LexicalPath::parse(name)) else {
            return Cow::Borrowed(name);
        };
        if base.absolute != path.absolute {
            return Cow::Borrowed(name);
        }
        let common = base
            .parts
            .iter()
            .zip(&path.parts)
            .take_while(|(left, right)| left == right)
            .count();
        // A `..` left in the base names a directory whose name the path does not give, so no
        // relative name can be formed.
        if base.parts[common..].iter().any(|part| part == "..") {
            return Cow::Borrowed(name);
        }
        let mut relative = String::from(".");
        for _ in common..base.parts.len() {
            relative.push_str("/..");
        }
        for part in &path.parts[common..] {
            relative.push('/');
            relative.push_str(part);
        }
        Cow::Owned(relative)
    }

    /// The report's name of the source recorded as `name`: [`Self::name`] without its leading
    /// `./` (`imp.k`, `lib/x.k`, `../lib/y.k`), so that a location prints as the path a reader
    /// writes from the main module's directory, and a rule reference built from it names the
    /// file ([`crate::target::RuleLocation`]).
    pub(crate) fn location(&self, name: &str) -> String {
        let named = self.name(name);
        named.strip_prefix("./").unwrap_or(&named).to_owned()
    }

    /// `json`, a compact `KRUST-PROVENANCE` document, with every source name of [`JSON_KEYS`]
    /// replaced by [`Self::name`]. A value that is not a JSON string is kept.
    pub(crate) fn provenance_json(&self, json: &str) -> String {
        let mut result = String::with_capacity(json.len());
        // The cursor, and the next occurrence of each key at or after it: each key is searched
        // for again only once the cursor has passed its occurrence, so the scan is linear.
        let mut cursor = 0;
        let mut next: Vec<Option<usize>> = JSON_KEYS.iter().map(|key| json.find(key)).collect();
        loop {
            for (key, at) in JSON_KEYS.iter().zip(next.iter_mut()) {
                if at.is_some_and(|at| at < cursor) {
                    *at = json[cursor..].find(key).map(|found| cursor + found);
                }
            }
            let Some((at, key)) = next
                .iter()
                .zip(JSON_KEYS)
                .filter_map(|(at, key)| at.map(|at| (at, key)))
                .min_by_key(|(at, _)| *at)
            else {
                break;
            };
            let value_start = at + key.len();
            result.push_str(&json[cursor..value_start]);
            cursor = value_start;
            let Some(length) = quoted_length(&json[cursor..]) else {
                continue;
            };
            let token = &json[cursor..cursor + length];
            match serde_json::from_str::<String>(token) {
                Ok(value) => result.push_str(
                    &serde_json::to_string(self.name(&value).as_ref())
                        .expect("a string serializes"),
                ),
                Err(_) => result.push_str(token),
            }
            cursor += length;
        }
        result.push_str(&json[cursor..]);
        result
    }

    /// `kore`, KORE text, with the name in every `Source{}("Source(<name>)")` attribute replaced
    /// by [`Self::name`] (an argument of another form is kept), and its layout normalized
    /// ([`normalized_layout`]): the printer breaks a line by the width of what it prints, so the
    /// length of a path moves line breaks around the attribute that holds it.
    pub(crate) fn kore(&self, kore: &str) -> String {
        normalized_layout(&self.renamed_kore(kore))
    }

    fn renamed_kore(&self, kore: &str) -> String {
        let mut result = String::with_capacity(kore.len());
        let mut rest = kore;
        while let Some(at) = rest.find(KORE_SOURCE) {
            let mut value_start = at + KORE_SOURCE.len();
            value_start += rest[value_start..].len() - rest[value_start..].trim_start().len();
            result.push_str(&rest[..value_start]);
            rest = &rest[value_start..];
            let Some(length) = quoted_length(rest) else {
                continue;
            };
            let token = &rest[..length];
            let renamed = string::unquote(token).ok().and_then(|value| {
                let text = std::str::from_utf8(value.as_bytes()).ok()?;
                let name = text.strip_prefix("Source(")?.strip_suffix(')')?;
                Some(string::quote(&KoreString::from(format!(
                    "Source({})",
                    self.name(name)
                ))))
            });
            result.push_str(renamed.as_deref().unwrap_or(token));
            rest = &rest[length..];
        }
        result.push_str(rest);
        result
    }
}

/// `kore` with its layout normalized: outside string literals, a run of whitespace is dropped
/// next to a delimiter (`( ) [ ] { } ,`) and is one space elsewhere. KORE reads whitespace only as
/// a separator of tokens, which a delimiter or one space still separates, so two texts with the
/// same normal layout have the same tokens; literals are kept byte for byte.
fn normalized_layout(kore: &str) -> String {
    let delimiter = |character: char| "()[]{},".contains(character);
    let mut result = String::with_capacity(kore.len());
    let mut pending_space = false;
    let mut characters = kore.chars();
    while let Some(character) = characters.next() {
        if character.is_whitespace() {
            pending_space = true;
            continue;
        }
        if pending_space
            && !delimiter(character)
            && result
                .chars()
                .next_back()
                .is_some_and(|last| !delimiter(last))
        {
            result.push(' ');
        }
        pending_space = false;
        result.push(character);
        if character == '"' {
            while let Some(inner) = characters.next() {
                result.push(inner);
                match inner {
                    '\\' => {
                        if let Some(escaped) = characters.next() {
                            result.push(escaped);
                        }
                    }
                    '"' => break,
                    _ => {}
                }
            }
        }
    }
    result
}

/// The byte length of the string literal `text` starts with (both quotes included), escapes
/// being a backslash and the character after it; `None` when `text` starts with no complete
/// literal.
fn quoted_length(text: &str) -> Option<usize> {
    let bytes = text.as_bytes();
    if bytes.first() != Some(&b'"') {
        return None;
    }
    let mut index = 1;
    while index < bytes.len() {
        match bytes[index] {
            b'\\' => index += 2,
            b'"' => return Some(index + 1),
            _ => index += 1,
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::{LexicalPath, SourceNames};

    fn names(main: &str) -> SourceNames {
        SourceNames {
            base: LexicalPath::parse(main).map(|mut path| {
                path.parts.pop();
                path
            }),
        }
    }

    #[test]
    fn sources_are_named_relative_to_the_main_file() {
        let at_a = names("/a/src/imp.k");
        let at_b = names("/b/deeper/src/imp.k");
        for (left, right) in [
            ("/a/src/imp.k", "/b/deeper/src/imp.k"),
            ("/a/src/expr.k", "/b/deeper/src/expr.k"),
            ("/a/src/lib/x.k", "/b/deeper/src/lib/x.k"),
            ("/a/lib/y.k", "/b/deeper/lib/y.k"),
            ("krust-builtin://domains.md", "krust-builtin://domains.md"),
        ] {
            assert_eq!(at_a.name(left), at_b.name(right), "{left} / {right}");
        }
        assert_eq!(at_a.name("/a/src/imp.k"), "./imp.k");
        assert_eq!(at_a.location("/a/src/imp.k"), "imp.k");
        assert_eq!(at_a.location("/a/lib/y.k"), "../lib/y.k");
        assert_eq!(
            at_a.location("krust-builtin://domains.md"),
            "krust-builtin://domains.md"
        );
        assert_eq!(at_a.name("/a/src/expr.k"), "./expr.k");
        assert_eq!(at_a.name("/a/lib/y.k"), "./../lib/y.k");
        assert_eq!(at_a.name("/a/src/./sub/../expr.k"), "./expr.k");
        // The bindings' default entry name, with its requires named relative to it: the main
        // file's own name is part of the names.
        let virtual_names = names("definition.k");
        assert_eq!(virtual_names.name("definition.k"), "./definition.k");
        assert_ne!(
            virtual_names.name("definition.k"),
            at_a.name("/a/src/imp.k")
        );
        assert_eq!(virtual_names.name("expr.k"), at_a.name("/a/src/expr.k"));
        // A name that cannot be made relative is kept as it is.
        assert_eq!(virtual_names.name("/abs/z.k"), "/abs/z.k");
        assert_eq!(names("../up/m.k").name("x.k"), "x.k");
    }

    #[test]
    fn only_source_references_are_renamed() {
        let names = names("/a/src/imp.k");
        let json = r#"{"att":{"org.kframework.attributes.Source":"/a/src/expr.k","s":"/a/src/expr.k"},"sources":[{"logical":"/a/src/imp.k","contentHash":"00"},{"logical":"krust-builtin://k.md"}],"t":"\"org.kframework.attributes.Source\":\"/a/src/expr.k\""}"#;
        assert_eq!(
            names.provenance_json(json),
            r#"{"att":{"org.kframework.attributes.Source":"./expr.k","s":"/a/src/expr.k"},"sources":[{"logical":"./imp.k","contentHash":"00"},{"logical":"krust-builtin://k.md"}],"t":"\"org.kframework.attributes.Source\":\"/a/src/expr.k\""}"#
        );
        let kore = "[org'Stop'kframework'Stop'attributes'Stop'Source{}(\n  \"Source(/a/src/expr.k)\"), other{}(\"Source(/a/src/expr.k)\")]";
        assert_eq!(
            names.kore(kore),
            "[org'Stop'kframework'Stop'attributes'Stop'Source{}(\"Source(./expr.k)\"),other{}(\"Source(/a/src/expr.k)\")]"
        );
        assert_eq!(
            names.kore("axiom{R} \\top{R}()\n  [ a{}( \"x  y\" ) ]\nendmodule  []"),
            "axiom{R}\\top{R}()[a{}(\"x  y\")]endmodule[]"
        );
    }
}
