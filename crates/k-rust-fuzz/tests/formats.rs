//! The format versions are tied to the formats they name (fz26 FZ-REPLAY-WHOLE, final review S2),
//! as `tests/golden.rs` ties [`k_rust_fuzz::ENGINE_VERSION`] to the case sequence.
//!
//! A format's *shape* is the serde-relevant source of every type its document holds: each struct
//! or enum that derives `Serialize` or `Deserialize`, its `#[serde]` attributes, its fields and
//! variants with their types, each hand-written `Serialize` or `Deserialize` impl and the macros
//! that write one, and each module or function a `#[serde]` attribute names (`with`,
//! `skip_serializing_if`, ...). It is read from the sources with comments and layout dropped, so
//! a documentation edit or a reformatting does not move it, while a field, a variant, a rename or
//! a serde attribute does. The types are those reachable from the document's root by name, so a
//! type no document holds does not move it. Each format pins its shape's digest beside its
//! version: a shape that changes without a version bump fails here until the version is bumped and
//! the digest re-pinned. A change that reaches the shape without changing the serialized form (a
//! field's Rust type changed to one that serializes alike) is re-pinned under the same version,
//! with the reason beside the pin.
//!
//! Not read: an inherent method a hand-written impl calls (`ComparableCondition::name`), the
//! body of an `impl Visitor` (the hand-written deserializers of `IntText` and `HoleChoice`,
//! campaign-file types no document holds), a `Deserialize` impl whose lifetime is not named
//! `'de`, and a type's serde code in a crate outside the files listed. A type alias is read and
//! followed (`Assignment`). A witness file holds a report, so its
//! shape is that of the types the witness holds beside its report: a witness of another report
//! version is refused by that version before anything else is read, so a type the two share is
//! guarded by the report's version.
//!
//! `KRUST_FUZZ_FORMATS_PRINT=1` prints each shape's digest and the types it reads.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use k_rust_fuzz::report::{REPORT_VERSION, digest_hex};

/// The report's shape at [`REPORT_VERSION`] 10 (FZ-REPLAY-WHOLE: the identity's `fuzz-revision`,
/// `parse-diagnostic-work` and `debug-assertions`, `totals.first-outside-determinism`, and source
/// locations named relative to the main module's file). Re-pinned within version 10 by the fix
/// round, in the same wave: `identity.debug-assertions` came in, and the reader now follows type
/// aliases (`Assignment`), which changes the digest and not the format. Re-pinned within
/// version 10 by FZ-ENGINE-R4, in the same wave: `totals.domain`, `totals.diverging`,
/// `totals.coverage-last-grew` and the unjudged reason `mutant-refused-state`. Re-pinned within
/// version 10 by FZ-ENGINE-R4's fix round, in the same wave: the unjudged reason
/// `end-names-undeclared-symbol`.
const REPORT_SHAPE: (u32, &str) = (
    10,
    "1ad45719b1897e936724e31c16a6637712a8e1fe0f39c6e4da106a62ee71b3ad",
);

/// The witness file's shape at its version 2 (FZ-CRASH), less the report it holds.
const WITNESS_SHAPE: (u32, &str) = (
    2,
    "85a30636b81c3f81a42d7dcd7cbd5281bf63f7d85845041476ad631741dd3531",
);

/// The witness file's version, as the `krust-fuzz` executable writes it (`replay.rs`): the
/// executable is no library, so the constant is read from its source.
fn witness_version() -> u32 {
    let source = fs::read_to_string(crate_dir().join("src/bin/krust-fuzz/replay.rs"))
        .expect("replay.rs reads");
    let line = source
        .lines()
        .find(|line| line.starts_with("pub const WITNESS_VERSION: u32 = "))
        .expect("replay.rs declares WITNESS_VERSION");
    line.trim_start_matches("pub const WITNESS_VERSION: u32 = ")
        .trim_end_matches(';')
        .parse()
        .expect("a version number")
}

fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Every `.rs` file under `directory`, recursively, except test modules kept in files of their
/// own (`tests.rs`, `*_tests.rs`) and, unless `with_bin`, the `bin` directory.
fn sources(directory: &Path, with_bin: bool, files: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = fs::read_dir(directory)
        .expect("a source directory")
        .flatten()
        .map(|entry| entry.path())
        .collect();
    entries.sort();
    for path in entries {
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("");
        if path.is_dir() {
            if with_bin || name != "bin" {
                sources(&path, with_bin, files);
            }
        } else if path.extension().is_some_and(|extension| extension == "rs")
            && name != "tests.rs"
            && !name.ends_with("_tests.rs")
        {
            files.push(path);
        }
    }
}

/// The files a format's types are read from: this crate's sources and the k-rust backend types
/// a report holds (`HaltReasonOutput`, `CompiledRuleKind`).
fn format_files(with_bin: bool) -> Vec<PathBuf> {
    let mut files = Vec::new();
    sources(&crate_dir().join("src"), with_bin, &mut files);
    for backend in ["mod.rs", "wire.rs"] {
        files.push(crate_dir().join("../k-rust/src/backend").join(backend));
    }
    files
}

/// `source` without comments, string and character literals kept whole.
fn without_comments(source: &str) -> String {
    let characters: Vec<char> = source.chars().collect();
    let mut out = String::with_capacity(source.len());
    let mut index = 0;
    while index < characters.len() {
        let character = characters[index];
        let next = characters.get(index + 1).copied();
        match (character, next) {
            ('/', Some('/')) => {
                while index < characters.len() && characters[index] != '\n' {
                    index += 1;
                }
            }
            ('/', Some('*')) => {
                index += 2;
                while index + 1 < characters.len()
                    && !(characters[index] == '*' && characters[index + 1] == '/')
                {
                    index += 1;
                }
                index += 2;
            }
            ('r', Some('"' | '#')) if index == 0 || !is_identifier(characters[index - 1]) => {
                // A raw string: `r`, hashes, a quote, up to a quote and as many hashes.
                let start = index;
                index += 1;
                let mut hashes = 0;
                while characters.get(index) == Some(&'#') {
                    hashes += 1;
                    index += 1;
                }
                if characters.get(index) != Some(&'"') {
                    out.extend(&characters[start..index]);
                    continue;
                }
                index += 1;
                // Written as an ordinary literal, so that later passes read one kind of string.
                out.push('"');
                while index < characters.len() {
                    if characters[index] == '"'
                        && (1..=hashes).all(|offset| characters.get(index + offset) == Some(&'#'))
                    {
                        index += 1 + hashes;
                        break;
                    }
                    if matches!(characters[index], '"' | '\\') {
                        out.push('\\');
                    }
                    out.push(characters[index]);
                    index += 1;
                }
                out.push('"');
            }
            ('"', _) => {
                let start = index;
                index += 1;
                while index < characters.len() && characters[index] != '"' {
                    if characters[index] == '\\' {
                        index += 1;
                    }
                    index += 1;
                }
                index += 1;
                out.extend(&characters[start..index.min(characters.len())]);
            }
            ('\'', Some(_)) => {
                // A character literal (`'x'`, `'\n'`), else a lifetime's quote.
                let literal_end = if next == Some('\\') {
                    characters[index + 2..]
                        .iter()
                        .position(|c| *c == '\'')
                        .map(|at| index + 2 + at + 1)
                } else if characters.get(index + 2) == Some(&'\'') {
                    Some(index + 3)
                } else {
                    None
                };
                // A character literal is written as one placeholder, so that a quote character
                // (`'"'`) opens no string for the later passes.
                if let Some(end) = literal_end {
                    out.push_str("'c'");
                    index = end;
                } else {
                    out.push('\'');
                    index += 1;
                }
            }
            _ => {
                out.push(character);
                index += 1;
            }
        }
    }
    out
}

fn is_identifier(character: char) -> bool {
    character.is_alphanumeric() || character == '_'
}

/// `text` with every run of whitespace outside literals dropped next to punctuation and one
/// space elsewhere.
fn normalized(text: &str) -> String {
    let mut out = String::new();
    let mut pending = false;
    let mut in_string = false;
    let mut escaped = false;
    for character in text.chars() {
        if in_string {
            out.push(character);
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                in_string = false;
            }
            continue;
        }
        if character.is_whitespace() {
            pending = true;
            continue;
        }
        if pending && is_identifier(character) && out.chars().next_back().is_some_and(is_identifier)
        {
            out.push(' ');
        }
        pending = false;
        if character == '"' {
            in_string = true;
        }
        out.push(character);
    }
    out
}

/// The items of `source` (comments dropped) at its top level and inside inline modules, each
/// normalized with its attributes; test-only items (`#[cfg(test)]`) are left out.
fn items(source: &str) -> Vec<String> {
    let mut items = Vec::new();
    let mut current = String::new();
    let mut depth = 0_i32;
    let mut in_string = false;
    let mut escaped = false;
    let flush = |current: &mut String, items: &mut Vec<String>| {
        let item = normalized(current);
        current.clear();
        let attributes = &item[..item.len() - strip_attributes(&item).len()];
        if item.is_empty() || attributes.contains("#[cfg(test)]") {
            return;
        }
        // An inline module: the module as an item, and its own items.
        if let Some(body) = module_body(&item) {
            items.extend(self::items(body));
        }
        items.push(item);
    };
    for character in source.chars() {
        current.push(character);
        if in_string {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                in_string = false;
            }
            continue;
        }
        match character {
            '"' => in_string = true,
            '{' | '(' | '[' => depth += 1,
            '}' | ')' | ']' => {
                depth -= 1;
                if depth == 0 && character == '}' {
                    flush(&mut current, &mut items);
                }
            }
            ';' if depth == 0 => flush(&mut current, &mut items),
            _ => {}
        }
    }
    flush(&mut current, &mut items);
    items
}

/// The body of an inline module item (`mod name { ... }`), if `item` is one.
fn module_body(item: &str) -> Option<&str> {
    let at = item.find("mod ")?;
    let header = &item[at..];
    let open = header.find('{')?;
    if header[4..open].contains(|c: char| !is_identifier(c) && c != ' ') {
        return None;
    }
    header[open + 1..].strip_suffix('}')
}

/// What an item is, for the shape: its name and whether it is a type, a serde impl, a macro or
/// a macro invocation (each found by the names its text uses), or a function or module (found
/// only by a `#[serde]` attribute naming it).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Type,
    Named,
}

/// The item's name and kind, when it can belong to a shape.
fn classify(item: &str) -> Option<(String, Kind)> {
    let derives_serde = item.contains("#[derive(")
        && item.split("#[derive(").skip(1).any(|derive| {
            let list = derive.split(')').next().unwrap_or("");
            list.contains("Serialize") || list.contains("Deserialize")
        });
    let body = strip_attributes(item);
    let body = body
        .strip_prefix("pub(crate)")
        .or_else(|| body.strip_prefix("pub(super)"))
        .or_else(|| body.strip_prefix("pub "))
        .unwrap_or(body);
    let name_after = |keyword: &str| {
        body.strip_prefix(keyword).map(|rest| {
            rest.chars()
                .take_while(|c| is_identifier(*c))
                .collect::<String>()
        })
    };
    if let Some(name) = name_after("struct ").or_else(|| name_after("enum ")) {
        return derives_serde.then_some((name, Kind::Type));
    }
    // A type alias is followed through: `Vec<Assignment>` serializes as what `Assignment` names
    // (fix round S-D).
    if let Some(name) = name_after("type ") {
        return Some((name, Kind::Type));
    }
    if body.starts_with("impl") {
        // Normalized: `impl Serialize for X`, `impl<'de>Deserialize<'de>for X`.
        let header = body.split('{').next().unwrap_or("");
        let (traits, name) = header.rsplit_once("for ")?;
        let serde_trait = traits.ends_with("Serialize ") || traits.ends_with("Deserialize<'de>");
        let name: String = name.chars().take_while(|c| is_identifier(*c)).collect();
        return serde_trait.then_some((name, Kind::Type));
    }
    if let Some(name) = name_after("macro_rules!") {
        let name = name.trim().to_owned();
        return item.contains("Serialize").then_some((name, Kind::Type));
    }
    if let Some(name) = name_after("mod ").or_else(|| name_after("fn ")) {
        return Some((name, Kind::Named));
    }
    // A macro invocation: `name!(Type, ...)` names the type it defines.
    let (macro_name, rest) = body.split_once("!(")?;
    if macro_name.chars().all(is_identifier) {
        let name: String = rest.chars().take_while(|c| is_identifier(*c)).collect();
        return Some((name, Kind::Type));
    }
    None
}

/// `item` without its leading attributes.
fn strip_attributes(item: &str) -> &str {
    let mut rest = item;
    while let Some(after) = rest.strip_prefix("#[") {
        let mut depth = 1;
        let mut end = after.len();
        for (index, character) in after.char_indices() {
            match character {
                '[' => depth += 1,
                ']' => {
                    depth -= 1;
                    if depth == 0 {
                        end = index + 1;
                        break;
                    }
                }
                _ => {}
            }
        }
        rest = after[end..].trim_start();
    }
    rest
}

/// The identifiers `text` uses, in and out of literals.
fn words(text: &str) -> BTreeSet<String> {
    text.split(|c: char| !is_identifier(c))
        .filter(|word| !word.is_empty())
        .map(str::to_owned)
        .collect()
}

/// The names a `#[serde]` attribute of `text` gives as a path in a string (`with = "a::b"`,
/// `skip_serializing_if = "no_rule"`), last segments.
fn serde_paths(text: &str) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for attribute in text.split("#[serde(").skip(1) {
        let attribute = attribute.split(")]").next().unwrap_or("");
        for value in attribute.split('"').skip(1).step_by(2) {
            if let Some(last) = value.rsplit("::").next()
                && last.chars().all(is_identifier)
            {
                names.insert(last.to_owned());
            }
        }
    }
    names
}

/// The shape of the types reachable from `roots` in `files`, less those reachable from `less`:
/// its digest and the names it read.
fn shape(files: &[PathBuf], roots: &[&str], less: &[&str]) -> (String, Vec<String>) {
    let mut candidates: BTreeMap<String, Vec<(Kind, String)>> = BTreeMap::new();
    for file in files {
        let source = fs::read_to_string(file).expect("a source reads");
        for item in items(&without_comments(&source)) {
            if let Some((name, kind)) = classify(&item) {
                candidates.entry(name).or_default().push((kind, item));
            }
        }
    }
    let reach = |roots: &[&str]| {
        let mut reached: BTreeSet<String> = BTreeSet::new();
        let mut pending: Vec<String> = roots.iter().map(|root| (*root).to_owned()).collect();
        while let Some(name) = pending.pop() {
            let Some(entries) = candidates.get(&name) else {
                continue;
            };
            if !reached.insert(name.clone()) {
                continue;
            }
            for (_, item) in entries {
                for word in words(item) {
                    let is_type = candidates
                        .get(&word)
                        .is_some_and(|entries| entries.iter().any(|(kind, _)| *kind == Kind::Type));
                    if is_type && !reached.contains(&word) {
                        pending.push(word);
                    }
                }
                for path in serde_paths(item) {
                    if candidates.contains_key(&path) && !reached.contains(&path) {
                        pending.push(path);
                    }
                }
            }
        }
        reached
    };
    let excluded = reach(less);
    let read: Vec<String> = reach(roots)
        .into_iter()
        .filter(|name| !excluded.contains(name))
        .collect();
    let mut texts: Vec<&str> = read
        .iter()
        .flat_map(|name| &candidates[name])
        .map(|(_, item)| item.as_str())
        .collect();
    texts.sort_unstable();
    (digest_hex(texts.join("\n").as_bytes()), read)
}

fn check(name: &str, pinned: (u32, &str), version: u32, computed: &(String, Vec<String>)) {
    if std::env::var_os("KRUST_FUZZ_FORMATS_PRINT").is_some() {
        println!(
            "{name} shape at version {version}: {}\n  reads {:?}",
            computed.0, computed.1
        );
    }
    assert_eq!(
        pinned.0, version,
        "the {name} version moved to {version}: re-pin its shape for the new version"
    );
    assert_eq!(
        computed.0, pinned.1,
        "the {name}'s shape changed without a version bump: bump the version and re-pin \
         ({version}, \"{}\"), or, when the serialized form is unchanged, re-pin under the same \
         version and say why; it reads {:?}",
        computed.0, computed.1
    );
}

#[test]
fn the_report_version_names_the_report_shape() {
    let computed = shape(&format_files(false), &["FuzzReport"], &[]);
    for name in [
        "FuzzReport",
        "ReportIdentity",
        "WitnessCase",
        "HaltReasonOutput",
        "decimal_u64",
        "Assignment",
    ] {
        assert!(
            computed.1.iter().any(|read| read == name),
            "{name}: {:?}",
            computed.1
        );
    }
    check("report", REPORT_SHAPE, REPORT_VERSION, &computed);
}

#[test]
fn the_witness_version_names_the_witness_shape() {
    let computed = shape(&format_files(true), &["WitnessFile"], &["FuzzReport"]);
    for name in ["WitnessFile", "ResolvedCampaign", "Target"] {
        assert!(
            computed.1.iter().any(|read| read == name),
            "{name}: {:?}",
            computed.1
        );
    }
    assert!(
        !computed.1.iter().any(|read| read == "ReportIdentity"),
        "{:?}",
        computed.1
    );
    check("witness", WITNESS_SHAPE, witness_version(), &computed);
}

/// The scanner reads what the shape needs: comments and layout drop out, literals and lifetimes
/// stay, test-only items are left out, and an item is found inside an inline module.
#[test]
fn the_shape_reader_reads_items_not_comments() {
    let source = "/// a doc\n#[derive(Serialize)]\n#[serde(rename_all = \"kebab-case\")]\npub struct A {\n    // a comment\n    pub b: Vec<B>, /* inline */\n    pub c: &'static str,\n}\n#[cfg(test)]\nmod tests { #[derive(Serialize)] struct T; }\nmod m { #[derive(Deserialize)] pub enum B { X('\"'), Y } }\n";
    let items_of = |source: &str| items(&without_comments(source));
    let items = items_of(source);
    assert!(
        items.contains(
            &"#[derive(Serialize)]#[serde(rename_all=\"kebab-case\")]pub struct A{pub b:Vec<B>,pub c:&'static str,}".to_owned()
        ),
        "{items:?}"
    );
    assert!(
        items
            .iter()
            .any(|item| item.starts_with("#[derive(Deserialize)]pub enum B")),
        "{items:?}"
    );
    assert!(
        !items.iter().any(|item| item.contains("struct T")),
        "{items:?}"
    );
    assert_eq!(classify(&items[0]), Some(("A".to_owned(), Kind::Type)));
    // A type alias is a type of the shape, followed through (fix round S-D).
    let alias = items_of("pub type Assignment = BTreeMap<String, Value>;\n");
    assert_eq!(
        classify(&alias[0]),
        Some(("Assignment".to_owned(), Kind::Type))
    );
}

/// k-rust-fuzz's build script digests this crate and its path dependencies outside k-rust's
/// digest (`build.rs`, `MEMBERS`): a new path dependency must join the list, or its sources
/// would reach reports without reaching `identity.fuzz-revision` (FZ-REPLAY-WHOLE S4).
#[test]
fn the_fuzz_revision_covers_every_path_dependency_beside_k_rust() {
    let workspace = crate_dir().join("../..");
    let build = fs::read_to_string(crate_dir().join("build.rs")).expect("build.rs reads");
    let members_line = build
        .lines()
        .find(|line| line.starts_with("const MEMBERS"))
        .expect("build.rs declares MEMBERS");
    let mut pending = vec![PathBuf::from("crates/k-rust-fuzz")];
    let mut seen = BTreeSet::new();
    while let Some(member) = pending.pop() {
        if !seen.insert(member.clone()) {
            continue;
        }
        let manifest: toml_lite::Table = toml_lite::parse(
            &fs::read_to_string(workspace.join(&member).join("Cargo.toml")).expect("a manifest"),
        );
        for path in manifest.dependency_paths() {
            let dependency = normalize(&member.join(path));
            // k-rust and its path dependencies are k-rust's own digest (`k_rust::build_identity`).
            if dependency == Path::new("crates/k-rust") {
                continue;
            }
            assert!(
                members_line.contains(&format!("\"{}\"", dependency.display())),
                "{} is a path dependency of {} outside k-rust's digest, missing from build.rs's \
                 MEMBERS: {members_line}",
                dependency.display(),
                member.display()
            );
            pending.push(dependency);
        }
    }
}

/// `path` with `..` steps resolved lexically.
fn normalize(path: &Path) -> PathBuf {
    let mut parts: Vec<&std::ffi::OsStr> = Vec::new();
    for component in path.components() {
        match component {
            std::path::Component::ParentDir => {
                parts.pop();
            }
            std::path::Component::CurDir => {}
            other => parts.push(other.as_os_str()),
        }
    }
    parts.iter().collect()
}

/// The little of a manifest the members check reads: the `path` of each entry of
/// `[dependencies]` (this test builds without the `toml` crate, which is the `cli` feature's).
mod toml_lite {
    pub struct Table(Vec<String>);

    pub fn parse(text: &str) -> Table {
        let mut paths = Vec::new();
        let mut in_dependencies = false;
        for line in text.lines() {
            let line = line.trim();
            if line.starts_with('[') {
                in_dependencies = line == "[dependencies]";
                continue;
            }
            if in_dependencies && let Some(at) = line.find("path = \"") {
                let rest = &line[at + "path = \"".len()..];
                if let Some(end) = rest.find('"') {
                    paths.push(rest[..end].to_owned());
                }
            }
        }
        Table(paths)
    }

    impl Table {
        pub fn dependency_paths(&self) -> impl Iterator<Item = &str> {
            self.0.iter().map(String::as_str)
        }
    }
}
