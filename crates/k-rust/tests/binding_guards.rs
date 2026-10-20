//! Source scans that keep the binding rule in one place (BIND/A9).
//!
//! After anonymous resolution a quantifier binds exactly its own variable, whatever its spelling
//! (`kast::binding`), so no pass may read what a variable is from how it is spelled, and every
//! binder the emitter generates is built where K3 is checked
//! (`kompile::module_to_kore::binders`). These scans hold the code to that. Each scan lists the
//! places allowed to write its text, each with its reason; a new place fails the scan until it is
//! listed with a reason, and a listed place that no longer writes the text fails it too, so the
//! list stays exact. Test modules (`#[cfg(test)] mod ...`) are not scanned.

use std::fs;
use std::path::{Path, PathBuf};

/// One allowed place: a source file under `crates/k-rust/src`, a text that identifies the line
/// within it, and why the place may write the scanned text.
struct Allowed {
    file: &'static str,
    line: &'static str,
    reason: &'static str,
}

const fn allowed(file: &'static str, line: &'static str, reason: &'static str) -> Allowed {
    Allowed { file, line, reason }
}

/// The places that write a `_Gen`, `?_Gen`, `!_Gen`, `@_Gen` or `_DotVar` literal: the sites that
/// mint the compiler's names, and the readers whose reason does not depend on binding.
const GENERATED_SPELLINGS: &[Allowed] = &[
    allowed(
        "kompile/fresh_names.rs",
        "{sigil}_Gen",
        "the shared minting rule: a variable the compiler introduces for one with a sigil keeps it",
    ),
    allowed(
        "kompile/passes/resolve_fun.rs",
        "{prefix}_Gen",
        "mint site: the anonymous variables of a local function's equation",
    ),
    allowed(
        "kompile/passes/minimize_term_construction.rs",
        "mint(\"_Gen\")",
        "mint site: the alias of a shared left-side subterm",
    ),
    allowed(
        "kompile/passes/guard_or_patterns.rs",
        "mint(\"_Gen\")",
        "mint site: the alias guarding an or-pattern",
    ),
    allowed(
        "kompile/sort_injections.rs",
        ".mint(\"_Gen\")",
        "mint site: the key of an injected search pattern or collection item",
    ),
    allowed(
        "kompile/module_to_kore/equations.rs",
        "fresh.mint(\"_Gen\")",
        "mint site: an owise competitor's free variables, refreshed",
    ),
    allowed(
        "kompile/passes/resolve_fresh_constants.rs",
        "names.mint(\"_Gen\")",
        "mint site: the generated counter's value before a claim",
    ),
    allowed(
        "kompile/passes/resolve_fresh_constants.rs",
        "names.mint(\"?_Gen\")",
        "mint site: the generated counter's value after a claim, existential",
    ),
    allowed(
        "kompile/passes/concretize_cells.rs",
        "\"_Gen\")",
        "mint site: a cell's value variable",
    ),
    allowed(
        "kompile/passes/concretize_cells.rs",
        "\"_DotVar\")",
        "mint site: a cell fragment's frame",
    ),
    allowed(
        "kompile/passes/concretize_cells.rs",
        "prefix == \"_DotVar\"",
        "the mint site records the frames it mints as frames",
    ),
    allowed(
        "kompile/passes/resolve_fresh_config_constants.rs",
        "starts_with(\"!_Gen\")",
        "reader in release builds: each anonymous fresh configuration variable takes its own value, \
         across sentences (only anonymous resolution mints `!_Gen`)",
    ),
    allowed(
        "kast/binding.rs",
        "[\"_Gen\", \"?_Gen\", \"!_Gen\", \"@_Gen\", \"_DotVar\"]",
        "reads_as_resolved_anonymous, allowlisted: Reservation::mint keeps its mints out of the \
         spellings its two readers interpret (C1/R3 in invariants/stage.rs, debug; \
         resolve_fresh_config_constants.rs, release); no binding depends on it",
    ),
    allowed(
        "kompile/invariants/stage.rs",
        "strip_prefix(\"_Gen\")",
        "reader in debug builds: C1's and R3's exemption for the names anonymous resolution gives",
    ),
];

/// The places that name `InternalLabel::Exists` or `InternalLabel::Forall`: binder recognition
/// lives in `kast::binding`, and these places read the label for something else.
const QUANTIFIER_LABELS: &[Allowed] = &[
    allowed(
        "kast/binding.rs",
        "label.is(InternalLabel::",
        "the binding module itself: quantifier_kind",
    ),
    allowed(
        "kast/convert.rs",
        "InternalLabel::Exists.as_str()",
        "construction: a KORE \\exists read back as a KAST quantifier",
    ),
    allowed(
        "kast/convert.rs",
        "InternalLabel::Forall.as_str()",
        "construction: a KORE \\forall read back as a KAST quantifier",
    ),
    allowed(
        "kompile/term_to_kore.rs",
        "Some(InternalLabel::Exists | InternalLabel::Forall) => {",
        "the converter dispatches the quantifier to `quantifier`, and reads its result sort",
    ),
    allowed(
        "kompile/term_to_kore.rs",
        "if label.is(InternalLabel::Exists) {",
        "the converter builds the KORE binder of the quantifier's own kind",
    ),
    allowed(
        "kompile/sort_injections.rs",
        "Some(InternalLabel::Exists | InternalLabel::Forall) => {",
        "the result sort of a quantifier application, its last parameter",
    ),
    allowed(
        "kompile/ml_constructs.rs",
        "InternalLabel::Exists,",
        "the matching-logic connectives a condition may hold",
    ),
    allowed(
        "kompile/ml_constructs.rs",
        "InternalLabel::Forall,",
        "the matching-logic connectives a condition may hold",
    ),
    allowed(
        "kompile/ml_constructs.rs",
        "label.is(InternalLabel::Exists) || label.is(InternalLabel::Forall)",
        "a quantifier is a predicate when its body is one",
    ),
];

/// The places in `kompile/` that construct a KORE `\exists` or `\forall`: every binder the
/// emitter generates is built in `binders.rs`, where K3 is checked.
const KORE_BINDERS: &[Allowed] = &[
    allowed(
        "kompile/module_to_kore/binders.rs",
        "pattern = Pattern::Exists {",
        "generated_exists_all: the constructor of every generated binder (K3)",
    ),
    allowed(
        "kompile/term_to_kore.rs",
        "Pattern::Exists {",
        "bind_quantifier: the authored quantifier, converted",
    ),
    allowed(
        "kompile/term_to_kore.rs",
        "Pattern::Forall {",
        "bind_quantifier: the authored quantifier, converted",
    ),
    allowed(
        "kompile/module_to_kore/equations.rs",
        "Pattern::Exists { variable, body, .. } => Pattern::Exists {",
        "predicate_at: rebuilds an existing binder at a new sort, generating none",
    ),
    allowed(
        "kompile/module_to_kore/equations.rs",
        "Pattern::Forall { variable, body, .. } => Pattern::Forall {",
        "predicate_at: rebuilds an existing binder at a new sort, generating none",
    ),
];

fn source_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src")
}

/// Every `.rs` file under `directory`, with its path relative to the source root.
fn rust_files(directory: &Path, files: &mut Vec<(String, String)>) {
    let mut entries = fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            rust_files(&path, files);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            let relative = path
                .strip_prefix(source_root())
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            files.push((relative, fs::read_to_string(&path).unwrap()));
        }
    }
}

/// `text` up to its first test module: a `#[cfg(test)]` line whose next line that is no
/// attribute declares a module.
fn without_test_module(text: &str) -> &str {
    let lines = text.split_inclusive('\n').collect::<Vec<_>>();
    let mut offset = 0;
    for (index, line) in lines.iter().enumerate() {
        if line.trim() == "#[cfg(test)]"
            && lines[index + 1..]
                .iter()
                .find(|next| !next.trim_start().starts_with("#["))
                .is_some_and(|next| next.trim_start().starts_with("mod "))
        {
            return &text[..offset];
        }
        offset += line.len();
    }
    text
}

/// Each occurrence of a scanned text that `matches` accepts: its file, line number and line.
fn occurrences(
    files: &[(String, String)],
    within: &str,
    matches: impl Fn(&str, usize) -> Vec<usize>,
) -> Vec<(String, usize, String)> {
    let mut found = Vec::new();
    for (file, text) in files {
        if !file.starts_with(within) {
            continue;
        }
        let text = without_test_module(text);
        for offset in matches(text, 0) {
            let line_start = text[..offset].rfind('\n').map_or(0, |at| at + 1);
            let line_end = text[offset..]
                .find('\n')
                .map_or(text.len(), |at| offset + at);
            found.push((
                file.clone(),
                text[..offset].matches('\n').count() + 1,
                text[line_start..line_end].to_owned(),
            ));
        }
    }
    found
}

/// Every offset of any of `needles` in `text`.
fn offsets_of(text: &str, needles: &[&str]) -> Vec<usize> {
    let mut found = needles
        .iter()
        .flat_map(|needle| text.match_indices(needle).map(|(at, _)| at))
        .collect::<Vec<_>>();
    found.sort_unstable();
    found.dedup();
    found
}

/// Check `found` against `allowlist`: every occurrence lies on a line an entry of its file
/// identifies, and every entry identifies some occurrence.
fn assert_allowed(scan: &str, found: &[(String, usize, String)], allowlist: &[Allowed]) {
    let mut problems = Vec::new();
    for (file, number, line) in found {
        if !allowlist
            .iter()
            .any(|entry| entry.file == file && line.contains(entry.line))
        {
            problems.push(format!("{file}:{number}: not allowed: {}", line.trim()));
        }
    }
    for entry in allowlist {
        assert!(
            !entry.reason.is_empty(),
            "{scan}: {} has no reason",
            entry.file
        );
        if !found
            .iter()
            .any(|(file, _, line)| file == entry.file && line.contains(entry.line))
        {
            problems.push(format!(
                "{}: the allowed `{}` ({}) no longer occurs; remove the entry",
                entry.file, entry.line, entry.reason
            ));
        }
    }
    assert!(problems.is_empty(), "{scan}:\n{}", problems.join("\n"));
}

fn sources() -> Vec<(String, String)> {
    let mut files = Vec::new();
    rust_files(&source_root(), &mut files);
    files
}

/// No pass spells the compiler's names outside the sites that mint them and the listed readers.
#[test]
fn generated_spellings_occur_only_at_mint_sites_and_listed_readers() {
    let files = sources();
    let found = occurrences(&files, "", |text, _| {
        offsets_of(
            text,
            &[
                "\"_Gen",
                "\"?_Gen",
                "\"!_Gen",
                "\"@_Gen",
                "\"_DotVar",
                "_Gen\"",
            ],
        )
    });
    assert_allowed("generated spellings", &found, GENERATED_SPELLINGS);
}

/// Quantifiers are recognised through `kast::binding`; the quantifier labels are named only where
/// something other than binding is read from them.
#[test]
fn quantifier_labels_are_named_only_where_binding_is_not_read() {
    let files = sources();
    let found = occurrences(&files, "", |text, _| {
        offsets_of(text, &["InternalLabel::Exists", "InternalLabel::Forall"])
    });
    assert_allowed("quantifier labels", &found, QUANTIFIER_LABELS);
}

/// Every KORE binder `kompile/` constructs is built by `binders.rs`, converted from an authored
/// quantifier, or rebuilt from an existing one. A `Pattern::Exists { .. }` that names `..` is a
/// match, not a construction.
#[test]
fn kore_binders_are_constructed_only_where_k3_is_checked_or_none_is_generated() {
    let files = sources();
    let found = occurrences(&files, "kompile/", |text, _| {
        offsets_of(text, &["Pattern::Exists {", "Pattern::Forall {"])
            .into_iter()
            .filter(|&offset| {
                let fields = &text[offset..];
                let close = fields.find('}').unwrap_or(fields.len());
                !fields[..close].contains("..")
            })
            .collect()
    });
    assert_allowed("KORE binders", &found, KORE_BINDERS);
}

/// `is_generated_anonymous`, the spelling classifier of anonymity, is gone (BIND/A3), and the
/// converter reads no anonymity: its only reading of `_` is the debug assertion that every
/// anonymous binder was resolved before conversion.
#[test]
fn no_anonymity_classifier_remains() {
    let files = sources();
    for (file, text) in &files {
        assert!(
            !text.contains("is_generated_anonymous"),
            "{file} still names is_generated_anonymous"
        );
    }
    let (_, converter) = files
        .iter()
        .find(|(file, _)| file == "kompile/term_to_kore.rs")
        .expect("the converter exists");
    let converter = without_test_module(converter);
    for spelling in [
        "anonymous_prefix",
        "generated_anonymous",
        "\"_Gen",
        "is_anonymous(",
    ] {
        assert!(
            !converter.contains(spelling),
            "the converter reads anonymity ({spelling})"
        );
    }
    assert_eq!(converter.matches("is_unresolved_anonymous").count(), 1);
}
