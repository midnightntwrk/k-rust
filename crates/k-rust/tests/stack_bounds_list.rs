//! The accepted stack bounds are listed once, in `docs/backend-port.md` "Stack bounds", and
//! marked at each site with `// stack-accepted(<id>): <reason>. See docs/backend-port.md#stack-bounds.`
//! (a `///` line on the facade methods). This test keeps the two from drifting apart: the ids of
//! the markers under `crates/*/src` and the ids of the table are the same set. It does not look
//! for unmarked recursions.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

const MARKER: &str = "stack-accepted(";
const POINTER: &str = "See docs/backend-port.md#stack-bounds.";
const SECTION: &str = "## Stack bounds";

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn is_id(id: &str) -> bool {
    !id.is_empty()
        && id
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
}

fn rust_files(directory: &Path, output: &mut Vec<PathBuf>) {
    let mut entries = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("reading {}: {error}", directory.display()))
        .map(|entry| entry.expect("directory entry").path())
        .collect::<Vec<_>>();
    entries.sort();
    // Invariant: `output` holds the `.rs` files below the entries before `path`; each iteration
    // consumes one entry, and source trees have no directory cycles.
    for path in entries {
        if path.is_dir() {
            rust_files(&path, output);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            output.push(path);
        }
    }
}

/// The marker ids under `crates/*/src`, each with the `file:line` sites that carry it.
fn marker_ids() -> BTreeMap<String, Vec<String>> {
    let workspace = workspace();
    let mut files = Vec::new();
    let mut crates = fs::read_dir(workspace.join("crates"))
        .expect("reading crates/")
        .map(|entry| entry.expect("directory entry").path().join("src"))
        .filter(|source| source.is_dir())
        .collect::<Vec<_>>();
    crates.sort();
    for source in crates {
        rust_files(&source, &mut files);
    }

    let mut ids = BTreeMap::<String, Vec<String>>::new();
    for file in files {
        let text = fs::read_to_string(&file)
            .unwrap_or_else(|error| panic!("reading {}: {error}", file.display()));
        for (index, line) in text.lines().enumerate() {
            let Some(start) = line.find(MARKER) else {
                continue;
            };
            let rest = &line[start + MARKER.len()..];
            let Some((id, after)) = rest.split_once(')') else {
                continue;
            };
            if !is_id(id) || !after.starts_with(':') {
                continue;
            }
            let site = format!(
                "{}:{}",
                file.strip_prefix(&workspace).unwrap_or(&file).display(),
                index + 1
            );
            let comment = line[..start].trim();
            assert!(
                comment == "//" || comment == "///",
                "{site}: a stack-accepted marker is a whole `//` or `///` comment line"
            );
            assert!(
                after.trim_end().ends_with(POINTER),
                "{site}: a stack-accepted marker ends with `{POINTER}`"
            );
            ids.entry(id.to_owned()).or_default().push(site);
        }
    }
    ids
}

/// The ids in the first column of the table under `## Stack bounds` in `docs/backend-port.md`.
fn table_ids() -> Vec<String> {
    let path = workspace().join("docs/backend-port.md");
    let text = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("reading {}: {error}", path.display()));
    let start = text
        .find(&format!("\n{SECTION}\n"))
        .unwrap_or_else(|| panic!("docs/backend-port.md has a `{SECTION}` section"));
    let section = &text[start + 1..];
    let section = section[SECTION.len()..]
        .find("\n## ")
        .map_or(section, |end| &section[..SECTION.len() + end]);

    section
        .lines()
        .filter_map(|line| {
            let cell = line.strip_prefix("| `")?;
            let (id, _) = cell.split_once('`')?;
            Some(id.to_owned())
        })
        .collect()
}

#[test]
fn stack_bound_markers_and_the_docs_table_name_the_same_cases() {
    let markers = marker_ids();
    let table = table_ids();

    let mut seen = BTreeSet::new();
    for id in &table {
        assert!(is_id(id), "table id `{id}` is kebab-case");
        assert!(seen.insert(id.clone()), "table id `{id}` is listed once");
    }
    assert!(
        !seen.is_empty(),
        "the Stack bounds table lists its accepted cases"
    );

    let marked = markers.keys().cloned().collect::<BTreeSet<_>>();
    let unlisted = markers
        .iter()
        .filter(|(id, _)| !seen.contains(*id))
        .map(|(id, sites)| format!("{id} at {}", sites.join(", ")))
        .collect::<Vec<_>>();
    let unmarked = seen.difference(&marked).collect::<Vec<_>>();
    assert!(
        unlisted.is_empty() && unmarked.is_empty(),
        "stack-accepted markers without a row in docs/backend-port.md#stack-bounds: {unlisted:?}; \
         rows without a marker: {unmarked:?}"
    );
}
