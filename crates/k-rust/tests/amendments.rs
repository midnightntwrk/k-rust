//! The amendments overlay ([docs/amendments.md](../../../docs/amendments.md), "The rule"): every
//! file of `crates/k-rust/builtin/` is the pinned K release's file byte for byte once its lines
//! marked `// k-rust: AM-<n>` are undone as their entries say, every entry quotes its upstream
//! passage verbatim at the location it cites, and every `AM-<n>` that `crates/` and `docs/` cite
//! names an entry.

use regex::Regex;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// The revision an entry names for a file of the pinned K release.
const K_REVISION: &str = "K v7.1.337";

/// SHA-256 of each file of `include/kframework/builtin/` of `runtimeverification/k` at
/// `4a46d1231473b599c699160132fd6e76a5c46406` (v7.1.337) that k-rust embeds.
const PINNED_BUILTINS: [(&str, &str); 9] = [
    (
        "domains.md",
        "eb5b7c3cd001d5fe3cbd481598bb53c3abfd417c409135276008d50edf79aa0d",
    ),
    (
        "ffi.md",
        "9715ca4b6424dc2d2c7145b356dd78138350d8ac7b7d42bd735b909582efa6aa",
    ),
    (
        "json.md",
        "f167dae52f2fb2cc0f87631b93b0bb5425f5f8adeb61d666126ddae25e6d12fa",
    ),
    (
        "kast.md",
        "42c815ea80ed522dde962e231bdacc3d0d7e643016f8d649eab8d4be1d570040",
    ),
    (
        "prelude.md",
        "60abd2e7ee255b202dd95f50f760ab09b71a78547454d99a8a3d0fc33020172c",
    ),
    (
        "rat.md",
        "685711fa32c16b27f4e4e9da20b2a9ea0d2a63a7dba566eba711e35dde31fd03",
    ),
    (
        "substitution.md",
        "c7e3fe10066a8b0cb8dcfd60c2b8e9bda78914b1e8d488ceeeacd16f231e293e",
    ),
    (
        "timer.md",
        "4b718e4ac1929f5bf9ccdb1f27a7998870c5105aeaeb300358a8a1fc601605e4",
    ),
    (
        "unification.k",
        "4a6fc7b72406d14a26c584366e8395b93071f6377ca8ca44aeba3edea5da8dbd",
    ),
];

/// blockchain-k-plugin's `plugin/krypto.md` at `651a2db5afc1789c89553f9113c1afa39e391e35`, as
/// kink embeds it (`NOTICE`), with the revision an entry names for it and its SHA-256.
const KRYPTO: (&str, &str, &str, &str) = (
    "krypto.md",
    "blockchain-k-plugin 651a2db5",
    "kink/crates/kink-native/reference/krypto.md",
    "cca4e2eb6767cbab9829bdcdfa0488c643caba511a66657ba35218881bb6c9e3",
);

const FIELDS: [&str; 8] = [
    "Upstream",
    "Passage",
    "k-rust reads",
    "Reason",
    "Evidence",
    "Upstream proposal",
    "Status",
    "Replaces",
];

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// Line numbers `:N` and `:N-M` in `text`, in order.
fn line_numbers(text: &str) -> Vec<usize> {
    let range = Regex::new(r":(\d+)(?:-(\d+))?").unwrap();
    range
        .captures_iter(text)
        .flat_map(|captures| {
            let first = captures[1].parse::<usize>().unwrap();
            let last = captures
                .get(2)
                .map_or(first, |last| last.as_str().parse().unwrap());
            assert!(first <= last, "range {}", &captures[0]);
            first..=last
        })
        .collect()
}

/// The groups of quoted lines in a field's text: each fenced block (its lines without the fence's
/// indentation) and each run of `>` lines (without the `>` and the space after it).
fn quoted_groups(field: &str) -> Vec<Vec<String>> {
    let mut groups = Vec::new();
    let mut lines = field.lines().peekable();
    while let Some(line) = lines.next() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("```") {
            let indent = line.len() - trimmed.len();
            let mut block = Vec::new();
            for line in lines.by_ref() {
                if line.trim_start().starts_with("```") {
                    break;
                }
                let (margin, content) = line.split_at(indent.min(line.len()));
                assert!(
                    margin.trim().is_empty() && (line.len() >= indent || line.trim().is_empty()),
                    "fenced line {line:?} starts before its fence"
                );
                block.push(content.to_owned());
            }
            groups.push(block);
        } else if trimmed.starts_with('>') {
            let mut quote = vec![unquote(trimmed)];
            while let Some(next) = lines.peek().map(|line| line.trim_start())
                && next.starts_with('>')
            {
                quote.push(unquote(next));
                lines.next();
            }
            groups.push(quote);
        }
    }
    groups
}

fn unquote(line: &str) -> String {
    let line = line.strip_prefix('>').unwrap();
    line.strip_prefix(' ').unwrap_or(line).to_owned()
}

fn normalized(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[derive(Debug)]
struct Entry {
    number: u32,
    fields: BTreeMap<&'static str, String>,
}

/// The entries of `docs/amendments.md`: each `### AM-<n>: <title>` heading and the fields of the
/// list under it, every field a `- <name>:` line with the indented lines after it.
fn entries(text: &str) -> Vec<Entry> {
    let heading = Regex::new(r"^### AM-(\d+): \S").unwrap();
    let mut entries: Vec<Entry> = Vec::new();
    // The entry the lines belong to, until a heading that is no entry's ends it.
    let mut open = false;
    let mut field: Option<&'static str> = None;
    for line in text.lines() {
        if let Some(captures) = heading.captures(line) {
            entries.push(Entry {
                number: captures[1].parse().unwrap(),
                fields: BTreeMap::new(),
            });
            (open, field) = (true, None);
            continue;
        }
        if line.starts_with('#') {
            assert!(!line.contains(" AM-"), "malformed entry heading {line:?}");
            (open, field) = (false, None);
            continue;
        }
        let Some(entry) = entries.last_mut().filter(|_| open) else {
            continue;
        };
        if let Some(rest) = line.strip_prefix("- ") {
            let name = FIELDS
                .iter()
                .find(|name| rest.starts_with(&format!("{name}:")))
                .unwrap_or_else(|| panic!("AM-{}: unknown field {line:?}", entry.number));
            let value = rest[name.len() + 1..].trim_start();
            assert!(
                entry.fields.insert(name, format!("{value}\n")).is_none(),
                "AM-{}: field {name} twice",
                entry.number
            );
            field = Some(name);
        } else if let Some(name) = field {
            assert!(
                line.is_empty() || line.starts_with("  "),
                "AM-{}: {line:?} is outside its field's indentation",
                entry.number
            );
            let value = entry.fields.get_mut(name).unwrap();
            value.push_str(line);
            value.push('\n');
        } else {
            assert!(
                line.trim().is_empty(),
                "AM-{}: {line:?} is in no field",
                entry.number
            );
        }
    }
    let mut numbers = BTreeSet::new();
    for entry in &entries {
        assert!(numbers.insert(entry.number), "AM-{} twice", entry.number);
        for name in FIELDS {
            let value = entry
                .fields
                .get(name)
                .unwrap_or_else(|| panic!("AM-{} has no {name}", entry.number));
            assert!(
                !value.trim().is_empty(),
                "AM-{}: {name} is empty",
                entry.number
            );
        }
        let status = entry.fields["Status"].trim();
        assert!(
            ["local", "proposed", "upstream"].contains(&status),
            "AM-{}: status {status:?}",
            entry.number
        );
    }
    entries
}

/// A K-text entry's marked lines: the file, its marked line numbers in the embedded copy, and the
/// upstream lines they replace in order (none when they are added).
#[derive(Debug)]
struct Marks {
    file: String,
    lines: Vec<usize>,
    replaced: Option<Vec<String>>,
}

fn marks(entry: &Entry) -> Option<Marks> {
    let replaces = &entry.fields["Replaces"];
    let first = replaces.lines().next().unwrap();
    let rest = first.strip_prefix("K text, marked lines ")?;
    let file = Regex::new(r"^`([^`]+)`").unwrap();
    let captures = file
        .captures(rest)
        .unwrap_or_else(|| panic!("AM-{}: no file in {first:?}", entry.number));
    let lines = line_numbers(&rest[captures[0].len()..]);
    assert!(
        !lines.is_empty(),
        "AM-{}: no lines in {first:?}",
        entry.number
    );
    let groups = quoted_groups(replaces);
    let replaced = match groups.as_slice() {
        [] => {
            assert!(
                first.contains(", added"),
                "AM-{}: marked lines that replace nothing are `added`",
                entry.number
            );
            None
        }
        [block] => {
            assert_eq!(
                block.len(),
                lines.len(),
                "AM-{}: one upstream line per marked line",
                entry.number
            );
            Some(block.clone())
        }
        _ => panic!("AM-{}: one block of replaced lines", entry.number),
    };
    Some(Marks {
        file: captures[1].to_owned(),
        lines,
        replaced,
    })
}

fn amendments() -> Vec<Entry> {
    entries(&std::fs::read_to_string(root().join("docs/amendments.md")).unwrap())
}

/// Each embedded builtin file with its marked lines undone, checked against its pinned digest.
fn pinned_builtins(entries: &[Entry]) -> BTreeMap<String, String> {
    let marks = entries
        .iter()
        .filter_map(|entry| Some((entry.number, marks(entry)?)))
        .collect::<BTreeMap<_, _>>();
    let mark = Regex::new(r"// k-rust: AM-(\d+)$").unwrap();
    let mut undone = BTreeMap::new();
    for (file, digest) in PINNED_BUILTINS {
        let text = k_rust::builtin::embedded(file)
            .unwrap_or_else(|| panic!("{file} is embedded"))
            .text;
        let path = root().join("crates/k-rust/builtin").join(file);
        assert_eq!(std::fs::read_to_string(&path).unwrap(), text, "{file}");
        let mut marked = BTreeMap::<u32, Vec<usize>>::new();
        let mut kept = Vec::new();
        for (index, line) in text.split_inclusive('\n').enumerate() {
            let content = line.strip_suffix('\n').unwrap_or(line);
            let Some(captures) = mark.captures(content) else {
                assert!(
                    !content.contains("k-rust: AM-"),
                    "{file}:{}: a mark ends its line",
                    index + 1
                );
                kept.push(Some(line.to_owned()));
                continue;
            };
            let number = captures[1].parse::<u32>().unwrap();
            marked.entry(number).or_default().push(index + 1);
            kept.push(None);
        }
        let mut lines = kept;
        for (number, at) in &marked {
            let entry = marks.get(number).unwrap_or_else(|| {
                panic!("{file}:{at:?}: AM-{number} is no K-text entry of docs/amendments.md")
            });
            assert_eq!(entry.file, file, "AM-{number} marks {file}:{at:?}");
            assert_eq!(&entry.lines, at, "AM-{number}: the marked lines of {file}");
            for (position, line) in at.iter().enumerate() {
                lines[line - 1] = entry
                    .replaced
                    .as_ref()
                    .map(|replaced| format!("{}\n", replaced[position]));
            }
        }
        for (number, entry) in &marks {
            if entry.file == file {
                assert!(
                    marked.contains_key(number),
                    "AM-{number}: {file} holds none of its marked lines"
                );
            }
        }
        let pinned = lines.into_iter().flatten().collect::<String>();
        assert_eq!(
            sha256(pinned.as_bytes()),
            digest,
            "{file} with its marked lines undone is not the pinned file"
        );
        undone.insert(file.to_owned(), pinned);
    }
    for (number, entry) in &marks {
        assert!(
            undone.contains_key(&entry.file),
            "AM-{number} marks {}, which is not embedded",
            entry.file
        );
    }
    undone
}

#[test]
fn every_builtin_file_is_the_pinned_file_once_its_marked_lines_are_undone() {
    let entries = amendments();
    let undone = pinned_builtins(&entries);
    assert_eq!(undone.len(), PINNED_BUILTINS.len());
    // The builtin directory holds exactly the embedded files.
    let files = std::fs::read_dir(root().join("crates/k-rust/builtin"))
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect::<BTreeSet<_>>();
    assert_eq!(files, undone.keys().cloned().collect());
}

#[test]
fn every_passage_occurs_verbatim_at_its_cited_location() {
    let entries = amendments();
    let mut upstream = pinned_builtins(&entries)
        .into_iter()
        .map(|(file, text)| (file, (K_REVISION, text)))
        .collect::<BTreeMap<_, _>>();
    let (file, revision, path, digest) = KRYPTO;
    let krypto = std::fs::read_to_string(root().join(path)).unwrap();
    assert_eq!(sha256(krypto.as_bytes()), digest, "{path}");
    upstream.insert(file.to_owned(), (revision, krypto));
    let citation =
        Regex::new(r"^`([^`]+)` at (.+?), (:\d+(?:-\d+)?(?:, :\d+(?:-\d+)?)*)$").unwrap();
    let range = Regex::new(r":(\d+)(?:-(\d+))?").unwrap();
    for entry in &entries {
        let number = entry.number;
        let mut locations = Vec::new();
        for cited in entry.fields["Upstream"].trim().split("; ") {
            let captures = citation
                .captures(cited)
                .unwrap_or_else(|| panic!("AM-{number}: citation {cited:?}"));
            let (revision, text) = upstream
                .get(&captures[1])
                .unwrap_or_else(|| panic!("AM-{number}: no upstream text {}", &captures[1]));
            assert_eq!(
                &captures[2], *revision,
                "AM-{number}: revision of {}",
                &captures[1]
            );
            for lines in range.captures_iter(&captures[3]) {
                let first = lines[1].parse::<usize>().unwrap();
                let last = lines
                    .get(2)
                    .map_or(first, |last| last.as_str().parse().unwrap());
                locations.push((captures[1].to_owned(), first, last, text));
            }
        }
        let passages = quoted_groups(&entry.fields["Passage"]);
        assert_eq!(
            passages.len(),
            locations.len(),
            "AM-{number}: one passage per cited location"
        );
        for ((file, first, last, text), passage) in locations.iter().zip(&passages) {
            let lines = text.lines().collect::<Vec<_>>();
            assert!(
                *first >= 1 && first <= last && *last <= lines.len(),
                "AM-{number}: {file}:{first}-{last} is outside the file"
            );
            let cited = &lines[first - 1..*last];
            let at = format!("AM-{number}: {file}:{first}-{last}");
            assert!(
                normalized(&cited.join(" ")).contains(&normalized(&passage.join(" "))),
                "{at} does not hold the passage {passage:#?}; it reads {cited:#?}"
            );
            let opening = normalized(passage.first().unwrap());
            let closing = normalized(passage.last().unwrap());
            assert!(
                normalized(cited[0]).contains(&opening),
                "{at}: the passage starts on another line than the first"
            );
            assert!(
                normalized(cited.last().unwrap()).contains(&closing),
                "{at}: the passage ends on another line than the last"
            );
        }
    }
}

fn text_files(directory: &Path, files: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(directory).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if entry.file_type().unwrap().is_dir() {
            if !matches!(
                path.file_name().and_then(|name| name.to_str()),
                Some("target" | "node_modules")
            ) {
                text_files(&path, files);
            }
        } else {
            files.push(path);
        }
    }
}

#[test]
fn every_cited_amendment_names_an_entry() {
    let numbers = amendments()
        .iter()
        .map(|entry| entry.number)
        .collect::<BTreeSet<_>>();
    let cited = Regex::new(r"\bAM-(\d+)\b").unwrap();
    let mut files = Vec::new();
    for directory in ["crates", "docs"] {
        text_files(&root().join(directory), &mut files);
    }
    let mut citations = 0;
    for path in files {
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        for (index, line) in text.lines().enumerate() {
            for captures in cited.captures_iter(line) {
                let number = captures[1].parse::<u32>().unwrap();
                assert!(
                    numbers.contains(&number),
                    "{}:{}: AM-{number} names no entry of docs/amendments.md",
                    path.display(),
                    index + 1
                );
                citations += 1;
            }
        }
    }
    assert!(citations > 0);
}

/// The parsers of this test read what the rule says: a fenced passage keeps its lines without
/// the fence's indentation, a quoted one without its `>`, and a citation's ranges are its lines.
#[test]
fn the_entry_format_is_read_as_the_rule_states() {
    assert_eq!(line_numbers(" `f`:3-5 and :9"), vec![3, 4, 5, 9]);
    let field = "x\n\n  ```k\n    a b\n  ```\n\n  > c\n  > d\nnot\n";
    assert_eq!(
        quoted_groups(field),
        vec![
            vec!["  a b".to_owned()],
            vec!["c".to_owned(), "d".to_owned()]
        ]
    );
    // The heading is built, so that this file cites no amendment.
    let entries = entries(&format!(
        "# T\n\n### AM-{}: t\n\n- Upstream: `domains.md` at K v7.1.337, :1\n- Passage: > x\n- k-rust reads: r\n- Reason: r\n- Evidence: e\n- Upstream proposal: p\n- Status: local\n- Replaces: K text, marked lines `kast.md`:2, added\n",
        3
    ));
    let [entry] = entries.as_slice() else {
        panic!("{entries:#?}")
    };
    assert_eq!(entry.number, 3);
    assert_eq!(
        quoted_groups(&entry.fields["Passage"]),
        vec![vec!["x".to_owned()]]
    );
    let marks = marks(entry).unwrap();
    assert_eq!(
        (marks.file.as_str(), marks.lines.as_slice()),
        ("kast.md", &[2][..])
    );
    assert!(marks.replaced.is_none());
}
