//! The entry table reads every entry the readable reader admits. Over every `k::rules!` and
//! `k::claims!` block written in the krs-cli test sources and the krs test fixtures, each clause
//! the readable reader admits whole (no refusal it carries until its entries are judged) has
//! records whose every field the entry reading spells: a field it reads as no spelling would
//! skip the table's judgement of that cell, its kind and its pairing, so the lowering would be
//! the table's only check. A block the reader refuses, or whose text is a template with holes,
//! is not counted. Blocks written here beside them hold the values the sources may not: a result
//! value whose top is an operator over a term holding a splice (`list::size([x, ..r]) + 1`),
//! whose splice is that term's, not a rest of the entry.

use std::fs;
use std::path::{Path, PathBuf};

use krs_syntax::cell_entry::{EntryForm, entry_fields, entry_result_fields};
use krs_syntax::{ClaimBlock, KrsSyntax, RuleBlock, RuleClause};

/// Every `.rs` file below `root`, recursively, skipping build outputs.
fn sources(root: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(root) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        if name == "target" || name.to_string_lossy().starts_with('.') {
            continue;
        }
        if path.is_dir() {
            sources(&path, out);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            out.push(path);
        }
    }
}

/// The payload of each `k::rules! { .. }` or `k::claims! { .. }` written in `text`, with whether
/// it is a claim block: the text between its braces, matched by counting them.
fn blocks(text: &str) -> Vec<(bool, &str)> {
    let mut found = Vec::new();
    for (claims, head) in [(false, "k::rules!"), (true, "k::claims!")] {
        let mut from = 0;
        while let Some(at) = text[from..].find(head) {
            let start = from + at + head.len();
            from = start;
            let Some(open) = text[start..].find('{') else {
                break;
            };
            if !text[start..start + open].trim().is_empty() {
                continue;
            }
            let body = start + open + 1;
            let mut depth = 1usize;
            let mut end = None;
            for (offset, character) in text[body..].char_indices() {
                match character {
                    '{' => depth += 1,
                    '}' => {
                        depth -= 1;
                        if depth == 0 {
                            end = Some(body + offset);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            if let Some(end) = end {
                found.push((claims, &text[body..end]));
            }
        }
    }
    found
}

/// Readable blocks whose result values hold a splice inside a term beside an operator at the
/// value's level, as the value, an item of its brackets, a record child's value, or a call's
/// argument.
const NESTED_SPLICES: [(bool, &str); 2] = [
    (
        false,
        "for Machine; use Cmd::*;
        nested_value: { k: [Go(), ..], ll: [x, r @ ..], n: _, out: _ } => {
            k: [..], n: list::size([x, ..r]) + 1, out: [list::size([x, ..r]) + 1, x],
        };
        nested_child: { k: [Go(), ..], ll: [x, r @ ..], th: { me @ Th { tl: [y, s @ ..], .. }, .. } } => {
            k: [list::size([x, ..r]) * 2, ..],
            th: { Th { tid: list::size([y, ..s]) + 1, tl: [y, ..s], ..me }, .. },
        };
        nested_argument: { k: [Go(), ..], ll: [x, r @ ..], out: _ } => {
            k: [..], out: list::concat([x, ..r], [list::size([x, ..r]) - 1]),
        };",
    ),
    (
        true,
        "for Machine; use Cmd::*;
        #[k::claim(all_paths)]
        nested_claim: { k: [Go(), ..], ll: [x, r @ ..], n: _, out: _ } => {
            k: [..], n: list::size([x, ..r]) + 1, out: [list::size([x, ..r]) + 1],
        };",
    ),
];

/// Whether the reader admits `clause` whole: it carries no refusal until its entries are judged.
fn admitted(clause: &RuleClause) -> bool {
    clause.pairing_refusal().is_none()
        && clause.part_refusal().is_none()
        && clause.subject_refusal().is_none()
        && clause.instances_only_refusals().next().is_none()
}

#[test]
fn the_entry_table_spells_every_entry_the_readable_reader_admits() {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut files = Vec::new();
    sources(&crates.join("krs-cli/tests"), &mut files);
    sources(&crates.join("../tests"), &mut files);
    files.sort();
    let mut read = 0usize;
    let mut unread = Vec::new();
    let mut texts = files
        .iter()
        .filter_map(|file| {
            let text = fs::read_to_string(file).ok()?;
            let name = file.strip_prefix(&crates).unwrap_or(file).display();
            Some((
                name.to_string(),
                blocks(&text)
                    .into_iter()
                    .map(|(claims, payload)| (claims, payload.to_owned()))
                    .collect::<Vec<_>>(),
            ))
        })
        .collect::<Vec<_>>();
    texts.push((
        "entry_reach.rs NESTED_SPLICES".to_owned(),
        NESTED_SPLICES
            .iter()
            .map(|(claims, payload)| (*claims, (*payload).to_owned()))
            .collect(),
    ));
    let mut nested = 0usize;
    for (name, payloads) in &texts {
        for (claims, payload) in payloads {
            let (claims, payload) = (*claims, payload.as_str());
            let (clauses, form) = if claims {
                match ClaimBlock::parse_source(payload) {
                    Ok(block) => (block.clauses().to_vec(), EntryForm::Claim),
                    Err(_) => continue,
                }
            } else {
                match RuleBlock::parse_source(payload) {
                    Ok(block) => (block.clauses().to_vec(), EntryForm::Readable),
                    Err(_) => continue,
                }
            };
            for clause in clauses.iter().filter(|clause| admitted(clause)) {
                let Some((subject, result)) = clause.records() else {
                    continue;
                };
                for fields in [
                    entry_fields(subject, form),
                    entry_result_fields(result, form),
                ] {
                    match fields {
                        Some(fields) => {
                            for field in fields {
                                read += 1;
                                nested += usize::from(name.ends_with("NESTED_SPLICES"));
                                if field.spelling.is_none() {
                                    unread.push(format!(
                                        "{name}: {}",
                                        quote::ToTokens::to_token_stream(&field.key)
                                    ));
                                }
                            }
                        }
                        None => unread.push(format!(
                            "{name}: a record the reading does not split into fields"
                        )),
                    }
                }
            }
        }
    }
    assert!(read > 1000, "the sources hold the readable entries: {read}");
    // Every clause written here is admitted whole, so each of its fields is counted.
    assert_eq!(nested, 24, "the nested splices' clauses are admitted whole");
    assert!(
        unread.is_empty(),
        "entries the readable reader admits and the table reads as no spelling:\n{}",
        unread.join("\n")
    );
}
