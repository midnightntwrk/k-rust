//! The entry table reads every entry the readable reader admits. Over every `k::rules!` and
//! `k::claims!` block written in the krs-cli test sources and the krs test fixtures, each clause
//! the readable reader admits whole (no refusal it carries until its entries are judged) has
//! records whose every field the entry reading spells: a field it reads as no spelling would
//! skip the table's judgement of that cell, its kind and its pairing, so the lowering would be
//! the table's only check. A block the reader refuses, or whose text is a template with holes,
//! is not counted.

use std::fs;
use std::path::{Path, PathBuf};

use krs_syntax::cell_entry::{EntryForm, entry_fields};
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
    for file in &files {
        let Ok(text) = fs::read_to_string(file) else {
            continue;
        };
        for (claims, payload) in blocks(&text) {
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
                for record in [subject, result] {
                    match entry_fields(record, form) {
                        Some(fields) => {
                            for field in fields {
                                read += 1;
                                if field.spelling.is_none() {
                                    unread.push(format!(
                                        "{}: {}",
                                        file.strip_prefix(&crates).unwrap_or(file).display(),
                                        quote::ToTokens::to_token_stream(&field.key)
                                    ));
                                }
                            }
                        }
                        None => unread.push(format!(
                            "{}: a record the reading does not split into fields",
                            file.strip_prefix(&crates).unwrap_or(file).display()
                        )),
                    }
                }
            }
        }
    }
    assert!(read > 1000, "the sources hold the readable entries: {read}");
    assert!(
        unread.is_empty(),
        "entries the readable reader admits and the table reads as no spelling:\n{}",
        unread.join("\n")
    );
}
