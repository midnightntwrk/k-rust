//! Snapshot files: values a user accepted for a case under a projection whose relation is a
//! snapshot (projections PJ-20, `relation = "snapshot"`).
//!
//! A snapshot is an input of a relation, not a derivation: it holds what an implementation
//! stated for a case once a user accepted it, so it is never in the lock, which holds what kink
//! derives (README, "The record and the cache"). Each (projection, case) has one file beside the
//! flow, `snapshots/<projection>/<case id>.json` ([`path`]), which only an explicit command
//! writes; `compare` reads it.
//!
//! Every value a snapshot projection observes is structured ([`observed`], [`crashed`]): under
//! an `accepts` projection the implementation's whole answer to whether it accepts the case
//! (`accepted`, `rejected` with its `message` and `refused` where stated, `crashed` with its exit
//! status or signal), under an `end` projection the end its answer states. A value is stored as
//! its document rendered with sorted keys and two-space indentation ([`SnapshotValue::render`])
//! and compared as a JSON value, so a file re-ordered or re-spaced by hand is no difference and a
//! difference reads line by line (G8).
//!
//! Every answered case has a value, so a case is `pending` exactly where its file does not exist.

use crate::compare::{Failure, Stated, StatedEnd};
use crate::manifest::ProjectionKind;
use serde_json::{Map, Value, json};
use std::path::{Path, PathBuf};

/// The directory beside the flow that holds the snapshots, one directory per projection.
pub const SNAPSHOTS_DIRECTORY: &str = "snapshots";

/// The extension of every snapshot file: each holds a JSON document.
pub const SNAPSHOT_EXTENSION: &str = "json";

/// The format of a snapshot view's difference ([`Judgement::Different`]).
pub const SNAPSHOT_DIFFERENCE_FORMAT: &str = "kink-snapshot/1";

/// The most lines a line diff computes a common subsequence over (the product of both sides'
/// line counts); beyond it every line of one side is removed and every line of the other added.
const DIFF_CELLS: usize = 1 << 22;

/// What a snapshot projection observes of an implementation's run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SnapshotKind {
    /// An `accepts` projection: the answer to whether it accepts the case.
    Acceptance,
    /// An `end` projection: the end its answer states.
    End,
}

impl SnapshotKind {
    /// The kind a snapshot projection of `kind` observes; `None` for a `trace` projection, which
    /// has no snapshot (decoding refuses one).
    #[must_use]
    pub const fn of(kind: ProjectionKind) -> Option<Self> {
        match kind {
            ProjectionKind::Accepts => Some(Self::Acceptance),
            ProjectionKind::End => Some(Self::End),
            ProjectionKind::Trace => None,
        }
    }
}

/// A value a snapshot holds or an implementation states: a document, compared as a JSON value.
#[derive(Clone, Debug, PartialEq)]
pub struct SnapshotValue(pub Value);

impl SnapshotValue {
    /// The file's contents: the document with its object keys in sorted order, indented by two
    /// spaces, and one newline at its end.
    #[must_use]
    pub fn render(&self) -> String {
        let mut text =
            serde_json::to_string_pretty(&sorted(&self.0)).unwrap_or_else(|_| self.0.to_string());
        text.push('\n');
        text
    }

    /// The value as a document member.
    #[must_use]
    pub fn value(&self) -> Value {
        self.0.clone()
    }
}

/// `value` with every object's keys inserted in sorted order, so its rendering lists them so
/// whether or not `serde_json` keeps insertion order.
fn sorted(value: &Value) -> Value {
    match value {
        Value::Object(members) => {
            let mut keys = members.keys().collect::<Vec<_>>();
            keys.sort();
            let mut ordered = Map::new();
            for key in keys {
                ordered.insert(key.clone(), sorted(&members[key]));
            }
            Value::Object(ordered)
        }
        Value::Array(items) => Value::Array(items.iter().map(sorted).collect()),
        other => other.clone(),
    }
}

/// The value a snapshot view of `kind` observes in an answer. [`SnapshotKind::Acceptance`]:
/// `{answer}`, `accepted` for `stopped` or `final`, `horizon` for an answer that has not ended,
/// `rejected` with the `message` and `refused` the answer states. [`SnapshotKind::End`]: the end
/// as the answer states it, `{end, cells?, message?, refused?}` with the members it states (its
/// `observations` are a trace's, not the end's). `None` for `could-not-apply`, which states
/// nothing of the program (a verdict of its own).
#[must_use]
pub fn observed(kind: SnapshotKind, stated: &Stated) -> Option<SnapshotValue> {
    let mut value = Map::new();
    match (kind, &stated.end) {
        (_, StatedEnd::CouldNotApply(_)) => return None,
        (SnapshotKind::Acceptance, StatedEnd::Ended(_)) => {
            value.insert("answer".into(), json!("accepted"));
        }
        (SnapshotKind::Acceptance, StatedEnd::Horizon) => {
            value.insert("answer".into(), json!("horizon"));
        }
        (SnapshotKind::Acceptance, StatedEnd::Rejected { .. }) => {
            value.insert("answer".into(), json!("rejected"));
        }
        (SnapshotKind::End, _) => {
            value.insert("end".into(), json!(stated.word()));
            if let Some(cells) = &stated.cells {
                value.insert("cells".into(), cells.clone());
            }
        }
    }
    if let StatedEnd::Rejected { message, refused } = &stated.end {
        if let Some(message) = message {
            value.insert("message".into(), json!(message));
        }
        if let Some(refused) = refused {
            value.insert("refused".into(), refused.clone());
        }
    }
    Some(SnapshotValue(Value::Object(value)))
}

/// The value a snapshot view of an `accepts` projection observes of a run that crashed (a
/// failure of kind `exit`): `{answer: "crashed", exit_code}` where it exited with a status,
/// `{answer: "crashed", signal}` where a signal ended it (null where the platform names none).
/// A status is a function of the binary and the request; a signal is too where the program
/// raises it (an abort, a fault), and depends on the host where something else sends it (the
/// out-of-memory killer, an operator), which kink cannot tell apart.
#[must_use]
pub fn crashed(failure: &Failure) -> SnapshotValue {
    SnapshotValue(match failure.exit_code {
        Some(code) => json!({"answer": "crashed", "exit_code": code}),
        None => json!({"answer": "crashed", "signal": failure.signal}),
    })
}

/// The path of the snapshot of `case` under `projection`, relative to the flow's directory:
/// `snapshots/<projection>/<case id>.json`, `/` separating its components. The projection's name
/// is one component and the case id's `/` separates directories, so the snapshots mirror the
/// cases; each component is escaped ([`component`]), so no two (projection, case) pairs share a
/// path and none leaves `snapshots/<projection>/`.
#[must_use]
pub fn relative(projection: &str, case: &str) -> String {
    let mut path = format!("{SNAPSHOTS_DIRECTORY}/{}/", component(projection));
    path.push_str(&case.split('/').map(component).collect::<Vec<_>>().join("/"));
    path.push('.');
    path.push_str(SNAPSHOT_EXTENSION);
    path
}

/// The snapshot of `case` under `projection` in the flow whose directory is `directory`
/// ([`relative`]).
#[must_use]
pub fn path(directory: &Path, projection: &str, case: &str) -> PathBuf {
    relative(projection, case)
        .split('/')
        .fold(directory.to_path_buf(), |path, part| path.join(part))
}

/// One path component for `name`: each byte outside `[A-Za-z0-9._#-]` as `%XX` (`%` itself
/// included, so the escape is reversible), the dots of `.` and `..` as `%2E`, so neither names a
/// directory of the walk, and the empty name as `%`, which no other name gives.
fn component(name: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    if name.is_empty() {
        return "%".to_owned();
    }
    if name == "." || name == ".." {
        return "%2E".repeat(name.len());
    }
    let mut escaped = String::new();
    for byte in name.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'#' | b'-') {
            escaped.push(char::from(byte));
        } else {
            escaped.push('%');
            escaped.push(char::from(HEX[usize::from(byte >> 4)]));
            escaped.push(char::from(HEX[usize::from(byte & 0xf)]));
        }
    }
    escaped
}

/// What a snapshot file holds.
#[derive(Clone, Debug, PartialEq)]
pub enum Reference {
    /// No file: no value was accepted.
    Missing,
    /// The accepted value.
    Value(SnapshotValue),
    /// The file cannot be read as a JSON document: why.
    Unreadable(String),
}

/// Read the snapshot at `path`.
#[must_use]
pub fn read(path: &Path) -> Reference {
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Reference::Missing,
        Err(error) => return Reference::Unreadable(format!("it cannot be read: {error}")),
    };
    match serde_json::from_slice(&bytes) {
        Ok(document) => Reference::Value(SnapshotValue(document)),
        Err(error) => Reference::Unreadable(format!("it is no JSON document: {error}")),
    }
}

/// The judgement of an observed value against a snapshot.
#[derive(Clone, Debug, PartialEq)]
pub enum Judgement {
    /// The observed value is the accepted one.
    Equal,
    /// They differ: the difference, `{format, snapshot, observed, lines}` ([`difference`]).
    Different(Value),
    /// No value was accepted.
    Pending,
    /// The snapshot cannot be read: why.
    Unreadable(String),
}

/// Judge `observed` against `reference`, as JSON values.
#[must_use]
pub fn judge(observed: &SnapshotValue, reference: &Reference) -> Judgement {
    match reference {
        Reference::Unreadable(why) => Judgement::Unreadable(why.clone()),
        Reference::Missing => Judgement::Pending,
        Reference::Value(accepted) if accepted == observed => Judgement::Equal,
        Reference::Value(accepted) => Judgement::Different(difference(accepted, observed)),
    }
}

/// The difference of a snapshot and an observed value: both values and `lines`, a line diff of
/// their renderings ([`SnapshotValue::render`]).
#[must_use]
pub fn difference(accepted: &SnapshotValue, observed: &SnapshotValue) -> Value {
    json!({
        "format": SNAPSHOT_DIFFERENCE_FORMAT,
        "snapshot": accepted.value(),
        "observed": observed.value(),
        "lines": line_diff(&accepted.render(), &observed.render()),
    })
}

/// The line diff from `old` to `new`: their lines around a longest common subsequence, ` `
/// before a line both have, `-` before one only `old` has and `+` before one only `new` has, in
/// the order of both texts, a removal before an addition. Lines are separated by `\n`.
#[must_use]
pub fn line_diff(old: &str, new: &str) -> Vec<String> {
    let old = old.split('\n').collect::<Vec<_>>();
    let new = new.split('\n').collect::<Vec<_>>();
    let (n, m) = (old.len(), new.len());
    if n.saturating_mul(m) > DIFF_CELLS {
        return old
            .iter()
            .map(|line| format!("-{line}"))
            .chain(new.iter().map(|line| format!("+{line}")))
            .collect();
    }
    // `common[i][j]`: the longest common subsequence of `old[i..]` and `new[j..]`.
    let mut common = vec![vec![0_usize; m + 1]; n + 1];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            common[i][j] = if old[i] == new[j] {
                common[i + 1][j + 1] + 1
            } else {
                common[i + 1][j].max(common[i][j + 1])
            };
        }
    }
    let (mut i, mut j) = (0, 0);
    let mut lines = Vec::new();
    while i < n || j < m {
        if i < n && j < m && old[i] == new[j] {
            lines.push(format!(" {}", old[i]));
            i += 1;
            j += 1;
        } else if i < n && (j == m || common[i + 1][j] >= common[i][j + 1]) {
            lines.push(format!("-{}", old[i]));
            i += 1;
        } else {
            lines.push(format!("+{}", new[j]));
            j += 1;
        }
    }
    lines
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rejected(message: Option<&str>, refused: Option<Value>) -> Stated {
        Stated {
            end: StatedEnd::Rejected {
                message: message.map(str::to_owned),
                refused,
            },
            cells: None,
            observations: None,
        }
    }

    /// The path keeps the case's directories and escapes what would leave them or collide.
    #[test]
    fn a_case_id_is_one_path_under_its_projection() {
        assert_eq!(
            relative("msg", "cases/bad/one.toml#b"),
            "snapshots/msg/cases/bad/one.toml#b.json"
        );
        assert_eq!(relative("a/b", "x"), "snapshots/a%2Fb/x.json");
        assert_eq!(
            relative("..", "../../etc/passwd"),
            "snapshots/%2E%2E/%2E%2E/%2E%2E/etc/passwd.json"
        );
        assert_eq!(relative("p", "a//b"), "snapshots/p/a/%/b.json");
        assert_eq!(relative("p", "100%"), "snapshots/p/100%25.json");
        assert_eq!(relative("p", "é "), "snapshots/p/%C3%A9%20.json");
        // Distinct ids give distinct paths, the escape's own characters included.
        let ids = ["%", "%25", "", ".", "%2E", "a b", "a%20b", "a/b", "a%2Fb"];
        let paths = ids
            .iter()
            .map(|id| relative("p", id))
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(paths.len(), ids.len(), "{paths:?}");
        assert_eq!(
            path(Path::new("flow"), "p", "a/b"),
            Path::new("flow")
                .join("snapshots")
                .join("p")
                .join("a")
                .join("b.json")
        );
    }

    /// A value is rendered with sorted keys and two-space indentation, and a newline at its end.
    #[test]
    fn a_value_is_rendered_with_sorted_keys() {
        let document = SnapshotValue(json!({"end": "final", "cells": {"b": 1, "a": [2]}}));
        assert_eq!(
            document.render(),
            "{\n  \"cells\": {\n    \"a\": [\n      2\n    ],\n    \"b\": 1\n  },\n  \"end\": \
             \"final\"\n}\n"
        );
    }

    /// An `accepts` snapshot observes the whole answer to whether the case is accepted; an
    /// `end` snapshot the stated end; a crash is a value of its own.
    #[test]
    fn the_observed_value_is_the_answer_s() {
        let value = |value: Value| Some(SnapshotValue(value));
        let refused = json!({"end": "crate::trap", "reason": 1});
        assert_eq!(
            observed(
                SnapshotKind::Acceptance,
                &rejected(Some("bad token"), Some(refused.clone()))
            ),
            value(json!({"answer": "rejected", "message": "bad token", "refused": refused}))
        );
        assert_eq!(
            observed(SnapshotKind::Acceptance, &rejected(None, None)),
            value(json!({"answer": "rejected"}))
        );
        let accepted = Stated {
            end: StatedEnd::Ended(crate::compare::EndWord::Final),
            cells: Some(json!({"acc": 3})),
            observations: Some(json!({"ticks": []})),
        };
        assert_eq!(
            observed(SnapshotKind::Acceptance, &accepted),
            value(json!({"answer": "accepted"}))
        );
        assert_eq!(
            observed(SnapshotKind::End, &accepted),
            value(json!({"end": "final", "cells": {"acc": 3}}))
        );
        assert_eq!(
            observed(SnapshotKind::End, &rejected(Some("no"), None)),
            value(json!({"end": "rejected", "message": "no"}))
        );
        let declined = Stated {
            end: StatedEnd::CouldNotApply("later".into()),
            cells: None,
            observations: None,
        };
        assert_eq!(observed(SnapshotKind::Acceptance, &declined), None);
        let exited = Failure {
            exit_code: Some(101),
            ..Failure::new("exit", "it exited with status 101")
        };
        assert_eq!(
            crashed(&exited),
            SnapshotValue(json!({"answer": "crashed", "exit_code": 101}))
        );
        let killed = Failure {
            signal: Some(6),
            ..Failure::new("exit", "it was killed by a signal")
        };
        assert_eq!(
            crashed(&killed),
            SnapshotValue(json!({"answer": "crashed", "signal": 6}))
        );
    }

    /// A missing file is pending; a value is compared as a JSON value, so re-ordering and
    /// re-spacing is no difference; an unreadable file says why.
    #[test]
    fn a_value_is_judged_against_its_snapshot() {
        let directory = std::env::temp_dir().join(format!(
            "kink-flow-snapshot-{}-{}",
            std::process::id(),
            line!()
        ));
        let _ = std::fs::remove_dir_all(&directory);
        let file = path(&directory, "end", "cases/a");
        let end = SnapshotValue(json!({"end": "final", "cells": {"a": 1, "b": [1, 2]}}));
        assert_eq!(judge(&end, &read(&file)), Judgement::Pending);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(&file, end.render()).unwrap();
        assert_eq!(judge(&end, &read(&file)), Judgement::Equal);
        std::fs::write(
            &file,
            "{\"end\":\"final\",   \"cells\": {\"b\": [1,2],\n\"a\": 1}}",
        )
        .unwrap();
        assert_eq!(
            judge(&end, &read(&file)),
            Judgement::Equal,
            "a re-ordered, re-spaced snapshot is no difference"
        );
        let moved = SnapshotValue(json!({"end": "final", "cells": {"a": 2, "b": [1, 2]}}));
        let Judgement::Different(difference) = judge(&moved, &read(&file)) else {
            panic!("another cell value is different");
        };
        assert_eq!(difference["format"], SNAPSHOT_DIFFERENCE_FORMAT);
        assert_eq!(difference["snapshot"], end.value());
        assert_eq!(difference["observed"], moved.value());
        let lines = difference["lines"].as_array().unwrap();
        assert!(lines.contains(&json!("-    \"a\": 1,")), "{lines:?}");
        assert!(lines.contains(&json!("+    \"a\": 2,")), "{lines:?}");
        std::fs::write(&file, "{").unwrap();
        assert!(matches!(
            judge(&end, &read(&file)),
            Judgement::Unreadable(why) if why.contains("JSON")
        ));
        let _ = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn a_line_diff_keeps_the_common_lines() {
        assert_eq!(
            line_diff("a\nb\nc", "a\nx\nc\nd"),
            [" a", "-b", "+x", " c", "+d"]
        );
        assert_eq!(line_diff("a", "a"), [" a"]);
    }
}
