//! The key ledger of one descriptor.
//!
//! A descriptor's sentence keys each authored node once, at parse, and its
//! anchors are those keys. Expansion turns authored nodes into wire nodes,
//! and each wire node either takes the key of the node it denotes as its own
//! ([`KeyLedger::define`]) or names a node another wire node denotes
//! ([`KeyLedger::refer`]). When the payload is built, every anchored key
//! must have been defined exactly once, except the keys the descriptor's
//! kind names by itself ([`KeyLedger::finish`]): an anchored node that no
//! wire node denotes would be dropped from the descriptor, and two wire
//! nodes that both claim one node would carry its location twice. Either is
//! a bug in KRS, reported here, at the node, inside the expansion that made
//! it.

use std::cell::Cell;
use std::collections::HashMap;

use krs_diagnostic::codes::expand;
use krs_ir::ProvenanceKey;
use krs_syntax::{ProvenanceAnchor, ProvenanceRole};

use crate::ExpandError;

/// Which anchored keys of one descriptor its wire nodes have defined.
pub(super) struct KeyLedger {
    anchors: Vec<ProvenanceAnchor>,
    index: HashMap<ProvenanceKey, usize>,
    defined: Vec<Cell<bool>>,
    fixed: Vec<ProvenanceKey>,
}

impl KeyLedger {
    /// Opens the ledger of a descriptor whose sentence anchored `anchors`.
    /// The first key of each of `fixed` is one the descriptor's kind names
    /// by itself (its primary declaration, or the clause keyword of an alias
    /// or desugar rule), which no wire field carries.
    pub(super) fn new(anchors: &[ProvenanceAnchor], fixed: &[ProvenanceRole]) -> Self {
        Self {
            anchors: anchors.to_vec(),
            index: anchors
                .iter()
                .enumerate()
                .map(|(index, anchor)| (anchor.key(), index))
                .collect(),
            defined: anchors.iter().map(|_| Cell::new(false)).collect(),
            fixed: fixed.iter().map(|role| role.key(0)).collect(),
        }
    }

    /// The key `read` of the authored node a wire node denotes, which the
    /// wire node takes as its own.
    pub(super) fn define(&self, read: Option<&ProvenanceKey>) -> crate::Result<ProvenanceKey> {
        self.define_key(held_key(read)?)
    }

    /// `key`, which a wire node takes as its own; the second wire node that
    /// takes one key is a KRS bug.
    pub(super) fn define_key(&self, key: ProvenanceKey) -> crate::Result<ProvenanceKey> {
        if let Some(index) = self.anchored(&key)?
            && self.defined[index].replace(true)
        {
            self.report(ExpandError::at_range(
                expand::DUPLICATE_PROVENANCE_KEY,
                self.anchors[index].range(),
                format_args!(
                    "two wire nodes take the provenance key `{} {}` of this node as their own; this is a bug in KRS, not in the definition",
                    key.role().as_str(),
                    key.ordinal(),
                ),
            ))?;
        }
        Ok(key)
    }

    /// The key `read` of an authored node that another wire node denotes,
    /// which this one names.
    pub(super) fn refer(&self, read: Option<&ProvenanceKey>) -> crate::Result<ProvenanceKey> {
        self.refer_key(held_key(read)?)
    }

    /// `key`, of a node another wire node denotes, which this one names.
    pub(super) fn refer_key(&self, key: ProvenanceKey) -> crate::Result<ProvenanceKey> {
        self.anchored(&key)?;
        Ok(key)
    }

    /// The anchor index of `key`; a key the sentence did not anchor names no
    /// authored node of this descriptor.
    fn anchored(&self, key: &ProvenanceKey) -> crate::Result<Option<usize>> {
        let index = self.index.get(key).copied();
        if index.is_none() {
            self.report(ExpandError::at_invocation(
                expand::UNANCHORED_PROVENANCE_KEY,
                format_args!(
                    "a wire node names the provenance key `{} {}`, which no authored node of this sentence holds; this is a bug in KRS, not in the definition",
                    key.role().as_str(),
                    key.ordinal(),
                ),
            ))?;
        }
        Ok(index)
    }

    /// Requires every anchored key to be defined, except the kind's fixed
    /// keys: the first one left is an authored node the expansion dropped.
    pub(super) fn finish(&self) -> crate::Result<()> {
        self.finish_with(|_| false)
    }

    /// [`Self::finish`] for a descriptor whose anchors repeat nodes of
    /// `sibling`, the other descriptor of the same item, whose wire nodes
    /// denote them: a constructor's descriptor lists its production's
    /// syntax, which only its grammar descriptor carries.
    pub(super) fn finish_beside(&self, sibling: &Self) -> crate::Result<()> {
        self.finish_with(|key| sibling.defines(key))
    }

    /// Whether a wire node of this descriptor took `key` as its own.
    fn defines(&self, key: &ProvenanceKey) -> bool {
        self.index
            .get(key)
            .is_some_and(|index| self.defined[*index].get())
    }

    fn finish_with(&self, elsewhere: impl Fn(&ProvenanceKey) -> bool) -> crate::Result<()> {
        for (anchor, defined) in self.anchors.iter().zip(&self.defined) {
            let key = anchor.key();
            if !defined.get() && !self.fixed.contains(&key) && !elsewhere(&key) {
                self.report(ExpandError::at_range(
                    expand::UNCONSUMED_PROVENANCE_KEY,
                    anchor.range(),
                    format_args!(
                        "no wire node takes the provenance key `{} {}` of this node, so the descriptor would drop it; this is a bug in KRS, not in the definition",
                        key.role().as_str(),
                        key.ordinal(),
                    ),
                ))?;
            }
        }
        Ok(())
    }

    /// Report mode, while the ledger's findings are surveyed: a finding is
    /// appended to the file `KRS_KEY_LEDGER_REPORT` names, when set, and
    /// expansion goes on.
    #[expect(
        clippy::needless_pass_by_value,
        clippy::unnecessary_wraps,
        reason = "Report mode records what refusing mode will return."
    )]
    fn report(&self, error: ExpandError) -> crate::Result<()> {
        use std::fmt::Write as _;
        use std::io::Write as _;
        let Some(path) = std::env::var_os("KRS_KEY_LEDGER_REPORT") else {
            return Ok(());
        };
        let mut lines = String::new();
        for diagnostic in error.diagnostics() {
            let span = match &diagnostic.primary.location {
                krs_diagnostic::Location::Span(span) => Some(*span),
                _ => self.anchors.first().map(|anchor| anchor.range().first()),
            };
            let place = span.map_or_else(String::new, |span| {
                let start = span.start();
                let file = span.local_file();
                let text = file
                    .as_ref()
                    .and_then(|file| std::fs::read_to_string(file).ok())
                    .and_then(|source| {
                        source
                            .lines()
                            .nth(start.line.saturating_sub(1))
                            .map(|line| line.trim().to_owned())
                    })
                    .unwrap_or_default();
                format!(
                    "{}:{}:{}\t{text}",
                    file.map_or_else(|| span.file(), |file| file.display().to_string()),
                    start.line,
                    start.column + 1,
                )
            });
            let sentence = match (self.anchors.first(), self.anchors.last()) {
                (Some(first), Some(last)) => first
                    .range()
                    .first()
                    .join(last.range().last())
                    .and_then(|span| span.source_text())
                    .unwrap_or_default(),
                _ => String::new(),
            };
            let node = span.and_then(|span| span.source_text()).unwrap_or_default();
            let sentence = sentence.split_whitespace().collect::<Vec<_>>().join(" ");
            let sentence = sentence.chars().take(300).collect::<String>();
            let _ = writeln!(
                lines,
                "{}\t{place}\t{}\t{node}\t{sentence}",
                diagnostic.code, diagnostic.message
            );
        }
        if let Ok(mut file) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
        {
            let _ = file.write_all(lines.as_bytes());
        }
        Ok(())
    }
}

/// The key of the authored node a wire node denotes, which its sentence
/// gave it at parse; a node expansion reaches without one is a KRS bug.
fn held_key(read: Option<&ProvenanceKey>) -> crate::Result<ProvenanceKey> {
    read.cloned().ok_or_else(|| {
        ExpandError::at_invocation(
            expand::MISSING_PROVENANCE_KEY,
            "an authored node holds no provenance key from its sentence's parse",
        )
    })
}
