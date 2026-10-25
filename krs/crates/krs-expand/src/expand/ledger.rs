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
pub(super) struct KeyLedger<'a> {
    anchors: &'a [ProvenanceAnchor],
    index: HashMap<ProvenanceKey, usize>,
    defined: Vec<Cell<bool>>,
    fixed: Vec<ProvenanceKey>,
}

impl<'a> KeyLedger<'a> {
    /// Opens the ledger of a descriptor whose sentence anchored `anchors`.
    /// The first key of each of `fixed` is one the descriptor's kind names
    /// by itself (its primary declaration, or the clause keyword of an alias
    /// or desugar rule), which no wire field carries.
    pub(super) fn new(anchors: &'a [ProvenanceAnchor], fixed: &[ProvenanceRole]) -> Self {
        Self {
            anchors,
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
        let index = self.anchored(&key)?;
        if self.defined[index].replace(true) {
            return Err(ExpandError::at_range(
                expand::DUPLICATE_PROVENANCE_KEY,
                self.anchors[index].range(),
                format_args!(
                    "two wire nodes take the provenance key `{} {}` of this node as their own; this is a bug in KRS, not in the definition",
                    key.role().as_str(),
                    key.ordinal(),
                ),
            ));
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
    fn anchored(&self, key: &ProvenanceKey) -> crate::Result<usize> {
        self.index.get(key).copied().ok_or_else(|| {
            ExpandError::at_invocation(
                expand::UNANCHORED_PROVENANCE_KEY,
                format_args!(
                    "a wire node names the provenance key `{} {}`, which no authored node of this sentence holds; this is a bug in KRS, not in the definition",
                    key.role().as_str(),
                    key.ordinal(),
                ),
            )
        })
    }

    /// Requires every anchored key to be defined, except the kind's fixed
    /// keys: the first one left is an authored node the expansion dropped.
    pub(super) fn finish(&self) -> crate::Result<()> {
        for (anchor, defined) in self.anchors.iter().zip(&self.defined) {
            let key = anchor.key();
            if !defined.get() && !self.fixed.contains(&key) {
                return Err(ExpandError::at_range(
                    expand::UNCONSUMED_PROVENANCE_KEY,
                    anchor.range(),
                    format_args!(
                        "no wire node takes the provenance key `{} {}` of this node, so the descriptor would drop it; this is a bug in KRS, not in the definition",
                        key.role().as_str(),
                        key.ordinal(),
                    ),
                ));
            }
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

#[cfg(test)]
mod tests {
    use krs_diagnostic::Location;
    use krs_diagnostic::codes::expand;
    use krs_syntax::{ProvenanceAnchor, ProvenanceRole, TokenRange};

    use super::KeyLedger;

    /// Anchors on `first second third` with the given keys, in that order.
    fn anchors(
        keys: [(ProvenanceRole, u32); 3],
    ) -> (Vec<ProvenanceAnchor>, Vec<proc_macro2::Span>) {
        let tokens: proc_macro2::TokenStream = "first second third".parse().unwrap();
        let spans = tokens
            .into_iter()
            .map(|token| token.span())
            .collect::<Vec<_>>();
        let anchors = keys
            .iter()
            .zip(&spans)
            .map(|((role, ordinal), span)| {
                ProvenanceAnchor::new(*role, *ordinal, TokenRange::new(*span, *span))
            })
            .collect();
        (anchors, spans)
    }

    /// The code of the one diagnostic of `error`, and the start of its span.
    fn located(error: &crate::ExpandError) -> (krs_diagnostic::Code, Option<proc_macro2::Span>) {
        let diagnostics = error.diagnostics().collect::<Vec<_>>();
        assert_eq!(diagnostics.len(), 1);
        let span = match diagnostics[0].primary.location {
            Location::Span(span) => Some(span),
            _ => None,
        };
        (diagnostics[0].code.clone(), span)
    }

    const KEYS: [(ProvenanceRole, u32); 3] = [
        (ProvenanceRole::RuleDeclaration, 0),
        (ProvenanceRole::KSequencePayload, 0),
        (ProvenanceRole::KSequencePayload, 1),
    ];

    #[test]
    fn every_anchor_defined_once_or_fixed_finishes() {
        let (anchors, _) = anchors(KEYS);
        let ledger = KeyLedger::new(&anchors, &[ProvenanceRole::RuleDeclaration]);
        ledger.define(Some(&anchors[1].key())).unwrap();
        ledger.refer(Some(&anchors[1].key())).unwrap();
        ledger.define_key(anchors[2].key()).unwrap();
        ledger.finish().unwrap();
    }

    #[test]
    fn a_second_definition_is_located_at_the_node() {
        let (anchors, spans) = anchors(KEYS);
        let ledger = KeyLedger::new(&anchors, &[ProvenanceRole::RuleDeclaration]);
        ledger.define_key(anchors[2].key()).unwrap();
        let error = ledger.define_key(anchors[2].key()).unwrap_err();
        let (code, span) = located(&error);
        assert_eq!(code, expand::DUPLICATE_PROVENANCE_KEY);
        assert_eq!(span.unwrap().start(), spans[2].start());
    }

    #[test]
    fn a_dropped_node_is_located_at_its_anchor() {
        let (anchors, spans) = anchors(KEYS);
        let ledger = KeyLedger::new(&anchors, &[]);
        ledger.define_key(anchors[2].key()).unwrap();
        // The first anchor left over, a kind's key that is not fixed here.
        let error = ledger.finish().unwrap_err();
        let (code, span) = located(&error);
        assert_eq!(code, expand::UNCONSUMED_PROVENANCE_KEY);
        assert_eq!(span.unwrap().start(), spans[0].start());
        assert_eq!(
            error.diagnostics().next().unwrap().message,
            "no wire node takes the provenance key `rule_declaration 0` of this node, so the descriptor would drop it; this is a bug in KRS, not in the definition"
        );
    }

    #[test]
    fn a_key_no_anchor_holds_is_refused() {
        let (anchors, _) = anchors(KEYS);
        let ledger = KeyLedger::new(&anchors, &[]);
        let unanchored = ProvenanceRole::KSequencePayload.key(2);
        for error in [
            ledger.define_key(unanchored.clone()).unwrap_err(),
            ledger.refer_key(unanchored.clone()).unwrap_err(),
        ] {
            let (code, span) = located(&error);
            assert_eq!(code, expand::UNANCHORED_PROVENANCE_KEY);
            assert!(span.is_none());
        }
        let missing = ledger.define(None).unwrap_err();
        assert_eq!(located(&missing).0, expand::MISSING_PROVENANCE_KEY);
    }
}
