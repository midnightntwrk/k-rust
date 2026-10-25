//! The provenance keys one descriptor payload carries, checked against the
//! descriptor's anchors.
//!
//! The parser keys every authored node of a descriptor once, and the
//! descriptor's provenance holds one anchor per key. A payload's wire nodes
//! carry those keys in typed fields. The transport checks three things of
//! them, none of which needs the parser's numbering:
//!
//! - each key a field holds has the role that field requires;
//! - each key is *defined* by one wire node, the node it names; a field that
//!   names a node another field defines is a *reference* to it;
//! - the defined keys, the kind's fixed declaration keys and the keys of
//!   the wire nodes that carry none ([`WireKeys::implicit`]) are exactly the
//!   anchors' keys (closure), and every reference names a defined key.

use std::collections::{BTreeMap, BTreeSet};

use crate::{ProvenanceKey, ProvenanceRole};

/// A failed key check, which each stage reports as its own transport error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum KeyFailure {
    /// A field held a key of another role than the field requires.
    Role {
        /// The field's role.
        expected: ProvenanceRole,
        /// The key the field held.
        actual: ProvenanceKey,
    },
    /// A second wire node defined a key.
    Duplicate(ProvenanceKey),
    /// A wire key that no anchor holds.
    Missing(ProvenanceKey),
    /// An anchor that no wire node consumes.
    Extra(ProvenanceKey),
}

/// The keys of one payload's wire nodes, gathered by its validator.
#[derive(Debug, Default)]
pub(crate) struct WireKeys {
    defined: BTreeSet<ProvenanceKey>,
    referred: BTreeSet<ProvenanceKey>,
    implicit: BTreeMap<ProvenanceRole, usize>,
}

impl WireKeys {
    /// Records `key` as the key of the node its field denotes: a key of
    /// `role`, which no other wire node of the payload defines.
    pub(crate) fn define(
        &mut self,
        key: &ProvenanceKey,
        role: ProvenanceRole,
    ) -> Result<(), KeyFailure> {
        require_role(key, role)?;
        if !self.defined.insert(key.clone()) {
            return Err(KeyFailure::Duplicate(key.clone()));
        }
        Ok(())
    }

    /// Records `key` as defined by a node whose field has no role contract
    /// on the wire yet: a cell, frame or term key of an equation's function
    /// context, which the transport gathers as a set.
    pub(crate) fn define_untyped(&mut self, key: &ProvenanceKey) -> Result<(), KeyFailure> {
        self.define(key, key.role())
    }

    /// Records `key` as naming a node another wire node defines: a key of
    /// `role`.
    pub(crate) fn refer(
        &mut self,
        key: &ProvenanceKey,
        role: ProvenanceRole,
    ) -> Result<(), KeyFailure> {
        require_role(key, role)?;
        self.referred.insert(key.clone());
        Ok(())
    }

    /// Records one of the kind's fixed declaration keys: the descriptor's own
    /// declaration of `role`, which no wire field carries. A descriptor
    /// declares one such node, so its key is the role's first.
    pub(crate) fn fixed(&mut self, role: ProvenanceRole) -> Result<(), KeyFailure> {
        self.define(&ProvenanceKey::new(role, 0), role)
    }

    /// Records one wire node that denotes an anchored node of `role` but has
    /// no key field to carry its key.
    ///
    /// This is the one positional pairing the transport keeps: at
    /// [`Self::close`], the anchors of `role` that no wire node defines pair,
    /// in their order, with the nodes recorded here, and the two counts must
    /// agree. The roles it covers, until the wire gains their key fields:
    /// a sort's parents ([`ProvenanceRole::SortParent`]) and a constructor's
    /// field sorts ([`ProvenanceRole::ConstructorFieldSort`]), whose host
    /// references carry type keys only; a constant's value
    /// ([`ProvenanceRole::ConstantValue`]); the spelling of a claim's
    /// anonymous constant ([`ProvenanceRole::ClaimAnonymousSpelling`]); the
    /// cell path of a `k::fragment!` in a rule term (the `*_path` role of
    /// its side); and, in a readable clause, the result type its header
    /// denotes beside the subject's ([`ProvenanceRole::RuleResultType`]),
    /// the key term and the value binder of a map read's entry
    /// ([`ProvenanceRole::RuleLeftMapKey`],
    /// [`ProvenanceRole::RuleLeftMapValue`]), and a spliced head result's
    /// sequence and items ([`ProvenanceRole::RuleRightKSequencePayload`],
    /// [`ProvenanceRole::RuleRightKSequenceItem`]).
    pub(crate) fn implicit(&mut self, role: ProvenanceRole) {
        *self.implicit.entry(role).or_default() += 1;
    }

    /// The keys defined so far, fixed ones included, implicit ones aside.
    #[cfg(test)]
    pub(crate) const fn defined(&self) -> &BTreeSet<ProvenanceKey> {
        &self.defined
    }

    /// The defined keys, fixed ones included: the anchors a payload needs
    /// besides those of its implicit nodes, which carry no key to name.
    pub(crate) fn into_defined(self) -> BTreeSet<ProvenanceKey> {
        self.defined
    }

    /// Checks that the payload's keys are exactly `anchors`: every defined
    /// key is anchored, every anchor is defined (an implicit node takes the
    /// next anchor of its role no wire node defines), and every reference
    /// names a defined key.
    pub(crate) fn close<'a>(
        mut self,
        anchors: impl IntoIterator<Item = &'a ProvenanceKey>,
    ) -> Result<(), KeyFailure> {
        let anchors = anchors.into_iter().collect::<BTreeSet<_>>();
        for (role, count) in std::mem::take(&mut self.implicit) {
            let paired = anchors
                .iter()
                .filter(|key| key.role() == role && !self.defined.contains(**key))
                .take(count)
                .map(|key| (*key).clone())
                .collect::<Vec<_>>();
            if paired.len() < count {
                // The key the first node left without an anchor would take.
                let anchored = anchors.iter().filter(|key| key.role() == role).count();
                return Err(KeyFailure::Missing(ProvenanceKey::new(
                    role,
                    u32::try_from(anchored).unwrap_or(u32::MAX),
                )));
            }
            self.defined.extend(paired);
        }
        if let Some(missing) = self.defined.iter().find(|key| !anchors.contains(key)) {
            return Err(KeyFailure::Missing(missing.clone()));
        }
        if let Some(extra) = anchors.iter().find(|key| !self.defined.contains(**key)) {
            return Err(KeyFailure::Extra((*extra).clone()));
        }
        if let Some(dangling) = self
            .referred
            .iter()
            .find(|key| !self.defined.contains(*key))
        {
            return Err(KeyFailure::Missing(dangling.clone()));
        }
        Ok(())
    }
}

/// Checks that a field's key has the field's role.
pub(crate) fn require_role(key: &ProvenanceKey, role: ProvenanceRole) -> Result<(), KeyFailure> {
    if key.role() == role {
        Ok(())
    } else {
        Err(KeyFailure::Role {
            expected: role,
            actual: key.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{KeyFailure, WireKeys};
    use crate::{ProvenanceKey, ProvenanceRole};

    fn key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
        ProvenanceKey::new(role, ordinal)
    }

    #[test]
    fn a_field_takes_only_its_role() {
        let mut keys = WireKeys::default();
        let label = key(ProvenanceRole::RuleLabel, 0);
        assert_eq!(
            keys.define(&label, ProvenanceRole::RulePattern),
            Err(KeyFailure::Role {
                expected: ProvenanceRole::RulePattern,
                actual: label.clone(),
            })
        );
        assert_eq!(
            keys.refer(&label, ProvenanceRole::RulePattern),
            Err(KeyFailure::Role {
                expected: ProvenanceRole::RulePattern,
                actual: label,
            })
        );
    }

    /// Any ordinal of the field's role is the parser's to give.
    #[test]
    fn a_key_of_the_role_is_accepted_at_any_ordinal() {
        let mut keys = WireKeys::default();
        let late = key(ProvenanceRole::RuleLeftPath, 7);
        keys.define(&late, ProvenanceRole::RuleLeftPath).unwrap();
        keys.close([&late]).unwrap();
    }

    #[test]
    fn a_second_definition_is_refused() {
        let mut keys = WireKeys::default();
        let path = key(ProvenanceRole::RuleLeftPath, 0);
        keys.define(&path, ProvenanceRole::RuleLeftPath).unwrap();
        assert_eq!(
            keys.define(&path, ProvenanceRole::RuleLeftPath),
            Err(KeyFailure::Duplicate(path.clone()))
        );
        // A reference may repeat a definition.
        keys.refer(&path, ProvenanceRole::RuleLeftPath).unwrap();
    }

    #[test]
    fn closure_requires_the_anchors_exactly() {
        let declaration = key(ProvenanceRole::RuleDeclaration, 0);
        let pattern = key(ProvenanceRole::RulePattern, 0);
        let result = key(ProvenanceRole::RuleResult, 0);
        let keys = || {
            let mut keys = WireKeys::default();
            keys.fixed(ProvenanceRole::RuleDeclaration).unwrap();
            keys.define(&pattern, ProvenanceRole::RulePattern).unwrap();
            keys
        };
        keys().close([&declaration, &pattern]).unwrap();
        assert_eq!(
            keys().close([&declaration]),
            Err(KeyFailure::Missing(pattern.clone()))
        );
        assert_eq!(
            keys().close([&declaration, &pattern, &result]),
            Err(KeyFailure::Extra(result.clone()))
        );
        let mut dangling = keys();
        dangling.refer(&result, ProvenanceRole::RuleResult).unwrap();
        assert_eq!(
            dangling.close([&declaration, &pattern]),
            Err(KeyFailure::Missing(result))
        );
    }

    #[test]
    fn implicit_nodes_pair_with_the_anchors_left_of_their_role() {
        let parents = [0, 1].map(|ordinal| key(ProvenanceRole::SortParent, ordinal));
        let declaration = key(ProvenanceRole::SortDeclaration, 0);
        let keys = |count| {
            let mut keys = WireKeys::default();
            keys.fixed(ProvenanceRole::SortDeclaration).unwrap();
            for _ in 0..count {
                keys.implicit(ProvenanceRole::SortParent);
            }
            keys
        };
        keys(2)
            .close([&declaration, &parents[0], &parents[1]])
            .unwrap();
        assert_eq!(
            keys(1).close([&declaration, &parents[0], &parents[1]]),
            Err(KeyFailure::Extra(parents[1].clone()))
        );
        assert_eq!(
            keys(3).close([&declaration, &parents[0], &parents[1]]),
            Err(KeyFailure::Missing(key(ProvenanceRole::SortParent, 2)))
        );
        // A node of the role that carries its key is no implicit one's.
        let mut mixed = keys(1);
        mixed
            .define(&parents[0], ProvenanceRole::SortParent)
            .unwrap();
        mixed
            .close([&declaration, &parents[0], &parents[1]])
            .unwrap();
    }
}
