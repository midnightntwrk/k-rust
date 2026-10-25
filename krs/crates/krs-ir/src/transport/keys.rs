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
use std::marker::PhantomData;

use super::grammar::{CellTermField, DescriptorApplicationHeadClass, DescriptorLiteral, Term};
use super::rule::{TermRole, ValidationSide};
use super::validation::{TermValidation, ValidationStage, validate_term};
use crate::{BuiltinSort, ProductionFieldId, ProvenanceKey, ProvenanceRole, SortTestKind};

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
    /// A field that names one particular node held another key.
    Mismatched {
        /// The key of the node the field names.
        expected: ProvenanceKey,
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
        self.anchored(&anchors)?;
        if let Some(extra) = anchors.iter().find(|key| !self.defined.contains(**key)) {
            return Err(KeyFailure::Extra((*extra).clone()));
        }
        Ok(())
    }

    /// Checks the part of closure that holds on a payload that keeps only
    /// some of its nodes: every defined key is one of `anchors`, and every
    /// reference names a defined key. Anchors no node consumes and the nodes
    /// that carry no key are not checked.
    pub(crate) fn close_within<'a>(
        self,
        anchors: impl IntoIterator<Item = &'a ProvenanceKey>,
    ) -> Result<(), KeyFailure> {
        self.anchored(&anchors.into_iter().collect())
    }

    /// Checks that every defined key is anchored and every reference names
    /// a defined key.
    fn anchored(&self, anchors: &BTreeSet<&ProvenanceKey>) -> Result<(), KeyFailure> {
        if let Some(missing) = self.defined.iter().find(|key| !anchors.contains(key)) {
            return Err(KeyFailure::Missing(missing.clone()));
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

/// A term node the key walk refuses, which each stage reports as its own
/// term reason.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TermRefusal {
    /// A wildcard outside a subject and a pattern, where no wildcard role
    /// exists.
    Wildcard,
    /// A builtin token that is no literal of its sort, which has no role.
    BuiltinToken,
    /// `name @ pattern` outside a left-hand side or a `k::matches!` pattern.
    PatternAs,
    /// `A | B` outside a left-hand side or a `k::matches!` pattern.
    PatternOr,
    /// `k::matches!` in a pattern.
    Matches,
    /// A `let` block in a pattern.
    Let,
    /// An `ml::exists` closure in a pattern.
    Closure,
    /// A record update whose base is not a variable outside a pattern.
    RecordUpdateBase,
}

/// How a rule term's nodes carry their keys, and what the walk checks of
/// them besides their roles.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TermKeying {
    /// A structured rule's or a constant's term: each path and each head is
    /// keyed, and the walk refuses a node its side does not admit (for a
    /// constant's value, no other check does).
    Grammar,
    /// A readable clause's term: each path and each head is keyed; where a
    /// node stands is the collector's and the compiler's to check.
    Readable,
    /// A readable term that repeats nodes another wire term carries, the
    /// bracket alternative's: it refers to their keys.
    ReadableClone,
    /// A cell value of a `cells!` pattern: a path there names its head's
    /// node and carries its key, and a fragment keys no cell path; where a
    /// node stands is its validator's to check.
    CellValue,
}

/// Collects the keys of a rule term's nodes on `side`, each checked for the
/// role its node has there: the one role table of structured rules,
/// constants and readable clauses.
pub(super) fn collect_term_keys<S, E>(
    term: &Term<S>,
    side: ValidationSide,
    keying: TermKeying,
    keys: &mut WireKeys,
) -> Result<(), E>
where
    S: ValidationStage,
    E: From<KeyFailure> + From<TermRefusal>,
{
    validate_term(
        term,
        &mut TermKeys {
            keys,
            side,
            keying,
            in_matches_pattern: false,
            in_let_pattern: false,
            error: PhantomData,
        },
    )
}

/// The term walk of [`collect_term_keys`].
struct TermKeys<'a, E> {
    keys: &'a mut WireKeys,
    side: ValidationSide,
    keying: TermKeying,
    in_matches_pattern: bool,
    in_let_pattern: bool,
    error: PhantomData<fn() -> E>,
}

impl<E: From<KeyFailure> + From<TermRefusal>> TermKeys<'_, E> {
    /// Records the key of a node of `role`: a clone refers to it.
    fn node(&mut self, key: &ProvenanceKey, role: ProvenanceRole) -> Result<(), E> {
        if self.keying == TermKeying::ReadableClone {
            self.keys.refer(key, role)?;
        } else {
            self.keys.define(key, role)?;
        }
        Ok(())
    }

    /// Records the path of a variable or an application whose head is keyed
    /// `head`: a node of its own, except in a cell value, where it names the
    /// head's node.
    fn path(&mut self, path: &ProvenanceKey, head: &ProvenanceKey) -> Result<(), E> {
        if self.keying != TermKeying::CellValue {
            return self.node(path, TermRole::Path.on_side(self.side));
        }
        if path == head {
            Ok(())
        } else {
            Err(KeyFailure::Mismatched {
                expected: head.clone(),
                actual: path.clone(),
            }
            .into())
        }
    }

    /// Refuses a node that stands where its side does not admit it, where
    /// the walk checks that.
    fn place(&self, misplaced: bool, refusal: TermRefusal) -> Result<(), E> {
        if misplaced && self.keying == TermKeying::Grammar {
            Err(refusal.into())
        } else {
            Ok(())
        }
    }

    /// Whether the walk stands in a left-hand side or a pattern, where an
    /// expression node is refused.
    fn in_pattern(&self) -> bool {
        matches!(self.side, ValidationSide::Left) || self.in_matches_pattern || self.in_let_pattern
    }
}

impl<S, E> TermValidation<S> for TermKeys<'_, E>
where
    S: ValidationStage,
    E: From<KeyFailure> + From<TermRefusal>,
{
    type Error = E;

    fn variable(
        &mut self,
        key: &ProvenanceKey,
        path_key: &ProvenanceKey,
        _: &str,
    ) -> Result<(), E> {
        self.path(path_key, key)?;
        self.node(key, TermRole::Reference.on_side(self.side))
    }

    fn application(
        &mut self,
        head_class: DescriptorApplicationHeadClass,
        reference: &S::Application,
        path_key: &ProvenanceKey,
        _: &crate::Arguments<S>,
    ) -> Result<(), E> {
        self.path(path_key, S::application_key(reference))?;
        let role = match head_class {
            DescriptorApplicationHeadClass::Applied => TermRole::ApplicationHead,
            DescriptorApplicationHeadClass::BareReference => TermRole::Reference,
        };
        self.node(S::application_key(reference), role.on_side(self.side))
    }

    fn literal(&mut self, key: &ProvenanceKey, _: &DescriptorLiteral) -> Result<(), E> {
        self.node(key, TermRole::Literal.on_side(self.side))
    }

    fn wildcard(&mut self, key: &ProvenanceKey) -> Result<(), E> {
        let role = if self.in_let_pattern {
            ProvenanceRole::LetWildcard
        } else if self.in_matches_pattern {
            ProvenanceRole::MatchesWildcard
        } else {
            match self.side {
                ValidationSide::Left => ProvenanceRole::RuleLeftWildcard,
                ValidationSide::Right => ProvenanceRole::RuleRightWildcard,
                ValidationSide::Requires
                | ValidationSide::Ensures
                | ValidationSide::RuleEnsures => return Err(TermRefusal::Wildcard.into()),
            }
        };
        self.node(key, role)
    }

    fn builtin_token(
        &mut self,
        key: &ProvenanceKey,
        sort: BuiltinSort,
        value: &str,
    ) -> Result<(), E> {
        let role = super::validation::builtin_token_literal_role(sort, value)
            .ok_or(TermRefusal::BuiltinToken)?;
        self.node(key, role)
    }

    fn anonymous(
        &mut self,
        key: &ProvenanceKey,
        sort: &S::Sort,
        spelling_key: &ProvenanceKey,
        _: &str,
    ) -> Result<(), E> {
        self.node(key, ProvenanceRole::ClaimAnonymous)?;
        self.node(S::sort_key(sort), ProvenanceRole::ClaimAnonymousSort)?;
        self.node(spelling_key, ProvenanceRole::ClaimAnonymousSpelling)
    }

    fn or_bool(&mut self, key: &ProvenanceKey, _: &crate::AtLeastTwo<Term<S>>) -> Result<(), E> {
        self.node(key, ProvenanceRole::ClaimOrBool)
    }

    fn lexeme(&mut self, key: &ProvenanceKey, sort: &S::Sort, _: &str) -> Result<(), E> {
        self.node(S::sort_key(sort), ProvenanceRole::LexemeSort)?;
        self.node(key, ProvenanceRole::LexemeText)
    }

    fn cell(
        &mut self,
        key: &ProvenanceKey,
        path_key: &ProvenanceKey,
        _: &S::Nominal,
        _: &[CellTermField<S>],
        _: bool,
    ) -> Result<(), E> {
        // The fragment's path is its declaration's, keyed as an
        // application's.
        self.path(path_key, key)?;
        self.node(key, TermRole::ApplicationHead.on_side(self.side))
    }

    fn sort_test(&mut self, key: &ProvenanceKey, _: SortTestKind, sort: &S::Sort) -> Result<(), E> {
        self.node(S::sort_key(sort), ProvenanceRole::SortTestSort)?;
        self.node(key, ProvenanceRole::SortTest)
    }

    fn application_instance(&mut self, sort: &S::Sort) -> Result<(), E> {
        self.node(S::sort_key(sort), ProvenanceRole::ApplicationInstance)
    }

    fn pattern_as(
        &mut self,
        key: &ProvenanceKey,
        binding_key: &ProvenanceKey,
        _: &str,
    ) -> Result<(), E> {
        self.place(
            self.in_let_pattern
                || (!matches!(self.side, ValidationSide::Left) && !self.in_matches_pattern),
            TermRefusal::PatternAs,
        )?;
        self.node(key, ProvenanceRole::PatternAs)?;
        self.node(binding_key, ProvenanceRole::PatternAsBinding)
    }

    fn pattern_or(&mut self, key: &ProvenanceKey) -> Result<(), E> {
        self.place(
            self.in_let_pattern
                || (!matches!(self.side, ValidationSide::Left) && !self.in_matches_pattern),
            TermRefusal::PatternOr,
        )?;
        self.node(key, ProvenanceRole::PatternOr)
    }

    fn matches(&mut self, key: &ProvenanceKey) -> Result<(), E> {
        self.place(self.in_pattern(), TermRefusal::Matches)?;
        self.node(key, ProvenanceRole::Matches)
    }

    fn matches_pattern(&mut self, inside: bool) {
        self.in_matches_pattern = inside;
    }

    fn let_binding(&mut self, key: &ProvenanceKey, sort: Option<&S::Sort>) -> Result<(), E> {
        self.place(self.in_pattern(), TermRefusal::Let)?;
        if let Some(sort) = sort {
            self.node(S::sort_key(sort), ProvenanceRole::LetSort)?;
        }
        self.node(key, ProvenanceRole::Let)
    }

    fn let_pattern(&mut self, inside: bool) {
        self.in_let_pattern = inside;
    }

    fn closure(
        &mut self,
        key: &ProvenanceKey,
        binder_key: &ProvenanceKey,
        sort: &S::Sort,
    ) -> Result<(), E> {
        self.place(self.in_pattern(), TermRefusal::Closure)?;
        self.node(key, ProvenanceRole::MlConnective)?;
        self.node(binder_key, ProvenanceRole::MlBinder)?;
        self.node(S::sort_key(sort), ProvenanceRole::MlBinderSort)
    }

    fn let_body(&mut self, _: Option<&BTreeSet<String>>) {}

    fn rewrite(
        &mut self,
        key: &ProvenanceKey,
        from_key: &ProvenanceKey,
        to_key: &ProvenanceKey,
        _: bool,
    ) -> Result<(), E> {
        self.node(key, ProvenanceRole::RuleLocalRewrite)?;
        self.node(from_key, ProvenanceRole::RuleLocalRewriteFrom)?;
        self.node(to_key, ProvenanceRole::RuleLocalRewriteTo)
    }

    fn rewrite_right(&mut self, _: bool) {}

    fn argument(
        &mut self,
        argument: crate::TermArgumentRef<'_, S>,
        _: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), E> {
        if let crate::TermArgumentRef::Named { key, .. } = argument {
            self.node(key, TermRole::RecordFieldName.on_side(self.side))?;
        }
        Ok(())
    }

    fn cell_field(
        &mut self,
        field: &CellTermField<S>,
        _: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), E> {
        self.node(&field.key, TermRole::RecordFieldName.on_side(self.side))
    }

    fn record_update(&mut self, base: &Term<S>) -> Result<(), E> {
        self.place(
            !matches!(base, Term::Variable { .. })
                || (matches!(self.side, ValidationSide::Left) && !self.in_matches_pattern),
            TermRefusal::RecordUpdateBase,
        )?;
        validate_term(base, self)
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
