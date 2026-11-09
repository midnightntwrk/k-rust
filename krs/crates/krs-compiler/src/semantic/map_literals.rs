//! The reading of a map literal without a rest, `map![k1 -> v1, .., kn -> vn]`, in a pattern.
//!
//! A pattern reads `map![k -> v, rest @ ..]` by its entries: the map holds an entry at each key,
//! the keys pairwise different, and the rest is the map without them
//! ([`DescriptorTerm::MapEntries`]). With no rest the entries are the whole map, so the literal
//! matches exactly the map of those entries. That is its meaning where a pattern matches a
//! value: a subject of a sentence whose pattern meets evaluated terms (a transition, an equation,
//! a context), outside a key, and a `let` or `k::matches!` pattern, which matches a value a rule
//! computed. There a built map, the updates `map::update(..)` a term's literal denotes, is a
//! function's application, which never matches an evaluated map.
//!
//! Everywhere else in a pattern the literal is the map it builds, as in a term:
//! - in a key, a set's element or a looked-up instance's cell, which the pattern computes and
//!   looks the collection up by, as a key's other constructs that compute are;
//! - in the subject of a sentence whose pattern meets unevaluated terms: a simplification's, which
//!   rewrites an application as written, a claim's, a symbolic state whose applications denote
//!   their values, and a static clause's, matched against a program as written, whose maps are
//!   written with their updates;
//! - as a sentence's whole subject, which is the function an equation defines, the term a rule
//!   rewrites or the production a context heats, read as its root is.
//!
//! This pass writes each such literal as the updates it denotes, the descriptor term every later
//! reading has always seen for it, so a map literal means there what it meant before map
//! patterns: `map::update(..map::update(map::empty(), k1, v1).., kn, vn)`. The updates' heads are
//! nodes the descriptor lacks, keyed afresh at the literal's own origin. A map pattern with a
//! rest is a pattern's construct wherever it stands, and is left to the readings that judge it.

use std::borrow::Cow;

use krs_ir::{
    CellCollectionType, Descriptor, DescriptorApplicationHeadClass, DescriptorApplicationRef,
    DescriptorApplicationReference, DescriptorCellIdentity, DescriptorIndex, DescriptorNodeOrigin,
    DescriptorPayload, DescriptorTerm, ProtocolHeadRuleExtra, ProtocolHeadRuleListRest,
    ProtocolRuleCells, ProtocolRuleMapBody, ProtocolRuleStateTerm, ProvenanceKey, ProvenanceRole,
    SetOperation, TermMapOperation,
};

use super::error::DescriptorLoweringError;

/// `descriptors`, each map literal without a rest that a pattern holds as the map it builds
/// written as the updates it denotes.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::UnsupportedShape`] when a fresh key collides.
pub(super) fn read_map_literals(
    descriptors: Vec<Cow<'_, Descriptor>>,
) -> Result<Vec<Cow<'_, Descriptor>>, DescriptorLoweringError> {
    let read = {
        let declarations = DescriptorIndex::from_descriptors(descriptors.iter().map(AsRef::as_ref));
        descriptors
            .iter()
            .map(|descriptor| {
                if !holds_map_pattern(descriptor.payload()) {
                    return Ok(None);
                }
                let mut payload = descriptor.payload().clone();
                let mut keys = FreshKeys::new(descriptor, &declarations);
                read_payload(&mut payload, &mut keys);
                if keys.origins.is_empty() {
                    return Ok(None);
                }
                descriptor
                    .with_generated_nodes(payload, keys.origins)
                    .map(Some)
                    .map_err(|error| {
                        DescriptorLoweringError::unsupported_shape("map literal", error.to_string())
                    })
            })
            .collect::<Result<Vec<_>, _>>()?
    };
    Ok(descriptors
        .into_iter()
        .zip(read)
        .map(|(descriptor, read)| read.map_or(descriptor, Cow::Owned))
        .collect())
}

/// Whether the payload's subject may hold a map literal this pass rewrites.
fn holds_map_pattern(payload: &DescriptorPayload) -> bool {
    matches!(
        payload,
        DescriptorPayload::StructuredRule(_)
            | DescriptorPayload::ConfigurationRule(_)
            | DescriptorPayload::HeadRule(_)
            | DescriptorPayload::ContextAlias(_)
    )
}

/// The subject of `payload`, each literal read where it stands: built everywhere in a sentence
/// whose pattern meets unevaluated terms, else only in a key.
fn read_payload(payload: &mut DescriptorPayload, keys: &mut FreshKeys<'_>) {
    let built = !super::function_patterns::matches_evaluated_sentence(payload);
    match payload {
        DescriptorPayload::StructuredRule(rule) => {
            read_root(&mut rule.subject, built, keys);
            if let Some(context) = &mut rule.function_context {
                read_cells(&mut context.cells, built, keys);
            }
        }
        DescriptorPayload::ConfigurationRule(rule) => read_cells(&mut rule.subject, built, keys),
        DescriptorPayload::ContextAlias(alias) => read_cells(&mut alias.pattern, built, keys),
        DescriptorPayload::HeadRule(rule) => {
            for item in rule.head.iter_mut().flat_map(|head| &mut head.items) {
                read_term(item, built, keys);
            }
            for extra in &mut rule.extras {
                match extra {
                    ProtocolHeadRuleExtra::HaveMap { entries, .. } => {
                        for entry in entries {
                            read_term(&mut entry.key, true, keys);
                        }
                    }
                    ProtocolHeadRuleExtra::RewriteCell { before, .. } => {
                        read_term(before, built, keys);
                    }
                    ProtocolHeadRuleExtra::RewriteState { cell, before, .. } => {
                        read_state(Some(&cell.cell), before, built, keys);
                    }
                    ProtocolHeadRuleExtra::RewriteList { before, .. } => {
                        for term in before.items.iter_mut().chain(&mut before.back) {
                            read_term(term, built, keys);
                        }
                        if let ProtocolHeadRuleListRest::Term(rest) = &mut before.rest {
                            read_term(rest, built, keys);
                        }
                    }
                    ProtocolHeadRuleExtra::UpdateMap { .. } => {}
                }
            }
        }
        _ => {}
    }
}

/// A sentence's whole subject: the function an equation defines, the term a rule rewrites or a
/// context heats, never a map's entries. A literal without a rest there is the map it builds,
/// which the subject root's own readings judge, as before map patterns; so is each alternative
/// of a root `|`.
fn read_root(subject: &mut DescriptorTerm, built: bool, keys: &mut FreshKeys<'_>) {
    match subject {
        DescriptorTerm::MapEntries { rest: None, .. } => read_term(subject, true, keys),
        DescriptorTerm::Or { alternatives, .. } => {
            for alternative in alternatives.iter_mut() {
                read_root(alternative, built, keys);
            }
        }
        _ => read_term(subject, built, keys),
    }
}

fn read_cells(
    cells: &mut ProtocolRuleCells<krs_ir::DescriptorCellReference, DescriptorTerm>,
    built: bool,
    keys: &mut FreshKeys<'_>,
) {
    for cell in &mut cells.cells {
        read_state(Some(&cell.field.cell), &mut cell.value, built, keys);
    }
}

/// The state of the cell `cell` names, when it names one: its map's keys are looked up, and
/// built, and so is a Set collection's instance, which the collection is looked up by.
///
/// The cell is read only to tell a Set collection's instances. An instance's or a group
/// record's child names no cell here: such a child is a term, a map, a computation or a
/// presence, never a list of instances (the syntax reads no other), so a collection nested in
/// an instance or a group is reached only as a cell a sentence names itself, a rule for the
/// instance's own group among them, whose identity [`read_cells`] passes.
fn read_state(
    cell: Option<&DescriptorCellIdentity>,
    state: &mut ProtocolRuleStateTerm<DescriptorTerm>,
    built: bool,
    keys: &mut FreshKeys<'_>,
) {
    match state {
        ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
            read_term(term, built, keys);
        }
        ProtocolRuleStateTerm::KSequence(sequence) => {
            for item in &mut sequence.items {
                read_term(&mut item.value, built, keys);
            }
        }
        ProtocolRuleStateTerm::Map(map) => match &mut map.body {
            ProtocolRuleMapBody::Items { items, .. } => {
                for item in items {
                    read_term(&mut item.key, true, keys);
                    read_term(&mut item.value, built, keys);
                }
            }
            ProtocolRuleMapBody::Update {
                base, key, value, ..
            } => {
                for term in [base, key, value] {
                    read_term(term, true, keys);
                }
            }
            ProtocolRuleMapBody::Empty { .. } => {}
        },
        ProtocolRuleStateTerm::Present { value } => read_state(cell, value, built, keys),
        ProtocolRuleStateTerm::Record(record) => {
            for field in &mut record.fields {
                read_state(None, &mut field.value, built, keys);
            }
        }
        ProtocolRuleStateTerm::Instances(instances) => {
            let looked_up = cell.is_some_and(|cell| {
                super::function_patterns::collection_type(keys.declarations, cell)
                    == Some(CellCollectionType::Set)
            });
            for instance in instances.front.iter_mut().chain(&mut instances.back) {
                for field in &mut instance.fields {
                    read_state(None, &mut field.value, built || looked_up, keys);
                }
            }
        }
        ProtocolRuleStateTerm::Absent => {}
    }
}

/// `term`, where a map literal without a rest is the map it builds when `built`.
fn read_term(term: &mut DescriptorTerm, built: bool, keys: &mut FreshKeys<'_>) {
    match term {
        DescriptorTerm::MapEntries {
            key, entries, rest, ..
        } => {
            if rest.is_none() && built {
                let key = key.clone();
                let entries = std::mem::take(entries);
                *term = keys.updates(&key, entries);
                // The updates' operands are built, as a function's arguments are.
                read_children(term, true, keys);
                return;
            }
            for entry in entries {
                // A key is what the map is looked up by.
                read_term(&mut entry.key, true, keys);
                read_term(&mut entry.value, built, keys);
            }
        }
        // A set's element is what the set is looked up by.
        DescriptorTerm::Application { reference, .. }
            if reference.application == DescriptorApplicationRef::Set(SetOperation::Item) =>
        {
            read_children(term, true, keys);
        }
        // A local pattern matches a value a rule computed.
        DescriptorTerm::Let {
            pattern,
            value,
            body,
            ..
        } => {
            read_term(pattern, false, keys);
            read_term(value, built, keys);
            read_term(body, built, keys);
        }
        DescriptorTerm::Matches {
            subject, pattern, ..
        } => {
            read_term(subject, built, keys);
            read_term(pattern, false, keys);
        }
        _ => read_children(term, built, keys),
    }
}

fn read_children(term: &mut DescriptorTerm, built: bool, keys: &mut FreshKeys<'_>) {
    match term {
        DescriptorTerm::Application {
            arguments, update, ..
        } => {
            match arguments {
                krs_ir::Arguments::Positional(values) => {
                    for value in values {
                        read_term(value, built, keys);
                    }
                }
                krs_ir::Arguments::Named(values) => {
                    let named = values
                        .iter()
                        .map(|argument| {
                            let mut value = argument.value.clone();
                            read_term(&mut value, built, keys);
                            krs_ir::NamedTermArgument {
                                key: argument.key.clone(),
                                field: argument.field.clone(),
                                value,
                            }
                        })
                        .collect::<Vec<_>>();
                    *arguments = krs_ir::Arguments::named(named);
                }
            }
            if let Some(update) = update {
                read_term(update, built, keys);
            }
        }
        DescriptorTerm::Cell { fields, update, .. } => {
            for field in fields {
                read_term(&mut field.value, built, keys);
            }
            if let Some(update) = update {
                read_term(update, built, keys);
            }
        }
        DescriptorTerm::OrBool { arguments, .. } => {
            for argument in arguments.iter_mut() {
                read_term(argument, built, keys);
            }
        }
        DescriptorTerm::Or { alternatives, .. } => {
            for alternative in alternatives.iter_mut() {
                read_term(alternative, built, keys);
            }
        }
        DescriptorTerm::MapEntries { entries, rest, .. } => {
            for entry in entries {
                read_term(&mut entry.key, true, keys);
                read_term(&mut entry.value, built, keys);
            }
            if let Some(rest) = rest {
                read_term(rest, built, keys);
            }
        }
        DescriptorTerm::SortTest { operand, .. } => read_term(operand, built, keys),
        DescriptorTerm::As { pattern, .. } => read_term(pattern, built, keys),
        DescriptorTerm::Rewrite { from, .. } => read_term(from, built, keys),
        DescriptorTerm::Matches { .. } | DescriptorTerm::Let { .. } => read_term(term, built, keys),
        DescriptorTerm::Closure { body, .. } => read_term(body, built, keys),
        DescriptorTerm::Variable { .. }
        | DescriptorTerm::Literal { .. }
        | DescriptorTerm::Wildcard { .. }
        | DescriptorTerm::KeptRest { .. }
        | DescriptorTerm::BuiltinToken { .. }
        | DescriptorTerm::Anonymous { .. }
        | DescriptorTerm::Lexeme { .. } => {}
    }
}

/// Fresh keys for the nodes the pass writes, each located where its literal is.
struct FreshKeys<'a> {
    descriptor: &'a Descriptor,
    /// The cells' declarations, which tell a Set collection.
    declarations: &'a DescriptorIndex<'a>,
    next: Option<u32>,
    origins: Vec<DescriptorNodeOrigin>,
}

impl<'a> FreshKeys<'a> {
    const ROLE: ProvenanceRole = ProvenanceRole::RuleLeftApplicationHead;

    const fn new(descriptor: &'a Descriptor, declarations: &'a DescriptorIndex<'a>) -> Self {
        Self {
            descriptor,
            declarations,
            next: None,
            origins: Vec::new(),
        }
    }

    /// A fresh application head key at the origin of `at`, past every key of its role the
    /// descriptor holds.
    fn key(&mut self, at: &ProvenanceKey) -> ProvenanceKey {
        let provenance = self.descriptor.provenance();
        let next = self.next.get_or_insert_with(|| {
            provenance
                .origins()
                .iter()
                .filter(|node| node.key.role() == Self::ROLE)
                .map(|node| node.key.ordinal() + 1)
                .max()
                .unwrap_or(0)
        });
        let fresh = ProvenanceKey::new(Self::ROLE, *next);
        *next += 1;
        if let Some(origin) = provenance.origin_for(at) {
            self.origins
                .push(DescriptorNodeOrigin::new(fresh.clone(), origin.clone()));
        }
        fresh
    }

    /// `map::update(..map::update(map::empty(), k1, v1).., kn, vn)`, the updates a literal of
    /// `entries` at `at` denotes: each entry written over the map before it.
    fn updates(
        &mut self,
        at: &ProvenanceKey,
        entries: Vec<krs_ir::DescriptorMapTermEntry>,
    ) -> DescriptorTerm {
        let empty = self.application(at, TermMapOperation::Empty, Vec::new());
        entries.into_iter().fold(empty, |map, entry| {
            self.application(
                at,
                TermMapOperation::Update,
                vec![map, *entry.key, *entry.value],
            )
        })
    }

    fn application(
        &mut self,
        at: &ProvenanceKey,
        operation: TermMapOperation,
        arguments: Vec<DescriptorTerm>,
    ) -> DescriptorTerm {
        let key = self.key(at);
        DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: key.clone(),
                application: DescriptorApplicationRef::Map(operation),
            },
            path_key: key,
            arguments: krs_ir::Arguments::Positional(arguments.into_iter().map(Box::new).collect()),
            instance: Vec::new(),
            update: None,
            open: false,
        }
    }
}
