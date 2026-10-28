//! A name a map key reads below a function application, which the pattern
//! binds nowhere else (`krs::expand::unbound-name`).
//!
//! A map pattern's key is evaluated: the rule looks its entry up by the
//! key's value. A name in the key binds where the key is matched as it
//! stands (`env: { k -> v, .. }`, `{ Pair(a, b) -> v, .. }`), but below a
//! function application the key computes a value from the name, which some
//! other part of the pattern must give it: `{ int::add(x, 1) -> v, .. }`
//! reads `x`. With `x` bound nowhere else the lookup reads a value nothing
//! gave, so the name is unbound, as a name only a result reads is.
//!
//! Whether an application in a key is a function's is a fact of the
//! declaration its head resolves to, so this is decided here, after
//! resolution: the front binds every name of a key, since it cannot tell
//! `Size(n)` the function from `Pair(n)` the constructor.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    Descriptor, DescriptorHeadRuleExtra, DescriptorPayload, DescriptorTerm, ProtocolHeadRuleExtra,
    ProtocolHeadRuleListRest, ProtocolRuleCells, ProtocolRuleFrame, ProtocolRuleMapBody,
    ProtocolRuleStateTerm, ProvenanceKey, StableItemId, TermArgumentRef,
};

use super::{
    Applied, DescriptorLoweringError, ProductionSignature, applied_function, key_range,
    matches_evaluated_sentence,
};

/// Refuses the first name that a map key of the descriptor's pattern reads
/// below a function application, and that the pattern binds nowhere else.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::UnboundKeyName`] at the name.
pub(super) fn check(
    descriptor: &Descriptor,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<(), DescriptorLoweringError> {
    let payload = descriptor.payload();
    if !matches_evaluated_sentence(payload) {
        return Ok(());
    }
    let mut names = Names {
        catalog,
        bound: BTreeSet::new(),
        read: Vec::new(),
    };
    names.sentence(payload);
    let Some(read) = names
        .read
        .iter()
        .find(|read| !names.bound.contains(read.name))
    else {
        return Ok(());
    };
    Err(DescriptorLoweringError::UnboundKeyName {
        item: Box::new(descriptor.id().clone()),
        reason: format!(
            "`{name}` is not bound in this sentence: it stands only below {function} in a map key, and a key is evaluated to look its entry up, so the key reads `{name}` and binds nothing; bind `{name}` elsewhere in the pattern",
            name = read.name,
            function = read.function,
        ),
        range: key_range(descriptor, read.key).map(Box::new),
    })
}

/// The names of one sentence's pattern.
struct Names<'a, 't> {
    catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    /// The names the pattern binds.
    bound: BTreeSet<&'t str>,
    /// The names a key reads below a function application, in pattern order.
    read: Vec<Read<'t>>,
}

/// A name a key reads below a function application.
struct Read<'t> {
    name: &'t str,
    key: &'t ProvenanceKey,
    /// The innermost function application above the name, described.
    function: String,
}

/// Where in a key a term stands.
#[derive(Clone, Copy)]
enum InKey {
    /// Outside every map key.
    No,
    /// In a key, matched as it stands.
    Matched,
    /// In a key, below a function application.
    Read,
}

impl<'t> Names<'_, 't> {
    fn sentence(&mut self, payload: &'t DescriptorPayload) {
        match payload {
            DescriptorPayload::StructuredRule(rule) => {
                self.term(&rule.subject, InKey::No, None);
                if let Some(context) = &rule.function_context {
                    self.cells(&context.cells);
                }
            }
            DescriptorPayload::HeadRule(rule) => {
                for item in rule.head.iter().flat_map(|head| &head.items) {
                    self.term(item, InKey::No, None);
                }
                for extra in &rule.extras {
                    self.extra(extra);
                }
            }
            DescriptorPayload::ConfigurationRule(rule) => self.cells(&rule.subject),
            _ => {}
        }
    }

    fn cells<I>(&mut self, cells: &'t ProtocolRuleCells<I, DescriptorTerm>) {
        for cell in &cells.cells {
            self.state(&cell.value);
        }
        self.frame(&cells.remainder);
    }

    fn frame(&mut self, frame: &'t ProtocolRuleFrame) {
        if let ProtocolRuleFrame::Bind { binding, .. } = frame {
            self.bound.insert(binding);
        }
    }

    fn state(&mut self, state: &'t ProtocolRuleStateTerm<DescriptorTerm>) {
        match state {
            ProtocolRuleStateTerm::Map(map) => match &map.body {
                ProtocolRuleMapBody::Items { items, remainder } => {
                    for item in items {
                        self.term(&item.key, InKey::Matched, None);
                        self.term(&item.value, InKey::No, None);
                    }
                    self.frame(remainder);
                }
                ProtocolRuleMapBody::Update { base, .. } => self.term(base, InKey::No, None),
                ProtocolRuleMapBody::Empty { .. } => {}
            },
            ProtocolRuleStateTerm::Present { value } => self.state(value),
            ProtocolRuleStateTerm::KSequence(sequence) => {
                for item in &sequence.items {
                    self.term(&item.value, InKey::No, None);
                }
                self.frame(&sequence.tail);
            }
            ProtocolRuleStateTerm::Instances(instances) => {
                for term in state.terms() {
                    self.term(term, InKey::No, None);
                }
                self.frame(&instances.rest);
            }
            ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
                self.term(term, InKey::No, None);
            }
            ProtocolRuleStateTerm::Absent => {}
        }
    }

    /// The matched side of a readable rule's cell; a map update is what the
    /// result writes, and its base binding names the whole map.
    fn extra(&mut self, extra: &'t DescriptorHeadRuleExtra) {
        match extra {
            ProtocolHeadRuleExtra::HaveMap { entries, .. } => {
                for entry in entries {
                    self.term(&entry.key, InKey::Matched, None);
                    self.bound.insert(&entry.value_binding);
                }
            }
            ProtocolHeadRuleExtra::UpdateMap { base_binding, .. } => {
                self.bound.insert(base_binding);
            }
            ProtocolHeadRuleExtra::RewriteCell { before, .. } => {
                self.term(before, InKey::No, None);
            }
            ProtocolHeadRuleExtra::RewriteState { before, .. } => self.state(before),
            ProtocolHeadRuleExtra::RewriteList { before, .. } => {
                for term in &before.items {
                    self.term(term, InKey::No, None);
                }
                if let ProtocolHeadRuleListRest::Term(rest) = &before.rest {
                    self.term(rest, InKey::No, None);
                }
                for term in &before.back {
                    self.term(term, InKey::No, None);
                }
            }
        }
    }

    /// A name at `key`: bound, unless a key reads it below `function`.
    fn name(
        &mut self,
        name: &'t str,
        key: &'t ProvenanceKey,
        in_key: InKey,
        function: Option<&str>,
    ) {
        match (in_key, function) {
            (InKey::Read, Some(function)) => self.read.push(Read {
                name,
                key,
                function: function.to_owned(),
            }),
            _ => {
                self.bound.insert(name);
            }
        }
    }

    /// `term`, `in_key`, below the innermost function application
    /// `function` when a key reads it.
    fn term(&mut self, term: &'t DescriptorTerm, in_key: InKey, function: Option<&str>) {
        match term {
            DescriptorTerm::Variable { key, name, .. } => self.name(name, key, in_key, function),
            DescriptorTerm::As {
                binding_key,
                name,
                pattern,
                ..
            } => {
                self.name(name, binding_key, in_key, function);
                self.term(pattern, in_key, function);
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                ..
            } => {
                let applied = applied_function(&reference.application, self.catalog);
                let (in_key, function) = match (&applied, in_key) {
                    (Applied::Function(applied), InKey::Matched | InKey::Read) => {
                        (InKey::Read, Some(applied.as_str()))
                    }
                    _ => (in_key, function),
                };
                for argument in arguments {
                    let (TermArgumentRef::Positional { value }
                    | TermArgumentRef::Named { value, .. }) = argument;
                    self.term(value, in_key, function);
                }
            }
            DescriptorTerm::Or { alternatives, .. } => {
                for alternative in alternatives {
                    self.term(alternative, in_key, function);
                }
            }
            DescriptorTerm::Rewrite { from, .. } => self.term(from, in_key, function),
            DescriptorTerm::Cell { fields, .. } => {
                for field in fields {
                    self.term(&field.value, in_key, function);
                }
            }
            DescriptorTerm::Literal { .. }
            | DescriptorTerm::Wildcard { .. }
            | DescriptorTerm::BuiltinToken { .. }
            | DescriptorTerm::Anonymous { .. }
            | DescriptorTerm::OrBool { .. }
            | DescriptorTerm::Lexeme { .. }
            | DescriptorTerm::SortTest { .. }
            | DescriptorTerm::Matches { .. }
            | DescriptorTerm::Let { .. }
            | DescriptorTerm::Closure { .. } => {}
        }
    }
}
