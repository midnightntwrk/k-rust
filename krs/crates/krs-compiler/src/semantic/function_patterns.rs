//! A function application below a pattern's root (`krs::analysis::function-in-pattern`).
//!
//! A pattern matches terms as they are. An application of a function denotes
//! the value evaluation produces, not a term of its own, and every term a
//! rule or an equation is applied to has its functions evaluated: a
//! configuration holds values, and an equation's arguments are values. So a
//! pattern with a function application below its root describes a term that
//! never occurs, and the sentence silently never applies. Whether a head is
//! a function is a fact of the declaration it resolves to
//! ([`ProductionSignature::function`], a builtin operation's
//! [`BuiltinOperation::is_functional`]), so this is decided here, after
//! resolution; the term walker admits the application
//! (`krs_syntax::positions`, `After(FunctionInPattern)`).
//!
//! The application is the meaning, and is admitted, where:
//! - it is the root of an equation's subject: the function the equation
//!   defines;
//! - it stands in a simplification's subject, which rewrites symbolic terms,
//!   whose applications stand unevaluated;
//! - it stands in a claim's subject, a symbolic state whose applications
//!   denote values;
//! - it stands in a collection's key, value or element: a collection is
//!   matched through its entries, so a lookup evaluates the key, and an
//!   entry is compared as the value it denotes.
//!
//! The positions are the sentence's own shape, which each descriptor carries:
//! every term of a subject the walker reads as one slot (a fn rule's or an
//! equation's subject, a computation item, a cell's content) is a root, and
//! its arguments are below it; a collection's entries are the keys and
//! values of a map, the elements of a list cell, the instances of a
//! collection cell, and the operands of the collection's unit, element and
//! concatenation. A `k::rewrite!`'s left side is matched where it stands; its
//! right side is built and is no pattern.

use std::collections::BTreeMap;

use krs_ir::{
    BuiltinOperation, Descriptor, DescriptorApplicationRef, DescriptorApplicationReference,
    DescriptorHeadRuleExtra, DescriptorPayload, DescriptorTerm, ListOperation,
    ProtocolHeadRuleExtra, ProtocolHeadRuleListRest, ProtocolRuleMapBody, ProtocolRuleStateTerm,
    SentenceKind, SetOperation, StableItemId, TermArgumentRef, TermMapOperation,
};

use super::catalog::ProductionSignature;
use super::error::DescriptorLoweringError;
use super::origin::key_range;

/// Refuses the first function application below the root of a pattern of
/// each sentence whose subject every term it applies to matches with its
/// functions evaluated.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::FunctionInPattern`] at the first such
/// application's head.
pub(super) fn check_function_patterns(
    descriptors: &[&Descriptor],
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<(), DescriptorLoweringError> {
    for descriptor in descriptors {
        sentence_patterns(descriptor.payload(), &Patterns { catalog })
            .map_err(|(reference, function)| refusal(descriptor, reference, &function))?;
    }
    Ok(())
}

/// Checks the patterns of a sentence whose subject every term it applies to
/// matches with its functions evaluated.
fn sentence_patterns<'t>(
    payload: &'t DescriptorPayload,
    patterns: &Patterns<'_>,
) -> Result<(), Found<'t>> {
    match payload {
        DescriptorPayload::StructuredRule(rule)
            if matches_evaluated_terms(rule.sentence_kind, false) && !rule.predicate =>
        {
            patterns.root(&rule.subject)?;
            rule.function_context
                .iter()
                .flat_map(|context| &context.cells.cells)
                .try_for_each(|cell| patterns.state(&cell.value))
        }
        DescriptorPayload::HeadRule(rule)
            if matches_evaluated_terms(rule.sentence_kind, rule.claim.is_some()) =>
        {
            rule.head
                .iter()
                .flat_map(|head| &head.items)
                .try_for_each(|item| patterns.root(item))?;
            rule.extras
                .iter()
                .try_for_each(|extra| patterns.extra(extra))
        }
        DescriptorPayload::ConfigurationRule(rule)
            if matches_evaluated_terms(
                rule.sentence_kind.sentence_kind(),
                rule.claim.is_some(),
            ) =>
        {
            rule.subject
                .cells
                .iter()
                .try_for_each(|cell| patterns.state(&cell.value))
        }
        _ => Ok(()),
    }
}

/// The refusal of the application `reference`, which applies `function`.
fn refusal(
    descriptor: &Descriptor,
    reference: &DescriptorApplicationReference,
    function: &str,
) -> DescriptorLoweringError {
    DescriptorLoweringError::FunctionInPattern {
        item: Box::new(descriptor.id().clone()),
        reason: format!(
            "{function}, and it is applied below the root of a pattern; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`"
        ),
        range: key_range(descriptor, &reference.key).map(Box::new),
    }
}

/// Whether a sentence of `kind` matches every term it applies to with the
/// term's functions evaluated: a transition and an equation, but no claim,
/// whose subject is a symbolic state, and no simplification, which rewrites
/// unevaluated applications. An alias, a desugar clause and a context rewrite
/// the program as written, before any evaluation.
const fn matches_evaluated_terms(kind: SentenceKind, claim: bool) -> bool {
    !claim && matches!(kind, SentenceKind::Transition | SentenceKind::Equation)
}

/// The patterns of one sentence.
struct Patterns<'a> {
    catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
}

/// The first function application below a pattern's root, and what it
/// applies.
type Found<'t> = (&'t DescriptorApplicationReference, String);

impl Patterns<'_> {
    /// A term at the root of a pattern slot.
    fn root<'t>(&self, term: &'t DescriptorTerm) -> Result<(), Found<'t>> {
        self.term(term, false)
    }

    /// One state of a cell a pattern names: its term, its computation items,
    /// or its map's base. A map's keys and values and a collection cell's
    /// instances are entries.
    fn state<'t>(&self, state: &'t ProtocolRuleStateTerm<DescriptorTerm>) -> Result<(), Found<'t>> {
        match state {
            ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
                self.root(term)
            }
            ProtocolRuleStateTerm::KSequence(sequence) => sequence
                .items
                .iter()
                .try_for_each(|item| self.root(&item.value)),
            ProtocolRuleStateTerm::Map(map) => match &map.body {
                ProtocolRuleMapBody::Update { base, .. } => self.root(base),
                ProtocolRuleMapBody::Empty { .. } | ProtocolRuleMapBody::Items { .. } => Ok(()),
            },
            ProtocolRuleStateTerm::Present { value } => self.state(value),
            ProtocolRuleStateTerm::Absent | ProtocolRuleStateTerm::Instances(_) => Ok(()),
        }
    }

    /// The matched side of a readable rule's cell: a cell's content, an
    /// optional cell's state, a list cell's rest. A map read's keys, a list
    /// cell's elements, and a map update, which the result writes, hold no
    /// pattern below a root.
    fn extra<'t>(&self, extra: &'t DescriptorHeadRuleExtra) -> Result<(), Found<'t>> {
        match extra {
            ProtocolHeadRuleExtra::RewriteCell { before, .. } => self.root(before),
            ProtocolHeadRuleExtra::RewriteState { before, .. } => self.state(before),
            ProtocolHeadRuleExtra::RewriteList { before, .. } => match &before.rest {
                ProtocolHeadRuleListRest::Term(rest) => self.root(rest),
                ProtocolHeadRuleListRest::Exact | ProtocolHeadRuleListRest::Shared => Ok(()),
            },
            ProtocolHeadRuleExtra::HaveMap { .. } | ProtocolHeadRuleExtra::UpdateMap { .. } => {
                Ok(())
            }
        }
    }

    /// `term`, below the root when `below_root`.
    fn term<'t>(&self, term: &'t DescriptorTerm, below_root: bool) -> Result<(), Found<'t>> {
        match term {
            DescriptorTerm::Application {
                reference,
                arguments,
                ..
            } => {
                match applied_function(&reference.application, self.catalog) {
                    Applied::Collection => return Ok(()),
                    Applied::Function(function) if below_root => {
                        return Err((reference, function));
                    }
                    Applied::Function(_) | Applied::Constructor => {}
                }
                arguments.iter().try_for_each(|argument| {
                    let (TermArgumentRef::Positional { value }
                    | TermArgumentRef::Named { value, .. }) = argument;
                    self.term(value, true)
                })
            }
            // An alias names the term its pattern matches, each alternative
            // is matched where the alternatives stand, and a rewrite's left
            // side is matched where the rewrite stands; its right side is
            // built.
            DescriptorTerm::As { pattern, .. } => self.term(pattern, below_root),
            DescriptorTerm::Or { alternatives, .. } => alternatives
                .iter()
                .try_for_each(|alternative| self.term(alternative, below_root)),
            DescriptorTerm::Rewrite { from, .. } => self.term(from, below_root),
            DescriptorTerm::Cell { fields, .. } => fields
                .iter()
                .try_for_each(|field| self.term(&field.value, true)),
            // The term walker refuses a test, a `let`, a predicate and a
            // claim's values in a pattern; the rest are leaves.
            DescriptorTerm::Variable { .. }
            | DescriptorTerm::Literal { .. }
            | DescriptorTerm::Wildcard { .. }
            | DescriptorTerm::BuiltinToken { .. }
            | DescriptorTerm::Anonymous { .. }
            | DescriptorTerm::OrBool { .. }
            | DescriptorTerm::Lexeme { .. }
            | DescriptorTerm::SortTest { .. }
            | DescriptorTerm::Matches { .. }
            | DescriptorTerm::Let { .. }
            | DescriptorTerm::Closure { .. } => Ok(()),
        }
    }
}

/// What an application head applies.
enum Applied {
    /// A function, described for a diagnostic.
    Function(String),
    /// A constructor, matched as written.
    Constructor,
    /// A collection's unit, element or concatenation, whose operands are its
    /// entries.
    Collection,
}

/// What `application` applies: a declared function, a builtin operation that
/// is a function (an operator denotes one in every domain), or one of a
/// collection's operations other than its unit, element and concatenation,
/// which are its functions (a lookup, a size, an update).
fn applied_function(
    application: &DescriptorApplicationRef,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Applied {
    match application {
        DescriptorApplicationRef::Declared(id) => {
            if catalog.get(id).is_some_and(|signature| signature.function) {
                Applied::Function(format!("`{}` is a function", id.item_name()))
            } else {
                Applied::Constructor
            }
        }
        DescriptorApplicationRef::Builtin(operation) => {
            if operation.is_functional() {
                Applied::Function(format!(
                    "`{}` is a builtin function",
                    builtin_path(*operation)
                ))
            } else {
                Applied::Constructor
            }
        }
        DescriptorApplicationRef::Operator(operator) => Applied::Function(format!(
            "`{}` applies a builtin function",
            operator.symbol()
        )),
        DescriptorApplicationRef::Map(operation) => match operation {
            TermMapOperation::Empty => Applied::Collection,
            other => collection_function(other.facade_marker()),
        },
        DescriptorApplicationRef::List(operation) => match operation {
            ListOperation::Empty | ListOperation::Item | ListOperation::Concat => {
                Applied::Collection
            }
            other => collection_function(other.facade_marker()),
        },
        DescriptorApplicationRef::Set(operation) => match operation {
            SetOperation::Empty | SetOperation::Item | SetOperation::Concat => Applied::Collection,
            other => collection_function(other.facade_marker()),
        },
        DescriptorApplicationRef::ListNotation(_) => Applied::Collection,
        // A predicate is no term; the term walker refuses it in a pattern.
        DescriptorApplicationRef::Ml(_) => Applied::Constructor,
    }
}

fn collection_function(marker: krs_ir::FacadeMarker) -> Applied {
    Applied::Function(format!(
        "`k::builtin::{}::{}` is a builtin function",
        marker.module, marker.name
    ))
}

fn builtin_path(operation: BuiltinOperation) -> String {
    let spec = operation.spec();
    format!("k::builtin::{}::{}", spec.rust_module, spec.rust_name)
}

#[cfg(test)]
mod tests;
