//! A function application where a pattern matches a term
//! (`krs::analysis::function-in-pattern`).
//!
//! A pattern matches terms as they are. An application of a function denotes
//! the value evaluation produces, not a term of its own, and every term a
//! rule or an equation is applied to has its functions evaluated: a
//! configuration holds values, and an equation's arguments are values. So a
//! pattern that applies a function where it matches a term, at a slot's root
//! as below it, describes a term that never occurs, and the sentence silently
//! never applies. Whether a head is a function is a fact of the declaration it
//! resolves to ([`ProductionSignature::function`], a builtin operation's
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
//! equation's subject, a computation item, a cell's content) is matched from
//! its root down; a collection's entries are the keys and values of a map,
//! the elements of a list cell, the instances of a collection cell, and the
//! operands of the collection's unit, element and concatenation. A
//! `k::rewrite!`'s left side is matched where it stands; its right side is
//! built and is no pattern.
//!
//! A key is evaluated, so a name below a function application in a map key
//! reads a value and binds none; [`key_names`] refuses a name that the
//! pattern binds nowhere else.

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

mod key_names;

/// Refuses the first function application where a pattern matches a term,
/// and then the first name a map key reads below a function application and
/// the pattern binds nowhere else, of each sentence whose subject every term
/// it applies to matches with its functions evaluated.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::FunctionInPattern`] at the first such
/// application's head, and [`DescriptorLoweringError::UnboundKeyName`] at
/// the first such name.
pub(super) fn check_function_patterns(
    descriptors: &[&Descriptor],
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<(), DescriptorLoweringError> {
    for descriptor in descriptors {
        sentence_patterns(descriptor.payload(), &Patterns { catalog })
            .map_err(|found| refusal(descriptor, &found))?;
        key_names::check(descriptor, catalog)?;
    }
    Ok(())
}

/// Whether the payload is a sentence whose subject matches every term it
/// applies to with the term's functions evaluated: a transition or an
/// equation, but neither a claim nor a predicate simplification.
fn matches_evaluated_sentence(payload: &DescriptorPayload) -> bool {
    match payload {
        DescriptorPayload::StructuredRule(rule) => {
            matches_evaluated_terms(rule.sentence_kind, false) && !rule.predicate
        }
        DescriptorPayload::HeadRule(rule) => {
            matches_evaluated_terms(rule.sentence_kind, rule.claim.is_some())
        }
        DescriptorPayload::ConfigurationRule(rule) => {
            matches_evaluated_terms(rule.sentence_kind.sentence_kind(), rule.claim.is_some())
        }
        _ => false,
    }
}

/// Checks the patterns of a sentence whose subject every term it applies to
/// matches with its functions evaluated.
fn sentence_patterns<'t>(
    payload: &'t DescriptorPayload,
    patterns: &Patterns<'_>,
) -> Result<(), Found<'t>> {
    if !matches_evaluated_sentence(payload) {
        return Ok(());
    }
    match payload {
        DescriptorPayload::StructuredRule(rule) => {
            // An equation's subject applies the function it defines; a
            // rule's subject is a term of the configuration, which a
            // single-body rule rewrites in place.
            let root = if rule.sentence_kind == SentenceKind::Equation {
                Root::Defined
            } else if rule.result.is_some() {
                Root::RuleSubject
            } else {
                Root::Slot
            };
            patterns.term(&rule.subject, Some(root))?;
            rule.function_context
                .iter()
                .flat_map(|context| &context.cells.cells)
                .try_for_each(|cell| patterns.state(&cell.value))
        }
        DescriptorPayload::HeadRule(rule) => {
            // A `for Sort` clause's subject is its one computation item.
            let root = if rule.head_sort.is_some() {
                Root::RuleSubject
            } else {
                Root::Slot
            };
            rule.head
                .iter()
                .flat_map(|head| &head.items)
                .try_for_each(|item| patterns.term(item, Some(root)))?;
            rule.extras
                .iter()
                .try_for_each(|extra| patterns.extra(extra))
        }
        DescriptorPayload::ConfigurationRule(rule) => rule
            .subject
            .cells
            .iter()
            .try_for_each(|cell| patterns.state(&cell.value)),
        _ => Ok(()),
    }
}

/// The refusal of the application `found` names.
fn refusal(descriptor: &Descriptor, found: &Found<'_>) -> DescriptorLoweringError {
    let instead = match found.root {
        Some(Root::RuleSubject) => {
            "match a variable and relate it to the application in a guard (`requires`), or, to define the function, write an equation (`#[k::equation]`, or a `k::equations!` row)"
        }
        _ => {
            "match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`"
        }
    };
    DescriptorLoweringError::FunctionInPattern {
        item: Box::new(descriptor.id().clone()),
        reason: format!(
            "{} stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule or an equation is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: {instead}",
            found.function
        ),
        range: key_range(descriptor, &found.reference.key).map(Box::new),
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

/// The root of a matched slot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Root {
    /// The root of an equation's subject: the function the equation defines.
    Defined,
    /// The root of the subject term a rule rewrites as a whole (a
    /// `#[k::rule]` fn's with a result, a `for Sort` clause's): a function
    /// there may be one the author meant to define.
    RuleSubject,
    /// The root of another matched slot: a single-body rule's subject, a
    /// computation item, a cell's content, a list cell's rest.
    Slot,
}

/// A function application where a pattern matches a term.
struct Found<'t> {
    /// The application.
    reference: &'t DescriptorApplicationReference,
    /// What it applies, described for a diagnostic.
    function: String,
    /// The root it stands at, or `None` below a root.
    root: Option<Root>,
}

impl Patterns<'_> {
    /// One state of a cell a pattern names: its term, its computation items,
    /// or its map's base. A map's keys and values and a collection cell's
    /// instances are entries.
    fn state<'t>(&self, state: &'t ProtocolRuleStateTerm<DescriptorTerm>) -> Result<(), Found<'t>> {
        let root = Some(Root::Slot);
        match state {
            ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
                self.term(term, root)
            }
            ProtocolRuleStateTerm::KSequence(sequence) => sequence
                .items
                .iter()
                .try_for_each(|item| self.term(&item.value, root)),
            ProtocolRuleStateTerm::Map(map) => match &map.body {
                ProtocolRuleMapBody::Update { base, .. } => self.term(base, root),
                ProtocolRuleMapBody::Empty { .. } | ProtocolRuleMapBody::Items { .. } => Ok(()),
            },
            ProtocolRuleStateTerm::Present { value } => self.state(value),
            ProtocolRuleStateTerm::Absent | ProtocolRuleStateTerm::Instances(_) => Ok(()),
        }
    }

    /// The matched side of a readable rule's cell: a cell's content, an
    /// optional cell's state, a list cell's rest. A map read's keys and a
    /// list cell's elements are entries, and a map update is what the result
    /// writes.
    fn extra<'t>(&self, extra: &'t DescriptorHeadRuleExtra) -> Result<(), Found<'t>> {
        let root = Some(Root::Slot);
        match extra {
            ProtocolHeadRuleExtra::RewriteCell { before, .. } => self.term(before, root),
            ProtocolHeadRuleExtra::RewriteState { before, .. } => self.state(before),
            ProtocolHeadRuleExtra::RewriteList { before, .. } => match &before.rest {
                ProtocolHeadRuleListRest::Term(rest) => self.term(rest, root),
                ProtocolHeadRuleListRest::Exact | ProtocolHeadRuleListRest::Shared => Ok(()),
            },
            ProtocolHeadRuleExtra::HaveMap { .. } | ProtocolHeadRuleExtra::UpdateMap { .. } => {
                Ok(())
            }
        }
    }

    /// `term`, matched at `root`, or below a root when `None`.
    fn term<'t>(&self, term: &'t DescriptorTerm, root: Option<Root>) -> Result<(), Found<'t>> {
        match term {
            DescriptorTerm::Application {
                reference,
                arguments,
                ..
            } => {
                match applied_function(&reference.application, self.catalog) {
                    Applied::Collection => return Ok(()),
                    Applied::Function(_) if root == Some(Root::Defined) => {}
                    Applied::Function(function) => {
                        return Err(Found {
                            reference,
                            function,
                            root,
                        });
                    }
                    Applied::Constructor => {}
                }
                arguments.iter().try_for_each(|argument| {
                    let (TermArgumentRef::Positional { value }
                    | TermArgumentRef::Named { value, .. }) = argument;
                    self.term(value, None)
                })
            }
            // An alias names the term its pattern matches, each alternative
            // is matched where the alternatives stand, and a rewrite's left
            // side is matched where the rewrite stands; its right side is
            // built.
            DescriptorTerm::As { pattern, .. } => self.term(pattern, root),
            DescriptorTerm::Or { alternatives, .. } => alternatives
                .iter()
                .try_for_each(|alternative| self.term(alternative, root)),
            DescriptorTerm::Rewrite { from, .. } => self.term(from, root),
            DescriptorTerm::Cell { fields, .. } => fields
                .iter()
                .try_for_each(|field| self.term(&field.value, None)),
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
    /// A function, named for a diagnostic: "the function `Size`".
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
                Applied::Function(format!("the function `{}`", id.item_name()))
            } else {
                Applied::Constructor
            }
        }
        DescriptorApplicationRef::Builtin(operation) => {
            if operation.is_functional() {
                Applied::Function(format!(
                    "the builtin function `{}`",
                    builtin_path(*operation)
                ))
            } else {
                Applied::Constructor
            }
        }
        DescriptorApplicationRef::Operator(operator) => Applied::Function(format!(
            "the operator `{}`, a builtin function,",
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
        "the builtin function `k::builtin::{}::{}`",
        marker.module, marker.name
    ))
}

fn builtin_path(operation: BuiltinOperation) -> String {
    let spec = operation.spec();
    format!("k::builtin::{}::{}", spec.rust_module, spec.rust_name)
}

#[cfg(test)]
mod tests;
