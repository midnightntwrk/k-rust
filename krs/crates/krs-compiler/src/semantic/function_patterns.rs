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
//! A context matches the configuration's terms as a rule does, so its subject
//! is such a pattern too. A collection's value or element in a pattern is
//! matched against the values the collection holds, which are evaluated: a
//! map's value and a list's element (a List cell's, a cons list's). So is a
//! cell collection's instance: a List collection's instance is its element,
//! and a Map collection pairs an instance's key cell with the whole instance,
//! key cell included, as the value it maps to. A record update there is
//! refused too: the walker cannot tell a Map collection's braces from a Set
//! collection's, so it leaves it here (and a sort test, which lowering
//! refuses in a pattern over evaluated terms). A `let` or
//! `k::matches!` pattern matches the value its term computed, evaluated as
//! well, wherever it stands ([`check_local_pattern`]).
//!
//! The application is the meaning, and is admitted, where:
//! - it is the root of an equation's subject: the function the equation
//!   defines;
//! - it stands in a simplification's subject, which rewrites symbolic terms,
//!   whose applications stand unevaluated;
//! - it stands in a claim's subject, a symbolic state whose applications
//!   denote values;
//! - it stands in a map's key or a set's element (a map read's or a `cells!`
//!   map's key, the operand of `set::item`, a Set collection's instance) that
//!   the pattern computes and looks up, which [`key_names`] judges, with the
//!   key's other names.
//!
//! The positions are the sentence's own shape, which each descriptor carries:
//! every term of a subject the walker reads as one slot (a fn rule's or an
//! equation's subject, a computation item, a cell's content) is matched from
//! its root down, a collection's values and elements with it. A
//! `k::rewrite!`'s left side is matched where it stands; its right side is
//! built and is no pattern.
//!
//! A key or a set element is computed and looked up when nothing in it
//! outside the constructs that compute selects an entry by matching; then a
//! name below a function application reads a value and binds none.
//! Otherwise it is a selection, matched, and a function there never matches.
//! [`key_names`] decides both.
//!
//! An alias's or a desugar clause's subject is matched by static expansion
//! against a program's terms as they are written, before anything evaluates
//! ([`static_subject`]). Below its root an application of a function would
//! match only its own spelling: `Foo(x + 1)` would expand the program
//! `foo(y + 1)` but not `foo(1 + y)`, where everywhere else the two denote
//! one value (decision NT-11-5). So a function there is refused too, a set's
//! element and a collection's entries included, since nothing is looked up
//! there; the root is the production the clause expands, which
//! `statics` judges.

use std::collections::BTreeMap;

use krs_ir::{
    BuiltinOperation, CellCollectionType, Descriptor, DescriptorApplicationRef,
    DescriptorCellIdentity, DescriptorHeadRuleExtra, DescriptorIndex, DescriptorPayload,
    DescriptorTerm, ListOperation, ProtocolCellContent, ProtocolHeadRuleExtra,
    ProtocolHeadRuleListRest, ProtocolRuleInstances, ProtocolRuleMapBody, ProtocolRuleStateTerm,
    ProvenanceKey, SentenceKind, SetOperation, StableItemId, TermArgumentRef, TermMapOperation,
};

use super::catalog::ProductionSignature;
use super::error::DescriptorLoweringError;
use super::origin::key_range;

mod key_names;

/// Refuses the first function application where a pattern matches a term,
/// and then the first name a map key or a set element reads below a function
/// application and the pattern binds nowhere else, of each sentence whose
/// subject every term it applies to matches with its functions evaluated.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::FunctionInPattern`] at the first such
/// application's head, and [`DescriptorLoweringError::UnboundKeyName`] at
/// the first such name.
pub(super) fn check_function_patterns(
    descriptors: &[&Descriptor],
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    for descriptor in descriptors {
        let patterns = Patterns {
            catalog,
            declarations: Some(declarations),
            place: Place::Pattern,
        };
        sentence_patterns(descriptor.payload(), &patterns)
            .and_then(|()| static_subject(descriptor.payload(), &patterns))
            .map_err(|found| refusal(descriptor, &found))?;
        key_names::check(descriptor, catalog, declarations)?;
    }
    Ok(())
}

/// Refuses the first function application in `pattern`, the pattern of a
/// `let` or a `k::matches!` of `descriptor`'s sentence, wherever it stands:
/// a local pattern matches the value its term computed, whose functions are
/// evaluated.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::FunctionInPattern`] at the first such
/// application's head.
pub(super) fn check_local_pattern(
    descriptor: &Descriptor,
    pattern: &DescriptorTerm,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<(), DescriptorLoweringError> {
    let patterns = Patterns {
        catalog,
        declarations: None,
        place: Place::Local,
    };
    patterns
        .term(pattern, None)
        .map_err(|found| refusal(descriptor, &found))
}

/// Whether the payload is a sentence whose subject matches every term it
/// applies to with the term's functions evaluated: a transition or an
/// equation, but neither a claim nor a predicate simplification.
pub(super) fn matches_evaluated_sentence(payload: &DescriptorPayload) -> bool {
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
        // A named configuration context, which a context's subject names.
        DescriptorPayload::ContextAlias(_) => true,
        _ => false,
    }
}

/// Checks the subject of an alias or a desugar clause below its root, which
/// static expansion matches against a program's terms as they are written. A
/// root that is no production the clause expands is `statics`'s to report.
fn static_subject<'t>(
    payload: &'t DescriptorPayload,
    patterns: &Patterns<'_>,
) -> Result<(), Found<'t>> {
    let DescriptorPayload::StructuredRule(rule) = payload else {
        return Ok(());
    };
    if !matches!(
        rule.sentence_kind,
        SentenceKind::Alias | SentenceKind::Desugar
    ) {
        return Ok(());
    }
    let written = Patterns {
        place: Place::AsWritten(rule.sentence_kind),
        ..*patterns
    };
    written.static_root(&rule.subject)
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
            // single-body rule rewrites in place, and a context's the one
            // whose hole it heats.
            let root = if rule.sentence_kind == SentenceKind::Equation {
                Root::Defined
            } else if rule.sentence_kind == SentenceKind::Context {
                Root::Slot
            } else if rule.result.is_some() {
                Root::RuleSubject
            } else {
                Root::Slot
            };
            patterns.term(&rule.subject, Some(root))?;
            rule.function_context
                .iter()
                .flat_map(|context| &context.cells.cells)
                .try_for_each(|cell| patterns.state(Some(&cell.field.cell), &cell.value))
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
            .try_for_each(|cell| patterns.state(Some(&cell.field.cell), &cell.value)),
        DescriptorPayload::ContextAlias(alias) => alias
            .pattern
            .cells
            .iter()
            .try_for_each(|cell| patterns.state(Some(&cell.field.cell), &cell.value)),
        _ => Ok(()),
    }
}

/// The refusal of the construct `found` names.
fn refusal(descriptor: &Descriptor, found: &Found<'_>) -> DescriptorLoweringError {
    let item = Box::new(descriptor.id().clone());
    let range = key_range(descriptor, found.key).map(Box::new);
    let function = match &found.what {
        What::Function(function) => function,
        What::RecordUpdate => {
            let instance = instance_place(found.place);
            return DescriptorLoweringError::RecordUpdateInPattern {
                item,
                reason: format!(
                    "a record update `Ctor {{ f: e, ..base }}` {instance}; `..base` builds a record from the record `base` matched, which only a term a sentence builds can say, and a pattern denotes no record by it: name the fields the pattern constrains, and leave out the others with `..`"
                ),
                range,
            };
        }
    };
    let reason = match (found.place, found.root) {
        (Place::AsWritten(kind), _) => format!(
            "{written} stands in the subject of {clause}, which static expansion matches against a program's terms as they are written, before anything evaluates: there an application stands for its own spelling, not for the value it denotes everywhere else (`f(x + 1)` would expand the program `f(y + 1)` but not `f(1 + y)`), so the clause would rewrite some spellings of a value and not others: to rewrite a computation, write a rule (`#[k::rule]`) or the function's equation (`#[k::equation]`); to expand a term a program writes, write it with constructors",
            clause = if kind == SentenceKind::Alias {
                "an alias clause"
            } else {
                "a desugar clause"
            },
            // A map literal denotes its updates, the one way KRS writes a map it builds; read
            // as written, even `map![k -> v]` would meet no term KRS writes as its entry.
            written = if matches!(
                found.application,
                Some(DescriptorApplicationRef::Map(TermMapOperation::Update))
            ) {
                format!("{function}, which a map literal `map![k -> v, ..]` denotes,")
            } else {
                function.clone()
            },
        ),
        (Place::Local, _) => format!(
            "{function} stands in a `let` or `k::matches!` pattern, which matches the value its term computed; a function application denotes the value evaluation produces, and a computed value has its functions evaluated, so this pattern describes a term that never occurs and never matches: match a variable here and compare it with the application (`==`), or apply the function in the value"
        ),
        (Place::Entry, _) => format!(
            "{function} stands in a collection's value or element (a map's value, a list's element), which the pattern matches against the values the collection holds; a function application denotes the value evaluation produces, and those values have their functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`); a map's key or a set's element whose every part is computed from names bound elsewhere is looked up by its value instead"
        ),
        (Place::Instance(_), _) => format!(
            "{function} {}; those cells have their functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: match a variable here and relate it to the application in a guard (`requires`)",
            instance_place(found.place)
        ),
        (Place::Pattern, root) => {
            let method = match found.application {
                Some(DescriptorApplicationRef::CollectionMethod(method)) => Some(method.spelling()),
                _ => None,
            };
            let instead = match (method, root) {
                // A map written with an entry (`map![k -> v]`, `map::update`)
                // or a union of sets builds a collection; a pattern reads a
                // collection's entries and elements instead.
                (None, _)
                    if matches!(
                        found.application,
                        Some(DescriptorApplicationRef::Map(TermMapOperation::Update))
                    ) =>
                {
                    "a pattern reads a map's entries (`{ k -> v, .. }` in a readable record, `map![k -> v, ..]` in a `cells!` entry), or match a variable here and relate it to the map in a guard (`requires`)"
                }
                (None, _)
                    if matches!(
                        found.application,
                        Some(DescriptorApplicationRef::Set(SetOperation::Union))
                    ) =>
                {
                    "match the elements with `set::concat(set::item(x), rest)`, whose operands are disjoint, or match a variable here and relate it to the set in a guard (`requires`)"
                }
                // A pattern reads an entry with braces, and a list's first
                // elements with brackets.
                (Some(krs_ir::CollectionMethodSpelling::Index), _) => {
                    "write `{ k -> v, .. }` to read an entry (`[x, ..]` reads a list's first element), or match a variable here and compare it with the index in a guard (`requires`)"
                }
                (Some(krs_ir::CollectionMethodSpelling::Method), _) => {
                    "read the value into a name and compare it in a guard (`requires`)"
                }
                (None, Some(Root::RuleSubject)) => {
                    "match a variable and relate it to the application in a guard (`requires`), or, to define the function, write an equation (`#[k::equation]`, or a `k::equations!` row)"
                }
                (None, _) => {
                    "match a variable here and relate it to the application in a guard (`requires`), or state a fact about the unevaluated application as a `#[k::simplification]`"
                }
            };
            format!(
                "{function} stands where the pattern matches a term; a function application denotes the value evaluation produces, and every term a rule, an equation or a context is applied to has its functions evaluated, so this pattern describes a term that never occurs and the sentence never applies: {instead}"
            )
        }
    };
    DescriptorLoweringError::FunctionInPattern {
        item,
        reason,
        range,
    }
}

/// Whether a sentence of `kind` matches every term it applies to with the
/// term's functions evaluated: a transition, an equation and a context,
/// which matches the configuration a computation reached as a rule does, but
/// no claim, whose subject is a symbolic state, and no simplification, which
/// rewrites unevaluated applications. An alias and a desugar clause rewrite
/// the program as written, before any evaluation.
const fn matches_evaluated_terms(kind: SentenceKind, claim: bool) -> bool {
    !claim
        && matches!(
            kind,
            SentenceKind::Transition | SentenceKind::Equation | SentenceKind::Context
        )
}

/// The patterns of one sentence.
#[derive(Clone, Copy)]
struct Patterns<'a> {
    catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    /// The cells' declarations, which tell a collection's type; `None` for a
    /// local pattern, which holds no cell.
    declarations: Option<&'a DescriptorIndex<'a>>,
    /// What the terms walked are matched as.
    place: Place,
}

/// What a matched term is part of, which the refusal explains.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Place {
    /// A sentence's subject.
    Pattern,
    /// A collection's value or element in the subject.
    Entry,
    /// A child of a List or a Map collection's instance in the subject, of the
    /// collection's type when the declarations tell it.
    Instance(Option<CellCollectionType>),
    /// A `let` or `k::matches!` pattern.
    Local,
    /// An alias's or a desugar clause's subject below its root, of that
    /// sentence kind, which static expansion matches against a program's
    /// terms as they are written.
    AsWritten(SentenceKind),
}

/// A construct that computes, which a pattern never meets.
enum What {
    /// A function's application, named for a diagnostic.
    Function(String),
    /// A record update, in a collection's instance.
    RecordUpdate,
}

/// Where a construct in a collection's instance stands, and why the instance
/// is matched, for a diagnostic.
fn instance_place(place: Place) -> &'static str {
    match place {
        Place::Instance(Some(CellCollectionType::Map)) => {
            "stands in a Map collection's instance, which the pattern matches against the instances the collection holds: a Map collection pairs an instance's key cell with the whole instance, key cell included, as the value it maps to, so its cells are values a match compares (decision D1), where a Set collection's computed instance is looked up as the set's element"
        }
        Place::Instance(Some(CellCollectionType::List)) => {
            "stands in a List collection's instance, which the pattern matches against the instances the collection holds: a List collection's instance is its element, matched as a list's element is (decision D1)"
        }
        _ => {
            "stands in a cell collection's instance, which the pattern matches against the instances the collection holds: a List collection's instance is its element, and a Map collection pairs an instance's key cell with the whole instance, key cell included, as the value it maps to"
        }
    }
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

/// A construct that computes where a pattern matches a term.
struct Found<'t> {
    /// Where it stands: an application's head, a sort test's or a record
    /// update's node.
    key: &'t ProvenanceKey,
    /// The application, if it is one.
    application: Option<&'t DescriptorApplicationRef>,
    /// What it is.
    what: What,
    /// The root it stands at, or `None` below a root.
    root: Option<Root>,
    /// What the pattern it stands in is.
    place: Place,
}

impl Patterns<'_> {
    /// These patterns, matching a collection's values and elements; a
    /// subject matched as written reads them as written too.
    const fn entries(self) -> Self {
        if matches!(self.place, Place::AsWritten(_)) {
            return self;
        }
        Self {
            place: Place::Entry,
            ..self
        }
    }

    /// A static clause's subject root: its arguments, when it is a
    /// production's application.
    fn static_root<'t>(&self, root: &'t DescriptorTerm) -> Result<(), Found<'t>> {
        match root {
            DescriptorTerm::Application {
                reference,
                arguments,
                ..
            } if matches!(
                applied_function(&reference.application, self.catalog),
                Applied::Constructor
            ) =>
            {
                arguments.iter().try_for_each(|argument| {
                    let (TermArgumentRef::Positional { value }
                    | TermArgumentRef::Named { value, .. }) = argument;
                    self.term(value, None)
                })
            }
            _ => Ok(()),
        }
    }

    /// One state of a cell a pattern names: its term, its computation items,
    /// its map's base and values, and a collection cell's instances, all
    /// matched. A map's keys are judged with their reading ([`key_names`]).
    fn state<'t>(
        &self,
        cell: Option<&DescriptorCellIdentity>,
        state: &'t ProtocolRuleStateTerm<DescriptorTerm>,
    ) -> Result<(), Found<'t>> {
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
                ProtocolRuleMapBody::Items { items, .. } => items
                    .iter()
                    .try_for_each(|item| self.entries().term(&item.value, None)),
                ProtocolRuleMapBody::Empty { .. } => Ok(()),
            },
            ProtocolRuleStateTerm::Present { value } => self.state(cell, value),
            ProtocolRuleStateTerm::Instances(instances) => self.instances(cell, instances),
            ProtocolRuleStateTerm::Absent => Ok(()),
        }
    }

    /// The instances of a collection cell, matched as the collection holds
    /// them: a List collection's instance is its element, and a Map
    /// collection's is the value its key cell maps to, key cell included. A
    /// Set collection is a set of its instances, looked up by an instance as
    /// by an element, which [`key_names`] judges.
    fn instances<'t>(
        &self,
        cell: Option<&DescriptorCellIdentity>,
        instances: &'t ProtocolRuleInstances<DescriptorTerm>,
    ) -> Result<(), Found<'t>> {
        let collection = cell
            .zip(self.declarations)
            .and_then(|(cell, declarations)| collection_type(declarations, cell));
        if collection == Some(CellCollectionType::Set) {
            return Ok(());
        }
        let children = Self {
            place: Place::Instance(collection),
            ..*self
        };
        instances
            .front
            .iter()
            .chain(&instances.back)
            .flat_map(|instance| &instance.fields)
            .try_for_each(|child| children.state(None, &child.value))
    }

    /// The matched side of a readable rule's cell: a cell's content, an
    /// optional cell's state, a list cell's elements and rest. A map read's
    /// keys are looked up, its values are binders, and a map update is what
    /// the result writes.
    fn extra<'t>(&self, extra: &'t DescriptorHeadRuleExtra) -> Result<(), Found<'t>> {
        let root = Some(Root::Slot);
        match extra {
            ProtocolHeadRuleExtra::RewriteCell { before, .. } => self.term(before, root),
            ProtocolHeadRuleExtra::RewriteState { cell, before, .. } => {
                self.state(Some(&cell.cell), before)
            }
            ProtocolHeadRuleExtra::RewriteList { before, .. } => {
                before
                    .items
                    .iter()
                    .chain(&before.back)
                    .try_for_each(|element| self.entries().term(element, None))?;
                match &before.rest {
                    ProtocolHeadRuleListRest::Term(rest) => self.term(rest, root),
                    ProtocolHeadRuleListRest::Exact | ProtocolHeadRuleListRest::Shared => Ok(()),
                }
            }
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
                update,
                ..
            } => {
                // The walker cannot tell a Map collection's braces from a Set
                // collection's, whose instance a record update may compute.
                if matches!(self.place, Place::Instance(_)) && update.is_some() {
                    return Err(Found {
                        key: &reference.key,
                        application: None,
                        what: What::RecordUpdate,
                        root,
                        place: self.place,
                    });
                }
                let below = match applied_function(&reference.application, self.catalog) {
                    // Nothing is looked up in a subject matched as written:
                    // a set's or a map's operands are matched as they are.
                    Applied::Collection if matches!(self.place, Place::AsWritten(_)) => *self,
                    // A set's elements are its keys ([`key_names`]); the
                    // other operands of its concatenation are the sets it
                    // holds besides them, matched as any term is.
                    Applied::Collection
                        if reference.application
                            == DescriptorApplicationRef::Set(SetOperation::Concat) =>
                    {
                        return arguments.iter().try_for_each(|argument| {
                            let (TermArgumentRef::Positional { value }
                            | TermArgumentRef::Named { value, .. }) = argument;
                            self.term(value, None)
                        });
                    }
                    Applied::Collection => return Ok(()),
                    Applied::Function(_) if root == Some(Root::Defined) => *self,
                    Applied::Function(function) => {
                        return Err(Found {
                            key: &reference.key,
                            application: Some(&reference.application),
                            what: What::Function(function),
                            root,
                            place: self.place,
                        });
                    }
                    Applied::Constructor => *self,
                    Applied::Elements => self.entries(),
                };
                arguments.iter().try_for_each(|argument| {
                    let (TermArgumentRef::Positional { value }
                    | TermArgumentRef::Named { value, .. }) = argument;
                    below.term(value, None)
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
pub(super) enum Applied {
    /// A function, named for a diagnostic: "the function `Size`".
    Function(String),
    /// A constructor, matched as written.
    Constructor,
    /// A list's unit, element or concatenation, or a level of list notation:
    /// constructors whose operands are the list's elements, matched as the
    /// values the list holds.
    Elements,
    /// A set's or a map's unit, element or concatenation, whose operands are
    /// what the collection is looked up by.
    Collection,
}

/// The type of the collection cell `cell` names; `None` when it names no
/// collection.
fn collection_type(
    declarations: &DescriptorIndex<'_>,
    cell: &DescriptorCellIdentity,
) -> Option<CellCollectionType> {
    let declared = super::references::require_cell_field(cell, declarations).ok()?;
    let ProtocolCellContent::Nested { .. } = &declared.content else {
        return None;
    };
    Some(CellCollectionType::from(declared.cell_type.as_ref()?.value))
}

/// What `application` applies: a declared function, a builtin operation that
/// is a function (an operator denotes one in every domain), or one of a
/// collection's operations other than its unit, element and concatenation,
/// which are its functions (a lookup, a size, an update).
pub(super) fn applied_function(
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
            ListOperation::Empty | ListOperation::Item | ListOperation::Concat => Applied::Elements,
            other => collection_function(other.facade_marker()),
        },
        DescriptorApplicationRef::Set(operation) => match operation {
            SetOperation::Empty | SetOperation::Item | SetOperation::Concat => Applied::Collection,
            other => collection_function(other.facade_marker()),
        },
        DescriptorApplicationRef::ListNotation(_) => Applied::Elements,
        // Every reading of an index or a collection method is a collection's
        // function: a lookup, a size, an update.
        DescriptorApplicationRef::CollectionMethod(method) => {
            Applied::Function(match method.spelling() {
                krs_ir::CollectionMethodSpelling::Index => {
                    "the index `[..]`, a builtin lookup,".to_owned()
                }
                krs_ir::CollectionMethodSpelling::Method => format!(
                    "the collection method `{}`, a builtin function,",
                    method.written()
                ),
            })
        }
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
