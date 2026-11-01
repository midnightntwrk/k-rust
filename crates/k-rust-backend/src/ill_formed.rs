//! The uses of a construct the definition's text does not type or bound that the load can see
//! (GAP category E): an arithmetic `Float` application whose operands have two formats, and a
//! machine-integer literal its width cannot hold.
//!
//! Neither is refused, since K's text does not forbid writing one: the load names each (a host
//! prints them as warnings), and evaluation treats them as before. The value of a mixed-format
//! operation is class `float-destination`, which an execution marks where it takes k-rust's
//! result format (`builtin::chosen_value`); the element of a literal outside its width is class
//! `literal`, which an execution marks on every attempt of the sentence holding it
//! (`crate::literal`). Only what the sentence's form shows is named: a literal's own text, and an
//! application whose operands' formats are fixed by their form (`builtin::evident_mixed_formats`);
//! an operand bound only at run time is the mark's alone.

use std::sync::Arc;

use k_rust_domain::float::FloatFormat;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    definition::BackendDefinition,
    rule::{PredicateRewriteRule, RewriteRule, RuleAttributes, RuleRhs},
    term::{Term, TermKind, immediate_children},
};

/// What a sentence holds that the text does not type or bound.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IllFormed {
    /// `hook`, one of `+Float`, `-Float`, `*Float`, `/Float`, `minFloat` and `maxFloat`, applied
    /// (`application`) to operands whose forms fix the two different formats `left` and `right`.
    MixedFormats {
        hook: String,
        application: Term,
        left: FloatFormat,
        right: FloatFormat,
    },
    /// A machine-integer literal, as written, whose value its width cannot hold
    /// (`term::mint_literal_open`).
    WideLiteral(Arc<str>),
}

/// The kind of sentence an [`IllFormedUse`] is in, as a diagnostic names it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Sentence {
    /// A rewrite rule.
    Rule,
    /// A function, simplification or ceil equation.
    Equation,
}

/// One ill-formed use, with the sentence that holds it.
#[derive(Clone, Debug)]
pub struct IllFormedUse<'a> {
    pub sentence: Sentence,
    /// The attributes of the sentence: its unique id and written position name it.
    pub attributes: &'a RuleAttributes,
    pub found: IllFormed,
}

/// The ill-formed uses of the sentences of `definition`, each once per sentence: in the order of
/// the rewrite theory, then the function, simplification, ceil and predicate simplification
/// theories, and within a sentence in the order its parts are read.
pub fn ill_formed_uses(definition: &BackendDefinition) -> Vec<IllFormedUse<'_>> {
    let mut uses = Vec::new();
    let mut seen = Vec::new();
    let mut add =
        |sentence, attributes, found| add_uses(&mut uses, &mut seen, sentence, attributes, found);
    for rule in definition
        .rewrite_theory()
        .values()
        .flat_map(|priorities| priorities.values().flatten())
    {
        add(Sentence::Rule, &rule.attributes, rule_uses(rule));
    }
    for theory in [
        definition.function_theory(),
        definition.simplification_theory(),
        definition.ceil_theory(),
    ] {
        for rule in theory
            .values()
            .flat_map(|priorities| priorities.values().flatten())
        {
            add(Sentence::Equation, &rule.attributes, rule_uses(rule));
        }
    }
    for rule in definition
        .predicate_simplification_theory()
        .values()
        .flatten()
    {
        add(
            Sentence::Equation,
            &rule.attributes,
            predicate_rule_uses(rule),
        );
    }
    uses
}

/// A sentence as the dedup reads it: its unique id and the written positions of its origins.
type SentenceIdentity = (String, Vec<Option<String>>);

/// Push onto `uses` an [`IllFormedUse`] for each of `found` that `seen` does not hold for the
/// sentence `attributes` names. A sentence internalized as several rules (the alternatives of a
/// left-hand side), or indexed under several heads, is named once for each thing it holds.
fn add_uses<'a>(
    uses: &mut Vec<IllFormedUse<'a>>,
    seen: &mut Vec<(SentenceIdentity, IllFormed)>,
    sentence: Sentence,
    attributes: &'a RuleAttributes,
    found: Vec<IllFormed>,
) {
    let identity = (
        attributes.unique_id.clone(),
        attributes
            .origins
            .iter()
            .map(|origin| origin.written_position())
            .collect::<Vec<_>>(),
    );
    for found in found {
        let key = (identity.clone(), found.clone());
        if !seen.contains(&key) {
            seen.push(key);
            uses.push(IllFormedUse {
                sentence,
                attributes,
                found,
            });
        }
    }
}

/// The ill-formed uses of `rule`: its open literals as the load recorded them, then its mixed
/// applications.
fn rule_uses(rule: &RewriteRule) -> Vec<IllFormed> {
    let mut found = wide_literals(&rule.computed_attributes.open_literals);
    let mut terms = vec![&rule.lhs];
    match &rule.rhs {
        RuleRhs::Term(term) => terms.push(term),
        RuleRhs::Disjunction(alternatives) => {
            for alternative in alternatives {
                terms.push(&alternative.term);
            }
        }
        RuleRhs::Predicates(_) | RuleRhs::Top | RuleRhs::Bottom => {}
    }
    for term in terms {
        mixed_applications(term, &mut found);
    }
    let mut predicates = rule
        .requires
        .iter()
        .chain(rule.ensures.iter())
        .collect::<Vec<_>>();
    match &rule.rhs {
        RuleRhs::Predicates(rhs) => predicates.extend(rhs),
        RuleRhs::Disjunction(alternatives) => {
            predicates.extend(
                alternatives
                    .iter()
                    .flat_map(|alternative| alternative.ensures.iter()),
            );
        }
        RuleRhs::Term(_) | RuleRhs::Top | RuleRhs::Bottom => {}
    }
    for predicate in predicates {
        predicate.visit_terms(&mut |term| mixed_applications(term, &mut found));
    }
    found
}

/// The ill-formed uses of the predicate equation `rule`.
fn predicate_rule_uses(rule: &PredicateRewriteRule) -> Vec<IllFormed> {
    let mut found = wide_literals(&rule.open_literals);
    let predicates = std::iter::once(&rule.lhs)
        .chain(&rule.rhs)
        .chain(rule.requires.iter());
    for predicate in predicates {
        predicate.visit_terms(&mut |term| mixed_applications(term, &mut found));
    }
    found
}

/// The machine-integer literals among a sentence's open literals: every open literal is one
/// (`literal::open`), so all of them.
fn wide_literals(open_literals: &[Arc<str>]) -> Vec<IllFormed> {
    open_literals
        .iter()
        .map(|literal| IllFormed::WideLiteral(Arc::clone(literal)))
        .collect()
}

/// Push onto `found` every mixed-format arithmetic application in `term` not already in it,
/// outermost first.
///
/// The evident format of every node is computed first, once, bottom-up ([`evident_formats`]),
/// and each application reads its operands' from there, so the scan is linear in the size of
/// `term`; both walks keep their pending nodes on explicit work lists, so they take the same
/// native stack at any depth. A node shared by several parents is read once.
fn mixed_applications(term: &Term, found: &mut Vec<IllFormed>) {
    let formats = evident_formats(term);
    let format = |operand: &Term| formats.get(&operand.node_address()).cloned().flatten();
    let mut seen = FxHashSet::default();
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if !seen.insert(term.node_address()) {
            continue;
        }
        if let TermKind::Application {
            symbol, arguments, ..
        } = term.kind()
            && let Some(hook) = symbol.attributes.hook.as_deref()
            && let Some((left, right)) =
                crate::builtin::evident_mixed_formats(hook, arguments, format)
        {
            let application = IllFormed::MixedFormats {
                hook: hook.to_owned(),
                application: term.clone(),
                left,
                right,
            };
            if !found.contains(&application) {
                found.push(application);
            }
        }
        // The subterms in order, pushed last first so that they are read first to last.
        pending.extend(immediate_children(term.kind()).into_iter().rev());
    }
}

/// The evident format of each node of `term` (`builtin::evident_format`), keyed by its address
/// (`term` is borrowed throughout, so no address is reused): a post-order walk on an explicit
/// work list, which computes a node's format when its children's are known.
fn evident_formats(term: &Term) -> FxHashMap<usize, Option<FloatFormat>> {
    let mut formats = FxHashMap::default();
    // Each node with whether its children are already computed.
    let mut pending = vec![(term, false)];
    while let Some((term, children_computed)) = pending.pop() {
        let address = term.node_address();
        if children_computed {
            let format = crate::builtin::evident_format(term, |operand| {
                formats.get(&operand.node_address()).cloned().flatten()
            });
            formats.insert(address, format);
        } else if !formats.contains_key(&address) {
            pending.push((term, true));
            pending.extend(
                immediate_children(term.kind())
                    .into_iter()
                    .map(|child| (child, false)),
            );
        }
    }
    formats
}
