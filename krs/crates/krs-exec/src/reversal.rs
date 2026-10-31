//! Which alias clauses printing reverses.
//!
//! A reversal prints a term as the alias application a clause's subject writes, and is right
//! only where that application is a term the author wrote for the state, and reads back as it.
//! `macros.kore` cannot tell either, so the printer is told which clauses it reverses, and
//! reverses no other axiom: one whose label names no alias clause of the definition, or none at
//! all, prints expanded. A clause is reversed when its written result constructs and every token
//! its subject writes reads back as itself; every other clause runs forward only:
//!
//! - **A clause whose written result computes** (a function's application, an operator, a sort
//!   test or projection, `let`, `k::matches!`, or a collection operation that does not write one
//!   term: anything but a collection's unit, a singleton, and a list's concatenation of items,
//!   units and at most one named list). Its axiom states the result after compilation, where an
//!   application on ground arguments is already its value (`three() => tag(1 + 2)` reaches
//!   `macros.kore` as `three() = tag(3)`), so reversing it would print every `tag(3)`, however
//!   the run computed it, as `three()`: an alias the author wrote for an expression, printed for a
//!   value that merely equals it. In a pattern the alias still means that value. A result built
//!   only of constructors, tokens, names and those collection terms is the very term a matched
//!   state holds, so its clause is reversed.
//! - **Which collection terms construct.** A list's items and units
//!   fix their own places, so a concatenation of them and at most one named list gives that list
//!   exactly the elements the others leave: `[x, ..rest]` matches `[5, 6, 7]` only with `x = 5`
//!   and `rest = [6, 7]`. With two named lists, `lc(a, b) => two(1, list::concat(a, b))`, the
//!   printed value `two(1, [5, 6, 7])` is the concatenation of four splits, and the one printed
//!   (`lc(ListItem(5), ListItem(6) ListItem(7))`) would come from how the backend's list happens
//!   to nest, not from anything the author wrote. A set's or a map's parts have no order, so even
//!   two items split a value by choice (`set![x, y]` binds `x` to either element): beyond its
//!   unit and singleton, a set or map term computes.
//! - **A clause whose subject writes a token that does not read back as itself** where it stands:
//!   printed, a token is its text, and the text may be another sort's token at that position
//!   (`word`, a `Word`, read as an `Id` where a `KItem` stands) or no token at all (`$x`).
//!   The printed alias would then read back as another application, which its clause does not
//!   expand. Whether the text reads back is the grammar's answer, so each token is parsed at its
//!   position with the grammar a printed term is read back with, a program's
//!   ([`Configuration::read_token`]), and compared with the token by the value each denotes
//!   (`same_token`): a token's text is one spelling of its value (`b"a\x22b"` and `b"a\"b"` are
//!   one byte string), and a value is what a program's expansion matches a token by. The text
//!   judged is the one a reversal prints, the token as the clause wrote it. A position that
//!   cannot be judged (a sort with parameters) does not read back. Each token is judged alone,
//!   not inside the printed application: the two differ only where a token sort's regex can take
//!   in what is printed after the token (a `)`, a `,`, or the next argument's text), so that the
//!   scanner reads a longer token in context. Such a clause is reversed though its print may not
//!   read back; judging the whole printed subject would need its arguments, which only a print
//!   has.
//!
//! Such a clause still expands wherever a program or a rule writes it; a term it would have
//! printed prints expanded, which is the state as it is.

use std::collections::BTreeSet;

use krs_ir::{ApplicationRef, SentenceKind};
use krs_ir_levels::{
    DefinitionApplicationRef, DefinitionIr, DefinitionSentence, DefinitionTerm, DefinitionTermKind,
    ListOperands, MapOperands, SetOperands, SymbolId,
};

use k_rust::kore::ast::Pattern;

use crate::configuration::Configuration;
use crate::values::{Value, ValueIndex};

/// The labels of the alias clauses printing reverses: those whose written result constructs and
/// whose subject writes only tokens `configuration` reads back as themselves where they stand.
pub(crate) fn reversed(
    definition: &DefinitionIr,
    unparser: &krs_unparse::Unparser,
    configuration: &mut Configuration,
    values: &ValueIndex,
) -> BTreeSet<String> {
    let (constructing, computing) = alias_clauses(definition);
    debug_assert!(
        {
            let emitted = unparser.clause_labels();
            computing
                .iter()
                .all(|label| emitted.contains(label.as_str()))
        },
        "an alias clause whose result computes has no axiom in macros.kore: {computing:?}"
    );
    unparser
        .reversed_clauses()
        .into_iter()
        .filter_map(|clause| {
            let label = clause.label.filter(|label| constructing.contains(label))?;
            clause
                .tokens
                .iter()
                .all(|token| {
                    configuration
                        .read_token(&token.position, &token.printed)
                        .is_some_and(|read| same_token(values, &read, &token.token))
                })
                .then_some(label)
        })
        .collect()
}

/// Whether `read` and `token`, two tokens, are one term: of one sort and denoting one value as
/// the definition reads them (`0.15000000000000000e1` and `1.5` are one `Float`), or, where
/// either denotes no value it reads, the same pattern.
fn same_token(values: &ValueIndex, read: &Pattern, token: &Pattern) -> bool {
    let value = |pattern: &Pattern| match pattern {
        Pattern::DomainValue { sort, .. } => values
            .decode(pattern)
            .ok()
            .filter(|value| !matches!(value, Value::Opaque(_)))
            .map(|value| (sort.clone(), value)),
        _ => None,
    };
    match (value(read), value(token)) {
        (Some(read), Some(token)) => read == token,
        _ => read == token,
    }
}

/// The labels of the definition's alias clauses: those whose written result constructs, and
/// those whose written result computes.
fn alias_clauses(definition: &DefinitionIr) -> (BTreeSet<String>, BTreeSet<String>) {
    let sentences = || {
        definition
            .modules()
            .iter()
            .flat_map(krs_ir_levels::DefinitionModule::sentences)
    };
    let functions = sentences()
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Production(production)
                if production.attributes().iter().any(|attribute| {
                    matches!(attribute, krs_ir::ProductionAttribute::Function { .. })
                }) =>
            {
                Some(production.symbol().id().clone())
            }
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    sentences()
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Rule(rule) if rule.kind() == SentenceKind::Alias => {
                rule.body().map(|body| {
                    (
                        rule.label().emitted_name().to_owned(),
                        computes(body.to(), &functions),
                    )
                })
            }
            _ => None,
        })
        .fold(
            (BTreeSet::new(), BTreeSet::new()),
            |(mut constructing, mut computing), (label, computes)| {
                if computes {
                    computing.insert(label);
                } else {
                    constructing.insert(label);
                }
                (constructing, computing)
            },
        )
}

/// Whether `term` holds a construct that computes: an application of a function, of a builtin
/// operation that is one, or of a generated sort test or projection; a collection operation
/// other than a collection's unit or singleton, or a list's concatenation whose split is
/// determined ([`named_lists`]); `let`; or `k::matches!`.
fn computes(term: &DefinitionTerm, functions: &BTreeSet<SymbolId>) -> bool {
    let here = match term.kind() {
        DefinitionTermKind::Application { application, .. } => {
            applies_function(application, functions)
        }
        DefinitionTermKind::List(operands) => match **operands {
            ListOperands::Empty | ListOperands::Item { .. } => false,
            ListOperands::Concat { .. } => named_lists(term).is_none_or(|named| named > 1),
            _ => true,
        },
        DefinitionTermKind::Set(operands) => {
            !matches!(**operands, SetOperands::Empty | SetOperands::Item { .. })
        }
        DefinitionTermKind::Map(operands) => match &**operands {
            MapOperands::Empty => false,
            MapOperands::Items(entries) => entries.len() > 1,
            _ => true,
        },
        DefinitionTermKind::Let { .. } | DefinitionTermKind::Matches { .. } => true,
        DefinitionTermKind::Variable { .. }
        | DefinitionTermKind::Token { .. }
        | DefinitionTermKind::KSequence { .. }
        | DefinitionTermKind::Cell { .. }
        | DefinitionTermKind::Rewrite { .. }
        | DefinitionTermKind::As { .. }
        | DefinitionTermKind::Or { .. } => false,
    };
    here || term
        .children()
        .into_iter()
        .any(|child| computes(child, functions))
}

/// How many named lists the list concatenation `term` joins, its nested concatenations
/// flattened, beside its items and units; `None` where an operand is any other term, whose
/// elements the concatenation cannot place. A concatenation of items, units and one named list
/// gives that list exactly the elements the others leave, so a value it matches splits one way.
fn named_lists(term: &DefinitionTerm) -> Option<usize> {
    match term.kind() {
        DefinitionTermKind::Variable { .. } => Some(1),
        DefinitionTermKind::List(operands) => match &**operands {
            ListOperands::Empty | ListOperands::Item { .. } => Some(0),
            ListOperands::Concat { left, right } => Some(named_lists(left)? + named_lists(right)?),
            _ => None,
        },
        _ => None,
    }
}

fn applies_function(
    application: &DefinitionApplicationRef,
    functions: &BTreeSet<SymbolId>,
) -> bool {
    match application {
        ApplicationRef::Declared(production) => functions.contains(production),
        ApplicationRef::Builtin(operation) => operation.is_functional(),
        ApplicationRef::Generated(_) => true,
    }
}
