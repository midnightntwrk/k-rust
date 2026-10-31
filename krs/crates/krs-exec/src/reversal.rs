//! Which alias clauses printing reverses.
//!
//! A reversal prints a term as the alias application a clause's subject writes, and is right
//! only where that application is a term the author wrote for the state, and reads back as it.
//! `macros.kore` cannot tell either, so the printer is told which clauses run forward only:
//!
//! - **A clause whose written result computes** (a function's application, an operator, a sort
//!   test or projection, a collection operation but writing a list's elements or a collection's
//!   unit or singleton, `let`, `k::matches!`). Its axiom states
//!   the result after compilation, where an application on ground arguments is already its value
//!   (`three() => tag(1 + 2)` reaches `macros.kore` as `three() = tag(3)`), so reversing it would
//!   print every `tag(3)`, however the run computed it, as `three()`: an alias the author wrote
//!   for an expression, printed for a value that merely equals it. In a pattern the alias still
//!   means that value. A result built only of constructors, tokens, names, lists' elements and
//!   collections' units and singletons is the very term a matched state holds, so its clause is reversed.
//! - **A clause whose subject writes a token that does not read back as itself** where it stands:
//!   printed, a token is its text, and the text may be another sort's token at that position
//!   (`word`, a `Word`, read as an `Id` where a `KItem` stands) or no token at all (`$x`).
//!   The printed alias would then read back as another application, which its clause does not
//!   expand. Whether the text reads back is the grammar's answer, so each token is parsed at its
//!   position with the grammar a printed term is read back with, a program's.
//!
//! Such a clause still expands wherever a program or a rule writes it; a term it would have
//! printed prints expanded, which is the state as it is.

use std::collections::BTreeSet;

use krs_ir::{ApplicationRef, SentenceKind};
use krs_ir_levels::{
    DefinitionApplicationRef, DefinitionIr, DefinitionSentence, DefinitionTerm, DefinitionTermKind,
    ListOperands, MapOperands, SetOperands, SymbolId,
};

use crate::configuration::Configuration;

/// The labels of the alias clauses printing does not reverse: those whose written result
/// computes, and those whose subject writes a token `configuration` does not read back as
/// itself where it stands.
pub(crate) fn forward_only(
    definition: &DefinitionIr,
    unparser: &krs_unparse::Unparser,
    configuration: &mut Configuration,
) -> BTreeSet<String> {
    let mut labels = computing_clauses(definition);
    for clause in unparser.reversed_clauses() {
        let Some(label) = clause.label else {
            continue;
        };
        if labels.contains(&label) {
            continue;
        }
        if clause.tokens.iter().any(|token| {
            !configuration.reads_back_token(&token.position, &token.printed, &token.token)
        }) {
            labels.insert(label);
        }
    }
    labels
}

/// The labels of the alias clauses whose written result computes.
fn computing_clauses(definition: &DefinitionIr) -> BTreeSet<String> {
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
            DefinitionSentence::Rule(rule) if rule.kind() == SentenceKind::Alias => rule
                .body()
                .filter(|body| computes(body.to(), &functions))
                .map(|_| rule.label().emitted_name().to_owned()),
            _ => None,
        })
        .collect()
}

/// Whether `term` holds a construct that computes: an application of a function, of a builtin
/// operation that is one, or of a generated sort test or projection; a collection operation
/// other than writing a list's elements in order or a collection's unit or singleton (a set's
/// concatenation is the union of its parts, a map of several entries their join); `let`; or
/// `k::matches!`.
fn computes(term: &DefinitionTerm, functions: &BTreeSet<SymbolId>) -> bool {
    let here = match term.kind() {
        DefinitionTermKind::Application { application, .. } => {
            applies_function(application, functions)
        }
        DefinitionTermKind::List(operands) => !matches!(
            **operands,
            ListOperands::Empty | ListOperands::Item { .. } | ListOperands::Concat { .. }
        ),
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
