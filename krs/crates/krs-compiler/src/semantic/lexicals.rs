//! Whole-theory checks of named lexicals and their `{Name}` references (KF-004).
//!
//! K resolves a `{Name}` in a regex against the `syntax lexical` sentences of
//! the definition. A lexical name is declared once; every reference in a
//! token, layout, or lexical regex names a declared lexical; and lexicals do
//! not refer to each other in a cycle, which K would expand forever.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{GrammarProductionItemKind, LexicalSentence, NodeOrigin, ProductionAttribute};
use krs_ir_levels::SemanticModule;
use krs_syntax::regex_references;

use super::error::{DescriptorLoweringError, LexicalProblem};

/// Checks every lexical, layout regex, and token regex of the theory.
pub(super) fn check_lexicals(modules: &[SemanticModule]) -> Result<(), DescriptorLoweringError> {
    let mut lexicals = BTreeMap::<&str, &LexicalSentence>::new();
    for lexical in modules.iter().flat_map(SemanticModule::lexicals) {
        if lexicals.insert(lexical.name(), lexical).is_some() {
            return Err(fail(
                LexicalProblem::Duplicate,
                lexical.origin(),
                format!(
                    "the lexical `{}` is declared more than once; K names lexicals in one namespace per definition, so rename one",
                    lexical.name()
                ),
            ));
        }
    }
    let undefined = |regex: &str, origin: &NodeOrigin, what: &str| {
        regex_references(regex)
            .into_iter()
            .find(|name| !lexicals.contains_key(name.as_str()))
            .map_or(Ok(()), |name| {
                Err(fail(
                    LexicalProblem::Undefined,
                    origin,
                    format!(
                        "the {what} regex {regex:?} refers to `{{{name}}}`, which no `k::lexical!` declares; declare it with `k::lexical! {{ {name} = r\"..\"; }}` or escape the brace as `\\{{`"
                    ),
                ))
            })
    };
    for module in modules {
        for lexical in module.lexicals() {
            undefined(lexical.regex(), lexical.origin(), "lexical")?;
        }
        for layout in module.layouts() {
            undefined(layout.regex(), layout.origin(), "layout")?;
        }
        for production in module.productions().iter().filter(|production| {
            production
                .attributes()
                .iter()
                .any(|attribute| matches!(attribute, ProductionAttribute::Token { .. }))
        }) {
            for item in production.items() {
                if let GrammarProductionItemKind::RegexTerminal {
                    precede_regex,
                    regex,
                    follow_regex,
                } = item.kind()
                {
                    for regex in precede_regex.iter().chain([regex]).chain(follow_regex) {
                        undefined(regex, production.origin(), "token")?;
                    }
                }
            }
        }
    }
    check_recursion(&lexicals)
}

/// Rejects a cycle among lexical references, reporting its first lexical in
/// name order.
fn check_recursion(
    lexicals: &BTreeMap<&str, &LexicalSentence>,
) -> Result<(), DescriptorLoweringError> {
    let edges = lexicals
        .iter()
        .map(|(name, lexical)| (*name, regex_references(lexical.regex())))
        .collect::<BTreeMap<_, _>>();
    let mut finished = BTreeSet::<&str>::new();
    for start in edges.keys() {
        let mut path = Vec::new();
        if let Some(cycle) = find_cycle(start, &edges, &mut path, &mut finished) {
            let lexical = lexicals[cycle[0].as_str()];
            return Err(fail(
                LexicalProblem::Recursive,
                lexical.origin(),
                format!(
                    "lexicals refer to each other in a cycle ({}); K expands `{{Name}}` references inline, so a lexical cannot reach itself",
                    cycle
                        .iter()
                        .map(|name| format!("`{name}`"))
                        .collect::<Vec<_>>()
                        .join(" -> ")
                ),
            ));
        }
    }
    Ok(())
}

fn find_cycle<'a>(
    name: &'a str,
    edges: &'a BTreeMap<&'a str, Vec<String>>,
    path: &mut Vec<&'a str>,
    finished: &mut BTreeSet<&'a str>,
) -> Option<Vec<String>> {
    if finished.contains(name) {
        return None;
    }
    if let Some(position) = path.iter().position(|entry| *entry == name) {
        let mut cycle = path[position..]
            .iter()
            .map(|entry| (*entry).to_owned())
            .collect::<Vec<_>>();
        cycle.push(name.to_owned());
        return Some(cycle);
    }
    let (key, references) = edges.get_key_value(name)?;
    path.push(key);
    for reference in references {
        if let Some(cycle) = find_cycle(reference, edges, path, finished) {
            return Some(cycle);
        }
    }
    path.pop();
    finished.insert(key);
    None
}

fn fail(problem: LexicalProblem, origin: &NodeOrigin, reason: String) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidLexical {
        problem,
        reason,
        range: origin.origin().exact_authored_range().map(Box::new),
    }
}
