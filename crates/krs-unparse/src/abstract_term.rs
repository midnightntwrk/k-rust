//! The term abstractions `kprint` applies before printing: binary `\and`/`\or`, sorted AC
//! collections, filtered substitutions, and deduplicated disjuncts.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use crate::data::PrintData;
use crate::format::{Problems, key_text, variable_text};
use crate::node::{App, Node, Sym};

/// `kore_composite_pattern::unflatten_and_or`: n-ary `\and` and `\or` become left-nested binary applications.
pub(crate) fn unflatten_and_or(node: &Node) -> Node {
    let Node::App(app) = node else {
        return node.clone();
    };
    let args = app.args.iter().map(unflatten_and_or).collect::<Vec<_>>();
    if matches!(app.sym.name.as_str(), "\\and" | "\\or") && args.len() != 2 && !args.is_empty() {
        let mut args = args.into_iter();
        let first = args.next().expect("arguments are not empty");
        return args.fold(first, |accumulated, argument| {
            Node::app(app.sym.clone(), vec![accumulated, argument])
        });
    }
    Node::app(app.sym.clone(), args)
}

/// `kllvm::flatten`: the arguments of nested applications of `name`, left to right.
fn flatten(app: &App, name: &str, items: &mut Vec<Node>) {
    for argument in &app.args {
        match argument {
            Node::App(child) if child.sym.name == name => flatten(child, name, items),
            _ => items.push(argument.clone()),
        }
    }
}

fn nest(sym: &Sym, items: Vec<Node>) -> Node {
    let mut items = items.into_iter();
    let first = items.next().expect("a flattened application has arguments");
    items.fold(first, |accumulated, item| {
        Node::app(sym.clone(), vec![accumulated, item])
    })
}

/// `kore_composite_pattern::sort_collections`: every associative-commutative application is
/// flattened and its items are ordered by their printed text (alphanumerically, so `x2` sorts before `x10`).
pub(crate) fn sort_collections(data: &PrintData, node: &Node, problems: &mut Problems) -> Node {
    let Node::App(app) = node else {
        return node.clone();
    };
    if app.args.is_empty() {
        return node.clone();
    }
    let name = app.sym.name.as_str();
    if data.comm.contains(name) && data.assoc.contains(name) {
        let mut items = Vec::new();
        flatten(app, name, &mut items);
        let mut printed = items
            .iter()
            .map(|item| {
                let item = sort_collections(data, item, problems);
                (key_text(data, &item, problems), item)
            })
            .collect::<Vec<_>>();
        printed.sort_by(|left, right| alphanumeric(&left.0, &right.0));
        return nest(
            &app.sym,
            printed.into_iter().map(|(_, item)| item).collect(),
        );
    }
    Node::app(
        app.sym.clone(),
        app.args
            .iter()
            .map(|argument| sort_collections(data, argument, problems))
            .collect(),
    )
}

/// `compare_first`: the alphanumeric order of `kprint`, which compares runs of digits by length, then digit by digit.
pub(crate) fn alphanumeric(left: &str, right: &str) -> Ordering {
    fn chunk(text: &[u8], start: usize) -> &[u8] {
        let digit = text[start].is_ascii_digit();
        let end = text[start..]
            .iter()
            .position(|byte| byte.is_ascii_digit() != digit)
            .map_or(text.len(), |offset| start + offset);
        &text[start..end]
    }
    let (left, right) = (left.as_bytes(), right.as_bytes());
    let (mut left_at, mut right_at) = (0, 0);
    while left_at < left.len() && right_at < right.len() {
        let left_chunk = chunk(left, left_at);
        let right_chunk = chunk(right, right_at);
        left_at += left_chunk.len();
        right_at += right_chunk.len();
        let order = if left_chunk[0].is_ascii_digit() && right_chunk[0].is_ascii_digit() {
            left_chunk
                .len()
                .cmp(&right_chunk.len())
                .then_with(|| left_chunk.cmp(right_chunk))
        } else {
            left_chunk.cmp(right_chunk)
        };
        if order != Ordering::Equal {
            return order;
        }
    }
    left.len().cmp(&right.len())
}

fn var_counts(node: &Node, counts: &mut BTreeMap<String, usize>) {
    match node {
        Node::Var { name, .. } => *counts.entry(name.clone()).or_default() += 1,
        Node::Str(_) => {}
        Node::App(app) => {
            for argument in &app.args {
                var_counts(argument, counts);
            }
        }
    }
}

/// `gather_singleton_vars`: the variables that occur exactly once.
pub(crate) fn singleton_vars(node: &Node) -> BTreeSet<String> {
    let mut counts = BTreeMap::new();
    var_counts(node, &mut counts);
    counts
        .into_iter()
        .filter(|(_, count)| *count == 1)
        .map(|(name, _)| name)
        .collect()
}

fn is_top(node: &Node) -> bool {
    matches!(node, Node::App(app) if app.sym.name == "\\top")
}

/// `filter_substitution`: an equation that binds an anonymous variable occurring nowhere else is dropped (`#Top`).
pub(crate) fn filter_substitution(
    data: &PrintData,
    node: &Node,
    vars: &BTreeSet<String>,
    problems: &mut Problems,
) -> Node {
    let Node::App(app) = node else {
        return node.clone();
    };
    match app.sym.name.as_str() {
        "\\equals" => {
            if let Some(variable @ Node::Var { name, .. }) = app.args.first() {
                let printed = variable_text(data, variable, problems);
                let bytes = printed.as_bytes();
                let anonymous = bytes.first() == Some(&b'_')
                    || (bytes.len() > 1
                        && matches!(bytes[0], b'@' | b'!' | b'?')
                        && bytes[1] == b'_');
                if vars.contains(name) && anonymous {
                    let sort = app.sym.formals.get(1).cloned();
                    return Node::app(Sym::new("\\top", sort.into_iter().collect()), Vec::new());
                }
            }
            node.clone()
        }
        "\\and" | "\\or" => {
            let args = app
                .args
                .iter()
                .map(|argument| {
                    if app.sym.name == "\\or" {
                        filter_substitution(data, argument, &singleton_vars(argument), problems)
                    } else {
                        filter_substitution(data, argument, vars, problems)
                    }
                })
                .collect::<Vec<_>>();
            if app.sym.name == "\\and"
                && let [first, second] = args.as_slice()
            {
                if is_top(first) {
                    return second.clone();
                }
                if is_top(second) {
                    return first.clone();
                }
            }
            Node::app(app.sym.clone(), args)
        }
        _ => node.clone(),
    }
}

/// `dedupe_disjuncts`: identical disjuncts of a top-level `\or` are printed once.
pub(crate) fn dedupe_disjuncts(node: &Node) -> Node {
    let Node::App(app) = node else {
        return node.clone();
    };
    if app.sym.name != "\\or" {
        return node.clone();
    }
    let mut items = Vec::new();
    flatten(app, "\\or", &mut items);
    let mut seen = BTreeSet::new();
    let items = items
        .into_iter()
        .filter(|item| seen.insert(item.key()))
        .collect::<Vec<_>>();
    nest(&app.sym, items)
}
