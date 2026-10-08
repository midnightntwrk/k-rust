//! Alias reversal: `kore_pattern::expand_macros(.., reverse = true)` of the LLVM backend's `kprint`.
//!
//! Every application whose symbol heads the right-hand side of a macro axiom is matched, after its
//! arguments are expanded, against each `alias` and `alias-rec` axiom's right-hand side in
//! `macros.kore` order; the first match is replaced by the left-hand side, which is expanded again.
//! A non-recursive alias applies at most once on one such chain; `macro` and `macro-rec` axioms are
//! never reversed (K's macros are one-way).

use std::collections::{BTreeMap, BTreeSet};

use crate::data::{Macro, PrintData};
use crate::node::{App, Node, Sym};

/// How many times one chain of reversals may re-expand before it is reported as unbounded.
pub(crate) const REVERSAL_BOUND: usize = 4096;

pub(crate) struct Reverser<'a> {
    data: &'a PrintData,
    macros: &'a [Macro],
    symbols: BTreeSet<&'a str>,
    /// Set when a chain of reversals reached [`REVERSAL_BOUND`]: the symbol whose reversal was cut off.
    pub exceeded: Option<String>,
}

type Substitution = BTreeMap<String, Node>;

impl<'a> Reverser<'a> {
    pub fn new(data: &'a PrintData, macros: &'a [Macro]) -> Self {
        let symbols = macros
            .iter()
            .filter_map(|rule| rule.right.as_app().map(|app| app.sym.name.as_str()))
            .collect();
        Self {
            data,
            macros,
            symbols,
            exceeded: None,
        }
    }

    pub fn expand(&mut self, node: &Node) -> Node {
        self.expand_with(node, &mut BTreeSet::new(), 0)
    }

    fn expand_with(
        &mut self,
        node: &Node,
        applied_rules: &mut BTreeSet<usize>,
        depth: usize,
    ) -> Node {
        let Node::App(app) = node else {
            return node.clone();
        };
        let applied = Node::App(App {
            sym: app.sym.clone(),
            args: app
                .args
                .iter()
                .map(|argument| self.expand_with(argument, &mut BTreeSet::new(), 0))
                .collect(),
        });
        if !self.symbols.contains(app.sym.name.as_str()) {
            return applied;
        }
        for (index, rule) in self.macros.iter().enumerate() {
            if rule.one_way {
                continue;
            }
            let mut substitution = Substitution::new();
            if matches(self.data, &rule.right, &applied, &mut substitution)
                && (rule.recursive || !applied_rules.contains(&index))
            {
                if depth >= REVERSAL_BOUND {
                    self.exceeded.get_or_insert_with(|| app.sym.name.clone());
                    return applied;
                }
                let saved = applied_rules.clone();
                applied_rules.insert(index);
                let result = self.expand_with(
                    &substitute(&rule.left, &substitution),
                    applied_rules,
                    depth + 1,
                );
                *applied_rules = saved;
                return result;
            }
        }
        applied
    }
}

/// `kore_pattern::matches`: syntactic matching of `pattern` against `subject`, where an injection
/// matches an injection between related sorts and an overloaded symbol matches its overload.
fn matches(
    data: &PrintData,
    pattern: &Node,
    subject: &Node,
    substitution: &mut Substitution,
) -> bool {
    match pattern {
        Node::Var { name, .. } => {
            if let Some(bound) = substitution.get(name) {
                return bound.key() == subject.key();
            }
            substitution.insert(name.clone(), subject.clone());
            true
        }
        Node::Str(text) => matches!(subject, Node::Str(other) if other == text),
        Node::App(pattern_app) => {
            let Node::App(subject_app) = subject else {
                return false;
            };
            if subject_app.sym != pattern_app.sym {
                return mismatched_symbols(data, pattern_app, subject_app, substitution);
            }
            subject_app.args.len() == pattern_app.args.len()
                && pattern_app
                    .args
                    .iter()
                    .zip(&subject_app.args)
                    .all(|(pattern, subject)| matches(data, pattern, subject, substitution))
        }
    }
}

fn injection(from: &k_rust::kore::ast::Sort, to: &k_rust::kore::ast::Sort, argument: Node) -> Node {
    let mut sym = Sym::new("inj", vec![from.clone(), to.clone()]);
    sym.arguments = vec![from.clone()];
    Node::app(sym, vec![argument])
}

fn mismatched_symbols(
    data: &PrintData,
    pattern: &App,
    subject: &App,
    substitution: &mut Substitution,
) -> bool {
    if subject.sym.name == "inj" && pattern.sym.name == "inj" {
        let (Some(subject_to), Some(pattern_to)) =
            (subject.sym.formals.get(1), pattern.sym.formals.get(1))
        else {
            return false;
        };
        if subject_to != pattern_to {
            return false;
        }
        let (Some(a), Some(b)) = (subject.sym.formals.first(), pattern.sym.formals.first()) else {
            return false;
        };
        let (Some(pattern_child), Some(subject_child)) =
            (pattern.args.first(), subject.args.first())
        else {
            return false;
        };
        if data
            .subsorts
            .get(b)
            .is_some_and(|supersorts| supersorts.contains(a))
        {
            let narrowed = injection(b, a, pattern_child.clone());
            return matches(data, &narrowed, subject_child, substitution);
        }
        if data
            .subsorts
            .get(a)
            .is_some_and(|supersorts| supersorts.contains(b))
        {
            let widened = injection(a, b, subject_child.clone());
            return matches(data, pattern_child, &widened, substitution);
        }
        return false;
    }
    if subject.sym.name != "inj" {
        return false;
    }
    let Some(Node::App(child)) = subject.args.first() else {
        return false;
    };
    if !data
        .overloads
        .get(&child.sym.name)
        .is_some_and(|overloads| overloads.contains(&pattern.sym.name))
    {
        return false;
    }
    let mut greater = App {
        sym: pattern.sym.clone(),
        args: Vec::with_capacity(pattern.args.len()),
    };
    for index in 0..pattern.args.len() {
        let (Some(wide), Some(narrow), Some(argument)) = (
            pattern.sym.arguments.get(index),
            child.sym.arguments.get(index),
            child.args.get(index),
        ) else {
            return false;
        };
        if wide == narrow {
            greater.args.push(argument.clone());
        } else {
            greater.args.push(injection(narrow, wide, argument.clone()));
        }
    }
    matches(
        data,
        &Node::App(pattern.clone()),
        &Node::App(greater),
        substitution,
    )
}

/// `kore_pattern::substitute`: replace variables, leaving the binder of `\exists` and `\forall` alone.
fn substitute(node: &Node, substitution: &Substitution) -> Node {
    match node {
        Node::Var { name, .. } => substitution
            .get(name)
            .cloned()
            .unwrap_or_else(|| node.clone()),
        Node::Str(_) => node.clone(),
        Node::App(app) => {
            if app.args.is_empty() {
                return node.clone();
            }
            if matches!(app.sym.name.as_str(), "\\forall" | "\\exists")
                && let [Node::Var { name, .. }, body] = app.args.as_slice()
            {
                let mut inner = substitution.clone();
                inner.remove(name);
                return Node::App(App {
                    sym: app.sym.clone(),
                    args: vec![app.args[0].clone(), substitute(body, &inner)],
                });
            }
            Node::App(App {
                sym: app.sym.clone(),
                args: app
                    .args
                    .iter()
                    .map(|argument| substitute(argument, substitution))
                    .collect(),
            })
        }
    }
}
