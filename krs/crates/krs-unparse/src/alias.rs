//! Alias reversal: printing an alias's application where a term matches its clause's result.
//!
//! The arguments of every application are reversed first, each on a chain of its own. Then the
//! application, if its symbol heads the right-hand side of a macro axiom, is matched against each
//! `alias` and `alias-rec` axiom's right-hand side in `macros.kore` order, and the first that
//! reverses replaces it by its left-hand side under the match. A non-recursive alias applies at
//! most once on one chain; `macro` and `macro-rec` axioms are never reversed (a desugar is
//! one-way).
//!
//! A reversal is printed only if the printed alias application expands back to the term
//! ([`reversal`]):
//!
//! - every variable of the left-hand side must be bound, through the right-hand side's match or
//!   through a conjunction: a subterm the subject shares with the result reaches `macros.kore`
//!   conjoined with the variable the result names it by (`whole(box(\and(\dv("1"), V))) =
//!   tag(V)`), and the term at a conjunction must match every conjunct, so `tag(3)`, which gives
//!   `V` the value `3`, does not reverse there;
//! - the left-hand side under the match, matched against the clause's left-hand side, must give
//!   back the term through its right-hand side, compared by key but for the sort an injection at
//!   the root injects into (the position's): the reversal is verified by construction, for every
//!   shape of clause;
//! - a variable is bound only to a term of its sort, as expansion binds it.
//!
//! After a reversal only the nodes the left-hand side writes are reversed again, on the chain
//! that applied it: the values the match bound are already reversed. So a clause whose subject
//! writes a term its result matches (`fc(kk(1), x) => kk(x)`) prints `kk(5)` as `fc(kk(1), 5)`
//! and stops there.
//!
//! An axiom whose right-hand side is a variable is never reversed: emission writes a clause whose
//! subject holds its whole result (`cc(x, hold(x)) => hold(x)`) as `cc(X, \and(hold(X), W)) = W`,
//! whose right-hand side names no head and matches every term, so printing it would write every
//! term inside a larger one that holds it again.

use std::collections::{BTreeMap, BTreeSet};

use crate::data::{Macro, PrintData};
use crate::node::{App, BUILTINS, Node, Sym};
use k_rust::kore::ast::Sort;

/// How many reversals one chain may make before it is reported as unbounded and printed
/// unreversed.
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
        self.expand_with(node)
    }

    /// `node` with its arguments reversed, each on a chain of its own, and then itself.
    fn expand_with(&mut self, node: &Node) -> Node {
        let Node::App(app) = node else {
            return node.clone();
        };
        let applied = App {
            sym: app.sym.clone(),
            args: app
                .args
                .iter()
                .map(|argument| self.expand_with(argument))
                .collect(),
        };
        self.reverse(applied, &BTreeSet::new(), 0)
    }

    /// `applied`, whose arguments are reversed, replaced by the first reversal on the chain that
    /// applied `applied_rules` after `depth` reversals.
    fn reverse(&mut self, applied: App, applied_rules: &BTreeSet<usize>, depth: usize) -> Node {
        if !self.symbols.contains(applied.sym.name.as_str()) {
            return Node::App(applied);
        }
        let term = Node::App(applied);
        for (index, rule) in self.macros.iter().enumerate() {
            if rule.one_way || rule.right.as_app().is_none() {
                continue;
            }
            if !rule.recursive && applied_rules.contains(&index) {
                continue;
            }
            let Some(substitution) = reversal(self.data, rule, &term) else {
                continue;
            };
            if depth >= REVERSAL_BOUND {
                if let Node::App(app) = &term {
                    self.exceeded.get_or_insert_with(|| app.sym.name.clone());
                }
                return term;
            }
            let mut chain = applied_rules.clone();
            chain.insert(index);
            return self.written(&rule.left, &substitution, &chain, depth + 1);
        }
        term
    }

    /// The left-hand side `node` of a reversal under `substitution`, which [`reversal`] resolved:
    /// a variable's value as it is, since the match bound it to a reversed term, a conjunction's
    /// the value of a variable conjunct or else of its first conjunct, and each application the
    /// left-hand side writes rebuilt and reversed on `chain`.
    fn written(
        &mut self,
        node: &Node,
        substitution: &Substitution,
        chain: &BTreeSet<usize>,
        depth: usize,
    ) -> Node {
        match node {
            Node::Var { name, .. } => substitution
                .get(name)
                .cloned()
                .unwrap_or_else(|| node.clone()),
            Node::Str(_) => node.clone(),
            Node::App(app) if is_conjunction(app) => {
                let conjunct = app
                    .args
                    .iter()
                    .find(|conjunct| matches!(conjunct, Node::Var { .. }))
                    .unwrap_or(&app.args[0]);
                self.written(conjunct, substitution, chain, depth)
            }
            Node::App(app) if app.sym.name == "\\dv" => node.clone(),
            Node::App(app) => {
                let rebuilt = App {
                    sym: app.sym.clone(),
                    args: app
                        .args
                        .iter()
                        .map(|argument| self.written(argument, substitution, chain, depth))
                        .collect(),
                };
                self.reverse(rebuilt, chain, depth)
            }
        }
    }
}

/// The substitution under which `rule` reverses `term`, or `None` if its printed left-hand side
/// would not expand back to `term`.
///
/// 1. The right-hand side matches `term`.
/// 2. Every conjunction of the left-hand side is resolved, until none is left: once one of its
///    conjuncts has a value under the substitution, every conjunct must match that value, which
///    binds their other variables. A conjunction none of whose conjuncts gets a value, or whose
///    conjuncts differ, is no reversal.
/// 3. The left-hand side under the substitution must bind every variable and write only
///    symbols, conjunctions and domain values (no other connective has one term to print).
/// 4. Verification by construction: that term, matched against the left-hand side, must give
///    back `term` through the right-hand side.
fn reversal(data: &PrintData, rule: &Macro, term: &Node) -> Option<Substitution> {
    let mut substitution = Substitution::new();
    if !matches(data, &rule.right, term, &mut substitution) || !writable(&rule.left) {
        return None;
    }
    let mut pending = Vec::new();
    conjunctions(&rule.left, &mut pending);
    while !pending.is_empty() {
        let before = pending.len();
        let mut unresolved = Vec::new();
        for conjunction in pending {
            let Some(value) = conjunction
                .args
                .iter()
                .find_map(|conjunct| instantiate(conjunct, &substitution))
            else {
                unresolved.push(conjunction);
                continue;
            };
            if !conjunction
                .args
                .iter()
                .all(|conjunct| matches(data, conjunct, &value, &mut substitution))
            {
                return None;
            }
        }
        if unresolved.len() == before {
            return None;
        }
        pending = unresolved;
    }
    let reversed = instantiate(&rule.left, &substitution)?;
    let mut expansion = Substitution::new();
    if !matches(data, &rule.left, &reversed, &mut expansion) {
        return None;
    }
    let expanded = instantiate(&rule.right, &expansion)?;
    same_value(data, &expanded, term).then_some(substitution)
}

/// Whether `expanded` is `term`, compared by key, but for the sort an injection at the root
/// injects into: a reversal replaces the term at its position, which injects the printed alias
/// into the position's sort, so `zeroAlias = inj{Int, Exp}(0)` prints `inj{Int, KItem}(0)`, the
/// alias's sort `Exp` being one the position (`KItem`) admits. An alias of a sort the position
/// does not admit (`Stmt` where a `Value` stands) is no term there.
fn same_value(data: &PrintData, expanded: &Node, term: &Node) -> bool {
    if let (Node::App(left), Node::App(right)) = (expanded, term)
        && left.sym.name == "inj"
        && right.sym.name == "inj"
    {
        let admitted = match (left.sym.formals.get(1), right.sym.formals.get(1)) {
            (Some(alias), Some(position)) => data.less_than_eq(alias, position),
            _ => false,
        };
        return admitted
            && left.sym.formals.first() == right.sym.formals.first()
            && left.args.len() == right.args.len()
            && left
                .args
                .iter()
                .zip(&right.args)
                .all(|(left, right)| left.key() == right.key());
    }
    expanded.key() == term.key()
}

/// Whether `node` writes only variables, domain values, conjunctions and symbols' applications.
fn writable(node: &Node) -> bool {
    match node {
        Node::Var { .. } | Node::Str(_) => true,
        Node::App(app) => {
            (app.sym.name == "\\and"
                || app.sym.name == "\\dv"
                || !BUILTINS.contains(&app.sym.name.as_str()))
                && app.args.iter().all(writable)
        }
    }
}

/// The conjunctions of `node`, outermost first.
fn conjunctions<'n>(node: &'n Node, found: &mut Vec<&'n App>) {
    if let Node::App(app) = node {
        if is_conjunction(app) {
            found.push(app);
        }
        for argument in &app.args {
            conjunctions(argument, found);
        }
    }
}

/// `node` under `substitution`, `None` while a variable of it is unbound; a conjunction is the
/// value of its first conjunct that has one ([`reversal`] checks that the others agree).
fn instantiate(node: &Node, substitution: &Substitution) -> Option<Node> {
    match node {
        Node::Var { name, .. } => substitution.get(name).cloned(),
        Node::Str(_) => Some(node.clone()),
        Node::App(app) if is_conjunction(app) => app
            .args
            .iter()
            .find_map(|conjunct| instantiate(conjunct, substitution)),
        Node::App(app) => Some(Node::App(App {
            sym: app.sym.clone(),
            args: app
                .args
                .iter()
                .map(|argument| instantiate(argument, substitution))
                .collect::<Option<_>>()?,
        })),
    }
}

/// The sort of `node` where it states one: a variable's, an injection's target, a domain
/// value's, or an instantiated symbol's result.
fn sort_of(node: &Node) -> Option<&Sort> {
    match node {
        Node::Var { sort, .. } => Some(sort),
        Node::Str(_) => None,
        Node::App(app) => match app.sym.name.as_str() {
            "inj" => app.sym.formals.get(1),
            "\\dv" => app.sym.formals.first(),
            _ => app.sym.sort.as_ref(),
        },
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
        Node::Var { name, sort, .. } => {
            if let Some(bound) = substitution.get(name) {
                return bound.key() == subject.key();
            }
            // A variable binds a term of its sort or a subsort, as expansion binds it.
            if matches!(sort, Sort::Application { .. })
                && sort_of(subject)
                    .is_some_and(|subject_sort| !data.less_than_eq(subject_sort, sort))
            {
                return false;
            }
            substitution.insert(name.clone(), subject.clone());
            true
        }
        Node::Str(text) => matches!(subject, Node::Str(other) if other == text),
        Node::App(pattern_app) if is_conjunction(pattern_app) => pattern_app
            .args
            .iter()
            .all(|conjunct| matches(data, conjunct, subject, substitution)),
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

/// Whether `app` is a conjunction of patterns, `\and{S}(P, Q, ..)`: a term matches it when it
/// matches every conjunct.
fn is_conjunction(app: &App) -> bool {
    app.sym.name == "\\and" && !app.args.is_empty()
}
