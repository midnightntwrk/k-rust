//! Whether an invariant excludes an obligation at a rewrite rule: the connection of an argued
//! obligation to the invariant its argument names ([`connection`]).
//!
//! # The question
//!
//! An obligation of a rewrite rule is a valuation of the rule at its left-hand side
//! ([`Valuation`]): the left-hand side matches (the rule's applicability), the `requires` holds or
//! is refuted (the rule's requirement outcome), or a node of the written `requires` is reached with
//! a truth. An invariant is a `Bool` function `F` of the definition over configuration cells
//! ([`Invariant`]), or none, which is `F ≡ true`. A compiled rewrite rule's left-hand side `L` is a
//! whole configuration, so each cell the invariant reads has one term `tᵢ` there, at the cell's
//! KORE path. The connection asks whether
//!
//! ```text
//! F(t₁, …, tₙ) = true  ∧  V
//! ```
//!
//! is unsatisfiable, where `V` is the valuation over `L`'s variables. Every state that `L` matches
//! is an instance of `L` under some valuation of its variables, and there the cells hold the
//! instances of the `tᵢ` and the obligation holds exactly where `V` does. So when the predicate
//! has no model, no state that `L` matches and that satisfies `F` has the obligation: wherever `F`
//! holds, the obligation is out of reach at this rule ([`Connection::Connected`]). An axiom
//! compiled to several rules (the alternatives of a disjunctive left-hand side) is connected when
//! every one of its rules is: the obligation is reached where any of them is.
//!
//! # The valuation of a reached node
//!
//! A node of the written `requires` is named by its path as k-rust's guard skeletons name it
//! (`k_rust_backend::coverage::GuardNode::path`): the conjunct's index, then the index of each
//! operand on the way down. The node counts for an entry only where it is reached, in written
//! order (`k_rust_backend::coverage` guards, "Reached outcomes"): an operand of a conjunction
//! where every operand before it is true, an operand of a disjunction where every operand before
//! it is false, the right operand of an implication where its left one is true, and the operand of
//! a negation, an `xorBool`, an `\iff` and an `\equals(b, literal)` where its node is. So the
//! valuation of a node with a truth is the conjunction of the node's truth with every truth on the
//! way from the root that reaches it. A `Bool` node is true or false where it is defined and has
//! that value (`\equals(b, true)`, `\equals(b, false)`); a predicate node is false where it does
//! not hold. Conditions of the rule's application that the valuation leaves out (a higher priority
//! rule's applicability, for one) only add models, which can make the answer undecided, never a
//! false connection.
//!
//! # How the answer is decided
//!
//! The predicate is simplified with the definition's equations and decided by the backend's
//! solver (`simplify_and_decide_predicate_with_solver`, on the proof route, which evaluates only
//! consequences of the definition). Simplification preserves the predicate's meaning, so a
//! predicate simplified to `\bottom` has no model. Where a residual is left, the solver is asked
//! for its satisfiability, and its `Unsat` refutes the predicate whatever form it has (kink's
//! trust-base item T-UNSAT, [`crate::feasibility`]): k-rust's solver reads each atom with its
//! operands' definedness, and a subterm it abstracts to a fresh constant only adds models.
//! Nothing else connects.
//!
//! The answer is [`Connection::NotConnected`] only with a state that shows it: a predicate
//! decided valid, or a solver `Sat` for a residual whose translation is exact
//! (`smt::translation_exactness`), at a left-hand side built only from free constructors,
//! injections, domain values and element variables of inhabited sorts (a cell the rule binds to a
//! variable, `\and(t, X)`, read as `t`), so that every valuation of its variables gives an
//! instance of it. The valuation of the model (any valuation, for a valid predicate) then gives
//! such a state, matched by `L`, where `F` holds and the obligation does. A left-hand side with a
//! builtin collection is no such term (its instances need the collection's keys distinct), so
//! there a satisfiable predicate is [`Undecided::InstancesUnshown`]. Every other outcome is
//! [`Connection::Undecided`] with its cause. Each `Unknown` the solver answers is counted in the
//! caller's counter, as the leaf questions of [`crate::feasibility`] are: that of this module's
//! satisfiability question, and each the simplification reports (its `UndecidedPredicate` and
//! `UndecidedCondition` diagnostics, for the residual it decides and the equation conditions it
//! leaves open).
//!
//! The whole decision, the simplification and every solver question, runs on the proof route
//! whatever evaluation mode the caller is in: an answer never rests on a value the definition
//! leaves to the implementation.
//!
//! # The rules that step where a rule matches
//!
//! A step at a state is taken by a rule whose left-hand side matches the state, so at a state
//! where a rule's left-hand side `L` matches, every rule that takes a step has a left-hand side
//! that matches it too, and the two left-hand sides have a common instance. [`stepping_rules`]
//! gives the rules whose left-hand side unifies with `L` under kink's may-follow abstraction
//! (`crate::coverage::may_follow`: every function application, builtin value, collection and
//! conjunction read as a fresh variable, each variable occurrence as its own), which only drops
//! constraints: it contains every rule that can step at such a state, and may contain others.
//!
//! # Evaluation at a state
//!
//! [`evaluate`] gives the value of the invariant's function at one state, from the cells it
//! reads, applied as the connection applies it ([`Invariant::cells`]), and evaluated with the
//! definition's equations on the proof route with no solver ([`evaluate_configuration`] first
//! evaluates a whole configuration, a program's initial one, to the term its cells are read
//! from). The value is decided only where the evaluation ends at a ground `true` or `false` with
//! no condition left: simplification preserves the term's meaning, so the function then has that
//! value at every instance of the state. Every other outcome, a residual, a condition left open,
//! a spent budget or a stop, leaves the value unknown.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use k_rust::kore::ast::Pattern as KorePattern;
use k_rust::names::BuiltinSort;
use k_rust_backend::coverage::Connective;
use k_rust_backend::definition::BackendDefinition;
use k_rust_backend::diagnostic::{self, BackendDiagnostic};
use k_rust_backend::evaluation::{EvaluationMode, with_evaluation};
use k_rust_backend::rule::{Predicate, RewriteRule};
use k_rust_backend::simplify::{
    self, ConditionIndeterminacy, SimplificationOptions, simplify_and_decide_predicate_with_solver,
};
use k_rust_backend::smt::{Satisfiability, SmtError, SmtSolver};
use k_rust_backend::substitution::Substitution;
use k_rust_backend::term::{Symbol, SymbolType, Term, TermKind, Variable, VariableKind};

use crate::coverage::unifies;
use crate::feasibility::{Inhabitation, constructor_term, translates_exactly};

/// An invariant over configuration cells: a `Bool` function of the definition, applied to the
/// cells it reads, in parameter order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Invariant<'a> {
    /// The function's KORE symbol.
    pub symbol: &'a str,
    /// Each cell, as the KORE cell symbols from the configuration's top cell down to it
    /// (`path[0]` is the configuration's own symbol), the path k-rust's stop arrivals read a cell
    /// at. The argument is the cell itself where the parameter's sort is the cell's sort, and
    /// otherwise the cell's content (its one argument, injected into the parameter's sort where
    /// it is of a subsort).
    pub cells: &'a [Vec<String>],
}

/// The valuation of a rewrite rule that an obligation states, over the rule's left-hand side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Valuation<'a> {
    /// The left-hand side matches: the predicate `true`, so the connection is that of the
    /// left-hand side and the invariant alone.
    Matches,
    /// The `requires` holds: the conjunction of its conjuncts as written. A rule fires only where
    /// this holds, so this is also the valuation of a rule's firing.
    Held,
    /// The `requires` is refuted: the negation of that conjunction.
    Refuted,
    /// The node at `path` of the written `requires` is reached with `truth` (module
    /// documentation, "The valuation of a reached node").
    Reached {
        /// The node's path: the conjunct's index, then each operand's index on the way down.
        path: &'a [u32],
        /// The node's truth.
        truth: bool,
    },
}

/// Whether the invariant excludes the obligation at the rule.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Connection {
    /// The invariant and the valuation have no model at the left-hand side: no state the rule
    /// matches and the invariant holds of has the obligation.
    Connected,
    /// A state the rule matches satisfies the invariant and has the obligation.
    NotConnected,
    /// Neither was shown.
    Undecided(Undecided),
}

/// Why a connection is undecided.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Undecided {
    /// Simplification left a residual and the build has no solver.
    NoSolver,
    /// The solver did not decide the residual within its bounds; the payload is its reason.
    SolverUnknown(String),
    /// The solver answered nothing about the residual (it could not translate it, or it failed);
    /// the payload is why.
    Solver(String),
    /// The solver found a model of a residual whose translation is approximate, which shows no
    /// state.
    Inexact,
    /// The predicate is satisfiable, but the left-hand side is not shown to have an instance
    /// under every valuation of its variables (it holds a builtin collection, a function
    /// application, or a variable of a sort with no value shown).
    InstancesUnshown,
    /// The simplification failed; the payload is why.
    Simplification(String),
    /// A stop ended the simplification or the solver's work.
    Stopped,
}

impl fmt::Display for Undecided {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoSolver => formatter.write_str("no solver decides the simplified predicate"),
            Self::SolverUnknown(reason) => {
                write!(formatter, "the solver answered unknown: {reason}")
            }
            Self::Solver(reason) => write!(formatter, "the solver answered nothing: {reason}"),
            Self::Inexact => formatter.write_str(
                "the solver found a model of an approximate translation, which shows no state",
            ),
            Self::InstancesUnshown => formatter.write_str(
                "the predicate is satisfiable, but the left-hand side is not shown to have an \
                 instance at its model",
            ),
            Self::Simplification(reason) => {
                write!(formatter, "the simplification failed: {reason}")
            }
            Self::Stopped => formatter.write_str("a stop ended the decision"),
        }
    }
}

/// Why no connection question can be asked.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Refusal {
    /// No rewrite rule of the definition has the axiom's `UNIQUE_ID`.
    NoRule(String),
    /// The `requires` has no node at the path.
    NoNode(Vec<u32>),
    /// The definition declares no such symbol.
    UnknownSymbol(String),
    /// The symbol is not a function with a `Bool` result and no sort parameters.
    NotBoolFunction(String),
    /// The function takes another number of arguments than the cells given.
    Arity {
        symbol: String,
        parameters: usize,
        cells: usize,
    },
    /// The left-hand side holds no cell at the path.
    NoCell(Vec<String>),
    /// Neither the cell nor its content has the parameter's sort or a subsort of it.
    CellSort {
        cell: Vec<String>,
        parameter: String,
    },
}

impl fmt::Display for Refusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoRule(axiom) => write!(formatter, "no rewrite rule has the id {axiom}"),
            Self::NoNode(path) => write!(formatter, "the requires has no node at {path:?}"),
            Self::UnknownSymbol(symbol) => {
                write!(formatter, "the definition declares no symbol {symbol}")
            }
            Self::NotBoolFunction(symbol) => write!(
                formatter,
                "{symbol} is not a function of result sort Bool without sort parameters"
            ),
            Self::Arity {
                symbol,
                parameters,
                cells,
            } => write!(
                formatter,
                "{symbol} takes {parameters} arguments, and {cells} cells are given"
            ),
            Self::NoCell(path) => {
                write!(formatter, "the left-hand side holds no cell at {path:?}")
            }
            Self::CellSort { cell, parameter } => write!(
                formatter,
                "neither the cell at {cell:?} nor its content is of the parameter's sort \
                 {parameter}"
            ),
        }
    }
}

impl std::error::Error for Refusal {}

/// Whether `invariant` (none: `true`) excludes `valuation` at every rewrite rule of `definition`
/// whose `UNIQUE_ID` is `axiom` (module documentation), decided with `solver`; each `Unknown` the
/// solver answers adds one to `undecided`.
///
/// One rule not connected makes the axiom not connected; otherwise one undecided rule makes it
/// undecided, with the first such rule's cause in the rewrite theory's order
/// ([`rule_connections`] gives each rule's answer).
///
/// # Errors
///
/// A [`Refusal`] when no rule has the id, or when the valuation or the invariant cannot be read at
/// one of its rules.
pub fn connection(
    definition: &BackendDefinition,
    solver: &dyn SmtSolver,
    axiom: &str,
    valuation: Valuation<'_>,
    invariant: Option<Invariant<'_>>,
    undecided: &Cell<usize>,
) -> Result<Connection, Refusal> {
    Ok(combined(rule_connections(
        definition, solver, axiom, valuation, invariant, undecided,
    )?))
}

/// The answer of [`connection`] from the answers of an axiom's rules: not connected where one
/// is, else undecided with the first undecided cause, else connected.
#[must_use]
pub fn combined(answers: Vec<Connection>) -> Connection {
    let mut first_undecided = None;
    for answer in answers {
        match answer {
            Connection::Connected => {}
            Connection::NotConnected => return Connection::NotConnected,
            Connection::Undecided(cause) => {
                first_undecided.get_or_insert(cause);
            }
        }
    }
    first_undecided.map_or(Connection::Connected, Connection::Undecided)
}

/// The answer of [`connection`] at each rewrite rule of `definition` whose `UNIQUE_ID` is
/// `axiom`, in the rewrite theory's order, up to and including the first rule not connected,
/// which decides the axiom: a caller that keeps an answer can judge each rule's apart.
///
/// # Errors
///
/// As [`connection`].
pub fn rule_connections(
    definition: &BackendDefinition,
    solver: &dyn SmtSolver,
    axiom: &str,
    valuation: Valuation<'_>,
    invariant: Option<Invariant<'_>>,
    undecided: &Cell<usize>,
) -> Result<Vec<Connection>, Refusal> {
    let rules = definition
        .rewrite_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
        .filter(|rule| rule.rule.attributes.unique_id == axiom)
        .map(|rule| Arc::clone(&rule.rule))
        .collect::<Vec<_>>();
    if rules.is_empty() {
        return Err(Refusal::NoRule(axiom.to_owned()));
    }
    let inhabitation = Inhabitation::of(definition);
    let mut answers = Vec::new();
    for rule in &rules {
        let question = question(definition, rule, valuation, invariant)?;
        let answer = decide(
            definition,
            solver,
            &inhabitation,
            &rule.lhs,
            &question,
            undecided,
        );
        let decides = answer == Connection::NotConnected;
        answers.push(answer);
        if decides {
            break;
        }
    }
    Ok(answers)
}

/// `F(t₁, …, tₙ) = true ∧ V` for `rule` (module documentation).
fn question(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    valuation: Valuation<'_>,
    invariant: Option<Invariant<'_>>,
) -> Result<Predicate, Refusal> {
    let requires = rule.requires.iter().cloned().collect::<Vec<_>>();
    let valuation = match valuation {
        Valuation::Matches => Predicate::True,
        Valuation::Held => conjunction(requires),
        Valuation::Refuted => Predicate::Not(Arc::new(conjunction(requires))),
        Valuation::Reached { path, truth } => reached(&requires, path, truth)?,
    };
    let Some(invariant) = invariant else {
        return Ok(valuation);
    };
    let holds = Predicate::Equals(applied(definition, &rule.lhs, invariant)?, Term::bool(true));
    Ok(conjunction(vec![holds, valuation]))
}

/// The conjunction of `predicates`: `true` for none, the predicate itself for one.
fn conjunction(mut predicates: Vec<Predicate>) -> Predicate {
    match predicates.len() {
        0 => Predicate::True,
        1 => predicates.pop().unwrap_or(Predicate::True),
        _ => Predicate::And(predicates.into()),
    }
}

/// `invariant`'s function applied to its cells' terms in `lhs`.
fn applied(
    definition: &BackendDefinition,
    lhs: &Term,
    invariant: Invariant<'_>,
) -> Result<Term, Refusal> {
    applied_to(definition, invariant, |path| cell_term(lhs, path))
}

/// `invariant`'s function applied to the cells `cell` gives, by path: the argument is the cell
/// itself where the parameter's sort is the cell's sort, and otherwise its content, injected into
/// the parameter's sort where it is of a subsort ([`Invariant::cells`]).
fn applied_to<'t>(
    definition: &BackendDefinition,
    invariant: Invariant<'_>,
    cell: impl Fn(&[String]) -> Option<&'t Term>,
) -> Result<Term, Refusal> {
    let symbol = definition
        .symbols()
        .get(invariant.symbol)
        .ok_or_else(|| Refusal::UnknownSymbol(invariant.symbol.to_owned()))?;
    if !bool_function(symbol) {
        return Err(Refusal::NotBoolFunction(invariant.symbol.to_owned()));
    }
    if symbol.argument_sorts.len() != invariant.cells.len() {
        return Err(Refusal::Arity {
            symbol: invariant.symbol.to_owned(),
            parameters: symbol.argument_sorts.len(),
            cells: invariant.cells.len(),
        });
    }
    let arguments = invariant
        .cells
        .iter()
        .zip(&symbol.argument_sorts)
        .map(|(path, parameter)| {
            let cell = cell(path).ok_or_else(|| Refusal::NoCell(path.clone()))?;
            if cell.sort() == *parameter {
                return Ok(cell.clone());
            }
            if let TermKind::Application { arguments, .. } = cell.kind()
                && let [content] = arguments.as_slice()
            {
                let content = bound(content);
                let sort = content.sort();
                if sort == *parameter {
                    return Ok(content.clone());
                }
                if definition
                    .sort_graph()
                    .check_subsort(&sort, parameter)
                    .unwrap_or(false)
                {
                    return Ok(Term::injection(sort, *parameter, content.clone()));
                }
            }
            Err(Refusal::CellSort {
                cell: path.clone(),
                parameter: parameter.name().to_string(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Term::application(Arc::clone(symbol), Vec::new(), arguments))
}

/// `term` with a binding conjunction at its root, `\and(t, X)` or `\and(X, t)` of a variable `X`,
/// read as `t`: a left-hand side writes a cell's content so where it names the content and binds it
/// (`<a> (0 #Or 1) </a>` binds each alternative to a variable). Where the conjunction is defined,
/// which it is at every state the left-hand side matches, `t` denotes the element it denotes, and
/// `t` says more of it than `X`.
fn bound(term: &Term) -> &Term {
    match term.kind() {
        TermKind::And(left, right) if matches!(right.kind(), TermKind::Variable(_)) => bound(left),
        TermKind::And(left, right) if matches!(left.kind(), TermKind::Variable(_)) => bound(right),
        _ => term,
    }
}

/// Whether `symbol` is a function of result sort `Bool` without sort parameters.
fn bool_function(symbol: &Symbol) -> bool {
    matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
        && symbol.sort_variables.is_empty()
        && symbol.result_sort.is_builtin(BuiltinSort::Bool)
}

/// The cell at `path` of `term`: `path[0]` is `term`'s own symbol, and each further symbol that of
/// a cell the previous one holds as a direct argument.
///
/// A left-hand side names a cell it binds as a conjunction of the cell and a variable
/// (`\and(<memory>(…), Gen)`), so a cell is the conjunct of an argument that applies the cell's
/// symbol. Where the conjunction is defined, which it is at every state the left-hand side
/// matches, each of its conjuncts denotes the one element it denotes, so the cell's conjunct is
/// the cell.
fn cell_term<'t>(term: &'t Term, path: &[String]) -> Option<&'t Term> {
    let (first, below) = path.split_first()?;
    let mut current = applying(term, first)?;
    for name in below {
        let TermKind::Application { arguments, .. } = current.kind() else {
            return None;
        };
        current = arguments
            .iter()
            .find_map(|argument| applying(argument, name))?;
    }
    Some(current)
}

/// The conjunct of `term` (itself, where it is no conjunction) that applies `symbol`.
fn applying<'t>(term: &'t Term, symbol: &str) -> Option<&'t Term> {
    match term.kind() {
        TermKind::Application { symbol: head, .. } if head.name.as_ref() == symbol => Some(term),
        TermKind::And(left, right) => applying(left, symbol).or_else(|| applying(right, symbol)),
        _ => None,
    }
}

/// A node of the written `requires`, as k-rust's guard skeletons read it: a predicate, or a `Bool`
/// term.
#[derive(Clone, Copy)]
enum Node<'p> {
    Predicate(&'p Predicate),
    Boolean(&'p Term),
}

/// The valuation of the node at `path` of `requires` reached with `truth` (module documentation,
/// "The valuation of a reached node").
fn reached(requires: &[Predicate], path: &[u32], truth: bool) -> Result<Predicate, Refusal> {
    let no_node = || Refusal::NoNode(path.to_vec());
    let (&first, below) = path.split_first().ok_or_else(no_node)?;
    let first = usize::try_from(first).map_err(|_| no_node())?;
    let mut conditions = requires.get(..first).ok_or_else(no_node)?.to_vec();
    let mut node = Node::Predicate(requires.get(first).ok_or_else(no_node)?);
    for &index in below {
        let index = usize::try_from(index).map_err(|_| no_node())?;
        node = operand(node, index, &mut conditions).ok_or_else(no_node)?;
    }
    conditions.push(match node {
        Node::Predicate(predicate) if truth => predicate.clone(),
        Node::Predicate(predicate) => Predicate::Not(Arc::new(predicate.clone())),
        Node::Boolean(term) => Predicate::Equals(term.clone(), Term::bool(truth)),
    });
    Ok(conjunction(conditions))
}

/// The operand `index` of `node`, with the truths that reach it from `node` pushed onto
/// `conditions`; `None` where `node` has no such operand.
fn operand<'p>(node: Node<'p>, index: usize, conditions: &mut Vec<Predicate>) -> Option<Node<'p>> {
    let boolean = |term: &Term, value: bool| Predicate::Equals(term.clone(), Term::bool(value));
    match node {
        Node::Predicate(predicate) => match predicate {
            Predicate::Equals(left, right) => {
                // `\equals(b, literal)` of a Boolean `b`, the literal on either side, as the
                // skeleton reads it; any other equality is an atom.
                let operand = [(right, left), (left, right)]
                    .into_iter()
                    .find(|(literal, operand)| {
                        is_boolean(operand)
                            && (**literal == Term::bool(true) || **literal == Term::bool(false))
                    })
                    .map(|(_, operand)| operand)?;
                (index == 0).then_some(Node::Boolean(operand))
            }
            Predicate::Term(term) => (index == 0).then_some(Node::Boolean(term)),
            Predicate::Not(inner) => (index == 0).then_some(Node::Predicate(inner)),
            Predicate::And(operands) => {
                let chosen = operands.get(index)?;
                conditions.extend(operands[..index].iter().cloned());
                Some(Node::Predicate(chosen))
            }
            Predicate::Or(operands) => {
                let chosen = operands.get(index)?;
                conditions.extend(
                    operands[..index]
                        .iter()
                        .map(|operand| Predicate::Not(Arc::new(operand.clone()))),
                );
                Some(Node::Predicate(chosen))
            }
            Predicate::Implies(left, right) => match index {
                0 => Some(Node::Predicate(left)),
                1 => {
                    conditions.push((**left).clone());
                    Some(Node::Predicate(right))
                }
                _ => None,
            },
            Predicate::Iff(left, right) => match index {
                0 => Some(Node::Predicate(left)),
                1 => Some(Node::Predicate(right)),
                _ => None,
            },
            _ => None,
        },
        Node::Boolean(term) => {
            let TermKind::Application {
                symbol, arguments, ..
            } = term.kind()
            else {
                return None;
            };
            let connective = connective(symbol)?;
            let chosen = arguments.get(index)?;
            let before = &arguments[..index];
            match connective {
                Connective::AndBool | Connective::AndThenBool => {
                    conditions.extend(before.iter().map(|operand| boolean(operand, true)));
                }
                Connective::OrBool | Connective::OrElseBool => {
                    conditions.extend(before.iter().map(|operand| boolean(operand, false)));
                }
                Connective::ImpliesBool => {
                    conditions.extend(before.iter().map(|operand| boolean(operand, true)));
                }
                _ => {}
            }
            Some(Node::Boolean(chosen))
        }
    }
}

/// The Boolean connective `symbol` is hooked to, as k-rust's guard skeletons recognize it.
fn connective(symbol: &Symbol) -> Option<Connective> {
    match symbol.attributes.hook.as_deref()? {
        "BOOL.not" => Some(Connective::NotBool),
        "BOOL.and" => Some(Connective::AndBool),
        "BOOL.andThen" => Some(Connective::AndThenBool),
        "BOOL.or" => Some(Connective::OrBool),
        "BOOL.orElse" => Some(Connective::OrElseBool),
        "BOOL.implies" => Some(Connective::ImpliesBool),
        "BOOL.xor" => Some(Connective::XorBool),
        _ => None,
    }
}

fn is_boolean(term: &Term) -> bool {
    term.sort().is_builtin(BuiltinSort::Bool)
}

/// Whether every valuation of `question`'s variables that values `lhs`'s variables over their
/// sorts extends to an instance of `lhs`: `lhs` with each binding conjunction `\and(t, X)` read as
/// `t` is built only from free constructors, injections, domain values and element variables of
/// inhabited sorts ([`constructor_term`]), where `X` is an element variable of `t`'s sort that
/// occurs once in `lhs` and not in `question`. Such an `X` takes the value of `t` under the
/// valuation, which makes the conjunction denote that value, and no other part of the question
/// constrains it.
fn instances(lhs: &Term, question: &Predicate, inhabitation: &Inhabitation) -> bool {
    let mut occurrences = BTreeMap::<Variable, usize>::new();
    count(lhs, &mut occurrences);
    let fixed = question.free_variables();
    let alias = |term: &Term, of: &Term| match term.kind() {
        TermKind::Variable(variable) => {
            variable.kind == VariableKind::Element
                && variable.sort == of.sort()
                && occurrences.get(variable) == Some(&1)
                && !fixed.contains(variable)
        }
        _ => false,
    };
    dealiased(lhs, &alias).is_some_and(|term| constructor_term(&term, inhabitation))
}

/// The number of occurrences of each variable in `term`.
fn count(term: &Term, occurrences: &mut BTreeMap<Variable, usize>) {
    match term.kind() {
        TermKind::Variable(variable) => *occurrences.entry(variable.clone()).or_default() += 1,
        TermKind::DomainValue { .. } => {}
        TermKind::Injection { term, .. } => count(term, occurrences),
        TermKind::And(left, right) => {
            count(left, occurrences);
            count(right, occurrences);
        }
        TermKind::Application { arguments, .. } => {
            for argument in arguments {
                count(argument, occurrences);
            }
        }
        // A collection makes `instances` false whatever it holds.
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. } => {}
    }
}

/// `term` with each conjunction `\and(t, X)` or `\and(X, t)` where `alias(X, t)` read as `t`;
/// `None` where it has another conjunction. A left-hand side is as deep as its author wrote it, so
/// the recursion is bounded by the definition, not by a run.
fn dealiased(term: &Term, alias: &impl Fn(&Term, &Term) -> bool) -> Option<Term> {
    Some(match term.kind() {
        TermKind::And(left, right) if alias(right, left) => dealiased(left, alias)?,
        TermKind::And(left, right) if alias(left, right) => dealiased(right, alias)?,
        TermKind::And(..) => return None,
        TermKind::Injection {
            source,
            target,
            term,
        } => Term::injection(*source, *target, dealiased(term, alias)?),
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => Term::application(
            Arc::clone(symbol),
            *sort_arguments,
            arguments
                .iter()
                .map(|argument| dealiased(argument, alias))
                .collect::<Option<Vec<_>>>()?,
        ),
        TermKind::Variable(_)
        | TermKind::DomainValue { .. }
        | TermKind::Map { .. }
        | TermKind::List { .. }
        | TermKind::Set { .. } => term.clone(),
    })
}

/// The connection of `question` at the left-hand side `lhs` (module documentation, "How the
/// answer is decided").
///
/// The whole decision runs on the proof route, the solver's questions included: the solver reads
/// a hook whose value the definition leaves to the implementation by the evaluation mode it is
/// asked in, so a question asked in an execution's scope could rest on k-rust's chosen value,
/// which is no consequence of the definition. Whatever scope the caller is in, the answer is the
/// definition's.
fn decide(
    definition: &BackendDefinition,
    solver: &dyn SmtSolver,
    inhabitation: &Inhabitation,
    lhs: &Term,
    question: &Predicate,
    undecided: &Cell<usize>,
) -> Connection {
    with_evaluation(EvaluationMode::Proof, || {
        decide_on_the_proof_route(definition, solver, inhabitation, lhs, question, undecided)
    })
}

/// The work of [`decide`], which runs it on the proof route.
fn decide_on_the_proof_route(
    definition: &BackendDefinition,
    solver: &dyn SmtSolver,
    inhabitation: &Inhabitation,
    lhs: &Term,
    question: &Predicate,
    undecided: &Cell<usize>,
) -> Connection {
    let count = || undecided.set(undecided.get().saturating_add(1));
    let shown = |connection: Connection| {
        if instances(lhs, question, inhabitation) {
            connection
        } else {
            Connection::Undecided(Undecided::InstancesUnshown)
        }
    };
    // The simplification asks the solver itself (its residual's decision, and the conditions of
    // the equations it applies) and reports an `Unknown` it keeps the subject of only as an
    // `UndecidedPredicate` or `UndecidedCondition` diagnostic, each counted here. The diagnostics
    // still reach the caller's collector (`diagnostic::collect` forwards them).
    let (simplified, diagnostics) = diagnostic::collect(|| {
        simplify_and_decide_predicate_with_solver(
            definition,
            question,
            &[],
            SimplificationOptions::default(),
            solver,
        )
    });
    for diagnostic in &diagnostics {
        if let BackendDiagnostic::UndecidedPredicate {
            reason: ConditionIndeterminacy::SmtUnknown(_),
            ..
        }
        | BackendDiagnostic::UndecidedCondition {
            reason: ConditionIndeterminacy::SmtUnknown(_),
            ..
        } = diagnostic
        {
            count();
        }
    }
    let residual = match simplified {
        Err(stop) => {
            stop.forgo_refinement();
            return Connection::Undecided(Undecided::Stopped);
        }
        Ok(Err(error)) => {
            return Connection::Undecided(Undecided::Simplification(error.to_string()));
        }
        Ok(Ok(Predicate::False)) => return Connection::Connected,
        Ok(Ok(Predicate::True)) => return shown(Connection::NotConnected),
        Ok(Ok(residual)) => residual,
    };
    let query = [residual];
    match solver.is_sat(&query, &Substitution::new()) {
        Err(stop) => {
            stop.forgo_refinement();
            Connection::Undecided(Undecided::Stopped)
        }
        Ok(Ok(Satisfiability::Unsat)) => Connection::Connected,
        Ok(Ok(Satisfiability::Sat)) if translates_exactly(&query) => {
            shown(Connection::NotConnected)
        }
        Ok(Ok(Satisfiability::Sat)) => Connection::Undecided(Undecided::Inexact),
        Ok(Ok(Satisfiability::Unknown(reason))) => {
            count();
            Connection::Undecided(Undecided::SolverUnknown(reason))
        }
        Ok(Err(SmtError::Unavailable)) => Connection::Undecided(Undecided::NoSolver),
        Ok(Err(error)) => Connection::Undecided(Undecided::Solver(error.to_string())),
    }
}

/// A rewrite rule of the definition that can take a step at a state where a given rule matches
/// ([`stepping_rules`]): its `UNIQUE_ID` and its label, where it has one.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SteppingRule {
    pub unique_id: String,
    pub label: Option<String>,
}

/// The rewrite rules of `definition` whose left-hand side unifies with the left-hand side of a
/// rule whose `UNIQUE_ID` is one of `axioms` (module documentation, "The rules that step where a
/// rule matches"), in `UNIQUE_ID` order, each once; the rules of `axioms` are among them.
///
/// # Errors
///
/// [`Refusal::NoRule`] for an id no rewrite rule has.
pub fn stepping_rules(
    definition: &BackendDefinition,
    axioms: &BTreeSet<String>,
) -> Result<Vec<SteppingRule>, Refusal> {
    let rules = definition
        .rewrite_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
        .map(|rule| &rule.rule)
        .collect::<Vec<_>>();
    let mut sides = Vec::new();
    for axiom in axioms {
        let before = sides.len();
        sides.extend(
            rules
                .iter()
                .filter(|rule| rule.attributes.unique_id == *axiom)
                .map(|rule| &rule.lhs),
        );
        if sides.len() == before {
            return Err(Refusal::NoRule(axiom.clone()));
        }
    }
    let graph = definition.sort_graph();
    let stepping = rules
        .iter()
        .filter(|rule| sides.iter().any(|lhs| unifies(&rule.lhs, lhs, graph)))
        .map(|rule| SteppingRule {
            unique_id: rule.attributes.unique_id.clone(),
            label: rule.attributes.label.clone(),
        })
        .collect::<BTreeSet<_>>();
    Ok(stepping.into_iter().collect())
}

/// The value of `invariant`'s function at a state whose cells are `cells`, the KORE of each cell
/// the invariant reads, in order (the cell's own application, as k-rust's probe states read it at
/// the cell's path), evaluated in `definition` (module documentation, "Evaluation at a state").
///
/// # Errors
///
/// Why the value is not known there: a cell that is no term of the definition, a stack the host
/// does not give or a pattern too deep for the largest one, or an evaluation that does not end at
/// a ground `true` or `false` with no condition left.
pub fn evaluate(
    definition: &BackendDefinition,
    cells: &[&KorePattern],
    invariant: Invariant<'_>,
) -> Result<bool, String> {
    if cells.len() != invariant.cells.len() {
        return Err(format!(
            "{} cells are read, and the invariant reads {}",
            cells.len(),
            invariant.cells.len()
        ));
    }
    on_stack(definition, cells, |associated| {
        let terms = associated
            .iter()
            .map(|cell| internalized(definition, cell))
            .collect::<Result<Vec<_>, _>>()?;
        let application = applied_to(definition, invariant, |path| {
            invariant
                .cells
                .iter()
                .position(|cell| cell.as_slice() == path)
                .map(|index| &terms[index])
        })
        .map_err(|refusal| refusal.to_string())?;
        value(definition, &application)
    })
}

/// The value of `invariant`'s function at the configuration `configuration` (KORE), which is first
/// evaluated in `definition` to the term its cells are read from, then as [`evaluate`] does; with
/// the cells read, in the invariant's order, as KORE.
///
/// # Errors
///
/// As [`evaluate`], and where the configuration's evaluation leaves a condition, or holds no cell
/// the invariant reads.
pub fn evaluate_configuration(
    definition: &BackendDefinition,
    configuration: &KorePattern,
    invariant: Invariant<'_>,
) -> Result<(bool, Vec<KorePattern>), String> {
    on_stack(definition, &[configuration], |associated| {
        let term = internalized(definition, associated[0])?;
        let state = with_evaluation(EvaluationMode::Proof, || simplified(definition, &term))?;
        let application = applied_to(definition, invariant, |path| cell_term(&state, path))
            .map_err(|refusal| refusal.to_string())?;
        let cells = invariant
            .cells
            .iter()
            .filter_map(|path| cell_term(&state, path))
            .map(k_rust_backend::externalize::term)
            .collect();
        Ok((value(definition, &application)?, cells))
    })
}

/// `work` on the stack k-rust gives an operation over `patterns`, or why it cannot run.
fn on_stack<R>(
    definition: &BackendDefinition,
    patterns: &[&KorePattern],
    work: impl FnOnce(&[&KorePattern]) -> Result<R, String>,
) -> Result<R, String> {
    match crate::feasibility::on_stack_for(definition, patterns, work) {
        Ok(Some(result)) => result,
        Ok(None) => Err("the state is too deep for the largest stack k-rust gives".to_owned()),
        Err(refused) => Err(refused.to_string()),
    }
}

/// `pattern` as a term of `definition`.
fn internalized(definition: &BackendDefinition, pattern: &KorePattern) -> Result<Term, String> {
    definition
        .admit_unverified(pattern, &[])
        .internalize_term()
        .map_err(|error| format!("the state is no term of the definition: {error}"))
}

/// `term` evaluated in `definition` on the proof route, with no condition left.
fn simplified(definition: &BackendDefinition, term: &Term) -> Result<Term, String> {
    let (result, _) = diagnostic::collect(|| {
        simplify::simplify(definition, term, SimplificationOptions::default())
    });
    match result {
        Err(stop) => {
            stop.forgo_refinement();
            Err("a stop ended the evaluation".to_owned())
        }
        Ok(Err(error)) => Err(format!("the evaluation failed: {error}")),
        Ok(Ok(simplification)) if simplification.exhausted.is_some() => {
            Err("the evaluation spent its simplification budget".to_owned())
        }
        Ok(Ok(simplification)) if !simplification.is_unconditional() => {
            Err("the evaluation leaves a condition".to_owned())
        }
        Ok(Ok(simplification)) => Ok(simplification.term),
    }
}

/// The value of the `Bool` term `application`: decided only where its evaluation ends at a ground
/// `true` or `false` with no condition left.
fn value(definition: &BackendDefinition, application: &Term) -> Result<bool, String> {
    let term = with_evaluation(EvaluationMode::Proof, || {
        simplified(definition, application)
    })?;
    if let TermKind::DomainValue { sort, value } = term.kind()
        && sort.is_builtin(BuiltinSort::Bool)
    {
        match value.as_bytes() {
            b"true" => return Ok(true),
            b"false" => return Ok(false),
            _ => {}
        }
    }
    Err("the invariant's evaluation ends at no Bool value".to_owned())
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::path::Path;

    use k_rust::backend::{Backend, BackendError};
    use k_rust::kompile::CompileOptions;
    use k_rust_backend::definition::BackendDefinition;
    use k_rust_backend::rule::Predicate;
    use k_rust_backend::smt::{Satisfiability, SmtError, SmtSolver, Validity};
    use k_rust_backend::stop::Stoppable;
    use k_rust_backend::substitution::Substitution;

    use super::{
        Connection, Invariant, Refusal, Undecided, Valuation, connection, evaluate, stepping_rules,
    };
    use crate::{NativeValidator, support};

    use Connection::{Connected, NotConnected};

    /// The fixture `testdata/k/invariant/invmem.k`.
    fn backend() -> Backend {
        let baseline = support::load_path(
            &Path::new(support::DIR).join("invariant/invmem.k"),
            "INVMEM",
        );
        let validator = NativeValidator::bind(baseline, CompileOptions::default());
        let side = validator.compile_baseline().expect("fixture compiles");
        Backend::new(
            &side.artifacts().definition_kore,
            "INVMEM",
            crate::BACKEND_OPTIONS,
        )
        .expect("backend")
    }

    /// `body` with the fixture's definition and the backend's solver.
    fn with_fixture(body: impl FnOnce(&BackendDefinition, &dyn SmtSolver)) {
        backend()
            .with_solver(None, |definition, solver| {
                body(definition, solver);
                Ok::<(), BackendError>(())
            })
            .expect("the fixture's backend runs the operation");
    }

    /// The KORE path of the cell `<name>` of the fixture's configuration.
    fn cell(name: &str) -> Vec<String> {
        ["generatedTop", "t", name]
            .into_iter()
            .map(|cell| format!("Lbl'-LT-'{cell}'-GT-'"))
            .collect()
    }

    fn memory() -> [Vec<String>; 2] {
        [cell("memory"), cell("romEnd")]
    }

    fn scalars() -> [Vec<String>; 2] {
        [cell("a"), cell("b")]
    }

    /// The `UNIQUE_ID` of the rewrite rule labelled `label`.
    fn axiom(definition: &BackendDefinition, label: &str) -> String {
        definition
            .rewrite_theory()
            .values()
            .flat_map(|priorities| priorities.values())
            .flatten()
            .find(|rule| {
                rule.rule
                    .attributes
                    .label
                    .as_deref()
                    .is_some_and(|written| written.rsplit('.').next() == Some(label))
            })
            .unwrap_or_else(|| panic!("no rule {label}"))
            .rule
            .attributes
            .unique_id
            .clone()
    }

    /// The paths of the atoms of `axiom`'s `requires`, in preorder, as k-rust's guard skeletons
    /// name them.
    #[cfg(feature = "z3")]
    fn atoms(definition: &BackendDefinition, axiom: &str) -> Vec<Vec<u32>> {
        let guards = k_rust_backend::coverage::skeletons(
            definition,
            &std::collections::BTreeSet::from([axiom.to_owned()]),
        );
        let [guard] = guards.as_slice() else {
            panic!("{axiom} has one skeleton: {guards:?}");
        };
        guard
            .nodes
            .iter()
            .filter(|node| node.shape.is_atom())
            .map(|node| node.path.clone())
            .collect()
    }

    /// The connection of `valuation` at the rule labelled `label` under `invariant`, which must be
    /// asked.
    fn ask(
        definition: &BackendDefinition,
        solver: &dyn SmtSolver,
        label: &str,
        valuation: Valuation<'_>,
        invariant: Option<Invariant<'_>>,
        undecided: &Cell<usize>,
    ) -> Connection {
        let id = axiom(definition, label);
        connection(definition, solver, &id, valuation, invariant, undecided)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}"))
    }

    /// The rules that can step where `readz` matches are the two rules of its left-hand side;
    /// where `bump` matches, `bump` alone, since every other rule's `<k>` cell begins with
    /// another constructor.
    #[test]
    fn the_rules_that_step_where_a_rule_matches_are_those_whose_left_hand_side_unifies() {
        with_fixture(|definition, _| {
            let labels = |label: &str| {
                let axioms = std::collections::BTreeSet::from([axiom(definition, label)]);
                stepping_rules(definition, &axioms)
                    .expect("the rule exists")
                    .into_iter()
                    .map(|rule| rule.label.unwrap_or_default())
                    .collect::<std::collections::BTreeSet<_>>()
            };
            let set = |labels: &[&str]| labels.iter().map(|&label| label.to_owned()).collect();
            assert_eq!(labels("readz"), set(&["INVMEM.readz", "INVMEM.readzRom"]));
            assert_eq!(labels("bump"), set(&["INVMEM.bump"]));
            let unknown = std::collections::BTreeSet::from(["no-such-id".to_owned()]);
            assert_eq!(
                stepping_rules(definition, &unknown),
                Err(Refusal::NoRule("no-such-id".to_owned()))
            );
        });
    }

    /// An invariant's value at a state is its function's evaluation at the state's cells: the walk
    /// over a ground memory is false exactly where a key lies below `romEnd`, the order of two
    /// ground scalars is their order, and a cell holding a variable gives no value.
    #[test]
    fn an_invariant_is_evaluated_at_the_cells_of_a_state() {
        use k_rust::kore::parser::parse_pattern;
        with_fixture(|definition, _| {
            let int = |n: i64| format!("\\dv{{SortInt{{}}}}(\"{n}\")");
            let key = |n: i64| format!("inj{{SortInt{{}}, SortKItem{{}}}}({})", int(n));
            let binding =
                |k: i64, v: i64| format!("Lbl'UndsPipe'-'-GT-Unds'{{}}({}, {})", key(k), key(v));
            let cell = |name: &str, content: &str| {
                parse_pattern(&format!("Lbl'-LT-'{name}'-GT-'{{}}({content})")).expect("a cell")
            };
            let rom = cell("romEnd", &int(4));
            let clean = cell("memory", &binding(8, 0));
            let dirty = cell(
                "memory",
                &format!(
                    "Lbl'Unds'Map'Unds'{{}}({}, {})",
                    binding(8, 0),
                    binding(2, 1)
                ),
            );
            let paths = memory();
            let walk = Invariant {
                symbol: "LbloutsideRom",
                cells: &paths,
            };
            assert_eq!(evaluate(definition, &[&clean, &rom], walk), Ok(true));
            assert_eq!(evaluate(definition, &[&dirty, &rom], walk), Ok(false));
            let paths = scalars();
            let order = Invariant {
                symbol: "Lblordered",
                cells: &paths,
            };
            let (zero, one, two) = (cell("a", &int(0)), cell("b", &int(1)), cell("a", &int(2)));
            assert_eq!(evaluate(definition, &[&zero, &one], order), Ok(true));
            assert_eq!(evaluate(definition, &[&two, &one], order), Ok(false));
            let symbolic = cell("a", "VarA : SortInt{}");
            assert!(evaluate(definition, &[&symbolic, &one], order).is_err());
        });
    }

    /// The probe of a whole-map invariant at a rule's map pattern. `outsideRom` walks a map's
    /// bindings (an equation on `(K:Int |-> _) M`); `readz` and `readzRom` match
    /// `<memory> (A |-> _) REST </memory>` and split on `inRom(E, A)`. At that left-hand side the
    /// definition's equation applies at the explicit binding of `A`, so the walk unfolds to
    /// `notBool inRom(E, A) andBool outsideRom(REST, E)`, and the simplification reduces the
    /// question with `inRom(E, A)` to `\bottom` (measured under Z3 5.3.3), before this module's
    /// satisfiability question.
    /// So the invariant connects `readz`'s refuted condition and `readzRom`'s held one, which the
    /// pattern and the condition alone do not exclude. The valuations the invariant admits stay
    /// undecided: the solver's model is of an approximate translation (the walk of `REST` is a
    /// fresh constant), and a left-hand side with a map shows no instance at a model anyway.
    #[cfg(feature = "z3")]
    #[test]
    fn a_map_walk_invariant_unfolds_at_the_binding_a_rule_matches() {
        with_fixture(|definition, solver| {
            let cells = memory();
            let walk = Invariant {
                symbol: "LbloutsideRom",
                cells: &cells,
            };
            let undecided = Cell::new(0);
            let ask = |label, valuation, invariant| {
                ask(definition, solver, label, valuation, invariant, &undecided)
            };
            assert_eq!(ask("readz", Valuation::Refuted, Some(walk)), Connected);
            assert_eq!(ask("readzRom", Valuation::Held, Some(walk)), Connected);
            let inexact = Connection::Undecided(Undecided::Inexact);
            assert_eq!(ask("readz", Valuation::Held, Some(walk)), inexact);
            assert_eq!(ask("readzRom", Valuation::Refuted, Some(walk)), inexact);
            assert_eq!(ask("readz", Valuation::Matches, Some(walk)), inexact);
            let unshown = Connection::Undecided(Undecided::InstancesUnshown);
            assert_eq!(ask("readz", Valuation::Refuted, None), unshown);
            assert_eq!(ask("readzRom", Valuation::Held, None), unshown);
            assert_eq!(undecided.get(), 0);
        });
    }

    /// The same invariant written as a fold over `keys_list(M)` does not unfold at the rule's map
    /// pattern: `keys_list((A |-> _) REST)` has no equation that gives a list headed by `A`, so the
    /// simplification leaves `keysOutside(keys_list((A |-> _) REST), E)` in the residual, beside
    /// `A <Int E` and the pattern's `notBool A in_keys(REST)`. The solver abstracts the fold, and
    /// nothing is connected.
    #[cfg(feature = "z3")]
    #[test]
    fn a_keys_list_fold_invariant_does_not_unfold_at_a_map_pattern() {
        with_fixture(|definition, solver| {
            let cells = memory();
            let keys = Invariant {
                symbol: "LbloutsideRomKeys",
                cells: &cells,
            };
            let undecided = Cell::new(0);
            let inexact = Connection::Undecided(Undecided::Inexact);
            for (label, valuation) in [("readz", Valuation::Refuted), ("readzRom", Valuation::Held)]
            {
                assert_eq!(
                    ask(definition, solver, label, valuation, Some(keys), &undecided),
                    inexact,
                    "{label}"
                );
            }
            assert_eq!(undecided.get(), 0);
        });
    }

    /// A scalar invariant `a <=Int b` connects the valuations it excludes and is not connected to
    /// those it admits; a reached node's valuation carries the truths that reach it; with no
    /// invariant the pattern and the condition alone decide.
    #[cfg(feature = "z3")]
    #[test]
    fn a_scalar_invariant_connects_exactly_the_valuations_it_excludes() {
        with_fixture(|definition, solver| {
            let cells = scalars();
            let ordered = Some(Invariant {
                symbol: "Lblordered",
                cells: &cells,
            });
            let undecided = Cell::new(0);
            let ask = |label, valuation, invariant| {
                ask(definition, solver, label, valuation, invariant, &undecided)
            };
            // bump requires `A >Int B`.
            assert_eq!(ask("bump", Valuation::Held, ordered), Connected);
            assert_eq!(ask("bump", Valuation::Refuted, ordered), NotConnected);
            assert_eq!(ask("bump", Valuation::Matches, ordered), NotConnected);
            assert_eq!(ask("bump", Valuation::Held, None), NotConnected);
            // tie requires `A >Int B andBool B >Int A`; its second atom is reached where the
            // first is true, so under `a <=Int b` it is reached with neither truth.
            let atoms = atoms(definition, &axiom(definition, "tie"));
            assert_eq!(atoms, [vec![0, 0, 0], vec![0, 0, 1]]);
            for truth in [true, false] {
                let second = Valuation::Reached {
                    path: &atoms[1],
                    truth,
                };
                assert_eq!(ask("tie", second, ordered), Connected, "{truth}");
            }
            let first_false = Valuation::Reached {
                path: &atoms[0],
                truth: false,
            };
            assert_eq!(ask("tie", first_false, ordered), NotConnected);
            // With no invariant, the second atom true contradicts the first, which reaches it.
            let second_true = Valuation::Reached {
                path: &atoms[1],
                truth: true,
            };
            let second_false = Valuation::Reached {
                path: &atoms[1],
                truth: false,
            };
            assert_eq!(ask("tie", second_true, None), Connected);
            assert_eq!(ask("tie", second_false, None), NotConnected);
            assert_eq!(ask("tie", Valuation::Held, None), Connected);
            assert_eq!(undecided.get(), 0);
        });
    }

    /// A solver that answers every satisfiability query with one scripted result and decides no
    /// validity question, so that simplification leaves its residual to the satisfiability
    /// question.
    struct Scripted(Result<Satisfiability, SmtError>);

    impl SmtSolver for Scripted {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            Ok(self.0.clone())
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(Err(SmtError::Unavailable))
        }
    }

    /// Only `Unsat` connects; `Sat` is not connected only for an exact translation at a
    /// left-hand side with an instance at every valuation; each `Unknown` is counted. Both
    /// profiles: the solver is scripted.
    #[test]
    fn only_unsat_connects_and_only_an_exact_sat_with_instances_does_not() {
        with_fixture(|definition, _| {
            let scalar_cells = scalars();
            let ordered = Some(Invariant {
                symbol: "Lblordered",
                cells: &scalar_cells,
            });
            let memory_cells = memory();
            let walk = Some(Invariant {
                symbol: "LbloutsideRom",
                cells: &memory_cells,
            });
            let rows = [
                ("bump", ordered, Ok(Satisfiability::Unsat), Connected, 0),
                ("bump", ordered, Ok(Satisfiability::Sat), NotConnected, 0),
                (
                    "bump",
                    ordered,
                    Ok(Satisfiability::Unknown("scripted".into())),
                    Connection::Undecided(Undecided::SolverUnknown("scripted".into())),
                    1,
                ),
                (
                    "bump",
                    ordered,
                    Err(SmtError::Unavailable),
                    Connection::Undecided(Undecided::NoSolver),
                    0,
                ),
                // The walk of the map's rest is abstracted: an approximate translation.
                (
                    "readz",
                    walk,
                    Ok(Satisfiability::Sat),
                    Connection::Undecided(Undecided::Inexact),
                    0,
                ),
                ("readz", walk, Ok(Satisfiability::Unsat), Connected, 0),
                // `inRom` unfolds to Int arithmetic, which translates exactly, but the map in
                // the left-hand side shows no instance.
                (
                    "readz",
                    None,
                    Ok(Satisfiability::Sat),
                    Connection::Undecided(Undecided::InstancesUnshown),
                    0,
                ),
            ];
            for (label, invariant, answer, expected, unknowns) in rows {
                let undecided = Cell::new(0);
                let solver = Scripted(answer.clone());
                assert_eq!(
                    ask(
                        definition,
                        &solver,
                        label,
                        Valuation::Held,
                        invariant,
                        &undecided
                    ),
                    expected,
                    "{label} {answer:?}"
                );
                assert_eq!(undecided.get(), unknowns, "{label} {answer:?}");
            }
        });
    }

    /// Each question that cannot be asked is refused with its reason, before the solver is.
    #[test]
    fn questions_that_cannot_be_asked_are_refused() {
        with_fixture(|definition, solver| {
            let undecided = Cell::new(0);
            let bump = axiom(definition, "bump");
            let scalar_cells = scalars();
            let memory_cells = memory();
            let ask = |axiom: &str, valuation, symbol, cells: &[Vec<String>]| {
                connection(
                    definition,
                    solver,
                    axiom,
                    valuation,
                    Some(Invariant { symbol, cells }),
                    &undecided,
                )
            };
            let held = Valuation::Held;
            assert_eq!(
                ask("no-such-id", held, "Lblordered", &scalar_cells),
                Err(Refusal::NoRule("no-such-id".into()))
            );
            assert_eq!(
                ask(&bump, held, "LblnoSuchSymbol", &scalar_cells),
                Err(Refusal::UnknownSymbol("LblnoSuchSymbol".into()))
            );
            assert_eq!(
                ask(&bump, held, "Lblread", &scalar_cells[..1]),
                Err(Refusal::NotBoolFunction("Lblread".into()))
            );
            assert_eq!(
                ask(&bump, held, "Lblordered", &scalar_cells[..1]),
                Err(Refusal::Arity {
                    symbol: "Lblordered".into(),
                    parameters: 2,
                    cells: 1,
                })
            );
            // bump's left-hand side does not name `<memory>`: K completes it with a variable of
            // the cell's sort, which is no cell term.
            assert_eq!(
                ask(&bump, held, "LbloutsideRom", &memory_cells),
                Err(Refusal::NoCell(cell("memory")))
            );
            // `ordered` takes Ints; `<memory>` holds a Map.
            let readz = axiom(definition, "readz");
            assert_eq!(
                ask(&readz, held, "Lblordered", &memory_cells),
                Err(Refusal::CellSort {
                    cell: cell("memory"),
                    parameter: "SortInt".into(),
                })
            );
            let path = [0, 0, 2];
            assert_eq!(
                ask(
                    &axiom(definition, "tie"),
                    Valuation::Reached {
                        path: &path,
                        truth: true
                    },
                    "Lblordered",
                    &scalar_cells
                ),
                Err(Refusal::NoNode(path.to_vec()))
            );
            assert_eq!(undecided.get(), 0);
        });
    }

    /// A solver with scripted answers to both kinds of question that records the evaluation mode
    /// each question is asked in.
    struct Probing {
        sat: Result<Satisfiability, SmtError>,
        validity: Result<Validity, SmtError>,
        modes: std::cell::RefCell<Vec<k_rust_backend::evaluation::EvaluationMode>>,
    }

    impl Probing {
        fn new(
            sat: Result<Satisfiability, SmtError>,
            validity: Result<Validity, SmtError>,
        ) -> Self {
            Self {
                sat,
                validity,
                modes: std::cell::RefCell::default(),
            }
        }
    }

    impl SmtSolver for Probing {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            self.modes
                .borrow_mut()
                .push(k_rust_backend::evaluation::current());
            Ok(self.sat.clone())
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            self.modes
                .borrow_mut()
                .push(k_rust_backend::evaluation::current());
            Ok(self.validity.clone())
        }
    }

    /// A connection asked from inside an execution's scope (a run's or an evidence callback's)
    /// still asks every solver question on the proof route, so no answer rests on a value the
    /// definition leaves to the implementation. Both profiles: the solver is scripted.
    #[test]
    fn every_solver_question_is_asked_on_the_proof_route() {
        use k_rust_backend::evaluation::{EvaluationMode, with_evaluation};
        with_fixture(|definition, _| {
            let cells = memory();
            let walk = Some(Invariant {
                symbol: "LbloutsideRom",
                cells: &cells,
            });
            let solver = Probing::new(
                Ok(Satisfiability::Sat),
                Ok(Validity::Unknown("scripted".into())),
            );
            let undecided = Cell::new(0);
            let answer = with_evaluation(EvaluationMode::Execution, || {
                ask(
                    definition,
                    &solver,
                    "readz",
                    Valuation::Held,
                    walk,
                    &undecided,
                )
            });
            assert_eq!(answer, Connection::Undecided(Undecided::Inexact));
            let modes = solver.modes.borrow();
            assert!(!modes.is_empty());
            assert!(
                modes.iter().all(|mode| *mode == EvaluationMode::Proof),
                "{modes:?}"
            );
        });
    }

    /// The simplification's own `Unknown`s are counted, though its result is only the undecided
    /// residual: here every validity question is undecided and the satisfiability question finds
    /// an approximate model, so the connection is `Inexact` with an undecided answer counted for
    /// each validity question. Both profiles: the solver is scripted.
    #[test]
    fn an_unknown_of_the_simplification_is_counted() {
        with_fixture(|definition, _| {
            let cells = memory();
            let walk = Some(Invariant {
                symbol: "LbloutsideRom",
                cells: &cells,
            });
            let solver = Probing::new(
                Ok(Satisfiability::Sat),
                Ok(Validity::Unknown("scripted".into())),
            );
            let undecided = Cell::new(0);
            assert_eq!(
                ask(
                    definition,
                    &solver,
                    "readz",
                    Valuation::Held,
                    walk,
                    &undecided
                ),
                Connection::Undecided(Undecided::Inexact)
            );
            // Two validity questions, both reported: the definedness condition of the walk's
            // equation at the binding of `A`, and the residual's decision.
            let modes = solver.modes.borrow();
            assert_eq!(modes.len(), 3, "{modes:?}");
            assert_eq!(undecided.get(), 2);
        });
    }

    /// A cell the rule binds by an alias (`#as C`) is read through the conjunction the alias
    /// compiles to, and the left-hand side with the alias read as its cell shows an instance at a
    /// model.
    #[cfg(feature = "z3")]
    #[test]
    fn a_cell_bound_by_an_alias_is_read_through_it() {
        with_fixture(|definition, solver| {
            let cells = scalars();
            let ordered = Some(Invariant {
                symbol: "Lblordered",
                cells: &cells,
            });
            let undecided = Cell::new(0);
            let ask = |valuation| {
                ask(
                    definition, solver, "aliased", valuation, ordered, &undecided,
                )
            };
            assert_eq!(ask(Valuation::Held), Connected);
            assert_eq!(ask(Valuation::Refuted), NotConnected);
            assert_eq!(undecided.get(), 0);
        });
    }

    /// An axiom compiled to several rules is connected only where each of its rules is: `either`
    /// matches `<a> 0 </a>` or `<a> 1 </a>`.
    #[cfg(feature = "z3")]
    #[test]
    fn an_axiom_of_several_rules_is_connected_only_where_each_is() {
        with_fixture(|definition, solver| {
            let id = axiom(definition, "either");
            let alternatives = definition
                .rewrite_theory()
                .values()
                .flat_map(|priorities| priorities.values())
                .flatten()
                .filter(|rule| rule.rule.attributes.unique_id == id)
                .count();
            assert_eq!(alternatives, 2);
            let cells = [cell("a")];
            let undecided = Cell::new(0);
            let ask = |symbol| {
                ask(
                    definition,
                    solver,
                    "either",
                    Valuation::Matches,
                    Some(Invariant {
                        symbol,
                        cells: &cells,
                    }),
                    &undecided,
                )
            };
            // `a <=Int 0` excludes `<a> 1 </a>` only; `a >Int 1` excludes both.
            assert_eq!(ask("Lblsmall"), NotConnected);
            assert_eq!(ask("Lblbig"), Connected);
            assert_eq!(undecided.get(), 0);
        });
    }

    /// The valuation of a node reached through `orBool` (every operand before it false) and
    /// through `impliesBool` (the right operand where the left one is true) carries the truths
    /// that reach it.
    #[cfg(feature = "z3")]
    #[test]
    fn disjunctions_and_implications_reach_their_operands_by_the_written_order() {
        with_fixture(|definition, solver| {
            let scalar_cells = scalars();
            let undecided = Cell::new(0);
            let reached = |path: &'static [u32], truth| Valuation::Reached { path, truth };
            // `disjoint` requires `A >Int B orBool B >Int A`. Under `inRom(a, b)`, `B <Int A`,
            // the first atom holds, so the second, reached only where the first is false, is
            // reached with neither truth; without the reaching truth, the second false would be
            // `B <=Int A`, which the invariant admits.
            let below = Some(Invariant {
                symbol: "LblinRom",
                cells: &scalar_cells,
            });
            assert_eq!(
                atoms(definition, &axiom(definition, "disjoint")),
                [vec![0, 0, 0], vec![0, 0, 1]]
            );
            for (path, truth, expected) in [
                (&[0, 0, 0][..], true, NotConnected),
                (&[0, 0, 0][..], false, Connected),
                (&[0, 0, 1][..], true, Connected),
                (&[0, 0, 1][..], false, Connected),
            ] {
                assert_eq!(
                    ask(
                        definition,
                        solver,
                        "disjoint",
                        reached(path, truth),
                        below,
                        &undecided
                    ),
                    expected,
                    "disjoint {path:?} {truth}"
                );
            }
            // `implied` requires `A >Int B impliesBool B >Int A`. Under `a <=Int b` the left
            // atom is false, so the right one, reached only where the left is true, is reached
            // with neither truth; without the reaching truth, the right false would be
            // `B <=Int A`, which the invariant admits at `A = B`.
            let ordered = Some(Invariant {
                symbol: "Lblordered",
                cells: &scalar_cells,
            });
            assert_eq!(
                atoms(definition, &axiom(definition, "implied")),
                [vec![0, 0, 0], vec![0, 0, 1]]
            );
            for (path, truth, expected) in [
                (&[0, 0, 0][..], true, Connected),
                (&[0, 0, 0][..], false, NotConnected),
                (&[0, 0, 1][..], true, Connected),
                (&[0, 0, 1][..], false, Connected),
            ] {
                assert_eq!(
                    ask(
                        definition,
                        solver,
                        "implied",
                        reached(path, truth),
                        ordered,
                        &undecided
                    ),
                    expected,
                    "implied {path:?} {truth}"
                );
            }
            assert_eq!(undecided.get(), 0);
        });
    }

    /// The matching-logic connectives reach their operands as the Boolean ones do: `\and` and the
    /// `requires`' conjuncts where the earlier ones hold, `\or` where they do not, the right of
    /// `\implies` where its left holds, the operand of `\not` and of `\iff` where the node is.
    /// The atoms are opaque here: only the shape of the valuation is checked.
    #[test]
    fn predicate_connectives_reach_their_operands_by_the_written_order() {
        use std::sync::Arc;

        use k_rust_backend::term::Term;

        use super::reached;

        let atom = |value: i64| Predicate::Ceil(Term::int(value));
        let not = |predicate: Predicate| Predicate::Not(Arc::new(predicate));
        let and = |predicates: Vec<Predicate>| Predicate::And(predicates.into());
        let (p, q, r) = (atom(1), atom(2), atom(3));
        let or = Predicate::Or(vec![q.clone(), r.clone()].into());
        let implies = Predicate::Implies(Arc::new(q.clone()), Arc::new(r.clone()));
        let iff = Predicate::Iff(Arc::new(q.clone()), Arc::new(r.clone()));
        let conjunction = Predicate::And(vec![q.clone(), r.clone()].into());
        let rows = [
            (
                vec![p.clone(), or.clone()],
                vec![1, 1],
                false,
                and(vec![p.clone(), not(q.clone()), not(r.clone())]),
            ),
            (vec![or.clone()], vec![0, 0], true, q.clone()),
            (
                vec![implies.clone()],
                vec![0, 1],
                true,
                and(vec![q.clone(), r.clone()]),
            ),
            (vec![implies.clone()], vec![0, 0], false, not(q.clone())),
            (vec![iff.clone()], vec![0, 1], true, r.clone()),
            (
                vec![conjunction.clone()],
                vec![0, 1],
                false,
                and(vec![q.clone(), not(r.clone())]),
            ),
            (vec![not(q.clone())], vec![0, 0], true, q.clone()),
            (
                vec![p.clone(), q.clone()],
                vec![1],
                true,
                and(vec![p.clone(), q.clone()]),
            ),
        ];
        for (requires, path, truth, expected) in rows {
            assert_eq!(
                reached(&requires, &path, truth),
                Ok(expected),
                "{path:?} {truth}"
            );
        }
        assert_eq!(
            reached(std::slice::from_ref(&p), &[0, 0], true),
            Err(Refusal::NoNode(vec![0, 0]))
        );
        assert_eq!(
            reached(&[implies], &[0, 2], true),
            Err(Refusal::NoNode(vec![0, 2]))
        );
    }
}
