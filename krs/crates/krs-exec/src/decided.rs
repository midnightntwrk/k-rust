//! Which partial functions defined by their equations alone are decided at values: where one of
//! them is applied to values and the backend leaves the application unevaluated, no equation of
//! it applies there, so the application has no value ([`crate::valueless`]).
//!
//! An equation applies where its left side matches and its condition holds. Matching values
//! against a left side is decided; the condition is decided at values where every function it
//! applies is *evaluated* at values: applied to values, it either reduces to what its equations
//! give or is decided to have no value. That holds of
//!
//! - a constructor or a builtin collection's builder (data);
//! - a hooked function: its hook computes it, and a hook the backend leaves unevaluated is listed
//!   on the run's result, which then decides nothing (`Semantics::run`);
//! - a partial function defined by its equations alone whose equations' conditions and results
//!   apply only evaluated functions: where none of its equations applies it has no value, so
//!   neither has the condition, which then does not hold; where one applies, its value is that
//!   equation's result, evaluated in turn;
//! - a `total` function whose equations' conditions and results apply only evaluated functions,
//!   and one of whose equations applies at every argument: an `owise` equation, or an equation
//!   with no condition whose arguments are pairwise distinct variables, such as the function a
//!   `#let` or `#fun` whose pattern covers its parameter sort is lowered to
//!   (`#let Y:Int = 1 #in Y` applies `λ(1)` under `λ(Y:Int) = Y`).
//!
//! Anything else may leave the condition open at a value: a `total` function no equation of
//! which names a value there (`Opaque` with no equation) has one the definition does not say, and
//! whether the equation applies depends on it; so does a function whose result applies such a
//! function. An application left because its condition is open is not one no equation applies
//! to, so its head is not decided at values. The head itself is judged by its conditions alone:
//! an application of it left unevaluated is one no equation applied to, whatever the results.
//!
//! The functions evaluated at values are the largest set closed under the rules above: a
//! function whose equations read itself, directly or through others, is evaluated where every
//! other function they read is, so recursion through it is decided where the rest is.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use k_rust::k_rust_backend::{
    definition::BackendDefinition,
    term::{FunctionType, HeadRole, SymbolType},
};
use k_rust::kore::{
    ast::{Pattern, Variable, VariableKind},
    walk,
};
use k_rust::names::WellKnownSymbol;

/// The symbols a pattern applies.
type Reads = HashSet<String>;

/// What one equation reads: the symbols its left side's arguments and its condition apply, and
/// those its result (with its `ensures`) applies.
struct EquationReads {
    condition: Reads,
    result: Reads,
}

/// How a head's application to values is judged.
#[derive(Clone, Copy, PartialEq)]
enum Role {
    /// Always evaluated: data, an injection, or a hooked function.
    Evaluated,
    /// Evaluated where every function its equations read is: a candidate, or a `total`
    /// function one of whose equations applies at every argument.
    Judged,
    /// Never known to be evaluated.
    Open,
}

/// Of `candidates`, the partial functions defined by their equations alone, those decided at
/// values ([module docs](self)).
pub(crate) fn decided_at_values(
    backend: &BackendDefinition,
    candidates: &HashSet<String>,
) -> HashSet<String> {
    let (equations, covered) = read_equations(backend);
    let symbols = backend
        .symbols()
        .iter()
        .map(|(name, symbol)| (name.to_string(), symbol))
        .collect::<HashMap<_, _>>();
    let role = |symbol: &str| -> Role {
        // A sort injection embeds a value as a value.
        if symbol == WellKnownSymbol::Inj.as_str() {
            return Role::Evaluated;
        }
        let Some(info) = symbols.get(symbol) else {
            return Role::Open;
        };
        let attributes = &info.attributes;
        if attributes.hook.is_some() || attributes.collection.is_some() {
            return Role::Evaluated;
        }
        match attributes.head_role() {
            HeadRole::FreeConstructor => Role::Evaluated,
            HeadRole::Function { declared: true, .. } if candidates.contains(symbol) => {
                Role::Judged
            }
            HeadRole::Function { declared: true, .. }
                if attributes.symbol_type == SymbolType::Function(FunctionType::Total)
                    && attributes.smt.is_none()
                    && covered.contains(symbol) =>
            {
                Role::Judged
            }
            _ => Role::Open,
        }
    };
    // The largest set of judged functions every read of whose equations is evaluated: every
    // judged function but those that read, directly or through other judged functions, a
    // function that is neither judged nor always evaluated.
    let judged = equations
        .keys()
        .chain(candidates)
        .filter(|symbol| role(symbol) == Role::Judged)
        .map(String::as_str)
        .collect::<HashSet<_>>();
    let mut readers = HashMap::<&str, Vec<&str>>::new();
    let mut dropped = Vec::new();
    for &symbol in &judged {
        let reads = equations
            .get(symbol)
            .into_iter()
            .flatten()
            .flat_map(|equation| equation.condition.iter().chain(&equation.result));
        for read in reads {
            if judged.contains(read.as_str()) {
                readers.entry(read).or_default().push(symbol);
            } else if role(read) != Role::Evaluated {
                dropped.push(symbol);
            }
        }
    }
    let mut evaluated = judged.clone();
    while let Some(symbol) = dropped.pop() {
        if evaluated.remove(symbol) {
            dropped.extend(readers.get(symbol).into_iter().flatten());
        }
    }
    let reads_evaluated = |reads: &Reads| {
        reads
            .iter()
            .all(|read| evaluated.contains(read.as_str()) || role(read) == Role::Evaluated)
    };
    candidates
        .iter()
        .filter(|candidate| {
            equations.get(*candidate).is_none_or(|equations| {
                equations
                    .iter()
                    .all(|equation| reads_evaluated(&equation.condition))
            })
        })
        .cloned()
        .collect()
}

/// The equations of `backend` (its simplifications aside), each head's with what each reads,
/// and the heads one of whose equations applies at every argument.
fn read_equations(
    backend: &BackendDefinition,
) -> (HashMap<String, Vec<EquationReads>>, HashSet<String>) {
    let mut equations = HashMap::<String, Vec<EquationReads>>::new();
    let mut covered = HashSet::<String>::new();
    for axiom in backend.axioms() {
        if has_attribute(&axiom.attributes.0, "simplification") {
            continue;
        }
        let Some(equation) = equation(&axiom.pattern) else {
            continue;
        };
        let mut condition = Reads::new();
        if let Some(premise) = equation.premise {
            applied(premise, &mut condition);
        }
        for argument in equation.arguments {
            applied(argument, &mut condition);
        }
        let mut result = Reads::new();
        applied(equation.result, &mut result);
        if has_attribute(&axiom.attributes.0, "owise")
            || !has_attribute(&axiom.attributes.0, "symbolic") && equation.covers()
        {
            covered.insert(equation.head.to_owned());
        }
        equations
            .entry(equation.head.to_owned())
            .or_default()
            .push(EquationReads { condition, result });
    }
    (equations, covered)
}

/// Whether `attributes` hold the attribute `name`.
fn has_attribute(attributes: &[Pattern], name: &str) -> bool {
    attributes.iter().any(
        |attribute| matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == name),
    )
}

/// An equation axiom, `\equals(f(..), result)` or that equality as the conclusion of an
/// `\implies`, read into its parts.
struct Equation<'a> {
    /// The head it defines.
    head: &'a str,
    /// The arguments of its left side.
    arguments: &'a [Pattern],
    /// The premise of its `\implies`: its condition, with the patterns its left side's
    /// argument variables are matched against (`\in(X0, P0)`).
    premise: Option<&'a Pattern>,
    /// Its result, with its `ensures`.
    result: &'a Pattern,
}

/// `axiom` read as an equation; a rewrite rule is no equation.
fn equation(axiom: &Pattern) -> Option<Equation<'_>> {
    let (premise, conclusion) = match axiom {
        Pattern::Implies { left, right, .. } => (Some(&**left), &**right),
        Pattern::Rewrites { .. } => return None,
        other => (None, other),
    };
    match conclusion {
        Pattern::Equals { left, right, .. } => match &**left {
            Pattern::Application { symbol, arguments } => Some(Equation {
                head: &symbol.name,
                arguments,
                premise,
                result: right,
            }),
            _ => None,
        },
        _ => None,
    }
}

impl Equation<'_> {
    /// Whether the equation applies at every argument: its premise states nothing but that
    /// each argument variable is an element variable (`\in(X0, Y)`), and the variables the
    /// arguments are matched against are pairwise distinct, each at its argument's sort. A
    /// variable at an argument position has that position's sort, and an `\in` of two element
    /// variables equates them, so every argument tuple matches.
    fn covers(&self) -> bool {
        let mut bound = BTreeMap::<&Variable, &Variable>::new();
        let mut conjuncts = self.premise.into_iter().collect::<Vec<_>>();
        while let Some(conjunct) = conjuncts.pop() {
            match conjunct {
                Pattern::Top { .. } => {}
                Pattern::And { arguments, .. } => conjuncts.extend(arguments),
                Pattern::In { left, right, .. } => {
                    let (Some(argument), Some(pattern)) = (element(left), element(right)) else {
                        return false;
                    };
                    if argument.sort != pattern.sort || bound.insert(argument, pattern).is_some() {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        let mut matched = BTreeSet::new();
        for argument in self.arguments {
            let Some(variable) = element(argument) else {
                return false;
            };
            let variable = bound.remove(variable).unwrap_or(variable);
            if !matched.insert(variable) {
                return false;
            }
        }
        // An `\in` over a variable that is no argument constrains something else.
        bound.is_empty()
    }
}

/// `pattern` as an element variable.
fn element(pattern: &Pattern) -> Option<&Variable> {
    match pattern {
        Pattern::Variable(variable) if variable.kind == VariableKind::Element => Some(variable),
        _ => None,
    }
}

/// Adds to `reads` each symbol `pattern` applies.
fn applied(pattern: &Pattern, reads: &mut Reads) {
    if let Pattern::Application { symbol, .. } | Pattern::AssociativeApplication { symbol, .. } =
        pattern
    {
        reads.insert(symbol.name.clone());
    }
    for child in walk::children(pattern) {
        applied(child, reads);
    }
}
