//! Which partial functions defined by their equations alone are decided at values: where one of
//! them is applied to values and the backend leaves the application unevaluated, no equation of
//! it applies there, so the application has no value ([`crate::valueless`]).
//!
//! An equation applies where its left side matches and its condition holds. Matching values
//! against a left side is decided; the condition is decided at values where every function it
//! applies is: a constructor or a builtin collection's builder (data), a hooked function (its
//! hook computes it, and a hook the backend leaves unevaluated is listed on the run's result,
//! which then decides nothing: `Semantics::run`), another such partial function decided at values
//! (where it has no value, neither has the condition, which then does not hold), or a `total`
//! function whose equations are decided at values and which has an `owise` equation, so one of
//! them applies at every argument. Anything else may leave the condition open at a value: a
//! `total` function no equation of which names a value there (`Opaque` with no equation) has one
//! the definition does not say, and whether the equation applies depends on it. An application
//! left because its condition is open is not one no equation applies to, so its head is not
//! decided at values.

use std::collections::{HashMap, HashSet};

use k_rust::k_rust_backend::{
    definition::BackendDefinition,
    term::{FunctionType, HeadRole, SymbolType},
};
use k_rust::kore::{ast::Pattern, walk};
use k_rust::names::WellKnownSymbol;

/// What one equation reads: the symbols it applies outside its result.
type Reads = HashSet<String>;

/// Of `candidates`, the partial functions defined by their equations alone, those decided at
/// values ([module docs](self)).
pub(crate) fn decided_at_values(
    backend: &BackendDefinition,
    candidates: &HashSet<String>,
) -> HashSet<String> {
    let mut equations = HashMap::<String, Vec<Reads>>::new();
    let mut owise = HashSet::<String>::new();
    for axiom in backend.axioms() {
        if has_attribute(&axiom.attributes.0, "simplification") {
            continue;
        }
        let Some((head, result)) = equation(&axiom.pattern) else {
            continue;
        };
        let mut reads = Reads::new();
        applied(&axiom.pattern, result, &mut reads);
        if has_attribute(&axiom.attributes.0, "owise") {
            owise.insert(head.to_owned());
        }
        equations.entry(head.to_owned()).or_default().push(reads);
    }
    let symbols = backend
        .symbols()
        .iter()
        .map(|(name, symbol)| (name.to_string(), symbol))
        .collect::<HashMap<_, _>>();
    let accepts = |symbol: &str, decided: &mut Judge<'_>| -> bool {
        // A sort injection embeds a value as a value.
        if symbol == WellKnownSymbol::Inj.as_str() {
            return true;
        }
        let Some(info) = symbols.get(symbol) else {
            return false;
        };
        let attributes = &info.attributes;
        if attributes.hook.is_some() || attributes.collection.is_some() {
            return true;
        }
        match attributes.head_role() {
            HeadRole::FreeConstructor => true,
            HeadRole::Function { declared: true, .. } if candidates.contains(symbol) => {
                decided.judge(symbol)
            }
            HeadRole::Function { declared: true, .. }
                if attributes.symbol_type == SymbolType::Function(FunctionType::Total)
                    && attributes.smt.is_none()
                    && owise.contains(symbol) =>
            {
                decided.judge(symbol)
            }
            _ => false,
        }
    };
    let mut judge = Judge {
        equations: &equations,
        verdicts: HashMap::new(),
        accepts: &accepts,
    };
    candidates
        .iter()
        .filter(|candidate| judge.judge(candidate))
        .cloned()
        .collect()
}

/// The memo of [`decided_at_values`]: a function is decided at values where every symbol each
/// of its equations reads is accepted. A function under judgement is taken as decided where it
/// reads itself: recursion through it is decided where the rest is.
struct Judge<'a> {
    equations: &'a HashMap<String, Vec<Reads>>,
    verdicts: HashMap<String, bool>,
    accepts: &'a dyn Fn(&str, &mut Judge<'_>) -> bool,
}

impl Judge<'_> {
    fn judge(&mut self, symbol: &str) -> bool {
        if let Some(verdict) = self.verdicts.get(symbol) {
            return *verdict;
        }
        self.verdicts.insert(symbol.to_owned(), true);
        let equations = self.equations;
        let accepts = self.accepts;
        let verdict = equations.get(symbol).is_none_or(|equations| {
            equations.iter().all(|reads| {
                reads
                    .iter()
                    .all(|read| read == symbol || accepts(read, self))
            })
        });
        self.verdicts.insert(symbol.to_owned(), verdict);
        verdict
    }
}

/// Whether `attributes` hold the attribute `name`.
fn has_attribute(attributes: &[Pattern], name: &str) -> bool {
    attributes.iter().any(
        |attribute| matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == name),
    )
}

/// The head an equation axiom defines, and its result: `\equals(f(..), result)`, or that
/// equality as the conclusion of an `\implies`. A rewrite rule is no equation.
fn equation(axiom: &Pattern) -> Option<(&str, &Pattern)> {
    let conclusion = match axiom {
        Pattern::Implies { right, .. } => right,
        Pattern::Rewrites { .. } => return None,
        other => other,
    };
    match conclusion {
        Pattern::Equals { left, right, .. } => match &**left {
            Pattern::Application { symbol, .. } => Some((&symbol.name, right)),
            _ => None,
        },
        _ => None,
    }
}

/// Adds to `reads` each symbol `pattern` applies outside `result`.
fn applied(pattern: &Pattern, result: &Pattern, reads: &mut Reads) {
    if std::ptr::eq(pattern, result) {
        return;
    }
    if let Pattern::Application { symbol, .. } | Pattern::AssociativeApplication { symbol, .. } =
        pattern
    {
        reads.insert(symbol.name.clone());
    }
    for child in walk::children(pattern) {
        applied(child, result, reads);
    }
}
