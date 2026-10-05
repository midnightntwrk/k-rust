//! ```toml algorithm
//! id = "backend.fresh.variables"
//! name = "request-scoped variable naming with collision retry"
//! sites = ["FreshCounter::mint", "fresh_name", "fresh_variable"]
//! variable = "c = colliding candidate names; v = variable names collected into a site's avoid set"
//! counters = []
//! no_counter = "fresh backend variable naming has no dedicated counter"
//! span = "none"
//!
//! [[cost]]
//! mode = "request counter"
//! bound = "O(c log v) per name, amortized O(log v) with one growing counter per request"
//!
//! [[cost]]
//! mode = "local counter"
//! bound = "O(c) per name, amortized O(1)"
//!
//! [[cost]]
//! mode = "avoid-set construction at a site (freshen_existentials, mint_unbound_rule_variables, freshen_claim, rename_apart, alias fresh_variable)"
//! bound = "O(v log v) per call before the retry loop"
//!
//! [[cost]]
//! mode = "freshen_existentials"
//! bound = "O(c) per name without amortization, since the suffix restarts at each existential's index"
//! ```
//!
//! Counter-suffixed fresh variable naming with collision retry against a name set, the one home
//! for backend-term names (alias unfolding keeps its own `{name}Alias{index}` loop in `alias.rs`,
//! a declared variant): one loop, O(collisions) per name; no measurement counter. The spelling is
//! `term::names::with_fresh_marker` (`{base}!{marker}{counter}`; marker `""` for variables a
//! rewrite introduces, `claim` for claim variables, `exists` for implication existentials,
//! `binder` for renamed quantifier variables).
//!
//! A variable a rewrite introduces into a state (a right-hand-side existential, a rule variable
//! the match left unbound, a narrowed collection frame) or a claim variable a proof renames is
//! minted by the request's [`FreshCounter`]: one counter that only grows through the request, so
//! no two such names of a request share a counter, and a name never denotes a second variable
//! after the first one left the state. The counter skips every candidate spelled like a variable
//! of the request ([`RequestNames`]), so no mint prints like a name of the request either.
//! Rule variables renamed apart from an application's scope (`rule::rename_apart`) use marker
//! `apart` with the counter of the enclosing request (`rule::ApartScope`); the other local
//! markers name variables bound inside one predicate or one check.

use std::{collections::BTreeSet, sync::Arc};

use crate::{
    rewrite::Pattern,
    rule::collect_all_variables,
    term::{
        Name, Term, Variable,
        names::{FreshMarker, encode_variable_name, with_fresh_marker},
    },
};

/// The printed spellings of every variable, free or bound, of the patterns of one request.
///
/// A name read from KORE never equals a name the backend makes (`term::names`), but it may be
/// spelled like one: a request variable named `Ex-hX-b0` prints like the mint `Ex#X!0`. A name
/// that the backend introduces into a response must therefore avoid the spellings of the
/// request, not only its names, or the response would print two variables alike. Bound names
/// count too: a mint may be substituted under a request binder of its spelling.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RequestNames(Arc<BTreeSet<String>>);

impl RequestNames {
    /// The spellings of every variable of `patterns`, free or bound.
    pub fn of(patterns: &[&Pattern]) -> Self {
        let mut names = Self::default();
        for pattern in patterns {
            names.add_pattern(pattern);
        }
        names
    }

    /// Add the spellings of every variable of `pattern`, free or bound.
    pub fn add_pattern(&mut self, pattern: &Pattern) {
        let mut variables = pattern.term.attributes().variables.clone();
        collect_all_variables(&pattern.constraints, &mut variables);
        self.add_variables(&variables);
    }

    /// Add the spellings of `variables`.
    pub fn add_variables<'a>(&mut self, variables: impl IntoIterator<Item = &'a Variable>) {
        let spellings = Arc::make_mut(&mut self.0);
        spellings.extend(
            variables
                .into_iter()
                .map(|variable| encode_variable_name(&variable.name)),
        );
    }

    /// Add the spellings of every name of `other`.
    pub fn extend(&mut self, other: &Self) {
        if !other.0.is_empty() {
            Arc::make_mut(&mut self.0).extend(other.0.iter().cloned());
        }
    }

    /// Whether some variable of the request prints as `name` prints.
    pub fn spells(&self, name: &str) -> bool {
        !self.0.is_empty() && self.0.contains(&encode_variable_name(name))
    }
}

/// The first `{base}!{marker}{counter}` not in `avoid`, added to `avoid`; `counter` ends one
/// past the value that was used.
pub(crate) fn fresh_name(
    base: &str,
    marker: FreshMarker,
    counter: &mut u64,
    avoid: &mut BTreeSet<Name>,
) -> String {
    fresh_name_apart(base, marker, counter, avoid, &RequestNames::default())
}

/// [`fresh_name`], skipping also every candidate spelled like a variable of `request`, for a
/// local mint that a response can print next to the request's variables.
pub(crate) fn fresh_name_apart(
    base: &str,
    marker: FreshMarker,
    counter: &mut u64,
    avoid: &mut BTreeSet<Name>,
    request: &RequestNames,
) -> String {
    // Invariant: `counter` only grows, so at most |avoid| + |request| + 1 names are tried.
    loop {
        let name = with_fresh_marker(base, marker, *counter);
        *counter += 1;
        if !request.spells(&name) && avoid.insert(name.as_str().into()) {
            return name;
        }
    }
}

/// The counter of one request (an execution, a search, a proof, or a sequence of steps a
/// caller treats as one), and the spellings of the request's variables.
///
/// Every name a rewrite introduces into a state, and every claim variable a proof renames, is
/// minted by [`FreshCounter::mint`], which takes the next value of one counter that only grows:
/// two mints of a request differ in their counter, so no name is reused along a path, even
/// after its first variable left the state. A candidate spelled like a variable of the request
/// is skipped, so no mint prints like a name of the request, free or bound. Requests built
/// from the same patterns mint the same names.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FreshCounter {
    next: u64,
    request: RequestNames,
}

impl FreshCounter {
    /// The counter of a request whose patterns are `patterns`: every variable of them, free or
    /// bound, is a name of the request.
    pub fn for_request(patterns: &[&Pattern]) -> Self {
        Self::for_request_names(RequestNames::of(patterns))
    }

    /// The counter of a request with the given names.
    pub fn for_request_names(request: RequestNames) -> Self {
        Self { next: 0, request }
    }

    /// The next value of the counter: how many values the request has used, so a caller can
    /// tell whether a step minted a name.
    pub fn next_index(&self) -> u64 {
        self.next
    }

    /// The names of the request.
    pub fn request(&self) -> &RequestNames {
        &self.request
    }

    /// The first `{base}!{marker}{counter}` from this request's counter that is not in `avoid`
    /// and that no variable of the request is spelled as, added to `avoid`.
    pub(crate) fn mint(
        &mut self,
        base: &str,
        marker: FreshMarker,
        avoid: &mut BTreeSet<Name>,
    ) -> String {
        // Invariant: `next` only grows, so at most |avoid| + |request| + 1 names are tried.
        loop {
            let name = with_fresh_marker(base, marker, self.next);
            self.next = self
                .next
                .checked_add(1)
                .expect("a request mints fewer than 2^64 names");
            if !self.request.spells(&name) && avoid.insert(name.as_str().into()) {
                return name;
            }
        }
    }
}

/// `variable` renamed to a `{name}!{counter}` from the request's counter
/// ([`FreshCounter::mint`]) that is not in `names_to_avoid`.
///
/// `name` is the variable's name up to its first `!`: a rule variable renamed apart
/// (`Rule#X!apart3`) or an earlier mint mints from its original name (`X`), since the new
/// counter alone makes the name new.
pub(crate) fn fresh_variable(
    variable: &Variable,
    names_to_avoid: &mut BTreeSet<Name>,
    counter: &mut FreshCounter,
) -> Term {
    let base = variable
        .name
        .split_once('!')
        .map_or(variable.name.as_ref(), |(base, _)| base);
    let name = counter.mint(base, FreshMarker::Rewrite, names_to_avoid);
    Term::variable(variable.with_name(name))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{rule::Predicate, term::Sort};

    fn variable(name: &str) -> Variable {
        Variable::new(name, Sort::simple("SortS"))
    }

    fn pattern(free: &str, bound: &str) -> Pattern {
        Pattern {
            term: Term::variable(variable(free)),
            constraints: vec![Predicate::Exists(
                variable(bound),
                Box::new(Predicate::True),
            )],
        }
    }

    #[test]
    fn request_names_hold_the_spellings_of_free_and_bound_variables() {
        let names = RequestNames::of(&[&pattern("Ex-hX-b0", "Y")]);
        assert!(names.spells("Ex-hX-b0"));
        assert!(
            names.spells("Ex#X!0"),
            "the mint prints like the request variable"
        );
        assert!(names.spells("Y"));
        assert!(!names.spells("Ex#Y!0"));
        assert!(!names.spells("X"));
    }

    #[test]
    fn a_request_counter_never_reuses_a_value() {
        let mut counter = FreshCounter::for_request(&[]);
        let mut first = BTreeSet::new();
        let mut second = BTreeSet::new();
        assert_eq!(counter.mint("X", FreshMarker::Rewrite, &mut first), "X!0");
        // Another avoid set, as in a later step whose state no longer has `X!0`.
        assert_eq!(counter.mint("X", FreshMarker::Rewrite, &mut second), "X!1");
        assert_eq!(
            counter.mint("Y", FreshMarker::Claim, &mut second),
            "Y!claim2"
        );
    }

    #[test]
    fn a_request_counter_skips_the_spellings_of_the_request() {
        let mut counter =
            FreshCounter::for_request(&[&pattern("Ex-hX-b0", "Ex-hX-b1"), &pattern("Z", "Y")]);
        let mut avoid = BTreeSet::new();
        assert_eq!(
            counter.mint("Ex#X", FreshMarker::Rewrite, &mut avoid),
            "Ex#X!2"
        );
        assert_eq!(
            counter.mint("Ex#Y", FreshMarker::Rewrite, &mut avoid),
            "Ex#Y!3"
        );
    }
}
