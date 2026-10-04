//! ```toml algorithm
//! id = "backend.fresh.variables"
//! name = "counter-suffixed backend variable naming with collision retry"
//! sites = ["fresh_name", "fresh_variable", "freshen_existential", "increment_name_counter"]
//! variable = "c = colliding candidate names; v = variable names collected into a site's avoid set"
//! counters = []
//! no_counter = "fresh backend variable naming has no dedicated counter"
//! span = "none"
//!
//! [[cost]]
//! mode = "shared counter"
//! bound = "O(c) per name, amortized O(1)"
//!
//! [[cost]]
//! mode = "Booster existential spelling"
//! bound = "O(c) trailing-decimal retries"
//!
//! [[cost]]
//! mode = "avoid-set construction at a site (freshen_existentials, freshen_claim, rename_apart, alias fresh_variable)"
//! bound = "O(v log v) per call before the retry loop"
//!
//! [[cost]]
//! mode = "freshen_existentials"
//! bound = "O(c) per name without amortization, since the suffix restarts at each existential's index"
//! ```
//!
//! Counter-suffixed fresh variable naming with collision retry against a name set, the one home for
//! backend-term names (alias unfolding keeps its own `{name}Alias{index}` loop in `alias.rs`, a
//! declared variant): one loop, O(collisions) per name, amortised O(1) with the shared counter; no
//! measurement counter. The spelling is `term::names::with_fresh_marker`
//! (`{base}!{marker}{counter}`; marker `""` for rewrite-introduced variables, `claim` for
//! claim variables, `exists` for implication existentials), so emitted names are byte-identical
//! to the three per-site loops this replaces. Existentials introduced by a rule's right-hand
//! side follow Booster instead: strip the `Ex#` marker, keep the original name when it is free,
//! and increment a trailing decimal counter only while the name collides. Rule variables renamed
//! apart from an application's scope (`rule::rename_apart`) use marker `apart` with the
//! counter of the enclosing request (`rule::ApartScope`), so no two renamings of one request
//! mint the same name and identical requests mint identical names.

use std::{collections::BTreeSet, sync::Arc};

use crate::{
    rewrite::Pattern,
    rule::collect_all_variables,
    term::{
        Name, Term, Variable,
        names::{
            FreshMarker, VariableProvenance, encode_variable_name, split_marker, with_fresh_marker,
        },
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
        self.0.contains(&encode_variable_name(name))
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
    // Invariant: `counter` only grows, so at most |avoid| + 1 names are tried.
    loop {
        let name = with_fresh_marker(base, marker, *counter);
        *counter += 1;
        if avoid.insert(name.as_str().into()) {
            return name;
        }
    }
}

/// `variable` renamed to a `{name}!{counter}` that is not in `names_to_avoid`.
pub(crate) fn fresh_variable(
    variable: &Variable,
    names_to_avoid: &mut BTreeSet<Name>,
    fresh_counter: &mut u64,
) -> Term {
    let name = fresh_name(
        &variable.name,
        FreshMarker::Rewrite,
        fresh_counter,
        names_to_avoid,
    );
    Term::variable(variable.with_name(name))
}

/// Give an existential introduced by a rewrite the same externally meaningful name Booster does.
///
/// `Ex#` is provenance used only while a rule is internalized. At application time Booster strips
/// that marker, keeps the original name when it is available, and increments a trailing decimal
/// counter only while the name collides with a variable in the current pattern. In particular,
/// names may be reused after an earlier variable disappears from the state.
pub(crate) fn freshen_existential(
    variable: &Variable,
    names_to_avoid: &mut BTreeSet<Name>,
) -> Term {
    // `rule.existentials` only carries `Ex#` names (`internalize_axiom`); the `Rule` arm mirrors
    // Booster and `Eq#` is deliberately not accepted here.
    let mut name = split_marker(
        &variable.name,
        &[VariableProvenance::Existential, VariableProvenance::Rule],
    )
    .1
    .into_owned();
    // Invariant: the trailing counter only grows, so at most |names_to_avoid| + 1 names are tried.
    while !names_to_avoid.insert(name.as_str().into()) {
        name = increment_name_counter(&name);
    }
    Term::variable(variable.with_name(name))
}

fn increment_name_counter(name: &str) -> String {
    let digits = name.bytes().rev().take_while(u8::is_ascii_digit).count();
    if digits == 0 {
        return format!("{name}0");
    }
    let prefix = &name[..name.len() - digits];
    let counter = &name[name.len() - digits..];
    match counter
        .parse::<u64>()
        .ok()
        .and_then(|value| value.checked_add(1))
    {
        Some(counter) => format!("{prefix}{counter}"),
        None => format!("{name}0"),
    }
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
}
