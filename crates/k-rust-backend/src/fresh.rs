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
//! mode = "avoid-set construction at a site (freshen_existentials, freshen_claim, alias fresh_variable)"
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
//! and increment a trailing decimal counter only while the name collides.

use std::collections::BTreeSet;

use crate::term::{
    Name, Term, Variable,
    names::{FreshMarker, VariableProvenance, split_marker, with_fresh_marker},
};

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
    .to_owned();
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
