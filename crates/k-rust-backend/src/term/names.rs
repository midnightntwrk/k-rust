//! Backend-internal variable naming: provenance markers and fresh counters.
//!
//! The marker is part of the name string on purpose: `Ord for Variable` is derived over
//! (`kind`, `sort`, `name`) and every `BTreeSet<Variable>` in the rewriter iterates in that
//! order, which decides fresh-counter assignment and therefore printed variable names.

use super::Variable;

/// Where a rule-side variable came from; Booster's `Rule#`/`Ex#` markers plus this port's `Eq#`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum VariableProvenance {
    /// Bound on a rewrite rule's left-hand side (`Rule#`).
    Rule,
    /// Bound on an equation (`Eq#`).
    Equation,
    /// Introduced existentially by a rule's right-hand side or by narrowing (`Ex#`).
    Existential,
}

impl VariableProvenance {
    /// In `external_variable_name`'s test order (`Rule#`, `Ex#`, `Eq#`); markers do not
    /// overlap, so the order only matters for documentation.
    pub const ALL: [Self; 3] = [Self::Rule, Self::Existential, Self::Equation];

    /// The marker prefixed to the variable name while a rule is internalized.
    pub const fn marker(self) -> &'static str {
        match self {
            Self::Rule => "Rule#",
            Self::Equation => "Eq#",
            Self::Existential => "Ex#",
        }
    }

    /// The letters `external_variable_name` keeps (`Rule`, `Eq`, `Ex`): the marker without
    /// its `#`.
    pub const fn external_prefix(self) -> &'static str {
        match self {
            Self::Rule => "Rule",
            Self::Equation => "Eq",
            Self::Existential => "Ex",
        }
    }
}

/// Split `name` at the first accepted marker it starts with, in the order given; a name that
/// starts with none of them is returned whole with `None`.
pub fn split_marker<'a>(
    name: &'a str,
    accepted: &[VariableProvenance],
) -> (Option<VariableProvenance>, &'a str) {
    accepted
        .iter()
        .find_map(|provenance| {
            name.strip_prefix(provenance.marker())
                .map(|rest| (Some(*provenance), rest))
        })
        .unwrap_or((None, name))
}

/// `base` followed by `!` and the counter, `fresh_variable`'s spelling.
pub fn with_fresh_counter(base: &str, counter: u64) -> String {
    format!("{base}!{counter}")
}

/// The inverse of [`with_fresh_counter`] when the name ends in `!` followed by one or more
/// ASCII digits; otherwise the whole name and `""`.
pub fn split_fresh_counter(name: &str) -> (&str, &str) {
    match name.rsplit_once('!') {
        Some((base, counter))
            if !counter.is_empty() && counter.bytes().all(|byte| byte.is_ascii_digit()) =>
        {
            (base, counter)
        }
        _ => (name, ""),
    }
}

impl Variable {
    /// The same variable with the provenance marker prefixed to its name.
    pub fn with_provenance(&self, provenance: VariableProvenance) -> Self {
        self.with_name(format!("{}{}", provenance.marker(), self.name))
    }

    /// The provenance marker the name starts with, if any.
    pub fn provenance(&self) -> Option<VariableProvenance> {
        split_marker(&self.name, &VariableProvenance::ALL).0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use VariableProvenance::{Equation, Existential, Rule};

    #[test]
    fn split_marker_strips_each_accepted_marker() {
        assert_eq!(split_marker("Rule#X", &[Rule, Equation]), (Some(Rule), "X"));
        assert_eq!(
            split_marker("Eq#X", &[Rule, Equation]),
            (Some(Equation), "X")
        );
        assert_eq!(
            split_marker("Ex#Frame", &[Existential, Rule]),
            (Some(Existential), "Frame")
        );
        assert_eq!(
            split_marker("Ex#Var'Unds'K!1", &VariableProvenance::ALL),
            (Some(Existential), "Var'Unds'K!1")
        );
    }

    #[test]
    fn split_marker_keeps_an_unmarked_name_whole() {
        assert_eq!(
            split_marker("VarX", &VariableProvenance::ALL),
            (None, "VarX")
        );
        assert_eq!(split_marker("", &VariableProvenance::ALL), (None, ""));
        let variable = Variable::new("VarX", super::super::Sort::simple("SortInt"));
        assert_eq!(variable.provenance(), None);
        assert_eq!(variable.with_provenance(Rule).name.as_ref(), "Rule#VarX");
        assert_eq!(variable.with_provenance(Rule).provenance(), Some(Rule));
    }

    #[test]
    fn split_marker_ignores_a_marker_that_is_not_accepted() {
        assert_eq!(split_marker("Eq#X", &[Existential, Rule]), (None, "Eq#X"));
        assert_eq!(split_marker("Ex#X", &[Rule, Equation]), (None, "Ex#X"));
    }

    #[test]
    fn fresh_counter_round_trips() {
        for base in ["VarX", "Frame", "Var'Unds'K", "X1", "a!b", "X!"] {
            for counter in [0, 7, 42] {
                let name = with_fresh_counter(base, counter);
                assert_eq!(
                    split_fresh_counter(&name),
                    (base, counter.to_string().as_str()),
                    "{name}"
                );
            }
        }
        assert_eq!(split_fresh_counter("VarX"), ("VarX", ""));
        assert_eq!(split_fresh_counter("X!"), ("X!", ""));
        assert_eq!(split_fresh_counter("X!1a"), ("X!1a", ""));
    }
}
