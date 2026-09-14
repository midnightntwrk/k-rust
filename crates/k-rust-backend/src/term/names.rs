//! Backend-internal variable naming: provenance markers, fresh counters, and hook names.
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

/// A hook attribute value, `NAMESPACE.operation`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HookName<'a> {
    pub namespace: &'a str,
    pub operation: &'a str,
}

impl<'a> HookName<'a> {
    /// `None` when there is no `.`; the namespace is everything before the first `.`.
    pub fn parse(hook: &'a str) -> Option<Self> {
        hook.split_once('.').map(|(namespace, operation)| Self {
            namespace,
            operation,
        })
    }

    pub fn kind(self) -> HookNamespace {
        match self.namespace {
            "INT" => HookNamespace::Int,
            "BOOL" => HookNamespace::Bool,
            "KEQUAL" => HookNamespace::KEqual,
            "IO" => HookNamespace::Io,
            "LIST" => HookNamespace::List,
            "MAP" => HookNamespace::Map,
            "SET" => HookNamespace::Set,
            "BYTES" => HookNamespace::Bytes,
            "FLOAT" => HookNamespace::Float,
            "STRING" => HookNamespace::String,
            "SUBSTITUTION" => HookNamespace::Substitution,
            namespace if PLUGIN_HOOK_NAMESPACES.contains(&namespace) => HookNamespace::Plugin,
            _ => HookNamespace::Other,
        }
    }
}

/// Hook namespaces this backend dispatches beyond K's fixed builtin set.
///
/// Java K only treats these plugin namespaces as hooked when `kompile --hook-namespaces` names
/// them; the Rust backend implements them natively, so KORE emitted for it admits them by default.
pub const PLUGIN_HOOK_NAMESPACES: [&str; 3] = ["KRYPTO", "HASH", "SECP256K1"];

/// The namespaces the backend evaluates natively or through the crypto plugin.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum HookNamespace {
    Int,
    Bool,
    KEqual,
    Io,
    List,
    Map,
    Set,
    Bytes,
    Float,
    String,
    Substitution,
    /// `KRYPTO`, `HASH`, `SECP256K1`: `builtin::krypto`.
    Plugin,
    Other,
}

impl HookNamespace {
    /// The namespace's spelling; `None` for the plugin family (three spellings) and for
    /// `Other`.
    pub const fn as_str(self) -> Option<&'static str> {
        match self {
            Self::Int => Some("INT"),
            Self::Bool => Some("BOOL"),
            Self::KEqual => Some("KEQUAL"),
            Self::Io => Some("IO"),
            Self::List => Some("LIST"),
            Self::Map => Some("MAP"),
            Self::Set => Some("SET"),
            Self::Bytes => Some("BYTES"),
            Self::Float => Some("FLOAT"),
            Self::String => Some("STRING"),
            Self::Substitution => Some("SUBSTITUTION"),
            Self::Plugin | Self::Other => None,
        }
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

    #[test]
    fn hook_name_parses_at_the_first_dot() {
        assert_eq!(
            HookName::parse("MAP.lookup"),
            Some(HookName {
                namespace: "MAP",
                operation: "lookup"
            })
        );
        assert_eq!(
            HookName::parse("KRYPTO.foo.bar"),
            Some(HookName {
                namespace: "KRYPTO",
                operation: "foo.bar"
            })
        );
        assert_eq!(HookName::parse("nodot"), None);
    }

    #[test]
    fn hook_namespace_kind_matches_every_spelling() {
        for namespace in [
            HookNamespace::Int,
            HookNamespace::Bool,
            HookNamespace::KEqual,
            HookNamespace::Io,
            HookNamespace::List,
            HookNamespace::Map,
            HookNamespace::Set,
            HookNamespace::Bytes,
            HookNamespace::Float,
            HookNamespace::String,
            HookNamespace::Substitution,
        ] {
            let spelling = namespace.as_str().expect("named namespace");
            let hook = format!("{spelling}.op");
            assert_eq!(HookName::parse(&hook).map(HookName::kind), Some(namespace));
        }
        for plugin in PLUGIN_HOOK_NAMESPACES {
            let hook = format!("{plugin}.op");
            assert_eq!(
                HookName::parse(&hook).map(HookName::kind),
                Some(HookNamespace::Plugin)
            );
        }
        assert_eq!(
            HookName::parse("KVAR.KVar").map(HookName::kind),
            Some(HookNamespace::Other)
        );
        assert_eq!(HookNamespace::Plugin.as_str(), None);
    }
}
