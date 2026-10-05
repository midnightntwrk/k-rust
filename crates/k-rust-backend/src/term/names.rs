//! Backend-internal variable naming: provenance markers, fresh counters, and hook names.
//!
//! The marker is part of the name string on purpose: `Ord for Variable` is derived over
//! (`kind`, `sort`, `name`) and every `BTreeSet<Variable>` in the rewriter iterates in that
//! order, which decides fresh-counter assignment and therefore printed variable names.
//!
//! # Two namespaces
//!
//! A variable name read from KORE is kept verbatim, and every reader accepts only a KORE
//! identifier there ([`variable_name_problems`]): `[A-Za-z][A-Za-z0-9'-]*` for an element
//! variable, `@` followed by such an identifier for a set variable. No such name contains `#`
//! or `!`. Every name the backend makes from another one adds `#` (a provenance marker,
//! [`VariableProvenance`]) or `!` (a fresh counter, [`FreshMarker`]). The two namespaces are
//! therefore disjoint inside the backend: no name read from a request or a definition is a
//! rule variable or a mint, whatever it is spelled, and no mint is a name of the input.
//!
//! # Printing
//!
//! [`encode_variable_name`] prints a name that is a KORE identifier unchanged and escapes any
//! other one so that it becomes one. The escape is injective, and the image of a marked name
//! contains `-h` or `-b`, so two distinct names of the backend print alike only when one is a
//! name of the input spelled like the escape of the other. The backend keeps such a pair out
//! of every response (`crate::fresh::FreshCounter`, and the binder renaming of
//! `crate::externalize`).

use std::{borrow::Cow, fmt};

use k_rust_kore::kore::lexical::{self, Problem};

use super::Variable;

/// The variable-name contract of the backend's responses, for consumers that depend on it.
/// A consumer that guards on this value notices every change of how a name is read or printed.
///
/// 1 (9e07ed10): printing through [`encode_variable_name`] and reading through
/// [`decode_variable_name`] are a bijection on the accepted names: a reader decodes `-h` and
/// `-b` back into the `#` and `!` markers, so a printed mint read back is that mint.
///
/// 2 (9494bb48, the integration K-in-K2 tested): version 1, and every free variable a rewrite
/// mints is drawn from one counter per request, seeded or reserved against the request's
/// names, so each mint is unique in the request, never reused on a path, and distinct from
/// every name of the request.
///
/// 3: names are read verbatim, not decoded. A variable name read from KORE must be a KORE
/// identifier ([`variable_name_problems`]) and is kept as it is spelled, so `Ex-hX-b0` read back
/// is a variable of that name, not the mint `Ex#X!0`; a printed response read back is the
/// internal one up to a bijective renaming that is the identity on the request's names. A name
/// that is a KORE identifier prints unchanged, every other name the backend prints is escaped
/// injectively by [`encode_variable_name`], and a printed binder never captures a variable it
/// did not bind. Every variable a rewrite introduces into a state (a right-hand-side
/// existential, a rule variable the match left unbound, a narrowed frame) is minted from one
/// counter per request (`crate::fresh::FreshCounter`), which only grows and skips every
/// spelling of the request's variables: it is unique in the request, never reused along a
/// path, and printed like no variable of the request. Since those names differ between two
/// branches, results equal up to an injective renaming of the variables the request does not
/// name are one result: a search reports one state or solution, and a state-set execution one
/// leaf, for each class (`crate::fresh::RequestNames::state_key`).
pub const VARIABLE_IDENTITY: u32 = 3;

/// Whether `name` is a variable name a KORE reader accepts: an identifier, or `@` followed by
/// an identifier for a set variable.
pub fn is_variable_identifier(name: &str) -> bool {
    lexical::identifier_problems(name.strip_prefix('@').unwrap_or(name)).is_empty()
}

/// The lexical problems of `name` as the name of a variable of the given kind: empty exactly
/// when a KORE reader accepts it.
pub fn variable_name_problems(name: &str, set: bool) -> Vec<Problem> {
    if set {
        lexical::set_variable_problems(name)
    } else {
        lexical::identifier_problems(name)
    }
}

/// The KORE spelling of a backend variable name.
///
/// A name that is already a variable identifier ([`is_variable_identifier`]) prints unchanged;
/// these are the names read from KORE. Any other name, which has a provenance marker or a
/// fresh counter, is escaped with `-` as the only escape character: `--` for `-`, `-h` for
/// `#`, `-b` for `!`, `-a` for an `@` away from the start, and `-u{lowercase hex}-` for any
/// other character outside the identifier alphabet. Letters, digits, `'` and a leading `@`
/// are kept. So `Ex#Frame!0` prints as `Ex-hFrame-b0`, `X!apart1` as `X-bapart1` and
/// `@Rule#M` as `@Rule-hM`.
///
/// For a name that starts with a letter after an optional `@`, as every backend name does,
/// the result is a variable identifier. The escape is injective, so two escaped names never
/// print alike, and an identifier never prints like another identifier. An identifier and an escaped name print alike only when the
/// identifier is spelled like the escape (a request variable named `Ex-hFrame-b0`).
pub fn encode_variable_name(name: &str) -> String {
    if is_variable_identifier(name) {
        name.to_owned()
    } else {
        escape_variable_name(name)
    }
}

fn escape_variable_name(name: &str) -> String {
    let mut wire = String::with_capacity(name.len() + 4);
    for (index, character) in name.chars().enumerate() {
        match character {
            'A'..='Z' | 'a'..='z' | '0'..='9' | '\'' => wire.push(character),
            '@' if index == 0 => wire.push('@'),
            '-' => wire.push_str("--"),
            '#' => wire.push_str("-h"),
            '!' => wire.push_str("-b"),
            '@' => wire.push_str("-a"),
            other => {
                use fmt::Write;
                write!(wire, "-u{:x}-", u32::from(other)).expect("writing to a string");
            }
        }
    }
    wire
}

/// A spelling that is not the escape of a backend name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VariableNameError {
    pub name: String,
}

impl fmt::Display for VariableNameError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "Invalid variable name '{}'", self.name)
    }
}

impl std::error::Error for VariableNameError {}

/// The backend name whose escape (as [`encode_variable_name`] writes it for a name that is not
/// an identifier) is `wire`, for consumers that classify printed names.
///
/// No reader uses it: a name read from KORE is kept verbatim. A printed name `wire` whose
/// decoding has a marker or a counter (`Ex-hFrame-b0` decodes to `Ex#Frame!0`) was printed
/// either from that backend name or from a request variable spelled `wire`; one response never
/// contains both. A spelling without `-` decodes to itself. Any other `-` sequence, a trailing
/// `-`, `-u`, or a result that is not a letter-initial name over letters, digits, `'`, `#`,
/// `!` and `-` (after a leading `@`) is an error.
pub fn decode_variable_name(wire: &str) -> Result<String, VariableNameError> {
    let invalid = || VariableNameError { name: wire.into() };
    let mut decoded = String::with_capacity(wire.len());
    let mut characters = wire.chars();
    while let Some(character) = characters.next() {
        match character {
            '-' => decoded.push(match characters.next() {
                Some('-') => '-',
                Some('h') => '#',
                Some('b') => '!',
                Some('a') => '@',
                _ => return Err(invalid()),
            }),
            other => decoded.push(other),
        }
    }
    let body = decoded.strip_prefix('@').unwrap_or(&decoded);
    if !body.starts_with(|character: char| character.is_ascii_alphabetic())
        || !body.chars().all(|character| {
            character.is_ascii_alphanumeric() || matches!(character, '\'' | '#' | '!' | '-')
        })
        || escape_variable_name(&decoded) != wire
    {
        return Err(invalid());
    }
    Ok(decoded)
}

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
    /// Markers do not overlap, so this order only matters for documentation.
    pub const ALL: [Self; 3] = [Self::Rule, Self::Existential, Self::Equation];

    /// The marker prefixed to the variable name while a rule is internalized.
    pub const fn marker(self) -> &'static str {
        match self {
            Self::Rule => "Rule#",
            Self::Equation => "Eq#",
            Self::Existential => "Ex#",
        }
    }

    /// The marker without its `#` (`Rule`, `Eq`, `Ex`), for consumers that name a provenance
    /// family. The printer writes the whole marker through [`encode_variable_name`].
    pub const fn external_prefix(self) -> &'static str {
        match self {
            Self::Rule => "Rule",
            Self::Equation => "Eq",
            Self::Existential => "Ex",
        }
    }
}

/// Split `name` at the first accepted marker it starts with, in the order given, after the
/// initial `@` of a set variable. The rest is the unmarked name, with a set variable's `@`
/// kept: `@Rule#M` gives `@M`, so a name rebuilt from the rest with
/// [`Variable::with_provenance`] is again a set name. A name that starts with none of the
/// markers is returned whole with `None`.
pub fn split_marker<'a>(
    name: &'a str,
    accepted: &[VariableProvenance],
) -> (Option<VariableProvenance>, Cow<'a, str>) {
    let (set, body) = match name.strip_prefix('@') {
        Some(body) => (true, body),
        None => (false, name),
    };
    accepted
        .iter()
        .find_map(|provenance| {
            body.strip_prefix(provenance.marker()).map(|rest| {
                let rest = if set {
                    Cow::Owned(format!("@{rest}"))
                } else {
                    Cow::Borrowed(rest)
                };
                (Some(*provenance), rest)
            })
        })
        .unwrap_or((None, Cow::Borrowed(name)))
}

/// The word between the `!` and the counter of a backend-minted fresh name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FreshMarker {
    /// `{base}!{counter}`: variables the rewriter introduces (narrowed frames, unbound rule
    /// variables, overload witnesses).
    Rewrite,
    /// `{base}!claim{counter}`: the variables of a claim applied as a circularity.
    Claim,
    /// `{base}!exists{counter}`: consequent existentials of an implication check.
    Exists,
    /// `{base}!apart{counter}`: rule variables renamed apart from the scope of an application.
    Apart,
    /// `{base}!binder{counter}`: quantifier variables renamed so that a substitution under
    /// them, or the printer, captures nothing; they stay bound.
    Binder,
}

impl FreshMarker {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Rewrite => "",
            Self::Claim => "claim",
            Self::Exists => "exists",
            Self::Apart => "apart",
            Self::Binder => "binder",
        }
    }
}

/// `base`, `!`, the marker, and the counter: the spelling of every fresh name `crate::fresh`
/// mints.
pub fn with_fresh_marker(base: &str, marker: FreshMarker, counter: u64) -> String {
    format!("{base}!{}{counter}", marker.as_str())
}

/// `base` followed by `!` and the counter, `fresh::fresh_variable`'s spelling.
pub fn with_fresh_counter(base: &str, counter: u64) -> String {
    with_fresh_marker(base, FreshMarker::Rewrite, counter)
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
    /// The same variable with the provenance marker prefixed to its name, after the initial
    /// `@` of a set variable (`@Rule#M`), so the name stays a set name.
    pub fn with_provenance(&self, provenance: VariableProvenance) -> Self {
        match self.name.strip_prefix('@') {
            Some(body) => self.with_name(format!("@{}{body}", provenance.marker())),
            None => self.with_name(format!("{}{}", provenance.marker(), self.name)),
        }
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

    fn split(name: &str, accepted: &[VariableProvenance]) -> (Option<VariableProvenance>, String) {
        let (provenance, rest) = split_marker(name, accepted);
        (provenance, rest.into_owned())
    }

    #[test]
    fn split_marker_strips_each_accepted_marker() {
        assert_eq!(
            split("Rule#X", &[Rule, Equation]),
            (Some(Rule), "X".to_owned())
        );
        assert_eq!(
            split("Eq#X", &[Rule, Equation]),
            (Some(Equation), "X".to_owned())
        );
        assert_eq!(
            split("Ex#Frame", &[Existential, Rule]),
            (Some(Existential), "Frame".to_owned())
        );
        assert_eq!(
            split("Ex#Var'Unds'K!1", &VariableProvenance::ALL),
            (Some(Existential), "Var'Unds'K!1".to_owned())
        );
    }

    #[test]
    fn split_marker_keeps_an_unmarked_name_whole() {
        assert_eq!(
            split("VarX", &VariableProvenance::ALL),
            (None, "VarX".to_owned())
        );
        assert_eq!(split("", &VariableProvenance::ALL), (None, "".to_owned()));
        let variable = Variable::new("VarX", super::super::Sort::simple("SortInt"));
        assert_eq!(variable.provenance(), None);
        assert_eq!(variable.with_provenance(Rule).name.as_ref(), "Rule#VarX");
        assert_eq!(variable.with_provenance(Rule).provenance(), Some(Rule));
    }

    #[test]
    fn split_marker_ignores_a_marker_that_is_not_accepted() {
        assert_eq!(
            split("Eq#X", &[Existential, Rule]),
            (None, "Eq#X".to_owned())
        );
        assert_eq!(split("Ex#X", &[Rule, Equation]), (None, "Ex#X".to_owned()));
    }

    #[test]
    fn a_set_variable_keeps_its_at_sign_first() {
        let variable = Variable::set("@M", super::super::Sort::simple("SortInt"));
        let marked = variable.with_provenance(Rule);
        assert_eq!(marked.name.as_ref(), "@Rule#M");
        assert_eq!(marked.provenance(), Some(Rule));
        assert_eq!(split("@Rule#M", &[Rule]), (Some(Rule), "@M".to_owned()));
        assert_eq!(split("@M", &[Rule]), (None, "@M".to_owned()));
        assert_eq!(encode_variable_name("@Rule#M"), "@Rule-hM");
        assert_eq!(encode_variable_name("@Ex#M!0"), "@Ex-hM-b0");
    }

    /// Every name up to four characters over an alphabet with the identifier characters, the
    /// markers and `@`.
    fn names() -> Vec<String> {
        const ALPHABET: [char; 9] = ['a', 'E', 'x', '0', '\'', '-', '#', '!', '@'];
        let mut names = vec![String::new()];
        let mut all = Vec::new();
        for _ in 0..4 {
            names = names
                .iter()
                .flat_map(|name| {
                    ALPHABET.iter().map(move |character| {
                        let mut name = name.clone();
                        name.push(*character);
                        name
                    })
                })
                .collect();
            all.extend(names.iter().cloned());
        }
        all
    }

    #[test]
    fn printing_keeps_identifiers_and_escapes_every_other_name_injectively() {
        let mut printed = std::collections::BTreeMap::<String, String>::new();
        for name in names() {
            // Every backend name starts with a letter, after the `@` of a set variable.
            let body = name.strip_prefix('@').unwrap_or(&name);
            if !body.starts_with(|character: char| character.is_ascii_alphabetic()) {
                continue;
            }
            let wire = encode_variable_name(&name);
            assert!(
                is_variable_identifier(&wire),
                "{name:?} printed as {wire:?}"
            );
            if is_variable_identifier(&name) {
                assert_eq!(wire, name);
                continue;
            }
            // Escaped names never print alike, and decode back.
            if let Some(other) = printed.insert(wire.clone(), name.clone()) {
                panic!("{other:?} and {name:?} both print as {wire:?}");
            }
            if !body.contains('@') {
                assert_eq!(decode_variable_name(&wire).as_deref(), Ok(name.as_str()));
            }
        }
    }

    #[test]
    fn escaped_names_print_as_documented() {
        for (name, wire) in [
            ("Rule#VarX", "Rule-hVarX"),
            ("Ex#VarI!0", "Ex-hVarI-b0"),
            ("Ex#VarI1!0", "Ex-hVarI1-b0"),
            ("Ex#VarI!10", "Ex-hVarI-b10"),
            ("Ex#Frame!0", "Ex-hFrame-b0"),
            ("X!apart1", "X-bapart1"),
            ("Ex#a-x!0", "Ex-ha--x-b0"),
            ("a.b", "a-u2e-b"),
        ] {
            assert_eq!(encode_variable_name(name), wire);
        }
        for identifier in ["ExFrame0", "X'Bang'apart1", "a-x", "Ex-hFrame-b0", "@M"] {
            assert_eq!(encode_variable_name(identifier), identifier);
        }
    }

    #[test]
    fn decoding_inverts_only_the_escape() {
        assert_eq!(decode_variable_name("ExFrame0").as_deref(), Ok("ExFrame0"));
        assert_eq!(
            decode_variable_name("Ex-hFrame-b0").as_deref(),
            Ok("Ex#Frame!0")
        );
        for wire in ["a-x", "a-", "a-u2e-b", "0a", "-hX", ""] {
            assert!(decode_variable_name(wire).is_err(), "{wire:?}");
        }
    }

    #[test]
    fn readers_accept_exactly_the_kore_identifiers() {
        assert!(variable_name_problems("Ex-hX-b0", false).is_empty());
        assert!(variable_name_problems("@M", true).is_empty());
        for name in ["Ex#X", "X!0", "@M", "0X", ""] {
            assert!(!variable_name_problems(name, false).is_empty(), "{name:?}");
        }
        for name in ["M", "@Ex#M", "@"] {
            assert!(!variable_name_problems(name, true).is_empty(), "{name:?}");
        }
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
        assert_eq!(
            with_fresh_marker("VarX", FreshMarker::Claim, 3),
            "VarX!claim3"
        );
        assert_eq!(
            with_fresh_marker("VarX", FreshMarker::Exists, 0),
            "VarX!exists0"
        );
        assert_eq!(split_fresh_counter("VarX!claim3"), ("VarX!claim3", ""));
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
