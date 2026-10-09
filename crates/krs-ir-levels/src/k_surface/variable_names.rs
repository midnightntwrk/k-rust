//! Readable, deterministic, injective K variable names for one sentence.
//!
//! Both the `.k` printer and the k-rust adapter must name variables through this module, so that
//! emitted K, native KORE, and every trace or residual derived from them spell a binder alike.
//! Stable identities stay in the IR and its sidecars; only the rendered spelling is derived here.
//!
//! K's variable token is `(\!|\?|@)?([A-Z][A-Za-z0-9'_]*|_|_[A-Z][A-Za-z0-9'_]*)` (`#KVariable` in
//! the pinned `kast.md`).
//! A spelling is taken from its binder as follows:
//!
//! - an authored name is converted from `snake_case` to `PascalCase` (`old_value` becomes
//!   `OldValue`); a raw identifier drops its `r#` prefix;
//! - an authored name with a leading `_` keeps K's `_`-prefixed form (`_x` becomes `_X`) only when
//!   the binder occurs at most once in the sentence, because K rejects a `_`-prefixed variable that is
//!   used more than once;
//! - an anonymous occurrence keeps its authored `_`-prefixed spelling, with the first letter
//!   capitalized when K requires it;
//! - a name that has no such form (non-ASCII, or starting with a digit) falls back to `V` followed by
//!   the identity's UTF-8 bytes in uppercase hexadecimal;
//! - a KRS-generated binder is spelled `Krs_` followed by its generated role in `PascalCase`, and a
//!   generated wildcard is additionally `_`-prefixed; no authored-derived spelling begins with
//!   `Krs_` or `_Krs_`, so this namespace is reserved for KRS;
//! - a claim existential is prefixed with `?`.
//!
//! Binders are named in a stable order: generated binders first, then anonymous occurrences, then
//! authored names, each ordered by semantic identity.
//! The first binder of a spelling keeps it; a later binder, or one whose spelling is reserved, takes
//! the first free suffix `_2`, `_3`, ... after the spelling.
//! Reserved spellings are the terminals of the definition and of the imported builtin modules, which
//! K's scanner would read as terminals, and the variables that K and k-rust generate inside a
//! sentence: `HERE`, `HOLE`, `K0`, `K1`, ... (strictness), `_Gen0`, ... and `_DotVar0`, ...
//! (anonymous variables and cell completion).
//! Every free base is kept before any suffix is chosen, and a base derived from an authored name
//! never contains `_` after its first character, so a suffixed spelling cannot displace one.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    CellContentFrame, CellPost, FixedInitializerCell, FixedInitializerContent,
    GrammarProductionItemKind, SemanticId, SemanticIdKind, ir::RESERVED_MARKER,
};

use crate::{
    ConfigurationSentence, ContextAliasSentence, DefinitionIr, DefinitionModule,
    DefinitionSentence, DefinitionTerm, DefinitionTermKind, RuleBodyRef, RuleSentence, SymbolId,
};

/// Identifier-shaped terminals of the pinned K 7.1.337 builtin modules that a KRS definition can
/// import (`domains.md`), which K's scanner would read as a terminal instead of a variable.
const BUILTIN_TERMINALS: &[&str] = &[
    "BE",
    "Base2String",
    "Bool2String",
    "Bytes2Hex",
    "Bytes2Int",
    "Bytes2MInt",
    "Bytes2String",
    "Float2Int",
    "Float2String",
    "Id2String",
    "Int2Bytes",
    "Int2Float",
    "Int2MInt",
    "Int2String",
    "LE",
    "List2Set",
    "ListItem",
    "MInt2Bytes",
    "MInt2Signed",
    "MInt2Unsigned",
    "Set2List",
    "SetItem",
    "Signed",
    "String2Base",
    "String2Bool",
    "String2Bytes",
    "String2Float",
    "String2Id",
    "String2Int",
    "StringBuffer2String",
    "Unsigned",
];

/// K variables with a fixed meaning in contexts and context aliases.
const K_RESERVED_VARIABLES: &[&str] = &["HERE", "HOLE"];

/// Prefix of every KRS-generated variable spelling.
const GENERATED_PREFIX: &str = "Krs_";

/// Definition-wide spellings that no rendered variable may take.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VariableNaming {
    reserved: BTreeSet<String>,
}

impl VariableNaming {
    /// Reserves every terminal of `definition`, the identifier-shaped builtin terminals, and K's
    /// reserved variables.
    #[must_use]
    pub fn new(definition: &DefinitionIr) -> Self {
        let mut reserved = definition_terminals(definition)
            .into_iter()
            .map(str::to_owned)
            .collect::<BTreeSet<_>>();
        reserved.extend(
            BUILTIN_TERMINALS
                .iter()
                .chain(K_RESERVED_VARIABLES)
                .map(|value| (*value).to_owned()),
        );
        Self { reserved }
    }

    /// Names the variables of a rule, claim, equation, or simplification.
    #[must_use]
    pub fn rule(&self, sentence: &RuleSentence) -> SentenceVariables {
        let mut scope = Scope::default();
        for variable in sentence.variables() {
            scope.declare(variable.id());
        }
        match sentence.relational_body() {
            RuleBodyRef::Term(rewrite) => {
                scope.term(rewrite.from());
                scope.term(rewrite.to());
            }
            RuleBodyRef::Predicate(rewrite) => {
                scope.predicate(rewrite.lhs());
                scope.predicate(rewrite.rhs());
            }
            RuleBodyRef::Configuration { body, .. } => {
                for clause in body.clauses() {
                    scope.term(clause.before());
                    let replaced = match clause.after() {
                        CellPost::Preserve => false,
                        CellPost::Replace { term } => {
                            scope.term(term);
                            true
                        }
                    };
                    // A named frame is printed on both sides of a replaced cell.
                    scope.frame(clause.frame(), if replaced { 2 } else { 1 });
                }
            }
        }
        // An equation's function context reads its cells beside the rewrite (KF-025).
        if let Some(context) = sentence.function_context() {
            for cell in context.cells().cells() {
                scope.term(cell.pattern());
                scope.frame(cell.frame(), 1);
            }
        }
        if let Some(condition) = sentence.requires() {
            scope.condition(condition);
        }
        if let Some(claim) = sentence.claim() {
            for binder in claim.universals() {
                scope.declare(binder.id());
            }
        }
        // Every sentence's existentials print with K's `?` prefix (D3).
        for binder in sentence.existentials() {
            scope.declare(binder.id());
            scope.existentials.insert(binder.id().clone());
        }
        // Fresh binders print with K's `!` prefix (KF-022).
        for binder in sentence.fresh() {
            scope.declare(binder.id());
            scope.fresh.insert(binder.id().clone());
        }
        if let Some(condition) = sentence.ensures() {
            scope.condition(condition);
        }
        scope.name(&self.reserved)
    }

    /// Names the variables of a context alias; its `HERE` binder is spelled `HERE`.
    #[must_use]
    pub fn context_alias(&self, sentence: &ContextAliasSentence) -> SentenceVariables {
        let mut scope = Scope::default();
        for variable in sentence.variables() {
            scope.declare(variable.id());
        }
        for cell in sentence.body().cells() {
            scope.term(cell.pattern());
            scope.frame(cell.frame(), 1);
        }
        scope
            .fixed
            .insert(sentence.here().clone(), "HERE".to_owned());
        scope.name(&self.reserved)
    }

    /// Names initializer variables that are not external configuration variables, which keep
    /// their `$NAME` spelling.
    #[must_use]
    pub fn configuration(&self, sentence: &ConfigurationSentence) -> SentenceVariables {
        let mut scope = Scope::default();
        scope.initializer(sentence.initializer());
        for variable in sentence.variables() {
            scope.occurrences.remove(variable.id());
        }
        scope.name(&self.reserved)
    }
}

/// Returns every plain terminal of every production in `definition`.
#[must_use]
pub fn definition_terminals(definition: &DefinitionIr) -> BTreeSet<&str> {
    definition
        .modules()
        .iter()
        .flat_map(DefinitionModule::sentences)
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Production(production) => Some(production.items()),
            _ => None,
        })
        .flatten()
        .filter_map(|item| match item.kind() {
            GrammarProductionItemKind::Terminal { text } => Some(text.as_str()),
            GrammarProductionItemKind::NonTerminal { .. }
            | GrammarProductionItemKind::RegexTerminal { .. } => None,
        })
        .collect()
}

/// The K spelling of every variable in one sentence.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SentenceVariables {
    names: BTreeMap<SemanticId, String>,
}

impl SentenceVariables {
    /// Returns the complete K spelling of `variable`, including a claim existential's `?`.
    #[must_use]
    pub fn name(&self, variable: &SemanticId) -> Option<&str> {
        self.names.get(variable).map(String::as_str)
    }

    /// Iterates over the named binders in identity order.
    pub fn iter(&self) -> impl Iterator<Item = (&SemanticId, &str)> {
        self.names
            .iter()
            .map(|(variable, name)| (variable, name.as_str()))
    }
}

#[derive(Default)]
struct Scope {
    occurrences: BTreeMap<SemanticId, usize>,
    existentials: BTreeSet<SemanticId>,
    fresh: BTreeSet<SemanticId>,
    fixed: BTreeMap<SemanticId, String>,
}

impl Scope {
    fn declare(&mut self, variable: &SemanticId) {
        self.occurrences.entry(variable.clone()).or_default();
    }

    fn occur(&mut self, variable: &SemanticId, count: usize) {
        *self.occurrences.entry(variable.clone()).or_default() += count;
    }

    fn frame(&mut self, frame: &CellContentFrame, count: usize) {
        if let CellContentFrame::KSequenceTail {
            binding: Some(binding),
            ..
        }
        | CellContentFrame::MapRemainder {
            binding: Some(binding),
            ..
        } = frame
        {
            self.occur(binding, count);
        }
    }

    fn condition(&mut self, condition: &crate::DefinitionCondition) {
        match condition {
            crate::IrCondition::Bool(condition) => self.term(condition.term()),
            crate::IrCondition::Predicate(predicate) => self.predicate(predicate),
        }
    }

    /// An `#Exists` binder occurs once where it is quantified (KF-039).
    fn predicate(&mut self, predicate: &crate::DefinitionMlPredicate) {
        for binder in predicate.binders() {
            self.occur(binder.id(), 1);
        }
        for term in predicate.terms() {
            self.term(term);
        }
    }

    fn initializer(&mut self, cells: &[FixedInitializerCell<SymbolId, DefinitionTerm>]) {
        for cell in cells {
            match cell.content() {
                FixedInitializerContent::Term { term } => self.term(term),
                FixedInitializerContent::Children { children } => self.initializer(children),
            }
        }
    }

    fn term(&mut self, term: &DefinitionTerm) {
        match term.kind() {
            DefinitionTermKind::Variable { variable } => self.occur(variable, 1),
            DefinitionTermKind::Token { .. } => {}
            DefinitionTermKind::Application { arguments, .. } => {
                for argument in arguments {
                    self.term(argument);
                }
            }
            DefinitionTermKind::KSequence { items, .. } => {
                for item in items {
                    self.term(item);
                }
            }
            DefinitionTermKind::Map(operands) => {
                for operand in operands.operands() {
                    self.term(operand);
                }
            }
            DefinitionTermKind::List(operands) => {
                for operand in operands.operands() {
                    self.term(operand);
                }
            }
            DefinitionTermKind::Set(operands) => {
                for operand in operands.operands() {
                    self.term(operand);
                }
            }
            DefinitionTermKind::Rewrite { from, to } => {
                self.term(from);
                self.term(to);
            }
            DefinitionTermKind::Cell { children, .. } => {
                for child in children {
                    self.term(child);
                }
            }
            DefinitionTermKind::As { alias, pattern } => {
                self.occur(alias, 1);
                self.term(pattern);
            }
            DefinitionTermKind::Or { alternatives } => {
                for alternative in alternatives {
                    self.term(alternative);
                }
            }
            DefinitionTermKind::Matches {
                subject, pattern, ..
            } => {
                self.term(subject);
                self.term(pattern);
            }
            DefinitionTermKind::Let {
                pattern,
                value,
                body,
                ..
            } => {
                self.term(pattern);
                self.term(value);
                self.term(body);
            }
        }
    }

    fn name(self, reserved: &BTreeSet<String>) -> SentenceVariables {
        let binders = self
            .occurrences
            .iter()
            .filter(|(variable, _)| !self.fixed.contains_key(*variable))
            .map(|(variable, occurrences)| Binder::new(variable, *occurrences))
            .collect();
        let mut names = assign(binders, reserved, self.fixed.values().cloned());
        for existential in &self.existentials {
            if let Some(name) = names.get_mut(existential) {
                name.insert(0, '?');
            }
        }
        for fresh in &self.fresh {
            if let Some(name) = names.get_mut(fresh) {
                name.insert(0, '!');
            }
        }
        names.extend(self.fixed);
        SentenceVariables { names }
    }
}

/// Naming precedence; generated binders claim their spellings first.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Origin {
    Generated,
    Anonymous,
    Authored,
    Local,
}

#[derive(Debug)]
struct Binder<'a> {
    variable: &'a SemanticId,
    origin: Origin,
    base: String,
}

impl<'a> Binder<'a> {
    fn new(variable: &'a SemanticId, occurrences: usize) -> Self {
        let (origin, base) = match variable.kind() {
            SemanticIdKind::Wildcard => (
                Origin::Generated,
                format!("_{}", generated_base(variable.as_str())),
            ),
            SemanticIdKind::Anonymous { name } => {
                (Origin::Anonymous, unreserved(anonymous_base(name)))
            }
            // A local binder (BIND-1) is spelled from its authored name; it
            // is named after every rule binder, so a collision gives the
            // local binder the suffix and emitted K never relies on K's
            // shadowing.
            SemanticIdKind::Local { name } => {
                (Origin::Local, unreserved(authored_base(name, occurrences)))
            }
            SemanticIdKind::Named if variable.as_str().contains(RESERVED_MARKER) => {
                (Origin::Generated, generated_base(variable.as_str()))
            }
            SemanticIdKind::Named => (
                Origin::Authored,
                unreserved(authored_base(variable.as_str(), occurrences)),
            ),
        };
        Self {
            variable,
            origin,
            base,
        }
    }
}

fn assign(
    mut binders: Vec<Binder<'_>>,
    reserved: &BTreeSet<String>,
    fixed: impl IntoIterator<Item = String>,
) -> BTreeMap<SemanticId, String> {
    binders
        .sort_by(|left, right| (left.origin, left.variable).cmp(&(right.origin, right.variable)));
    let mut taken = fixed.into_iter().collect::<BTreeSet<_>>();
    let mut names = BTreeMap::new();
    let mut pending = Vec::new();
    let reserved = |name: &str| reserved.contains(name) || generated_by_frontend(name);
    for binder in binders {
        if !reserved(&binder.base) && taken.insert(binder.base.clone()) {
            names.insert(binder.variable.clone(), binder.base);
        } else {
            pending.push(binder);
        }
    }
    for binder in pending {
        let mut suffix = 2_usize;
        let name = loop {
            let candidate = format!("{}_{suffix}", binder.base);
            if !reserved(&candidate) && !taken.contains(&candidate) {
                break candidate;
            }
            suffix += 1;
        };
        taken.insert(name.clone());
        names.insert(binder.variable.clone(), name);
    }
    names
}

/// Returns whether K or k-rust may generate a variable with this spelling inside a sentence.
fn generated_by_frontend(name: &str) -> bool {
    let numbered = |prefix: &str| {
        name.strip_prefix(prefix).is_some_and(|ordinal| {
            !ordinal.is_empty() && ordinal.bytes().all(|byte| byte.is_ascii_digit())
        })
    };
    numbered("K") || numbered("_Gen") || numbered("_DotVar")
}

/// Converts `snake_case` or `camelCase` ASCII to `PascalCase` without separators.
fn pascal_case(value: &str) -> Option<String> {
    let mut output = String::with_capacity(value.len());
    for segment in value.split('_').filter(|segment| !segment.is_empty()) {
        if !segment.bytes().all(|byte| byte.is_ascii_alphanumeric()) {
            return None;
        }
        let mut characters = segment.chars();
        if let Some(first) = characters.next() {
            output.push(first.to_ascii_uppercase());
            output.extend(characters);
        }
    }
    output
        .starts_with(|character: char| character.is_ascii_uppercase())
        .then_some(output)
}

fn authored_base(identity: &str, occurrences: usize) -> String {
    let name = identity.strip_prefix("r#").unwrap_or(identity);
    match pascal_case(name) {
        Some(body) if name.starts_with('_') && occurrences <= 1 => format!("_{body}"),
        Some(body) => body,
        None => hex_fallback(identity),
    }
}

/// Keeps a K-legal anonymous spelling and capitalizes the letter after `_` otherwise.
fn anonymous_base(spelling: &str) -> String {
    let rest = spelling.trim_start_matches('_');
    let mut characters = rest.chars();
    match characters.next() {
        Some(first)
            if first.is_ascii_alphabetic()
                && characters
                    .clone()
                    .all(|character| character == '_' || character.is_ascii_alphanumeric()) =>
        {
            format!("_{}{}", first.to_ascii_uppercase(), characters.as_str())
        }
        _ => format!("_{}", hex_fallback(spelling)),
    }
}

/// Spells a generated identity by its role after the reserved marker.
fn generated_base(identity: &str) -> String {
    let role = identity
        .split_once(RESERVED_MARKER)
        .map_or(identity, |(_, role)| role);
    let role = pascal_case(role).unwrap_or_else(|| hex_fallback(role));
    format!("{GENERATED_PREFIX}{role}")
}

/// Keeps a non-generated spelling out of the generated namespace.
fn unreserved(base: String) -> String {
    let (prefix, body) = base
        .strip_prefix('_')
        .map_or(("", base.as_str()), |body| ("_", body));
    if body.starts_with(GENERATED_PREFIX) {
        format!("{prefix}V{body}")
    } else {
        base
    }
}

fn hex_fallback(identity: &str) -> String {
    use std::fmt::Write as _;

    let mut output = String::from("V");
    for byte in identity.as_bytes() {
        write!(output, "{byte:02X}").expect("writing to String cannot fail");
    }
    output
}

/// Returns the K spelling of a variable that the KRS adapter itself introduces for `role`.
///
/// The spelling lies in the generated namespace, so it cannot equal any binder's spelling.
#[must_use]
pub fn generated_variable_name(role: &str) -> String {
    generated_base(&format!("{RESERVED_MARKER}{role}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(value: &str) -> SemanticId {
        SemanticId::new(value).expect("valid semantic ID")
    }

    fn named(entries: &[(&str, usize)], reserved: &[&str]) -> Vec<(String, String)> {
        let ids = entries
            .iter()
            .map(|(value, occurrences)| (id(value), *occurrences))
            .collect::<Vec<_>>();
        let binders = ids
            .iter()
            .map(|(variable, occurrences)| Binder::new(variable, *occurrences))
            .collect();
        let reserved = reserved.iter().map(|value| (*value).to_owned()).collect();
        assign(binders, &reserved, [])
            .into_iter()
            .map(|(variable, name)| (variable.as_str().to_owned(), name))
            .collect()
    }

    fn pairs(expected: &[(&str, &str)]) -> Vec<(String, String)> {
        let mut pairs = expected
            .iter()
            .map(|(left, right)| ((*left).to_owned(), (*right).to_owned()))
            .collect::<Vec<_>>();
        pairs.sort();
        pairs
    }

    #[test]
    fn authored_names_take_k_pascal_case() {
        assert_eq!(
            named(
                &[
                    ("rest", 2),
                    ("w0", 1),
                    ("old_value", 3),
                    ("s1", 2),
                    ("tail", 2)
                ],
                &[],
            ),
            pairs(&[
                ("old_value", "OldValue"),
                ("rest", "Rest"),
                ("s1", "S1"),
                ("tail", "Tail"),
                ("w0", "W0"),
            ]),
        );
    }

    #[test]
    fn leading_underscore_survives_only_for_a_single_occurrence() {
        assert_eq!(
            named(&[("_x", 1), ("_unused", 0), ("_twice", 2)], &[]),
            pairs(&[("_twice", "Twice"), ("_unused", "_Unused"), ("_x", "_X")]),
        );
    }

    #[test]
    fn collisions_take_stable_suffixes() {
        assert_eq!(
            named(&[("old_value", 1), ("oldValue", 1), ("old__value", 1)], &[]),
            pairs(&[
                ("oldValue", "OldValue"),
                ("old__value", "OldValue_2"),
                ("old_value", "OldValue_3"),
            ]),
        );
        // The same binders in another order receive the same names.
        assert_eq!(
            named(&[("old__value", 1), ("old_value", 1), ("oldValue", 1)], &[]),
            named(&[("old_value", 1), ("oldValue", 1), ("old__value", 1)], &[]),
        );
    }

    #[test]
    fn reserved_spellings_are_never_produced() {
        assert_eq!(
            named(
                &[("here", 1), ("list_item", 1), ("x", 1)],
                &["HERE", "ListItem", "X"]
            ),
            pairs(&[("here", "Here"), ("list_item", "ListItem_2"), ("x", "X_2")]),
        );
        let mut reserved = BTreeSet::new();
        reserved.extend(["HERE".to_owned(), "HOLE".to_owned()]);
        let ids = [id("h_e_r_e")];
        let binders = ids
            .iter()
            .map(|variable| Binder::new(variable, 1))
            .collect();
        assert_eq!(assign(binders, &reserved, [])[&ids[0]], "HERE_2");
    }

    #[test]
    fn frontend_generated_variables_are_reserved() {
        assert_eq!(
            named(
                &[
                    ("k0", 2),
                    ("k", 2),
                    ("_gen1", 1),
                    ("_dot_var0", 1),
                    ("kx1", 1)
                ],
                &[],
            ),
            pairs(&[
                ("_dot_var0", "_DotVar0_2"),
                ("_gen1", "_Gen1_2"),
                ("k", "K"),
                ("k0", "K0_2"),
                ("kx1", "Kx1"),
            ]),
        );
    }

    #[test]
    fn raw_and_non_ascii_names_have_k_legal_fallbacks() {
        assert_eq!(
            named(&[("r#type", 1), ("éλ", 1), ("_1", 1), ("café", 1)], &[]),
            pairs(&[
                ("_1", "V5F31"),
                ("café", "V636166C3A9"),
                ("r#type", "Type"),
                ("éλ", "VC3A9CEBB"),
            ]),
        );
    }

    #[test]
    fn generated_binders_use_the_reserved_namespace() {
        let wildcard = SemanticId::wildcard(3);
        let anonymous = SemanticId::anonymous("_B_PROGRAM", 4).expect("anonymous ID");
        let lower = SemanticId::anonymous("_b", 5).expect("anonymous ID");
        let repeated = SemanticId::anonymous("_B_PROGRAM", 6).expect("anonymous ID");
        let impostor = SemanticId::anonymous("_Krs_Wildcard3", 7).expect("anonymous ID");
        let ids = [
            (wildcard.clone(), 1),
            (anonymous.clone(), 1),
            (lower.clone(), 1),
            (repeated.clone(), 1),
            (impostor.clone(), 1),
            (id("krs_wildcard3"), 2),
        ];
        let binders = ids
            .iter()
            .map(|(variable, occurrences)| Binder::new(variable, *occurrences))
            .collect();
        let names = assign(binders, &BTreeSet::new(), []);
        assert_eq!(names[&wildcard], "_Krs_Wildcard3");
        assert_eq!(names[&anonymous], "_B_PROGRAM");
        assert_eq!(names[&repeated], "_B_PROGRAM_2");
        assert_eq!(names[&lower], "_B");
        assert_eq!(names[&impostor], "_VKrs_Wildcard3");
        assert_eq!(names[&id("krs_wildcard3")], "KrsWildcard3");
        assert_eq!(generated_variable_name("counter7"), "Krs_Counter7");
    }

    #[test]
    fn every_name_is_k_legal_and_distinct() {
        let ids = [
            "a", "A", "_a", "a_", "__a", "a__b", "aB", "a_b", "_", "__", "x9", "r#match", "ß",
        ];
        let entries = ids.iter().map(|value| (*value, 1)).collect::<Vec<_>>();
        let names = named(&entries, &[]);
        let distinct = names.iter().map(|(_, name)| name).collect::<BTreeSet<_>>();
        assert_eq!(distinct.len(), names.len());
        for (_, name) in &names {
            let body = name.strip_prefix('_').unwrap_or(name);
            assert!(body.starts_with(|character: char| character.is_ascii_uppercase()));
            assert!(
                body.chars()
                    .all(|character| character == '_' || character.is_ascii_alphanumeric())
            );
        }
    }

    #[test]
    fn local_binders_take_their_authored_name_and_yield_on_collision() {
        let first = SemanticId::local("x", 0).expect("local ID");
        let second = SemanticId::local("x", 1).expect("local ID");
        let other = SemanticId::local("pair_left", 2).expect("local ID");
        let ids = [
            (first.clone(), 2),
            (second.clone(), 2),
            (other.clone(), 2),
            (id("pairLeft"), 1),
        ];
        let binders = ids
            .iter()
            .map(|(variable, occurrences)| Binder::new(variable, *occurrences))
            .collect();
        let names = assign(binders, &BTreeSet::new(), []);
        assert_eq!(names[&first], "X");
        assert_eq!(names[&second], "X_2");
        assert_eq!(names[&id("pairLeft")], "PairLeft");
        assert_eq!(names[&other], "PairLeft_2");
    }

    #[test]
    fn fresh_binders_take_the_bang_prefix() {
        let mut scope = Scope::default();
        scope.occur(&id("l"), 2);
        scope.occur(&id("x"), 2);
        scope.fresh.insert(id("l"));
        let names = scope.name(&BTreeSet::new());
        assert_eq!(names.name(&id("l")), Some("!L"));
        assert_eq!(names.name(&id("x")), Some("X"));
    }

    #[test]
    fn a_colliding_fresh_binder_keeps_its_suffix_after_the_bang() {
        // `L` (a pattern binder) and fresh `l` both spell `L`; the collision
        // suffix is assigned before the `!` prefix.
        let mut scope = Scope::default();
        scope.occur(&id("L"), 2);
        scope.occur(&id("l"), 2);
        scope.fresh.insert(id("l"));
        let names = scope.name(&BTreeSet::new());
        assert_eq!(names.name(&id("L")), Some("L"));
        assert_eq!(names.name(&id("l")), Some("!L_2"));
    }
}
