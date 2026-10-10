//! What a priority conjunct of a rewrite axiom excludes, read from the written definition.
//!
//! A *priority conjunct* is a left-hand-side component `\not{S}(A{}())` of a rewrite axiom with
//! `A` a nullary alias (no sort parameters, no parameters), recognised by shape. It states that
//! the rule applies only outside what `A` denotes. The *applicability pattern* `App(ρ)` of a
//! rewrite axiom ρ is its written left-hand-side components (nested `\and` flattened) other than
//! priority conjuncts and `\top`s, in written order; the requires is among them, so a
//! configuration satisfies `App(ρ)` exactly when ρ applies to it.
//!
//! A disjunct δ of a nullary alias (the arguments of its written body after flattening nested
//! `\or`, `\bottom`s discarded) *names* the rewrite axiom ρ' when:
//! 1. δ is `\exists w1 .. \exists wn. B` (n ≥ 0) with `{w1..wn}` exactly the free variables of
//!    `B` (same name, sort and kind, no binder repeated), so δ denotes "ρ' applies";
//! 2. the components of `B` (nested `\and` flattened, `\top`s removed) equal `App(ρ')` in order
//!    under one bijective, sort- and kind-preserving renaming of variables, everything else
//!    compared literally as written ([`VariableRenaming`]);
//! 3. ρ' is executable and has no sort parameters.
//!
//! The summary of a nullary alias `A` ([`PriorityConjuncts::summary`]) is computed once and
//! memoised: `None` when `A` denotes nothing, the highest priority `A` names with a witness, or
//! the first disjunct that names no rule. Each disjunct, in written order, contributes the
//! smallest priority among the rules it names when it names one; otherwise, when it is an
//! application `A'{}()` of a nullary alias, the summary of `A'`; otherwise a failure.
//!
//! Soundness, by induction on alias nesting: every configuration `A` denotes satisfies `App(ρ')`
//! for an executable ρ' whose priority is at most the summary's. A naming disjunct denotes exactly
//! where its rule applies, a nested alias holds by hypothesis, and a union keeps the bound. Since a
//! rule of priority `p` is offered only subjects to which no executable rule of smaller priority
//! applies, a conjunct whose alias summarises below `p` holds on every subject the rule is offered.
//! The check is sufficient, not complete.
//!
//! "Names a rule" is tried before "nested alias" because a rule without variables can be named by
//! a bare application of the alias that is its whole left-hand side: read as a nested alias, that
//! alias's body is the rule's unfolded left-hand side, which is not `App` as written, so the other
//! order refuses a valid definition. Both readings are sound. The recursion through nested
//! aliases ends because alias cycles are refused at declaration (`alias::measure_aliases`).
//!
//! A conjunct of a rule of priority `p` is *discharged* when its alias denotes nothing or
//! summarises strictly below `p` (rules of equal priority are not tried before one another). The
//! load replaces it by `\top` in the written pattern ([`Discharge::discharge`]), before aliases
//! are unfolded, so a priority alias is never unfolded and the rule internalised equals the rule
//! written without the conjunct. A conjunct that is not discharged refuses the load: krust has no
//! predicate "the subject is not in this set", and reading it as a predicate misreads it.
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::hash::{Hash, Hasher};

use k_rust_kore::kore::ast as kore;

use crate::{
    alias::AliasDefinition,
    definition::DefinitionError,
    rule::{
        AxiomError, RuleAttributes, SentenceKey, VariableRenaming, flatten_and, hash_pattern_shape,
    },
    term::Name,
};

/// A step from a nullary alias to one of its disjuncts: the alias and the disjunct's index among
/// its disjuncts (nested `\or` flattened, `\bottom`s discarded).
pub type DisjunctStep = (String, usize);

/// Why a disjunct of a priority alias was not read as a set of rules that apply.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DisjunctFailure {
    /// The disjunct names no rewrite axiom and applies no nullary alias.
    NamesNoRule,
    /// The disjunct has the applicability pattern of rewrite axioms that are all non-executable,
    /// so no step ever applies them and they exclude nothing from a lower priority.
    NamedRuleNotExecutable,
    /// The disjunct has the applicability pattern of rewrite axioms that are all sort-parametric
    /// (or non-executable), whose instances are not the written pattern.
    ParametricNamedRule,
}

/// Why a priority conjunct is not discharged.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum PriorityConjunctFailure {
    /// The disjunct at the end of `path` is not read as a set of rules that apply; `path` lists
    /// the steps from the conjunct's alias down to it.
    Disjunct {
        path: Vec<DisjunctStep>,
        reason: DisjunctFailure,
    },
    /// The alias names `rule`, of priority `named`, which is not strictly below the priority
    /// `own` of the rule carrying the conjunct; `path` lists the steps from the conjunct's alias
    /// down to the disjunct that names `rule`.
    NotStrictlyHigher {
        named: u8,
        own: u8,
        rule: SentenceKey,
        path: Vec<DisjunctStep>,
    },
}

impl fmt::Display for DisjunctFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::NamesNoRule => "it names no rewrite axiom and applies no nullary alias",
            Self::NamedRuleNotExecutable => "the rewrite axioms it names are not executable",
            Self::ParametricNamedRule => {
                "the rewrite axioms it names are sort-parametric or not executable"
            }
        })
    }
}

impl fmt::Display for PriorityConjunctFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn write_path(formatter: &mut fmt::Formatter<'_>, path: &[DisjunctStep]) -> fmt::Result {
            for (position, (alias, index)) in path.iter().enumerate() {
                if position > 0 {
                    formatter.write_str(", then ")?;
                }
                write!(formatter, "disjunct {index} of {alias}")?;
            }
            Ok(())
        }
        match self {
            Self::Disjunct { path, reason } => {
                write_path(formatter, path)?;
                write!(formatter, ": {reason}")
            }
            Self::NotStrictlyHigher {
                named,
                own,
                rule: (module, index),
                path,
            } => {
                write_path(formatter, path)?;
                write!(
                    formatter,
                    " names the rule at sentence {index} of module {module}, of priority \
                     {named}, not strictly below the priority {own} of the rule carrying it"
                )
            }
        }
    }
}

/// The highest priority a nullary alias names, and where.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Witness {
    pub(crate) priority: u8,
    /// The named rule of that priority.
    pub(crate) rule: SentenceKey,
    /// The steps from the summarised alias down to the disjunct that names `rule`.
    pub(crate) path: Vec<DisjunctStep>,
}

/// Why a nullary alias has no summary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SummaryError {
    Failure(PriorityConjunctFailure),
    /// The attributes of a rule a disjunct names are malformed: the error classifying that axiom
    /// gives.
    Axiom(AxiomError),
}

/// `Ok(None)` when the alias denotes nothing.
pub(crate) type Summary = Result<Option<Witness>, SummaryError>;

/// One written rewrite axiom.
struct WrittenRule<'a> {
    sentence: SentenceKey,
    parametric: bool,
    attributes: &'a kore::Attributes,
    application: Vec<&'a kore::Pattern>,
    /// `(priority, executable)` once the attributes are parsed: only rules a disjunct names are.
    facts: Option<(u8, bool)>,
}

/// The rewrite axioms of a definition by applicability pattern, and the memoised summaries of its
/// nullary aliases.
pub(crate) struct PriorityConjuncts<'a> {
    aliases: &'a BTreeMap<String, AliasDefinition>,
    rules: Vec<WrittenRule<'a>>,
    /// Indices into `rules` by [`application_shape`].
    by_shape: HashMap<u64, Vec<usize>>,
    summaries: HashMap<&'a str, Summary>,
}

impl<'a> PriorityConjuncts<'a> {
    /// Every rewrite axiom written in `modules` (each module once), with `aliases` the aliases
    /// they declare.
    pub(crate) fn collect(
        modules: &[&'a kore::Module],
        aliases: &'a BTreeMap<String, AliasDefinition>,
    ) -> Self {
        let mut rules = Vec::new();
        let mut by_shape = HashMap::<u64, Vec<usize>>::new();
        for module in modules {
            for (index, sentence) in module.sentences.iter().enumerate() {
                let kore::Sentence::Axiom {
                    parameters,
                    pattern,
                    attributes,
                } = sentence
                else {
                    continue;
                };
                let kore::Pattern::Rewrites { left, .. } = pattern.as_ref() else {
                    continue;
                };
                let mut components = Vec::new();
                flatten_and(left, &mut components);
                components.retain(|component| {
                    !matches!(component, kore::Pattern::Top { .. })
                        && priority_conjunct(component, aliases).is_none()
                });
                by_shape
                    .entry(application_shape(&components))
                    .or_default()
                    .push(rules.len());
                rules.push(WrittenRule {
                    sentence: (Name::from(module.name.as_str()), index),
                    parametric: !parameters.is_empty(),
                    attributes,
                    application: components,
                    facts: None,
                });
            }
        }
        Self {
            aliases,
            rules,
            by_shape,
            summaries: HashMap::new(),
        }
    }

    /// The summary of the nullary alias `alias`, computed once.
    pub(crate) fn summary(&mut self, alias: &'a str) -> Summary {
        if let Some(summary) = self.summaries.get(alias) {
            return summary.clone();
        }
        let summary = self.compute_summary(alias);
        self.summaries.insert(alias, summary.clone());
        summary
    }

    fn compute_summary(&mut self, alias: &'a str) -> Summary {
        let aliases = self.aliases;
        let definition = &aliases[alias];
        debug_assert!(is_nullary(definition), "only a nullary alias is summarised");
        let mut disjuncts = Vec::new();
        flatten_or(&definition.right, &mut disjuncts);
        let mut highest: Option<Witness> = None;
        for (index, disjunct) in disjuncts.into_iter().enumerate() {
            let step = (alias.to_owned(), index);
            let witness = match self.named_rules(disjunct)? {
                Named::Rule { priority, rule } => Some(Witness {
                    priority,
                    rule,
                    path: vec![step],
                }),
                named => match nested_alias(disjunct, aliases) {
                    Some(nested) => self
                        .summary(nested)
                        .map_err(|error| prefixed(error, &step))?
                        .map(|mut witness| {
                            witness.path.insert(0, step);
                            witness
                        }),
                    None => {
                        let reason = match named {
                            Named::Excluded(reason) => reason,
                            Named::Rule { .. } | Named::Nothing => DisjunctFailure::NamesNoRule,
                        };
                        return Err(SummaryError::Failure(PriorityConjunctFailure::Disjunct {
                            path: vec![step],
                            reason,
                        }));
                    }
                },
            };
            if let Some(witness) = witness
                && highest
                    .as_ref()
                    .is_none_or(|highest| witness.priority > highest.priority)
            {
                highest = Some(witness);
            }
        }
        Ok(highest)
    }

    /// The rules `disjunct` names (conditions 1 to 3 of the module documentation).
    fn named_rules(&mut self, disjunct: &kore::Pattern) -> Result<Named, SummaryError> {
        let (body, binders) = disjunct.leading_existentials();
        let binders_set = binders.iter().copied().cloned().collect::<BTreeSet<_>>();
        if binders_set.len() != binders.len() || binders_set != body.free_variables() {
            return Ok(Named::Nothing);
        }
        let mut components = Vec::new();
        flatten_and(body, &mut components);
        components.retain(|component| !matches!(component, kore::Pattern::Top { .. }));
        let Some(candidates) = self.by_shape.get(&application_shape(&components)) else {
            return Ok(Named::Nothing);
        };
        let matching = candidates
            .iter()
            .copied()
            .filter(|&candidate| {
                let application = &self.rules[candidate].application;
                let mut renaming = VariableRenaming::default();
                application.len() == components.len()
                    && components
                        .iter()
                        .zip(application)
                        .all(|(component, applied)| renaming.pattern(component, applied))
            })
            .collect::<Vec<_>>();
        let mut named: Option<(u8, SentenceKey)> = None;
        let mut excluded = None;
        for candidate in matching {
            let (priority, executable) = self.facts(candidate)?;
            let rule = &self.rules[candidate];
            if !executable {
                excluded.get_or_insert(DisjunctFailure::NamedRuleNotExecutable);
            } else if rule.parametric {
                excluded.get_or_insert(DisjunctFailure::ParametricNamedRule);
            } else if named.as_ref().is_none_or(|(least, _)| priority < *least) {
                named = Some((priority, rule.sentence.clone()));
            }
        }
        Ok(match (named, excluded) {
            (Some((priority, rule)), _) => Named::Rule { priority, rule },
            (None, Some(reason)) => Named::Excluded(reason),
            (None, None) => Named::Nothing,
        })
    }

    fn facts(&mut self, rule: usize) -> Result<(u8, bool), SummaryError> {
        let rule = &mut self.rules[rule];
        if let Some(facts) = rule.facts {
            return Ok(facts);
        }
        let attributes = RuleAttributes::parse(rule.attributes).map_err(SummaryError::Axiom)?;
        let facts = (attributes.priority, attributes.executable);
        rule.facts = Some(facts);
        Ok(facts)
    }
}

/// The discharge of the priority conjuncts of the rewrite axioms of one load.
pub(crate) struct Discharge<'m, 'a> {
    modules: &'m [&'a kore::Module],
    aliases: &'a BTreeMap<String, AliasDefinition>,
    /// Built at the first priority conjunct, so a definition without one takes no new path.
    conjuncts: Option<PriorityConjuncts<'a>>,
}

impl<'m, 'a> Discharge<'m, 'a> {
    /// The discharge against the rewrite axioms of every module of `modules`, which declare
    /// `aliases`.
    pub(crate) fn new(
        modules: &'m [&'a kore::Module],
        aliases: &'a BTreeMap<String, AliasDefinition>,
    ) -> Self {
        Self {
            modules,
            aliases,
            conjuncts: None,
        }
    }

    /// The axiom `pattern`, written with `attributes` as the sentence `sentence`, with each
    /// priority conjunct of its rewrite left-hand side replaced by `\top` of its sort: borrowed
    /// when it has none. Refused when one is not discharged; a malformed attribute of the axiom
    /// or of a rule a disjunct names gives the error classifying that axiom gives.
    pub(crate) fn discharge(
        &mut self,
        pattern: &'a kore::Pattern,
        attributes: &kore::Attributes,
        sentence: &SentenceKey,
    ) -> Result<Cow<'a, kore::Pattern>, DefinitionError> {
        let kore::Pattern::Rewrites { sort, left, right } = pattern else {
            return Ok(Cow::Borrowed(pattern));
        };
        let aliases = self.aliases;
        let mut components = Vec::new();
        flatten_and(left, &mut components);
        let mut carried = components
            .into_iter()
            .filter_map(|component| priority_conjunct(component, aliases))
            .peekable();
        if carried.peek().is_none() {
            return Ok(Cow::Borrowed(pattern));
        }
        let own = RuleAttributes::parse(attributes)
            .map_err(DefinitionError::Axiom)?
            .priority;
        let modules = self.modules;
        let conjuncts = self
            .conjuncts
            .get_or_insert_with(|| PriorityConjuncts::collect(modules, aliases));
        for alias in carried {
            let failure = match conjuncts.summary(alias) {
                Ok(None) => continue,
                Ok(Some(witness)) if witness.priority < own => continue,
                Ok(Some(Witness {
                    priority,
                    rule,
                    path,
                })) => PriorityConjunctFailure::NotStrictlyHigher {
                    named: priority,
                    own,
                    rule,
                    path,
                },
                Err(SummaryError::Failure(failure)) => failure,
                Err(SummaryError::Axiom(error)) => return Err(DefinitionError::Axiom(error)),
            };
            return Err(DefinitionError::PriorityConjunct {
                sentence: Box::new(sentence.clone()),
                alias: alias.to_owned(),
                failure,
            });
        }
        Ok(Cow::Owned(kore::Pattern::Rewrites {
            sort: sort.clone(),
            left: Box::new(without_conjuncts(left, aliases)),
            right: right.clone(),
        }))
    }
}

/// `pattern` with each priority conjunct among its components (nested `\and` flattened) replaced
/// by `\top` of its sort.
fn without_conjuncts(
    pattern: &kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
) -> kore::Pattern {
    match pattern {
        kore::Pattern::And { sort, arguments } => kore::Pattern::And {
            sort: sort.clone(),
            arguments: arguments
                .iter()
                .map(|argument| without_conjuncts(argument, aliases))
                .collect(),
        },
        kore::Pattern::Not { sort, .. } if priority_conjunct(pattern, aliases).is_some() => {
            kore::Pattern::Top { sort: sort.clone() }
        }
        _ => pattern.clone(),
    }
}

/// What a disjunct names.
enum Named {
    /// The rules of least priority among the qualifying rules it names.
    Rule {
        priority: u8,
        rule: SentenceKey,
    },
    /// It has the applicability pattern of rules, none of which qualifies.
    Excluded(DisjunctFailure),
    Nothing,
}

/// The nullary alias whose negation `component` is, when it is a priority conjunct.
pub(crate) fn priority_conjunct<'p>(
    component: &'p kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
) -> Option<&'p str> {
    let kore::Pattern::Not { argument, .. } = component else {
        return None;
    };
    nested_alias(argument, aliases)
}

/// The alias `pattern` applies when it is an application `A{}()` of a nullary alias.
fn nested_alias<'p>(
    pattern: &'p kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
) -> Option<&'p str> {
    let kore::Pattern::Application { symbol, arguments } = pattern else {
        return None;
    };
    (symbol.sort_parameters.is_empty()
        && arguments.is_empty()
        && aliases.get(&symbol.name).is_some_and(is_nullary))
    .then_some(symbol.name.as_str())
}

fn is_nullary(alias: &AliasDefinition) -> bool {
    alias.sort_parameters.is_empty() && alias.parameters.is_empty()
}

fn flatten_or<'p>(pattern: &'p kore::Pattern, output: &mut Vec<&'p kore::Pattern>) {
    match pattern {
        kore::Pattern::Or { arguments, .. } => {
            for argument in arguments {
                flatten_or(argument, output);
            }
        }
        kore::Pattern::Bottom { .. } => {}
        _ => output.push(pattern),
    }
}

/// A hash of what the renaming comparison of two component lists compares literally, so only
/// lists with one shape are compared.
fn application_shape(components: &[&kore::Pattern]) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    components.len().hash(&mut hasher);
    for component in components {
        hash_pattern_shape(component, &mut hasher);
    }
    hasher.finish()
}

fn prefixed(error: SummaryError, step: &DisjunctStep) -> SummaryError {
    match error {
        SummaryError::Failure(mut failure) => {
            match &mut failure {
                PriorityConjunctFailure::Disjunct { path, .. }
                | PriorityConjunctFailure::NotStrictlyHigher { path, .. } => {
                    path.insert(0, step.clone());
                }
            }
            SummaryError::Failure(failure)
        }
        SummaryError::Axiom(error) => SummaryError::Axiom(error),
    }
}

#[cfg(test)]
mod tests {

    use indoc::indoc;
    use k_rust_kore::kore::parser::parse_definition;

    use super::*;
    use crate::{definition::DefinitionError, tests::priority_conjunct::FIXTURE};

    /// The sentence indices of `r0`, `r1` and `r2` in `FIXTURE`'s module.
    const R0: usize = 14;
    const R1: usize = 15;
    const R2: usize = 16;

    /// `FIXTURE` with each `(from, to)` replacement applied once.
    fn variant(replacements: &[(&str, &str)]) -> String {
        replacements
            .iter()
            .fold(FIXTURE.to_owned(), |text, (from, to)| {
                assert!(text.contains(from), "the fixture contains {from}");
                text.replacen(from, to, 1)
            })
    }

    /// The summary of each alias of `aliases`, in order, for the definition `text`.
    fn summaries(text: &str, aliases: &[&str]) -> Vec<Summary> {
        let definition = parse_definition(text).expect("the fixture parses");
        let modules = definition.modules.iter().collect::<Vec<_>>();
        let declared = crate::alias::collect(&modules, &BTreeMap::new())
            .expect("the fixture's aliases are well formed");
        let mut conjuncts = PriorityConjuncts::collect(&modules, &declared);
        aliases
            .iter()
            .map(|alias| conjuncts.summary(alias))
            .collect()
    }

    fn summary(text: &str, alias: &str) -> Summary {
        summaries(text, &[alias]).remove(0)
    }

    fn rule(index: usize) -> SentenceKey {
        (Name::from("PRIO"), index)
    }

    fn path(steps: &[(&str, usize)]) -> Vec<DisjunctStep> {
        steps
            .iter()
            .map(|&(alias, index)| (alias.to_owned(), index))
            .collect()
    }

    fn witness(priority: u8, index: usize, steps: &[(&str, usize)]) -> Summary {
        Ok(Some(Witness {
            priority,
            rule: rule(index),
            path: path(steps),
        }))
    }

    fn failure(steps: &[(&str, usize)], reason: DisjunctFailure) -> Summary {
        Err(SummaryError::Failure(PriorityConjunctFailure::Disjunct {
            path: path(steps),
            reason,
        }))
    }

    #[test]
    fn the_sentence_indices_are_those_of_the_rules() {
        let definition = parse_definition(FIXTURE).expect("the fixture parses");
        let labels = [R0, R1, R2].map(|index| {
            let kore::Sentence::Axiom { attributes, .. } = &definition.modules[0].sentences[index]
            else {
                panic!("sentence {index} is an axiom");
            };
            RuleAttributes::parse(attributes)
                .expect("the fixture's attributes parse")
                .label
        });
        assert_eq!(
            labels,
            ["r0", "r1", "r2"].map(|label| Some(label.to_owned()))
        );
    }

    #[test]
    fn a_nested_alias_contributes_its_summary_and_the_highest_priority_is_kept() {
        assert_eq!(
            summaries(FIXTURE, &["priorityLE35", "priorityLE40"]),
            [
                witness(35, R0, &[("priorityLE35", 0)]),
                // r1 and r2 are both 40; the first disjunct naming one is the witness.
                witness(40, R1, &[("priorityLE40", 1)]),
            ]
        );
    }

    #[test]
    fn a_priority_reached_only_through_nesting_is_witnessed_by_its_path() {
        let text = variant(&[(
            r#"[priority{}("35"), label{}("r0")]"#,
            r#"[priority{}("60"), label{}("r0")]"#,
        )]);
        assert_eq!(
            summary(&text, "priorityLE40"),
            witness(60, R0, &[("priorityLE40", 0), ("priorityLE35", 0)])
        );
    }

    /// `rule0LHS` is itself a nullary alias: read as one, its body's components `[f(e)]` are not
    /// `App(r0) = [rule0LHS()]` as written, so it names no rule. Reading the disjunct
    /// `rule0LHS{}()` of `priorityLE35` as a nested alias first would refuse the definition.
    #[test]
    fn a_disjunct_naming_a_rule_is_not_read_as_a_nested_alias() {
        assert_eq!(
            summaries(FIXTURE, &["rule0LHS", "priorityLE35"]),
            [
                failure(&[("rule0LHS", 0)], DisjunctFailure::NamesNoRule),
                witness(35, R0, &[("priorityLE35", 0)]),
            ]
        );
    }

    #[test]
    fn a_rule_is_named_under_a_renaming_of_its_variables() {
        let text = variant(&[(
            r#"\exists{SortS{}}(VarY:SortS{}, rule1LHS{}(VarY:SortS{}))"#,
            r#"\exists{SortS{}}(VarZ:SortS{}, rule1LHS{}(VarZ:SortS{}))"#,
        )]);
        assert_eq!(
            summary(&text, "priorityLE40"),
            witness(40, R1, &[("priorityLE40", 1)])
        );
    }

    /// A free variable of the disjunct makes it denote more than "the rule applies".
    #[test]
    fn a_disjunct_naming_a_rule_binds_exactly_its_free_variables() {
        for disjunct in [
            r#"rule1LHS{}(VarY:SortS{})"#,
            r#"\exists{SortS{}}(VarZ:SortS{}, rule1LHS{}(VarY:SortS{}))"#,
            r#"\exists{SortS{}}(VarY:SortS{}, \exists{SortS{}}(VarY:SortS{}, rule1LHS{}(VarY:SortS{})))"#,
        ] {
            let text = variant(&[(
                r#"\exists{SortS{}}(VarY:SortS{}, rule1LHS{}(VarY:SortS{}))"#,
                disjunct,
            )]);
            assert_eq!(
                summary(&text, "priorityLE40"),
                failure(&[("priorityLE40", 1)], DisjunctFailure::NamesNoRule),
                "{disjunct}"
            );
        }
    }

    #[test]
    fn a_disjunct_naming_no_rule_fails_with_its_path_through_nesting() {
        let text = variant(&[(
            r#"\or{SortS{}}(rule0LHS{}(), \bottom{SortS{}}())"#,
            r#"\or{SortS{}}(rule0LHS{}(), \or{SortS{}}(f{}(d{}()), \bottom{SortS{}}()))"#,
        )]);
        assert_eq!(
            summaries(&text, &["priorityLE35", "priorityLE40"]),
            [
                failure(&[("priorityLE35", 1)], DisjunctFailure::NamesNoRule),
                failure(
                    &[("priorityLE40", 0), ("priorityLE35", 1)],
                    DisjunctFailure::NamesNoRule
                ),
            ]
        );
    }

    #[test]
    fn a_non_executable_named_rule_excludes_nothing() {
        let text = variant(&[(
            r#"[priority{}("40"), label{}("r1")]"#,
            r#"[priority{}("40"), label{}("r1"), non-executable{}()]"#,
        )]);
        assert_eq!(
            summary(&text, "priorityLE40"),
            failure(
                &[("priorityLE40", 1)],
                DisjunctFailure::NamedRuleNotExecutable
            )
        );
    }

    #[test]
    fn a_sort_parametric_named_rule_is_refused() {
        let text = variant(&[(
            r#"axiom{} \rewrites{SortS{}}(\and{SortS{}}(\not{SortS{}}(priorityLE35{}()), rule1LHS"#,
            r#"axiom{R} \rewrites{SortS{}}(\and{SortS{}}(\not{SortS{}}(priorityLE35{}()), rule1LHS"#,
        )]);
        assert_eq!(
            summary(&text, "priorityLE40"),
            failure(&[("priorityLE40", 1)], DisjunctFailure::ParametricNamedRule)
        );
    }

    /// Two rules with one applicability pattern both apply wherever it holds, so the disjunct
    /// excludes the configurations of the smaller priority.
    #[test]
    fn a_disjunct_naming_several_rules_contributes_their_smallest_priority() {
        let text = variant(&[(
            "endmodule []",
            indoc! {r#"
                  alias only{}() : SortS{}
                  where only{}() := \exists{SortS{}}(VarY:SortS{}, rule1LHS{}(VarY:SortS{})) []
                  axiom{} \rewrites{SortS{}}(\and{SortS{}}(\top{SortS{}}(), rule1LHS{}(VarV:SortS{})),
                    \and{SortS{}}(\top{SortS{}}(), d{}())) [priority{}("30"), label{}("r1b")]
                endmodule []"#},
        )]);
        let found = summary(&text, "only");
        let Ok(Some(Witness { priority, .. })) = found else {
            panic!("`only` names r1 and r1b: {found:?}");
        };
        assert_eq!(priority, 30);
    }

    #[test]
    fn an_alias_of_bottoms_denotes_nothing() {
        let text = variant(&[(
            r#"\or{SortS{}}(rule0LHS{}(), \bottom{SortS{}}())"#,
            r#"\or{SortS{}}(\bottom{SortS{}}(), \bottom{SortS{}}())"#,
        )]);
        assert_eq!(
            summaries(&text, &["priorityLE35", "priorityLE40"]),
            [Ok(None), witness(40, R1, &[("priorityLE40", 1)])]
        );
    }

    #[test]
    fn a_nested_summary_is_computed_once() {
        let definition = parse_definition(FIXTURE).expect("the fixture parses");
        let modules = definition.modules.iter().collect::<Vec<_>>();
        let declared = crate::alias::collect(&modules, &BTreeMap::new())
            .expect("the fixture's aliases are well formed");
        let mut conjuncts = PriorityConjuncts::collect(&modules, &declared);
        conjuncts.summary("priorityLE40").expect("LE40 summarises");
        assert!(conjuncts.summaries.contains_key("priorityLE35"));
        // Only r1 and r2 are named on the way, and r0: no other rule's attributes are parsed.
        let parsed = conjuncts
            .rules
            .iter()
            .filter(|rule| rule.facts.is_some())
            .map(|rule| rule.sentence.1)
            .collect::<Vec<_>>();
        assert_eq!(parsed, [R0, R1, R2]);
    }

    /// The summary recurses through nested aliases without a cycle check: declaration refuses
    /// a cycle before any summary is asked.
    #[test]
    fn a_cycle_of_priority_aliases_is_refused_at_declaration() {
        let text = variant(&[(
            r#"\or{SortS{}}(rule0LHS{}(), \bottom{SortS{}}())"#,
            r#"\or{SortS{}}(rule0LHS{}(), priorityLE40{}())"#,
        )]);
        let definition = parse_definition(&text).expect("the variant parses");
        let modules = definition.modules.iter().collect::<Vec<_>>();
        assert!(matches!(
            crate::alias::collect(&modules, &BTreeMap::new()),
            Err(DefinitionError::AliasCycle(_))
        ));
    }
}
