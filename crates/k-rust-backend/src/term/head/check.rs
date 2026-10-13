//! An independent check of the two normal-form claims (feature `check-normal-forms`).
//!
//! The backend claims that a term is a normal form of the definition's equations in two places:
//! the simplifier's `evaluated` mark (`Term::with_evaluated_cache`, which needs a
//! `NormalFormCertificate`) and an instance-normal equation-head or collection token (minted only
//! by `NoEquationReaches::scan`). Both include that the left-hand side of no term equation of the
//! definition matches the term at its root: the mark needs every equation the simplifier tried to
//! end in a failed match, and the scan excludes an equation only when its left-hand side cannot
//! match an instance of the term, so neither claim survives an equation whose left-hand side
//! matches. Both rest on equation selection, on the equation matcher and on the scan that
//! enumerates the selected equations; this module checks that consequence without any of them.
//!
//! [`assert_no_equation_matches`] panics when some term equation's left-hand side surely matches
//! the term at its root. The equations are read from a catalog built once per definition from
//! every left-hand side of the function and simplification theories, under every index key, and
//! the term conjuncts of every predicate-simplification left-hand side, indexed by root symbol
//! here rather than through `rule::term_index`. "Surely matches" is decided by a syntactic matcher
//! over borrowed terms that answers yes only when a match certainly exists:
//!
//! - a pattern element variable binds a subterm of the identical sort, and a variable that occurs
//!   twice binds equal subterms;
//! - a domain value matches an equal domain value of the same sort;
//! - an application matches an application of the same symbol with the same sort arguments and
//!   arity whose arguments the pattern's arguments surely match;
//! - an injection matches an injection between the same sorts whose operand the pattern's operand
//!   surely matches;
//! - a conjunction matches when each conjunct does, with one set of bindings.
//!
//! Everything else answers "not surely": a collection pattern (the collection axioms let one
//! value have several representations), a set variable, an uninterpreted application
//! (no declaration individuates its arguments, or identifying axioms relate them), a subterm whose sort differs from
//! the variable's (whether its values belong to the variable's sort is a question about the sort
//! graph and injections), and a predicate-simplification left-hand side with a conjunct that is
//! neither a term nor `\top` (left out of the catalog). In each a match may exist that the checker
//! does not establish, so an alarm is either a violated claim or a checker bug, never a guessed
//! match. `requires` clauses are not evaluated, because neither claim depends on them.
//!
//! The check reads and panics. It constructs no `Term`, runs no backend matcher and bumps no
//! `k_rust_kore::measure` counter, so the work-counter ratchets, which run with this feature on,
//! count exactly what they count without it.

use std::{fmt, sync::Arc};

use rustc_hash::FxHashMap;

use crate::{
    definition::BackendDefinition,
    rule::{Predicate, PredicateRewriteRule, RewriteRule, RuleAttributes, Theory},
    term::{HeadRole, Name, Sort, Term, TermKind, Variable, VariableKind},
};

/// Which claim about `term` is being checked.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Claim {
    /// The simplifier is about to set the `evaluated` mark on the term.
    EvaluatedMark,
    /// The instance-normal scan found no equation that reaches the term.
    InstanceNormal,
}

impl fmt::Display for Claim {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::EvaluatedMark => "the evaluated mark",
            Self::InstanceNormal => "an instance-normal token",
        })
    }
}

/// Panics when some term equation of `definition` surely matches `term` at its root (module
/// documentation), naming the claim, the equation and the term.
pub(crate) fn assert_no_equation_matches(
    definition: &BackendDefinition,
    term: &Term,
    claim: Claim,
) {
    if let Some(entry) = definition.normal_form_catalog().surely_matching(term) {
        panic!(
            "{claim} was claimed for {}, but the {} equation {} surely matches it at its root \
             (left-hand side {})",
            Shown(term),
            entry.equation.theory(),
            entry.equation,
            ShownConjunction(&entry.conjuncts),
        );
    }
}

/// Every term equation's left-hand side, indexed by the symbol at its root. Built once per
/// definition by `BackendDefinition::normal_form_catalog`.
#[derive(Clone, Debug, Default)]
pub(crate) struct Catalog {
    /// The entries with an application root (for a conjunction, the first conjunct's that has
    /// one), by symbol name: only an application of that symbol can surely match them.
    by_symbol: FxHashMap<Name, Vec<Entry>>,
    /// The entries without an application root (a variable, a domain value, an injection, a
    /// collection), tried on every term.
    rootless: Vec<Entry>,
}

/// One left-hand side: the conjunction of its term conjuncts, and the equation it comes from.
#[derive(Clone, Debug)]
struct Entry {
    conjuncts: Vec<Term>,
    equation: Equation,
}

#[derive(Clone, Debug)]
enum Equation {
    Function(Arc<RewriteRule>),
    Simplification(Arc<RewriteRule>),
    PredicateSimplification(Arc<PredicateRewriteRule>),
}

impl Equation {
    fn theory(&self) -> &'static str {
        match self {
            Self::Function(_) => "function",
            Self::Simplification(_) => "simplification",
            Self::PredicateSimplification(_) => "predicate-simplification",
        }
    }

    fn attributes(&self) -> &RuleAttributes {
        match self {
            Self::Function(rule) | Self::Simplification(rule) => &rule.attributes,
            Self::PredicateSimplification(rule) => &rule.attributes,
        }
    }
}

impl fmt::Display for Equation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let attributes = self.attributes();
        write!(formatter, "{}", attributes.unique_id)?;
        if let Some(label) = &attributes.label {
            write!(formatter, " [{label}]")?;
        }
        if let Some(origin) = attributes.origins.first() {
            for part in [&origin.source, &origin.location].into_iter().flatten() {
                write!(formatter, " {part}")?;
            }
        }
        Ok(())
    }
}

impl Catalog {
    /// The catalog of `definition`'s term equations: every rule of the function and
    /// simplification theories under every index key, and every predicate-simplification rule
    /// whose left-hand side is a conjunction of term patterns (and `\top`).
    pub(crate) fn of(definition: &BackendDefinition) -> Self {
        let mut catalog = Self::default();
        let mut term_theory = |theory: &Theory, equation: fn(Arc<RewriteRule>) -> Equation| {
            for rule in theory.values().flat_map(|groups| groups.values().flatten()) {
                catalog.insert(Entry {
                    conjuncts: vec![rule.lhs.clone()],
                    equation: equation(rule.clone()),
                });
            }
        };
        term_theory(definition.function_theory(), Equation::Function);
        term_theory(definition.simplification_theory(), Equation::Simplification);
        for rule in definition
            .predicate_simplification_theory()
            .values()
            .flatten()
        {
            let mut conjuncts = Vec::new();
            if term_conjuncts(&rule.lhs, &mut conjuncts) && !conjuncts.is_empty() {
                catalog.insert(Entry {
                    conjuncts,
                    equation: Equation::PredicateSimplification(rule.clone()),
                });
            }
        }
        catalog
    }

    fn insert(&mut self, entry: Entry) {
        match entry.conjuncts.iter().find_map(root_symbol) {
            Some(symbol) => self
                .by_symbol
                .entry(symbol.clone())
                .or_default()
                .push(entry),
            None => self.rootless.push(entry),
        }
    }

    /// The first entry whose left-hand side surely matches `term` at its root.
    fn surely_matching(&self, term: &Term) -> Option<&Entry> {
        let indexed = match term.kind() {
            TermKind::Application { symbol, .. } => self.by_symbol.get(&symbol.name),
            _ => None,
        };
        indexed
            .into_iter()
            .flatten()
            .chain(&self.rootless)
            .find(|entry| {
                let mut bindings = Vec::new();
                entry
                    .conjuncts
                    .iter()
                    .all(|conjunct| surely_matches(conjunct, term, &mut bindings))
            })
    }
}

/// Appends the term conjuncts of `predicate` to `conjuncts`, flattening nested conjunctions, and
/// answers whether every conjunct is a term or `\top`. Any other conjunct constrains the match in
/// a way the checker does not decide, so such a left-hand side is left out of the catalog.
fn term_conjuncts(predicate: &Predicate, conjuncts: &mut Vec<Term>) -> bool {
    match predicate {
        Predicate::Term(term) => {
            conjuncts.push(term.clone());
            true
        }
        Predicate::True => true,
        Predicate::And(inner) => inner
            .iter()
            .all(|predicate| term_conjuncts(predicate, conjuncts)),
        Predicate::False
        | Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Defined(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Absent(_)
        | Predicate::Not(_)
        | Predicate::Or(_)
        | Predicate::Implies(..)
        | Predicate::Iff(..)
        | Predicate::Exists(..)
        | Predicate::Forall(..) => false,
    }
}

/// The symbol at the root of `pattern`, for a conjunction the first conjunct's that has one.
fn root_symbol(pattern: &Term) -> Option<&Name> {
    match pattern.kind() {
        TermKind::Application { symbol, .. } => Some(&symbol.name),
        TermKind::And(left, right) => root_symbol(left).or_else(|| root_symbol(right)),
        _ => None,
    }
}

/// Whether `pattern` surely matches `subject` (module documentation), extending `bindings`,
/// which pairs each pattern variable bound so far with its subterm.
#[deny(clippy::wildcard_enum_match_arm)]
fn surely_matches<'p, 's>(
    pattern: &'p Term,
    subject: &'s Term,
    bindings: &mut Vec<(&'p Variable, &'s Term)>,
) -> bool {
    match pattern.kind() {
        TermKind::Variable(variable) => match variable.kind {
            VariableKind::Element => {
                if let Some((_, bound)) = bindings.iter().find(|(bound, _)| *bound == variable) {
                    return *bound == subject;
                }
                if !has_sort(subject, &variable.sort) {
                    return false;
                }
                bindings.push((variable, subject));
                true
            }
            VariableKind::Set => false,
        },
        TermKind::DomainValue { sort, value } => matches!(
            subject.kind(),
            TermKind::DomainValue { sort: subject_sort, value: subject_value }
                if subject_sort == sort && subject_value == value
        ),
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => {
            if symbol.attributes.head_role() == HeadRole::Uninterpreted {
                return false;
            }
            let TermKind::Application {
                symbol: subject_symbol,
                sort_arguments: subject_sort_arguments,
                arguments: subject_arguments,
            } = subject.kind()
            else {
                return false;
            };
            symbol.name == subject_symbol.name
                && sort_arguments == subject_sort_arguments
                && arguments.len() == subject_arguments.len()
                && arguments
                    .iter()
                    .zip(subject_arguments)
                    .all(|(argument, subject_argument)| {
                        surely_matches(argument, subject_argument, bindings)
                    })
        }
        TermKind::Injection {
            source,
            target,
            term,
        } => {
            let TermKind::Injection {
                source: subject_source,
                target: subject_target,
                term: subject_term,
            } = subject.kind()
            else {
                return false;
            };
            source == subject_source
                && target == subject_target
                && surely_matches(term, subject_term, bindings)
        }
        TermKind::And(left, right) => {
            surely_matches(left, subject, bindings) && surely_matches(right, subject, bindings)
        }
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. } => false,
    }
}

/// Whether `term` has exactly the sort `sort`.
fn has_sort(term: &Term, sort: &Sort) -> bool {
    term.sort() == *sort
}

/// The term conjuncts of a left-hand side, joined by `/\`.
struct ShownConjunction<'t>(&'t [Term]);

impl fmt::Display for ShownConjunction<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, conjunct) in self.0.iter().enumerate() {
            if index > 0 {
                formatter.write_str(" /\\ ")?;
            }
            write!(formatter, "{}", Shown(conjunct))?;
        }
        Ok(())
    }
}

/// A sort in KORE syntax.
struct ShownSort<'s>(&'s Sort);

impl fmt::Display for ShownSort<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Sort::Variable(name) => formatter.write_str(name),
            Sort::Application { name, arguments } => {
                write!(formatter, "{name}{{")?;
                for (index, argument) in arguments.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "{}", ShownSort(argument))?;
                }
                formatter.write_str("}")
            }
        }
    }
}

/// A compact KORE-like rendering of a term for the panic message, written from the borrowed term
/// without building any other representation.
struct Shown<'t>(&'t Term);

impl fmt::Display for Shown<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn list<'t>(
            formatter: &mut fmt::Formatter<'_>,
            items: impl IntoIterator<Item = &'t Term>,
        ) -> fmt::Result {
            for (index, item) in items.into_iter().enumerate() {
                if index > 0 {
                    formatter.write_str(", ")?;
                }
                write!(formatter, "{}", Shown(item))?;
            }
            Ok(())
        }
        match self.0.kind() {
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } => {
                write!(formatter, "{}{{", symbol.name)?;
                for (index, sort) in sort_arguments.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "{}", ShownSort(sort))?;
                }
                formatter.write_str("}(")?;
                list(formatter, arguments)?;
                formatter.write_str(")")
            }
            TermKind::DomainValue { sort, value } => {
                write!(formatter, "\\dv{{{}}}({value:?})", ShownSort(sort))
            }
            TermKind::Variable(variable) => {
                write!(formatter, "{}:{}", variable.name, ShownSort(&variable.sort))
            }
            TermKind::Injection {
                source,
                target,
                term,
            } => write!(
                formatter,
                "inj{{{}, {}}}({})",
                ShownSort(source),
                ShownSort(target),
                Shown(term)
            ),
            TermKind::And(left, right) => {
                write!(formatter, "\\and({}, {})", Shown(left), Shown(right))
            }
            TermKind::Map { entries, rest, .. } => {
                formatter.write_str("map(")?;
                for (index, (key, value)) in entries.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "{} |-> {}", Shown(key), Shown(value))?;
                }
                if let Some(rest) = rest {
                    write!(formatter, "; {}", Shown(rest))?;
                }
                formatter.write_str(")")
            }
            TermKind::List { heads, rest, .. } => {
                formatter.write_str("list(")?;
                list(formatter, heads)?;
                if let Some((middle, tails)) = rest {
                    write!(formatter, "; {}; ", Shown(middle))?;
                    list(formatter, tails)?;
                }
                formatter.write_str(")")
            }
            TermKind::Set { elements, rest, .. } => {
                formatter.write_str("set(")?;
                list(formatter, elements)?;
                if let Some(rest) = rest {
                    write!(formatter, "; {}", Shown(rest))?;
                }
                formatter.write_str(")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::panic::{AssertUnwindSafe, catch_unwind};

    use k_rust_kore::{
        kore::parser::{parse_definition, parse_pattern},
        measure::{Snapshot, snapshot},
    };

    use super::*;

    fn internalized(source: &str) -> BackendDefinition {
        let syntax = parse_definition(source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize")
    }

    fn check(definition: &BackendDefinition, source: &str) {
        assert_no_equation_matches(definition, &term(definition, source), Claim::EvaluatedMark);
    }

    /// The symbols and equations of the structural-distinctness fixture
    /// (`tests/backend/structural_distinctness.rs`) that the two counterexamples below involve:
    /// `z` and `s` are constructors, `wrap` and `tag` are `anywhere` productions, `wrap` carries
    /// `wrap(s(X)) = wrap(X)` with `attribute` (a KORE attribute or empty), and `lemma` is
    /// appended to the module.
    fn wrap_tag_source(attribute: &str, lemma: &str) -> String {
        format!(
            r#"[]
            module MAIN
                sort SortNat{{}} []
                sort SortAddress{{}} []
                symbol z{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol s{{}}(SortNat{{}}) : SortNat{{}}
                    [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol wrap{{}}(SortNat{{}}) : SortAddress{{}}
                    [anywhere{{}}(), functional{{}}(), injective{{}}()]
                symbol tag{{}}(SortNat{{}}) : SortAddress{{}} [anywhere{{}}(), functional{{}}()]
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \top{{R}}(),
                        \and{{R}}(\in{{SortNat{{}}, R}}(X0:SortNat{{}}, s{{}}(X:SortNat{{}})), \top{{R}}())
                    ),
                    \equals{{SortAddress{{}}, R}}(
                        wrap{{}}(X0:SortNat{{}}),
                        \and{{SortAddress{{}}}}(wrap{{}}(X:SortNat{{}}), \top{{SortAddress{{}}}}())
                    )
                ) [label{{}}("unwrap"), anywhere{{}}(){attribute}]
                {lemma}
            endmodule []"#
        )
    }

    /// ece6117d: `\and(tag(s(X)), tag(s(X))) = tag(X)`, a simplification whose left-hand side
    /// is a conjunction of term patterns, filed in the predicate theory.
    const CONJUNCTIVE_LEMMA: &str = r#"
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortAddress{}, R}(
                        \and{SortAddress{}}(tag{}(s{}(X:SortNat{})), tag{}(s{}(X:SortNat{}))),
                        \and{SortAddress{}}(tag{}(X:SortNat{}), \top{SortAddress{}}())
                    )
                ) [simplification{}()]"#;

    /// ece6117d: the conjunctive simplification rewrites `tag(s(z))` to `tag(z)`, although no
    /// equation selection offers `tag(s(z))` reaches it.
    #[test]
    #[should_panic(expected = "predicate-simplification equation")]
    fn tag_s_z_is_matched_by_the_conjunctive_simplification() {
        let definition = internalized(&wrap_tag_source("", CONJUNCTIVE_LEMMA));
        check(&definition, "tag{}(s{}(z{}()))");
    }

    /// The conjunction needs both conjuncts, so `tag(z)` is not matched.
    #[test]
    fn tag_z_is_not_matched_by_the_conjunctive_simplification() {
        let definition = internalized(&wrap_tag_source("", CONJUNCTIVE_LEMMA));
        check(&definition, "tag{}(z{}())");
    }

    /// 65429baa: `[symbolic]` only chooses when the evaluator uses `wrap(s(X)) = wrap(X)`; the
    /// equation still rewrites the ground `wrap(s(z))`.
    #[test]
    #[should_panic(expected = "function equation")]
    fn wrap_s_z_is_matched_by_the_symbolic_equation() {
        let definition = internalized(&wrap_tag_source(", symbolic{}()", ""));
        check(&definition, "wrap{}(s{}(z{}()))");
    }

    #[test]
    fn wrap_z_is_not_matched_by_the_symbolic_equation() {
        let definition = internalized(&wrap_tag_source(", symbolic{}()", ""));
        check(&definition, "wrap{}(z{}())");
    }

    /// The fixture of `instance_normal.rs`'s unit tests: `wrap(s(z)) = wrap(z)`, the non-linear
    /// `twin(X, X) = wrap(z)` and the unconditional `any(X) = wrap(z) [owise]`; `f` is a declared
    /// function.
    const INSTANCE_NORMAL_FIXTURE: &str = r#"[]
            module MAIN
                sort SortNat{} []
                sort SortAddress{} []
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol f{}(SortNat{}) : SortNat{} [function{}(), total{}(), no-evaluators{}()]
                symbol wrap{}(SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}()]
                symbol twin{}(SortNat{}, SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}()]
                symbol any{}(SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(z{}())), \top{R}())
                    ),
                    \equals{SortAddress{}, R}(
                        wrap{}(X0:SortNat{}),
                        \and{SortAddress{}}(wrap{}(z{}()), \top{SortAddress{}}())
                    )
                ) [anywhere{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortNat{}, R}(X0:SortNat{}, X:SortNat{}),
                            \and{R}(\in{SortNat{}, R}(X1:SortNat{}, X:SortNat{}), \top{R}())
                        )
                    ),
                    \equals{SortAddress{}, R}(
                        twin{}(X0:SortNat{}, X1:SortNat{}),
                        \and{SortAddress{}}(wrap{}(z{}()), \top{SortAddress{}}())
                    )
                ) [anywhere{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortNat{}, R}(X0:SortNat{}, X:SortNat{}), \top{R}())
                    ),
                    \equals{SortAddress{}, R}(
                        any{}(X0:SortNat{}),
                        \and{SortAddress{}}(wrap{}(z{}()), \top{SortAddress{}}())
                    )
                ) [anywhere{}(), owise{}()]
            endmodule []"#;

    /// 5104f81b: the ground `wrap(s(z))` is concrete after normalization, yet `wrap(s(z)) =
    /// wrap(z)` rewrites it.
    #[test]
    #[should_panic(expected = "surely matches")]
    fn wrap_s_z_is_matched_in_the_instance_normal_fixture() {
        let definition = internalized(INSTANCE_NORMAL_FIXTURE);
        assert_no_equation_matches(
            &definition,
            &term(&definition, "wrap{}(s{}(z{}()))"),
            Claim::InstanceNormal,
        );
    }

    /// The other fixture terms: a non-linear pattern binds equal subterms only, and an
    /// unconditional equation matches every application of its symbol.
    #[test]
    fn the_instance_normal_fixture_matches_exactly_its_redexes() {
        let definition = internalized(INSTANCE_NORMAL_FIXTURE);
        let matched = |source: &str| {
            definition
                .normal_form_catalog()
                .surely_matching(&term(&definition, source))
                .is_some()
        };
        assert!(matched("wrap{}(s{}(z{}()))"));
        assert!(!matched("wrap{}(s{}(s{}(z{}())))"));
        assert!(!matched("wrap{}(z{}())"));
        assert!(!matched("wrap{}(s{}(X:SortNat{}))"));
        assert!(matched("twin{}(s{}(z{}()), s{}(z{}()))"));
        assert!(matched("twin{}(X:SortNat{}, X:SortNat{})"));
        assert!(!matched("twin{}(z{}(), s{}(z{}()))"));
        assert!(!matched("twin{}(X:SortNat{}, Y:SortNat{})"));
        assert!(matched("any{}(f{}(z{}()))"));
    }

    /// `look(M) = z` for a map pattern `M` holding the key `z`: the map value `z |-> s(z)` is
    /// matched by the collection axioms, which the checker does not decide.
    #[test]
    fn a_map_pattern_equation_raises_no_alarm() {
        let definition = internalized(
            r#"[]
            module MAIN
                sort SortNat{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortNat{}, SortNat{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol look{}(SortMap{}) : SortNat{} [anywhere{}(), functional{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortMap{}, R}(
                                X0:SortMap{},
                                mapConcat{}(mapItem{}(z{}(), V:SortNat{}), M:SortMap{})
                            ),
                            \top{R}()
                        )
                    ),
                    \equals{SortNat{}, R}(
                        look{}(X0:SortMap{}),
                        \and{SortNat{}}(V:SortNat{}, \top{SortNat{}}())
                    )
                ) [anywhere{}()]
            endmodule []"#,
        );
        let subject = term(&definition, "look{}(mapItem{}(z{}(), s{}(z{}())))");
        assert!(matches!(
            subject.kind(),
            TermKind::Application { arguments, .. } if matches!(arguments[0].kind(), TermKind::Map { .. })
        ));
        assert!(
            definition
                .normal_form_catalog()
                .by_symbol
                .contains_key("look")
        );
        assert_no_equation_matches(&definition, &subject, Claim::EvaluatedMark);
    }

    /// `pack(cat(X, Y)) = z` with `cat` associative: the checker does not decide matching
    /// modulo associativity, even where the subject is written exactly as the pattern.
    #[test]
    fn an_assoc_symbol_raises_no_alarm() {
        let definition = internalized(
            r#"[]
            module MAIN
                sort SortNat{} []
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol cat{}(SortNat{}, SortNat{}) : SortNat{}
                    [functional{}(), assoc{}()]
                symbol pack{}(SortNat{}) : SortNat{} [anywhere{}(), functional{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortNat{}, R}(X0:SortNat{}, cat{}(X:SortNat{}, Y:SortNat{})),
                            \top{R}()
                        )
                    ),
                    \equals{SortNat{}, R}(
                        pack{}(X0:SortNat{}),
                        \and{SortNat{}}(z{}(), \top{SortNat{}}())
                    )
                ) [anywhere{}()]
            endmodule []"#,
        );
        assert!(
            definition
                .normal_form_catalog()
                .by_symbol
                .contains_key("pack")
        );
        check(&definition, "pack{}(cat{}(z{}(), s{}(z{}())))");
        // The same shape without `assoc` is matched.
        let free = internalized(&wrap_tag_source("", ""));
        assert!(
            free.normal_form_catalog()
                .surely_matching(&term(&free, "wrap{}(s{}(z{}()))"))
                .is_some()
        );
    }

    /// `keep(X:SortAddress) = z`: a subject argument of the subsort `SortSub` without an
    /// injection has another sort than the variable, and the checker does not decide whether a
    /// match through a subsort exists.
    #[test]
    fn a_sort_mismatched_variable_raises_no_alarm() {
        let definition = internalized(
            r#"[]
            module MAIN
                sort SortNat{} []
                sort SortAddress{} []
                sort SortSub{} []
                symbol inj{From, To}(From) : To [sortInjection{}()]
                axiom{R} \exists{R}(
                    Value:SortAddress{},
                    \equals{SortAddress{}, R}(Value:SortAddress{}, inj{SortSub{}, SortAddress{}}(From:SortSub{}))
                ) [subsort{SortSub{}, SortAddress{}}()]
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol sub{}() : SortSub{} [constructor{}(), functional{}(), injective{}()]
                symbol keep{}(SortAddress{}) : SortNat{} [anywhere{}(), functional{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortAddress{}, R}(X0:SortAddress{}, X:SortAddress{}), \top{R}())
                    ),
                    \equals{SortNat{}, R}(
                        keep{}(X0:SortAddress{}),
                        \and{SortNat{}}(z{}(), \top{SortNat{}}())
                    )
                ) [anywhere{}()]
            endmodule []"#,
        );
        let TermKind::Application { symbol, .. } =
            term(&definition, "keep{}(X:SortAddress{})").kind().clone()
        else {
            unreachable!("keep is an application");
        };
        let bare = Term::application(symbol, Vec::new(), vec![term(&definition, "sub{}()")]);
        assert_no_equation_matches(&definition, &bare, Claim::EvaluatedMark);
        // With the injection the argument has the variable's sort, and the equation matches.
        assert!(
            definition
                .normal_form_catalog()
                .surely_matching(&term(
                    &definition,
                    "keep{}(inj{SortSub{}, SortAddress{}}(sub{}()))"
                ))
                .is_some()
        );
    }

    /// The check counts nothing: no term is constructed and no backend algorithm runs, so the
    /// work counters do not move, whether the check passes or panics.
    #[test]
    fn the_check_moves_no_measure_counter() {
        const {
            assert!(
                cfg!(feature = "measure"),
                "the counters count in test builds"
            )
        };
        let definition = internalized(INSTANCE_NORMAL_FIXTURE);
        let redex = term(&definition, "wrap{}(s{}(z{}()))");
        let normal = term(&definition, "wrap{}(s{}(s{}(z{}())))");
        let before = snapshot();
        let panicked = catch_unwind(AssertUnwindSafe(|| {
            assert_no_equation_matches(&definition, &redex, Claim::EvaluatedMark);
        }))
        .is_err();
        let delta = snapshot().delta(&before);
        assert!(panicked, "wrap(s(z)) is matched");
        assert_eq!(delta, Snapshot::default());
        let before = snapshot();
        assert_no_equation_matches(&definition, &normal, Claim::InstanceNormal);
        assert_eq!(snapshot().delta(&before), Snapshot::default());
    }
}
