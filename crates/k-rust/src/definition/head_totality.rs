//! ```toml algorithm-site
//! id = "kompile.kore.axioms"
//! role = "part"
//! sites = ["EquationTotality::judge"]
//! ```
//!
//! A value production that heads no equation builds values from defined arguments. An equation
//! equates its head with its right-hand side conjoined with its `ensures` wherever its condition
//! holds. Conditions and patterns only restrict applicability; a non-trivial `ensures` can make
//! the result undefined. The compiler therefore claims totality only when every right-hand side
//! is syntactically defined and every `ensures` is true.
//!
//! An application is defined when its label and all its arguments are defined. Equations may
//! depend on declarations that state totality and on value heads admitted earlier. A least fixed
//! point forbids circular evidence: assuming a head total while its equations reapply it can
//! identify an integer with itself minus one, or a value with a strictly larger constructor.
//!
//! The judgement costs O(P + R + Σ|right-hand sides| + O²), with expected constant-time equation
//! index lookups, for P productions, R rules and O elements of the transitive overload order.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::{HashMap, HashSet, VecDeque};

use super::production_kind::{BracketName, DeclaredTotality, ProductionKind, Totality};
use super::{
    AttributeKey, Attributes, LabelHead, Location, OverloadOrder, ProductionCatalog, ProductionId,
    RuleCatalog, RuleId, Sentence, match_rule_label,
};
use crate::kast::{GeneratedLabel, InternalLabel, Label, Sort, Term};
use crate::names::{BuiltinSort, WellKnownSymbol};

/// The syntactic definedness walk of a term whose variables denote values.
pub(crate) fn term_is_defined(term: &Term, defined: &mut dyn FnMut(&Label) -> bool) -> bool {
    match term.unannotated() {
        Term::Variable { .. } | Term::Token { .. } | Term::InjectedLabel(_) => true,
        Term::Sequence(items) => items.iter().all(|item| term_is_defined(item, defined)),
        Term::Apply { label, arguments } => {
            defined(label) && arguments.iter().all(|item| term_is_defined(item, defined))
        }
        Term::Rewrite { .. } | Term::As { .. } => false,
        Term::Annotated { .. } => unreachable!("unannotated terms carry no annotation"),
    }
}

/// Judge the right-hand side of a rule body without constructing it.
pub(crate) fn right_side_is_defined(body: &Term, defined: &mut dyn FnMut(&Label) -> bool) -> bool {
    match body.unannotated() {
        Term::Rewrite { right, .. } => term_is_defined(right, defined),
        Term::As { alias, .. } => term_is_defined(alias, defined),
        Term::Apply { label, arguments } => {
            defined(label)
                && arguments
                    .iter()
                    .all(|item| right_side_is_defined(item, defined))
        }
        Term::Sequence(items) => items
            .iter()
            .all(|item| right_side_is_defined(item, defined)),
        Term::Variable { .. } | Term::Token { .. } | Term::InjectedLabel(_) => true,
        Term::Annotated { .. } => unreachable!("unannotated terms carry no annotation"),
    }
}

/// Evidence that a value production's applications are defined, minted by the judgement only.
#[derive(Clone, Copy, Debug)]
pub(crate) struct TotalHead(());

impl TotalHead {
    #[cfg(test)]
    pub(crate) fn assumed_for_test() -> Self {
        Self(())
    }
}

/// What the module's equations leave of a value production's totality.
#[derive(Clone, Debug)]
pub(crate) enum HeadTotality {
    /// No equation heads it: applications to values are values.
    Free,
    /// Every equation preserves definedness, using declarations and heads admitted earlier.
    Defined,
    /// An equation blocks the evidence, or it depends on a blocked or circular head.
    Unshown(UnshownCause),
}

/// The source location of an equation that prevents a totality claim, when supplied.
#[derive(Clone, Debug)]
pub(crate) struct EquationLocation {
    source: Option<String>,
    location: Option<Location>,
}

impl EquationLocation {
    fn of(attributes: &Attributes) -> Self {
        Self {
            source: attributes.source().map(str::to_owned),
            location: attributes.location(),
        }
    }
}

/// Why the sufficient definedness test could not establish a head's totality.
#[derive(Clone, Debug)]
pub(crate) enum UnshownCause {
    /// A right-hand side applies the first label not shown defined (or contains non-value syntax).
    Rule {
        location: EquationLocation,
        label: Option<Label>,
    },
    /// Conjoining the equation's postcondition can make its right-hand side undefined.
    Ensures(EquationLocation),
    /// An overload equation lowers to a production not shown total.
    Overload(ProductionId),
    /// The evidence requires a head on a dependency cycle.
    Cycle,
}

impl std::fmt::Display for UnshownCause {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let at = |formatter: &mut std::fmt::Formatter<'_>, location: &EquationLocation| {
            write!(
                formatter,
                " at {:?}:{:?}",
                location.source, location.location
            )
        };
        match self {
            Self::Rule { location, label } => {
                write!(formatter, "right-hand side not shown defined: {label:?}")?;
                at(formatter, location)
            }
            Self::Ensures(location) => {
                write!(formatter, "non-trivial ensures")?;
                at(formatter, location)
            }
            Self::Overload(lesser) => write!(formatter, "overload lesser {lesser:?} is not total"),
            Self::Cycle => write!(formatter, "circular totality evidence"),
        }
    }
}

#[derive(Clone, Copy)]
struct ProductionFact {
    totality: DeclaredTotality,
    ml_op: bool,
    semantic: bool,
}

#[derive(Default)]
struct IndexedEquations {
    rules: Vec<RuleId>,
    anywhere: bool,
    macro_like: bool,
}

/// One module's equation index and least-fixed-point judgement, owned by its consuming stage.
pub(crate) struct EquationTotality {
    heads: Vec<Option<HeadTotality>>,
    productions: Vec<ProductionFact>,
    labels: HashMap<LabelHead, Vec<ProductionId>>,
    equations: HashMap<LabelHead, IndexedEquations>,
}

/// The label a production's declaration is made under: its own label, or an unlabelled
/// bracket's `bracketLabel`.
pub(crate) fn declared_under(production: &Sentence, kind: ProductionKind) -> Option<LabelHead> {
    let Sentence::Production {
        label, attributes, ..
    } = production
    else {
        unreachable!("production catalogs contain productions")
    };
    if let ProductionKind::Bracket(BracketName::BracketLabel) = kind {
        attributes
            .label(AttributeKey::BracketLabel)
            .as_ref()
            .map(LabelHead::from)
    } else {
        label.as_ref().map(LabelHead::from)
    }
}

impl EquationTotality {
    /// Judge catalogs from the same module view and production order as the overload order.
    #[must_use]
    pub(crate) fn judge(
        productions: &ProductionCatalog<'_>,
        rules: &RuleCatalog<'_>,
        overloads: &OverloadOrder<'_>,
    ) -> Self {
        let macro_labels = rules.all_macro_labels(productions);
        let mut equations = HashMap::<LabelHead, IndexedEquations>::new();
        for (id, rule) in rules.rules() {
            if rule.attributes().has(AttributeKey::Simplification) {
                continue;
            }
            let head = LabelHead::from(&match_rule_label(rule));
            let anywhere = rule.attributes().has(AttributeKey::Anywhere);
            let macro_like = macro_labels.contains(&head);
            if anywhere || macro_like {
                let entry = equations.entry(head).or_default();
                entry.rules.push(id);
                entry.anywhere |= anywhere;
                entry.macro_like |= macro_like;
            }
        }
        let mut lessers = vec![Vec::new(); productions.len()];
        for lesser in overloads.order().elements() {
            if let Some(greaters) = overloads.order().relations_from(lesser) {
                for greater in greaters {
                    lessers[greater.0].push(*lesser);
                }
            }
        }
        let mut labels = HashMap::<LabelHead, Vec<ProductionId>>::new();
        let mut facts = Vec::with_capacity(productions.len());
        let mut heads = Vec::with_capacity(productions.len());
        let mut candidates = vec![false; productions.len()];
        for (id, production) in productions.productions() {
            let kind = ProductionKind::of(production);
            let label = declared_under(production, kind);
            let effective = match kind {
                ProductionKind::Bracket(_) => ProductionKind::of_unbracketed(production),
                ProductionKind::Subsort
                | ProductionKind::Builtin
                | ProductionKind::Function { .. }
                | ProductionKind::MacroProduction
                | ProductionKind::Token { .. }
                | ProductionKind::Unlabelled
                | ProductionKind::Algebraic
                | ProductionKind::Base => kind,
            };
            let totality = effective.declared_totality();
            let head = match totality {
                DeclaredTotality::NoSymbol | DeclaredTotality::Function(_) => None,
                DeclaredTotality::ValuesUnlessEquations => {
                    if label
                        .as_ref()
                        .is_some_and(|head| equations.contains_key(head))
                        || !lessers[id.0].is_empty()
                    {
                        candidates[id.0] = true;
                        Some(HeadTotality::Unshown(UnshownCause::Cycle))
                    } else {
                        Some(HeadTotality::Free)
                    }
                }
            };
            if let Some(label) = label {
                labels.entry(label).or_default().push(id);
            }
            facts.push(ProductionFact {
                totality,
                ml_op: production.attributes().has(AttributeKey::MlOp),
                semantic: !matches!(kind, ProductionKind::Bracket(_)),
            });
            heads.push(head);
        }
        let mut judgement = Self {
            heads,
            productions: facts,
            labels,
            equations,
        };
        let mut dependencies = vec![HashSet::new(); productions.len()];
        let mut blocked = vec![None; productions.len()];
        for (id, production) in productions.productions() {
            if !candidates[id.0] {
                continue;
            }
            if let Some(label) = declared_under(production, ProductionKind::of(production))
                && let Some(index) = judgement.equations.get(&label)
            {
                for rule_id in &index.rules {
                    let Sentence::Rule {
                        body,
                        ensures,
                        attributes,
                        ..
                    } = rules.rule(*rule_id)
                    else {
                        unreachable!("rule catalogs contain rules")
                    };
                    if !is_true(ensures) {
                        blocked[id.0] =
                            Some(UnshownCause::Ensures(EquationLocation::of(attributes)));
                        break;
                    }
                    let mut missing = None;
                    let defined = right_side_is_defined(body, &mut |label| {
                        if judgement.label_is_defined(label) {
                            return true;
                        }
                        let ids = judgement.labels.get(&LabelHead::from(label));
                        if let Some(ids) = ids
                            && label.generated().is_none()
                            && InternalLabel::of(&label.name).is_none()
                            && !ids.is_empty()
                            && ids.iter().all(|id| {
                                candidates[id.0]
                                    && !judgement.productions[id.0].ml_op
                                    && judgement.productions[id.0].semantic
                            })
                        {
                            dependencies[id.0].extend(ids.iter().copied());
                            true
                        } else {
                            missing = Some(label.clone());
                            false
                        }
                    });
                    if !defined {
                        blocked[id.0] = Some(UnshownCause::Rule {
                            location: EquationLocation::of(attributes),
                            label: missing,
                        });
                        break;
                    }
                }
            }
            for lesser in &lessers[id.0] {
                let fine = match judgement.productions[lesser.0].totality {
                    DeclaredTotality::Function(Totality::Total) => true,
                    DeclaredTotality::Function(Totality::Partial) | DeclaredTotality::NoSymbol => {
                        false
                    }
                    DeclaredTotality::ValuesUnlessEquations => {
                        matches!(judgement.heads[lesser.0], Some(HeadTotality::Free))
                    }
                };
                if !fine {
                    if candidates[lesser.0] {
                        dependencies[id.0].insert(*lesser);
                    } else if blocked[id.0].is_none() {
                        blocked[id.0] = Some(UnshownCause::Overload(*lesser));
                    }
                }
            }
        }
        let mut remaining = dependencies.iter().map(HashSet::len).collect::<Vec<_>>();
        let mut dependents = vec![Vec::new(); productions.len()];
        for (index, dependencies) in dependencies.iter().enumerate() {
            for dependency in dependencies {
                dependents[dependency.0].push(ProductionId(index));
            }
        }
        let mut ready = productions
            .ids()
            .filter(|id| candidates[id.0] && blocked[id.0].is_none() && remaining[id.0] == 0)
            .collect::<VecDeque<_>>();
        while let Some(id) = ready.pop_front() {
            judgement.heads[id.0] = Some(HeadTotality::Defined);
            for dependent in &dependents[id.0] {
                remaining[dependent.0] -= 1;
                if remaining[dependent.0] == 0 && blocked[dependent.0].is_none() {
                    ready.push_back(*dependent);
                }
            }
        }
        // A direct blocker also blocks every still-unshown dependent. Propagating it once per
        // head leaves precisely the cycles and the heads behind cycles with the Cycle cause.
        let mut causes = productions
            .ids()
            .filter(|id| blocked[id.0].is_some())
            .collect::<VecDeque<_>>();
        for id in &causes {
            judgement.heads[id.0] = Some(HeadTotality::Unshown(
                blocked[id.0].take().expect("queued heads have a blocker"),
            ));
        }
        let mut propagated = vec![false; productions.len()];
        for id in &causes {
            propagated[id.0] = true;
        }
        while let Some(id) = causes.pop_front() {
            let Some(HeadTotality::Unshown(cause)) = &judgement.heads[id.0] else {
                unreachable!("only unshown heads propagate a blocker")
            };
            let cause = cause.clone();
            for dependent in &dependents[id.0] {
                if !propagated[dependent.0]
                    && !matches!(judgement.heads[dependent.0], Some(HeadTotality::Defined))
                {
                    judgement.heads[dependent.0] = Some(HeadTotality::Unshown(cause.clone()));
                    propagated[dependent.0] = true;
                    causes.push_back(*dependent);
                }
            }
        }
        judgement
    }

    /// The judgement for a value production; non-value productions have no such judgement.
    pub(crate) fn of(&self, id: ProductionId) -> &HeadTotality {
        self.heads[id.0]
            .as_ref()
            .expect("head totality is defined only for value productions")
    }

    pub(crate) fn total_value_head(&self, id: ProductionId) -> Option<TotalHead> {
        self.heads[id.0].as_ref()?;
        match self.of(id) {
            HeadTotality::Free | HeadTotality::Defined => Some(TotalHead(())),
            HeadTotality::Unshown(_) => None,
        }
    }

    pub(crate) fn heads_anywhere(&self, label: &LabelHead) -> bool {
        self.equations
            .get(label)
            .is_some_and(|index| index.anywhere)
    }

    pub(crate) fn heads_macro(&self, label: &LabelHead) -> bool {
        self.equations
            .get(label)
            .is_some_and(|index| index.macro_like)
    }

    /// Layer zero, extended by the value heads established by the least fixed point.
    pub(crate) fn label_is_defined(&self, label: &Label) -> bool {
        // A sort injection maps every source value to a target value. KORE declares this
        // total symbol in its prelude, without a production in the module's catalog.
        if label.is(WellKnownSymbol::Inj) {
            return true;
        }
        match label.generated() {
            Some(GeneratedLabel::SemanticCast { .. }) => return true,
            Some(
                GeneratedLabel::Projection { .. }
                | GeneratedLabel::FieldProjection { .. }
                | GeneratedLabel::Lambda { .. }
                | GeneratedLabel::Freezer { .. },
            ) => {
                return self.labels.get(&LabelHead::from(label)).is_some_and(|ids| {
                    !ids.is_empty()
                        && ids.iter().all(|id| {
                            self.productions[id.0].semantic
                                && matches!(
                                    self.productions[id.0].totality,
                                    DeclaredTotality::Function(Totality::Total)
                                )
                        })
                });
            }
            None => {}
        }
        if InternalLabel::of(&label.name).is_some() {
            return false;
        }
        self.labels.get(&LabelHead::from(label)).is_some_and(|ids| {
            !ids.is_empty()
                && ids.iter().all(|id| {
                    let fact = self.productions[id.0];
                    fact.semantic
                        && !fact.ml_op
                        && match fact.totality {
                            DeclaredTotality::Function(Totality::Total) => true,
                            DeclaredTotality::NoSymbol
                            | DeclaredTotality::Function(Totality::Partial) => false,
                            DeclaredTotality::ValuesUnlessEquations => {
                                match self.heads[id.0].as_ref() {
                                    Some(HeadTotality::Free | HeadTotality::Defined) => true,
                                    Some(HeadTotality::Unshown(_)) | None => false,
                                }
                            }
                        }
                })
        })
    }
}

pub(crate) fn is_true(term: &Term) -> bool {
    matches!(term.unannotated(), Term::Token { token, sort }
        if token == "true" && *sort == Sort::builtin(BuiltinSort::Bool))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::ResolvedDefinition;

    fn judged(source: &str) -> HashMap<String, HeadTotality> {
        let parsed = crate::outer::parse("totality.k", source).expect("definition should parse");
        let lowered = crate::outer::lower(&parsed, "MAIN").expect("definition should lower");
        let definition =
            crate::inner::resolve_rule_bubbles(&lowered).expect("rule bubbles should resolve");
        let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
        let module = resolved.module_id("MAIN").unwrap();
        let productions = resolved.production_catalog(module);
        let overloads = resolved.overloads(module).expect("no overload cycle");
        let totality =
            EquationTotality::judge(&productions, &resolved.rule_catalog(module), &overloads);
        productions
            .productions()
            .filter_map(|(id, production)| {
                let Sentence::Production {
                    label: Some(label), ..
                } = production
                else {
                    return None;
                };
                totality.heads[id.0]
                    .as_ref()
                    .map(|head| (label.name.clone(), head.clone()))
            })
            .collect()
    }

    fn arithmetic(extra: &str) -> HashMap<String, HeadTotality> {
        judged(&format!(
            r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax Bool ::= "true" [token]
              syntax Int ::= Int "/Int" Int [function, symbol(_/Int_)]
                           | Int "+Int" Int [function, total, symbol(_+Int_)]
              syntax Bool ::= Int "=/=Int" Int [function, total, symbol(_=/=Int_)]
                            | Int ">Int" Int [function, total, symbol(_>Int_)]
              syntax S ::= "mk(" Int ")" [symbol(mk)]
                         | "wrap(" Int ")" [symbol(wrap)]
              {extra}
            endmodule
            "#
        ))
    }

    #[test]
    fn anywhere_partial_arithmetic_is_unshown_and_total_arithmetic_is_defined() {
        let partial = arithmetic("rule wrap(X:Int) => mk(X:Int /Int 0) [anywhere]");
        assert!(matches!(partial["wrap"], HeadTotality::Unshown(_)));
        let total = arithmetic("rule wrap(X:Int) => mk(X:Int +Int 1) [anywhere]");
        assert!(matches!(total["wrap"], HeadTotality::Defined));
    }

    #[test]
    fn a_guard_does_not_establish_syntactic_definedness() {
        let heads =
            arithmetic("rule wrap(X:Int) => mk(10 /Int X:Int) requires X:Int =/=Int 0 [anywhere]");
        assert!(matches!(heads["wrap"], HeadTotality::Unshown(_)));
    }

    #[test]
    fn a_nested_anywhere_rewrite_cannot_use_its_own_head_as_evidence() {
        let heads = judged(indoc::indoc! {r#"
            module MAIN
              syntax S ::= "a" [symbol(a)] | "b" [symbol(b)]
                         | "foo(" S ")" [symbol(foo)]
              rule foo(a => b) [anywhere]
            endmodule
        "#});
        assert!(matches!(
            heads["foo"],
            HeadTotality::Unshown(UnshownCause::Cycle)
        ));
    }

    #[test]
    fn acyclic_dependencies_admit_a_chain_and_a_blocked_head_blocks_its_dependents() {
        let total = judged(indoc::indoc! {r#"
            module MAIN
              syntax S ::= "mk(" S ")" [symbol(mk)]
                         | "h1(" S ")" [symbol(h1)]
                         | "h2(" S ")" [symbol(h2)]
              rule h1(X:S) => mk(h2(X:S)) [anywhere]
              rule h2(X:S) => mk(X:S) [anywhere]
            endmodule
        "#});
        assert!(matches!(total["h1"], HeadTotality::Defined));
        assert!(matches!(total["h2"], HeadTotality::Defined));
        let partial = arithmetic(indoc::indoc! {r#"
            syntax S ::= "dependent(" Int ")" [symbol(dependent)]
            rule wrap(X:Int) => mk(X:Int /Int 0) [anywhere]
            rule dependent(X:Int) => wrap(X:Int) [anywhere]
        "#});
        assert!(matches!(partial["dependent"], HeadTotality::Unshown(_)));
    }

    #[test]
    fn an_overload_greater_cannot_lower_to_a_partial_function() {
        let heads = judged(indoc::indoc! {r#"
            module MAIN
              syntax Int
              syntax Exp ::= Int
                           | "fe(" Exp ")" [overload(f), symbol(fE)]
              syntax Int ::= "fi(" Int ")" [overload(f), function, symbol(fI)]
            endmodule
        "#});
        assert!(matches!(
            heads["fE"],
            HeadTotality::Unshown(UnshownCause::Overload(_))
        ));
    }

    #[test]
    fn constructor_overload_chains_preserve_definedness_transitively() {
        let source = include_str!("../../tests/fixtures/reference/overload-constructors.k")
            .replace("OVERLOAD-CONSTRUCTORS", "MAIN");
        let heads = judged(&source);
        for label in ["wide", "widest", "asMedium", "fromMedium"] {
            assert!(matches!(heads[label], HeadTotality::Defined), "{label}");
        }
        for label in ["narrow", "asSmall", "fromSmall"] {
            assert!(matches!(heads[label], HeadTotality::Free), "{label}");
        }
    }

    #[test]
    fn macro_expansions_need_definedness_evidence_but_a_macro_without_a_rule_is_free() {
        let partial = arithmetic(indoc::indoc! {r#"
            syntax S ::= "half(" Int ")" [macro, symbol(half)]
            rule half(X:Int) => mk(X:Int /Int 0)
        "#});
        assert!(matches!(partial["half"], HeadTotality::Unshown(_)));
        let total = arithmetic(indoc::indoc! {r#"
            syntax S ::= "half(" Int ")" [macro, symbol(half)]
            rule half(X:Int) => mk(X:Int +Int 1)
        "#});
        assert!(matches!(total["half"], HeadTotality::Defined));
        let free = arithmetic("syntax S ::= \"half(\" Int \")\" [macro, symbol(half)]");
        assert!(matches!(free["half"], HeadTotality::Free));
    }

    #[test]
    fn a_nontrivial_ensures_blocks_totality_and_a_simplification_does_not_define_a_head() {
        let heads = arithmetic("rule wrap(X:Int) => mk(X:Int) ensures X:Int >Int 0 [anywhere]");
        assert!(matches!(
            heads["wrap"],
            HeadTotality::Unshown(UnshownCause::Ensures(_))
        ));
        let lemma = arithmetic("rule wrap(X:Int) => mk(X:Int /Int 0) [anywhere, simplification]");
        assert!(matches!(lemma["wrap"], HeadTotality::Free));
    }
}
