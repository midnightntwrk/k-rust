//! ```toml algorithm-site
//! id = "kompile.sort_helpers.generate"
//! role = "part"
//! sites = ["subsort_kitem", "subsort_kitem_pass"]
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Add backend subsort declarations from every user sort to `KItem`.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{fmt, sync::Arc};

use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, PartialOrder, ProductionItem, Sentence, retain_new_sentences,
    },
    kast::Sort,
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SubsortKItemError(pub String);

impl fmt::Display for SubsortKItemError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for SubsortKItemError {}

/// Apply Java's `Kompile.subsortKItem` module transformation.
pub fn subsort_kitem(definition: &Definition) -> Result<Definition, SubsortKItemError> {
    super::super::pipeline::run_standalone(
        definition,
        subsort_kitem_pass,
        Some(GeneratingPass::SubsortKItem),
    )
}

pub(crate) fn subsort_kitem_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, SubsortKItemError> {
    let resolved = input
        .resolved_raw()
        .map_err(|error| SubsortKItemError(error.to_string()))?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let sorts = views.sort_catalog(module_id);
        let visible = resolved.sentences(module_id);
        let mut generated = Vec::new();
        // Invariant: `generated` holds a `KItem ::= Sort` subsort production for every non-parser sort of `sorts.all_sorts()` before `sort`; each iteration consumes one sort.
        for sort in sorts.all_sorts() {
            if !sort.role().has_implicit_kitem_subsort() {
                continue;
            }
            let production = Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: Sort::builtin(BuiltinSort::KItem),
                items: vec![ProductionItem::NonTerminal {
                    sort: sort.clone(),
                    name: None,
                }],
                attributes: Attributes::default(),
            };
            generated.push(production);
        }
        let generated = retain_new_sentences(
            visible
                .iter()
                .copied()
                .chain(module.local_sentences.iter().map(Arc::as_ref)),
            generated,
        );
        module
            .local_sentences
            .extend(generated.into_iter().map(Arc::new));
    }
    Ok(output)
}

/// `subsorts` with the `KItem ::= S` subsorts this stage adds for every sort `S` of `sorts` that is
/// not a parser sort: the order sort injection works in after this stage has run.
pub(crate) fn with_kitem_subsorts<'a>(
    subsorts: &PartialOrder<Sort>,
    sorts: impl IntoIterator<Item = &'a Sort>,
) -> Result<PartialOrder<Sort>, crate::definition::PartialOrderCycle<Sort>> {
    let kitem = Sort::builtin(BuiltinSort::KItem);
    PartialOrder::new(
        subsorts.direct_relations().iter().cloned().chain(
            sorts
                .into_iter()
                .filter(|sort| sort.role().has_implicit_kitem_subsort())
                .map(|sort| (sort.clone(), kitem.clone())),
        ),
    )
}

/// Whether the emitted theory has a subsort axiom for a declared subsort into `greater`: every
/// declared subsort except those into `K`, since a `KItem` becomes a `K` as a one-element
/// sequence, not by injection.
pub(crate) fn has_subsort_axiom(greater: &Sort) -> bool {
    !greater.is_builtin(BuiltinSort::K)
}

pub(crate) use witness::Injectable;

/// The witness lives in its own module so that nothing else in this file, which also defines
/// the relations it is minted from, can build one by struct literal.
mod witness {
    use super::injectable;
    use crate::{
        definition::PartialOrder,
        kast::{Label, Sort, Term},
        kore::ast::{Pattern, Symbol},
        names::WellKnownSymbol,
    };

    /// Evidence that `inj{source, target}` denotes the embedding of `source` in `target`:
    /// `source != target` and `source < target` along the subsort axioms of the emitted theory
    /// (`injectable`), under the module order the witness was minted against.
    ///
    /// The fields are private to this module, so a value exists only after
    /// `Injectable::between` has decided the pair, and the only builders of an injection,
    /// `Injectable::apply` in KAST and `Injectable::apply_kore` in KORE, take
    /// one.
    #[must_use]
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub(crate) struct Injectable {
        source: Sort,
        target: Sort,
    }

    impl Injectable {
        /// The witness for `inj{source, target}`, or `None` when `source == target` (no
        /// injection is needed) or no chain of subsort axioms leads from `source` to `target`.
        ///
        /// `subsorts` must be the module's semantic subsort order (`ResolvedDefinition::subsorts`,
        /// the injector's order, or either extended by `with_kitem_subsorts`); the syntactic and
        /// disambiguation orders contain edges that are not subsort axioms.
        #[must_use]
        pub(crate) fn between(
            source: &Sort,
            target: &Sort,
            subsorts: &PartialOrder<Sort>,
        ) -> Option<Self> {
            (source != target && injectable(source, target, subsorts)).then(|| Self {
                source: source.clone(),
                target: target.clone(),
            })
        }

        /// The sort the injection embeds.
        pub(crate) fn source(&self) -> &Sort {
            &self.source
        }

        /// The sort the injection embeds into.
        pub(crate) fn target(&self) -> &Sort {
            &self.target
        }

        /// Encode a licensed injection using the sentence's formal sort scope.
        pub(crate) fn apply_kore(self, pattern: Pattern, formals: &[Sort]) -> Pattern {
            self.try_apply_kore(pattern, |sort| {
                Ok::<_, std::convert::Infallible>(
                    crate::kompile::module_to_kore::encode_kore_sort_with_formals(sort, formals),
                )
            })
            .expect("the ordinary sort encoder is infallible")
        }

        /// Encode the witnessed pair with a scope-aware sort encoder.
        /// The encoder must preserve each witnessed sort and its formal scope, as
        /// `TermConverter::kore_sort` and `encode_kore_sort_with_formals` do; replacing
        /// either sort with a different one would invalidate the witness.
        pub(crate) fn try_apply_kore<E>(
            self,
            pattern: Pattern,
            mut encode: impl FnMut(&Sort) -> Result<crate::kore::ast::Sort, E>,
        ) -> Result<Pattern, E> {
            Ok(Pattern::Application {
                symbol: Symbol {
                    name: WellKnownSymbol::Inj.as_str().into(),
                    sort_parameters: vec![encode(&self.source)?, encode(&self.target)?],
                },
                arguments: vec![pattern],
            })
        }

        /// `inj{source, target}(term)`: the only KAST construction of an injection application
        /// in kompile's emitted definition.
        pub(crate) fn apply(self, term: Term) -> Term {
            Term::Apply {
                label: Label::with_parameters(
                    WellKnownSymbol::Inj.as_str(),
                    vec![self.source, self.target],
                ),
                arguments: vec![term],
            }
        }
    }
}

pub(crate) use placement::{Placement, PlacementKind};

// A separate module keeps even the relation's callers from assembling a plan by hand.
mod placement {
    use super::{BuiltinSort, Injectable, PartialOrder, Sort};
    /// An outer coercion of an already typed term, without revisiting its chosen instances.
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub(crate) enum PlacementKind {
        Identity,
        Injection(Injectable),
        SingletonK {
            item: Option<Injectable>,
        },
        SingletonKInjection {
            item: Option<Injectable>,
            sequence: Injectable,
        },
    }

    /// A plan minted only by the semantic placement relation.
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub(crate) struct Placement {
        kind: PlacementKind,
    }

    impl Placement {
        pub(crate) fn kind(&self) -> &PlacementKind {
            &self.kind
        }

        pub(crate) fn between(
            actual: &Sort,
            expected: &Sort,
            subsorts: &PartialOrder<Sort>,
        ) -> Option<Self> {
            if actual == expected {
                return Some(Self {
                    kind: PlacementKind::Identity,
                });
            }
            if let Some(witness) = Injectable::between(actual, expected, subsorts) {
                return Some(Self {
                    kind: PlacementKind::Injection(witness),
                });
            }
            let k = Sort::builtin(BuiltinSort::K);
            let sequence = if *expected == k {
                None
            } else {
                Some(Injectable::between(&k, expected, subsorts)?)
            };
            let kitem = Sort::builtin(BuiltinSort::KItem);
            let item = if *actual == kitem {
                None
            } else {
                Some(Injectable::between(actual, &kitem, subsorts)?)
            };
            Some(Self {
                kind: match sequence {
                    None => PlacementKind::SingletonK { item },
                    Some(sequence) => PlacementKind::SingletonKInjection { item, sequence },
                },
            })
        }

        pub(crate) fn apply(self, term: crate::kast::Term) -> crate::kast::Term {
            use crate::kast::Term;
            match self.kind {
                PlacementKind::Identity => term,
                PlacementKind::Injection(witness) => witness.apply(term),
                PlacementKind::SingletonK { item } => Term::Sequence(vec![match item {
                    None => term,
                    Some(witness) => witness.apply(term),
                }]),
                PlacementKind::SingletonKInjection { item, sequence } => sequence.apply(
                    Self {
                        kind: PlacementKind::SingletonK { item },
                    }
                    .apply(term),
                ),
            }
        }

        pub(crate) fn apply_kore(
            self,
            pattern: crate::kore::ast::Pattern,
            formals: &[Sort],
        ) -> crate::kore::ast::Pattern {
            use crate::{
                kore::ast::{Pattern, Symbol},
                names::WellKnownSymbol,
            };
            match self.kind {
                PlacementKind::Identity => pattern,
                PlacementKind::Injection(witness) => witness.apply_kore(pattern, formals),
                PlacementKind::SingletonK { item } => Pattern::Application {
                    symbol: Symbol {
                        name: WellKnownSymbol::KSeq.as_str().into(),
                        sort_parameters: Vec::new(),
                    },
                    arguments: vec![
                        match item {
                            None => pattern,
                            Some(witness) => witness.apply_kore(pattern, formals),
                        },
                        Pattern::Application {
                            symbol: Symbol {
                                name: WellKnownSymbol::DotK.as_str().into(),
                                sort_parameters: Vec::new(),
                            },
                            arguments: Vec::new(),
                        },
                    ],
                },
                PlacementKind::SingletonKInjection { item, sequence } => sequence.apply_kore(
                    Self {
                        kind: PlacementKind::SingletonK { item },
                    }
                    .apply_kore(pattern, formals),
                    formals,
                ),
            }
        }
    }
}

/// Whether a single `inj{actual, expected}` is justified: `actual <= expected` along subsort axioms
/// of the emitted theory.
///
/// Those axioms are the declared subsorts except the ones into `K` (the emitted definition has no
/// subsort axiom into `K`: a `KItem` becomes a `K` as a one-element sequence, not by injection),
/// plus `S <= KItem` for every sort `S` that is not a parser sort, which this stage declares and
/// which semantic-cast resolution and sort injection may need before it has run. The relation is
/// their transitive closure; it continues above `KItem` only through declared supersorts of
/// `KItem` that are not reached through `K`.
pub(crate) fn injectable(actual: &Sort, expected: &Sort, subsorts: &PartialOrder<Sort>) -> bool {
    if actual == expected {
        return true;
    }
    if !has_subsort_axiom(expected) {
        return false;
    }
    let k = Sort::builtin(BuiltinSort::K);
    let k_item = Sort::builtin(BuiltinSort::KItem);
    if subsorts.less_than_eq(&k, expected) {
        return injectable_path(actual, expected, subsorts);
    }
    // No path to `expected` passes through `K`, since `K` is not below it.
    subsorts.less_than_eq(actual, expected)
        || ((expected == &k_item || subsorts.less_than_eq(&k_item, expected))
            && reaches_k_item(actual, subsorts))
}

/// Whether compilation can place a term of sort `actual` at a position of sort `expected`: by one
/// injection ([`injectable`]); at a `K` position as the one-element sequence of a `KItem`; or at a
/// position above `K` as the injection of that sequence (`inj{K, expected}` of `actual ~> .K`).
/// Collection and user-list positions, where the injector also wraps an element, are the
/// injector's own concern.
pub(crate) fn placeable(actual: &Sort, expected: &Sort, subsorts: &PartialOrder<Sort>) -> bool {
    let k = Sort::builtin(BuiltinSort::K);
    injectable(actual, expected, subsorts)
        || (injectable(actual, &Sort::builtin(BuiltinSort::KItem), subsorts)
            && (expected == &k || injectable(&k, expected, subsorts)))
}

/// Whether `actual <= KItem` along the axioms of [`injectable`], none of which leads out of `K`.
fn reaches_k_item(actual: &Sort, subsorts: &PartialOrder<Sort>) -> bool {
    let k = Sort::builtin(BuiltinSort::K);
    let k_item = Sort::builtin(BuiltinSort::KItem);
    actual == &k_item
        || subsorts.less_than_eq(actual, &k_item)
        || actual.role().has_implicit_kitem_subsort()
        || subsorts.relations_from(actual).is_some_and(|supersorts| {
            supersorts.iter().any(|sort| {
                sort.role().has_implicit_kitem_subsort() && !subsorts.less_than_eq(&k, sort)
            })
        })
}

/// [`injectable`] for an `expected` above `K`: a search over the axioms, which excludes the
/// declared edges without one ([`has_subsort_axiom`]).
// Invariant: `seen` holds every sort reached from `actual` so far, each expanded once, so the search visits at most every declared sort plus `KItem`, scanning the direct relations once per sort.
fn injectable_path(actual: &Sort, expected: &Sort, subsorts: &PartialOrder<Sort>) -> bool {
    let k_item = Sort::builtin(BuiltinSort::KItem);
    let mut seen = std::collections::BTreeSet::from([actual.clone()]);
    let mut pending = vec![actual.clone()];
    while let Some(sort) = pending.pop() {
        if &sort == expected {
            return true;
        }
        let implicit = sort
            .role()
            .has_implicit_kitem_subsort()
            .then(|| k_item.clone());
        let declared = subsorts
            .direct_relations()
            .iter()
            .filter(|(lesser, greater)| *lesser == sort && has_subsort_axiom(greater))
            .map(|(_, greater)| greater.clone());
        for next in declared.chain(implicit) {
            if seen.insert(next.clone()) {
                pending.push(next);
            }
        }
    }
    false
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use super::{Injectable, Placement, PlacementKind};
    use crate::definition::{
        AttributeKey, Attributes, PartialOrder, ProductionItem, Sentence,
        compute_disambiguation_subsorts, compute_subsorts,
    };
    use crate::kast::{Label, Sort, Term};
    use crate::names::{BuiltinSort, WellKnownSymbol};
    use serde_json::Value;

    fn order(edges: &[(Sort, Sort)]) -> PartialOrder<Sort> {
        PartialOrder::new(edges.iter().cloned()).expect("the test order is acyclic")
    }

    fn production(sort: &str, items: Vec<ProductionItem>, user_list: bool) -> Sentence {
        let mut attributes = Attributes::default();
        if user_list {
            attributes.set(AttributeKey::UserList, Value::String("*".into()));
        }
        Sentence::Production {
            label: Some(Label::new(format!("{sort}Cons"))),
            parameters: Vec::new(),
            sort: Sort::new(sort),
            items,
            attributes,
        }
    }

    /// The sort parameters of the `inj` application `witness` builds, after checking that it
    /// applies `inj` to the term it is given.
    fn injected_pair(witness: Injectable) -> Vec<Sort> {
        let term = Term::Variable {
            name: "X".into(),
            sort: None,
        };
        let Term::Apply { label, arguments } = witness.apply(term.clone()) else {
            panic!("an injection is an application");
        };
        assert!(label.is(WellKnownSymbol::Inj));
        assert_eq!(arguments, [term]);
        label.parameters
    }

    fn nonterminal(sort: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(sort),
            name: None,
        }
    }

    /// The order a witness is minted against decides what it certifies: the rule-disambiguation
    /// order of a user list `Items ::= List{Item, ","}` relates `Item < Items` so that a single
    /// element parses as a list, but the emitted theory has no subsort axiom for that edge (an
    /// element becomes a list by the list constructor), so only the semantic order is a valid
    /// argument of `Injectable::between`.
    #[test]
    fn between_certifies_against_the_order_it_is_given() {
        let cons = production(
            "Items",
            vec![
                nonterminal("Item"),
                ProductionItem::Terminal(",".into()),
                nonterminal("Items"),
            ],
            true,
        );
        let nil = production(
            "Items",
            vec![ProductionItem::Terminal(".Items".into())],
            true,
        );
        let sentences = [&cons, &nil];
        let semantic = compute_subsorts(sentences, false).expect("acyclic");
        let disambiguation = compute_disambiguation_subsorts(&sentences).expect("acyclic");
        let item = Sort::new("Item");
        let items = Sort::new("Items");

        assert_eq!(Injectable::between(&item, &items, &semantic), None);
        let witness = Injectable::between(&item, &items, &disambiguation)
            .expect("the disambiguation order relates an element to its list");
        assert_eq!(injected_pair(witness), [item, items]);
    }

    /// Above `K`, only `K` itself and sorts reaching it by a subsort axiom inject: `Int < KItem`
    /// and `K < KList` are axioms, `KItem < K` is not (a `KItem` becomes a `K` as a one-element
    /// sequence), so no chain of axioms leads from `Int` to `KList`.
    #[test]
    fn between_follows_only_subsort_axioms_across_k() {
        let int = Sort::new("Int");
        let k_item = Sort::builtin(BuiltinSort::KItem);
        let k = Sort::builtin(BuiltinSort::K);
        let k_list = Sort::new("KList");
        let subsorts = order(&[
            (int.clone(), k_item.clone()),
            (k_item.clone(), k.clone()),
            (k.clone(), k_list.clone()),
        ]);

        assert_eq!(Injectable::between(&int, &k_list, &subsorts), None);
        assert_eq!(Injectable::between(&k_item, &k, &subsorts), None);
        let into_item = Injectable::between(&int, &k_item, &subsorts).expect("Int < KItem");
        assert_eq!(injected_pair(into_item), [int, k_item]);
        let into_list = Injectable::between(&k, &k_list, &subsorts).expect("K < KList");
        assert_eq!(injected_pair(into_list), [k, k_list]);
    }

    /// A term already of the position's sort needs no injection, so there is no witness for it.
    #[test]
    fn between_a_sort_and_itself_is_none() {
        let int = Sort::new("Int");
        let subsorts = order(&[(int.clone(), Sort::builtin(BuiltinSort::KItem))]);
        assert_eq!(Injectable::between(&int, &int, &subsorts), None);
        let k = Sort::builtin(BuiltinSort::K);
        assert_eq!(Injectable::between(&k, &k, &subsorts), None);
    }

    #[test]
    fn placement_preserves_whole_k_and_uses_singletons_for_items() {
        let int = Sort::new("Int");
        let item = Sort::builtin(BuiltinSort::KItem);
        let k = Sort::builtin(BuiltinSort::K);
        let list = Sort::builtin(BuiltinSort::List);
        let subsorts = order(&[
            (int.clone(), item.clone()),
            (item.clone(), k.clone()),
            (k.clone(), list.clone()),
        ]);
        let whole_k = Term::Sequence(vec![]);
        let identity = Placement::between(&k, &k, &subsorts).unwrap();
        assert!(matches!(identity.kind(), PlacementKind::Identity));
        assert_eq!(identity.apply(whole_k.clone()), whole_k);
        assert!(Placement::between(&k, &item, &subsorts).is_none());

        let singleton = Placement::between(&item, &k, &subsorts).unwrap();
        assert!(matches!(
            singleton.kind(),
            PlacementKind::SingletonK { item: None }
        ));
        let variable = Term::Variable {
            name: "X".into(),
            sort: Some(item.clone()),
        };
        assert_eq!(
            singleton.apply(variable.clone()),
            Term::Sequence(vec![variable])
        );

        let into_item = Placement::between(&int, &item, &subsorts).unwrap();
        assert!(matches!(into_item.kind(), PlacementKind::Injection(_)));
        let singleton = Placement::between(&int, &k, &subsorts).unwrap();
        assert!(matches!(
            singleton.kind(),
            PlacementKind::SingletonK { item: Some(_) }
        ));
        let into_list = Placement::between(&int, &list, &subsorts).unwrap();
        assert!(matches!(
            into_list.kind(),
            PlacementKind::SingletonKInjection { item: Some(_), .. }
        ));
        let variable = Term::Variable {
            name: "X".into(),
            sort: Some(int.clone()),
        };
        assert_eq!(
            into_list.apply(variable.clone()),
            Injectable::between(&k, &list, &subsorts)
                .unwrap()
                .apply(Term::Sequence(vec![
                    Injectable::between(&int, &item, &subsorts)
                        .unwrap()
                        .apply(variable)
                ]))
        );
    }
}
