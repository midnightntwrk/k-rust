//! This definition-layer module holds no algorithm of its own: the kind of a production is a
//! constant number of attribute lookups, and [`SortGenerators::of`] is one scan of a production
//! catalog and one of a sort catalog per sort, which the `kompile.kore.axioms` card of its caller
//! (`no_junk_axioms`) counts.
//!
//! What a production's own declaration makes its symbol, decided once.
//!
//! [`ProductionKind::of`] classifies a production by its declaration alone, before rules and
//! overloads are consulted, in one precedence order. Every consumer that decides a claim of the
//! emitted theory from whether a production is a subsort, a matching-logic builtin, a bracket, a
//! function, a macro production or a token reads that decision from the kind, so no two claims
//! about one production can rest on two different readings of its attributes.
//! [`SortGenerators`] derives the alternatives of a sort's no-junk axiom from the kinds of its
//! productions.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::BTreeMap;

use super::{
    AttributeKey, Attributes, PartialOrder, ProductionCatalog, ProductionId, ProductionItem,
    Sentence, SortCatalog, SortHead,
};
use crate::kast::{InternalLabel, Sort};
use crate::kompile::Injectable;

/// Whether each application of a function production denotes exactly one value, as its
/// declaration states.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Totality {
    /// The declaration carries `total`.
    Total,
    /// The declaration carries no `total`: an application may denote no value.
    Partial,
}

/// The name a bracket's syntax-module declaration is made under.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BracketName {
    /// The bracket is labelled, and its label names the declaration.
    OwnLabel,
    /// The bracket is unlabelled and carries a readable `bracketLabel`, which names the
    /// declaration.
    BracketLabel,
    /// The bracket has neither, so it is declared in neither module.
    Undeclared,
}

/// What a production's own declaration makes its symbol, before rules and overloads.
///
/// [`ProductionKind::of`] tests the variants in declaration order; the first that holds is the
/// kind. Where one combination of attributes would fit two variants, the earlier variant keeps the
/// later one's fact as a field (`Function { macro_like }`, `Token { algebraic }`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProductionKind {
    /// Unlabelled `S ::= T`: an injection, stated by the subsort axiom; declares no symbol.
    Subsort,
    /// Labelled with a matching-logic connective: the prelude declares it.
    Builtin,
    /// Carries `bracket`, which only groups program or rule text.
    ///
    /// Every parser erases a bracket node before a term exists, and the generated bison grammar
    /// reduces a bracket to its child, so no term the frontend builds contains a bracket's
    /// symbol, whatever its label. A bracket's label (or `bracketLabel` when it has none) names
    /// only its syntax-module declaration and its priority and associativity tag: it is never
    /// declared in the semantic module, and no generated axiom mentions it.
    Bracket(BracketName),
    /// Carries `function`: its applications are evaluated by its equations.
    ///
    /// `macro_like` keeps a macro-like attribute, which the declaration still carries as `macro`
    /// and which keeps the label from counting as defined in the definedness judgement.
    Function {
        totality: Totality,
        macro_like: bool,
    },
    /// Carries a macro-like attribute: its applications are replaced by its macro equations.
    MacroProduction,
    /// Carries `token`: it defines the lexical form of its sort's domain values.
    ///
    /// Every term it parses is a domain value, its sort is declared `hasDomainValues`, and its
    /// label is never applied. Its symbol therefore denotes no element of the term algebra, and
    /// classifying it as a constructor would assert a rigid element provably distinct from every
    /// domain value of the sort. `algebraic` keeps an `assoc`/`comm`/`idem` attribute, which
    /// withholds `injective`.
    Token { algebraic: bool },
    /// Unlabelled and none of the above: declares no symbol.
    Unlabelled,
    /// Carries `assoc`, `comm` or `idem`: its algebraic axioms identify applications with
    /// different arguments.
    Algebraic,
    /// Any other labelled production: its applications are values unless an equation heads it.
    Base,
}

/// A production's alternative in its sort's no-junk axiom.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NoJunk {
    /// `\top`: the production parses domain values of its sort, which no symbol generates.
    DomainValues,
    /// The production's symbol applied to fresh variables.
    Generator,
    /// The production's applications are no value of the sort that another alternative does not
    /// already cover, or it declares no symbol.
    Absent,
}

impl ProductionKind {
    /// The kind of `production`.
    ///
    /// # Panics
    ///
    /// When `production` is not a [`Sentence::Production`]; every caller reads a production
    /// catalog.
    pub(crate) fn of(production: &Sentence) -> Self {
        Self::classify(production, true)
    }

    /// [`ProductionKind::of`] with the `bracket` test skipped: the kind whose claims a bracket's
    /// syntax-module declaration carries.
    ///
    /// That declaration is made under the bracket's label, or under its `bracketLabel` when it
    /// has none, so a readable `bracketLabel` counts as a label here: an unlabelled bracket is
    /// classified as the labelled production its declaration states, never as `Unlabelled`.
    pub(crate) fn of_unbracketed(production: &Sentence) -> Self {
        Self::classify(production, false)
    }

    fn classify(production: &Sentence, bracket_test: bool) -> Self {
        let Sentence::Production {
            label,
            items,
            attributes,
            ..
        } = production
        else {
            unreachable!("production kinds classify productions")
        };
        if label.is_none() && matches!(items.as_slice(), [ProductionItem::NonTerminal { .. }]) {
            return Self::Subsort;
        }
        if label
            .as_ref()
            .is_some_and(|label| is_builtin_label(&label.name))
        {
            return Self::Builtin;
        }
        if bracket_test && attributes.has(AttributeKey::Bracket) {
            return Self::Bracket(if label.is_some() {
                BracketName::OwnLabel
            } else if attributes.label(AttributeKey::BracketLabel).is_some() {
                BracketName::BracketLabel
            } else {
                BracketName::Undeclared
            });
        }
        let macro_like = attributes.has_any(&AttributeKey::MACRO_LIKE);
        if attributes.has(AttributeKey::Function) {
            return Self::Function {
                totality: if attributes.has(AttributeKey::Total) {
                    Totality::Total
                } else {
                    Totality::Partial
                },
                macro_like,
            };
        }
        if macro_like {
            return Self::MacroProduction;
        }
        let algebraic = is_algebraic(attributes);
        if attributes.has(AttributeKey::Token) {
            return Self::Token { algebraic };
        }
        if label.is_none()
            && (bracket_test || attributes.label(AttributeKey::BracketLabel).is_none())
        {
            return Self::Unlabelled;
        }
        if algebraic {
            return Self::Algebraic;
        }
        Self::Base
    }

    /// Whether the semantic declaration carries `functional` and the functional axiom: every
    /// application of the symbol denotes exactly one value.
    ///
    /// A symbol that is not declared in the semantic module (a subsort, a builtin, a bracket or
    /// an unlabelled production) has no such claim.
    pub(crate) fn functional(self) -> bool {
        match self {
            Self::Subsort | Self::Builtin | Self::Bracket(_) | Self::Unlabelled => false,
            Self::Function { totality, .. } => totality == Totality::Total,
            Self::MacroProduction | Self::Token { .. } | Self::Algebraic | Self::Base => true,
        }
    }

    /// `MacroProduction`, or `Function` with `macro_like`.
    pub(crate) fn is_macro_like(self) -> bool {
        match self {
            Self::MacroProduction => true,
            Self::Function { macro_like, .. } => macro_like,
            Self::Subsort
            | Self::Builtin
            | Self::Bracket(_)
            | Self::Token { .. }
            | Self::Unlabelled
            | Self::Algebraic
            | Self::Base => false,
        }
    }

    /// The production's alternative in its sort's no-junk axiom.
    ///
    /// A token production parses domain values, so `\top` is its complete alternative whatever
    /// its label. A function or macro production is evaluated or expanded away, a bracket is
    /// erased, a builtin is no symbol of the sort, and a subsort production is covered by the
    /// injection alternatives, so none of them is listed.
    pub(crate) fn no_junk(self) -> NoJunk {
        match self {
            Self::Token { .. } => NoJunk::DomainValues,
            Self::Algebraic | Self::Base => NoJunk::Generator,
            Self::Subsort
            | Self::Builtin
            | Self::Bracket(_)
            | Self::Function { .. }
            | Self::MacroProduction
            | Self::Unlabelled => NoJunk::Absent,
        }
    }
}

fn is_algebraic(attributes: &Attributes) -> bool {
    attributes.has_any(&[AttributeKey::Assoc, AttributeKey::Comm, AttributeKey::Idem])
}

/// Whether `label` is a matching-logic connective, which the prelude declares.
pub(crate) fn is_builtin_label(label: &str) -> bool {
    InternalLabel::of(label).is_some_and(|label| InternalLabel::MATCHING_LOGIC.contains(&label))
}

/// Bind the sort parameters `parameters` occurring in `pattern` so that `pattern` becomes
/// `concrete`, extending `substitution`; `None` when no binding consistent with `substitution`
/// does.
// Invariant: each call matches one node of `pattern` against `concrete` and recurses only into their `parameters`, so the finite `pattern` bounds the calls; `substitution` binds every element of `parameters` met so far to one concrete sort.
pub(crate) fn match_sort_parameters(
    pattern: &Sort,
    concrete: &Sort,
    parameters: &[Sort],
    substitution: &mut BTreeMap<Sort, Sort>,
) -> Option<()> {
    if parameters.contains(pattern) {
        return match substitution.get(pattern) {
            Some(existing) if existing != concrete => None,
            Some(_) => Some(()),
            None => {
                substitution.insert(pattern.clone(), concrete.clone());
                Some(())
            }
        };
    }
    if pattern.name != concrete.name || pattern.parameters.len() != concrete.parameters.len() {
        return None;
    }
    for (pattern, concrete) in pattern.parameters.iter().zip(&concrete.parameters) {
        match_sort_parameters(pattern, concrete, parameters, substitution)?;
    }
    Some(())
}

/// One alternative of a concrete sort's no-junk axiom, in axiom order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NoJunkAlternative<'g> {
    /// `\top`: the domain values of the sort.
    DomainValues,
    /// The symbol of this production, instantiated at the sort, applied to fresh variables.
    Generator(ProductionId),
    /// The injection of a strict subsort into the sort, along the subsort axioms of the emitted
    /// theory.
    Injection(&'g Injectable),
}

/// An alternative a production of the sort contributes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Alternative {
    DomainValues,
    Generator(ProductionId),
}

/// The no-junk alternatives of one concrete sort: every value of the sort is one of them.
///
/// The productions of the sort contribute their [`ProductionKind::no_junk`] alternatives in
/// catalog order, with a single `\top` at the position of the first token production however many
/// token productions the sort has, since each of them contributes the same alternative. The
/// injections of the strict subsorts along subsort axioms follow ([`injected_subsorts`]), and a sort whose own declaration carries `token` but
/// that has no token production ends with `\top`.
#[derive(Debug)]
pub(crate) struct SortGenerators {
    alternatives: Vec<Alternative>,
    injections: Vec<Injectable>,
    token_sort: bool,
}

impl SortGenerators {
    /// The no-junk alternatives of the concrete sort `sort` in a module whose productions,
    /// sorts and subsort order are `productions`, `sorts` and `subsorts`.
    ///
    /// A parametric production generates `sort` when its result sort matches `sort` by
    /// instantiating its sort parameters ([`match_sort_parameters`]).
    pub(crate) fn of(
        productions: &ProductionCatalog<'_>,
        sorts: &SortCatalog<'_>,
        subsorts: &PartialOrder<Sort>,
        sort: &Sort,
    ) -> Self {
        let head = SortHead::from(sort);
        let mut alternatives = Vec::new();
        // Invariant: `alternatives` holds, in catalog order, the generator of every production of `head` before this one whose kind is a generator and whose result sort instantiates to `sort`, plus one domain-values alternative at the position of the first earlier production whose kind contributes domain values; this scan runs once per sort, O(|productions|).
        for (id, production) in productions.productions() {
            let Sentence::Production {
                parameters,
                sort: production_sort,
                ..
            } = production
            else {
                unreachable!("production catalogs contain productions")
            };
            if SortHead::from(production_sort) != head {
                continue;
            }
            match ProductionKind::of(production).no_junk() {
                NoJunk::DomainValues => {
                    if !alternatives.contains(&Alternative::DomainValues) {
                        alternatives.push(Alternative::DomainValues);
                    }
                }
                NoJunk::Generator => {
                    if match_sort_parameters(
                        production_sort,
                        sort,
                        parameters,
                        &mut BTreeMap::new(),
                    )
                    .is_some()
                    {
                        alternatives.push(Alternative::Generator(id));
                    }
                }
                NoJunk::Absent => {}
            }
        }
        let token_sort = !alternatives.contains(&Alternative::DomainValues)
            && sorts
                .attributes_for(&head)
                .is_some_and(|attributes| attributes.has(AttributeKey::Token));
        Self {
            alternatives,
            injections: injected_subsorts(sorts, subsorts, sort),
            token_sort,
        }
    }

    /// Whether the sort has no alternative at all, so that it gets no no-junk axiom.
    pub(crate) fn is_empty(&self) -> bool {
        self.alternatives.is_empty() && self.injections.is_empty() && !self.token_sort
    }

    /// The alternatives in axiom order.
    pub(crate) fn alternatives(&self) -> impl Iterator<Item = NoJunkAlternative<'_>> {
        self.alternatives
            .iter()
            .map(|alternative| match *alternative {
                Alternative::DomainValues => NoJunkAlternative::DomainValues,
                Alternative::Generator(id) => NoJunkAlternative::Generator(id),
            })
            .chain(self.injections.iter().map(NoJunkAlternative::Injection))
            .chain(self.token_sort.then_some(NoJunkAlternative::DomainValues))
    }
}

/// The injections of the strict subsorts of `sort` that are alternatives of its no-junk axiom, in
/// the sort catalog's order: one for every declared strict subsort from which a chain of subsort
/// axioms of the emitted theory leads to `sort` ([`Injectable::between`]).
///
/// An alternative is a disjunct of an axiom stating what every value of `sort` is, so it may only
/// name an embedding the theory defines. A declared subsort without such a chain is left out: the
/// theory has no subsort axiom into `K`, whose values are sequences of `KItem`s, so `K` gets no
/// injection alternative, and a sort above `K` gets none from the sorts below `K` (its values of
/// those sorts are covered by the alternative for `K`). The declared order bounds the candidates:
/// a subsort axiom is emitted only for a declared subsort, while the witness also counts the
/// `S < KItem` subsorts that a definition declares only once `subsort KItem` has run.
///
/// This is the one place that enumerates the injection alternatives.
fn injected_subsorts(
    sorts: &SortCatalog<'_>,
    subsorts: &PartialOrder<Sort>,
    sort: &Sort,
) -> Vec<Injectable> {
    sorts
        .sorted_all_sorts()
        .filter(|subsort| subsorts.less_than(subsort, sort))
        .filter_map(|subsort| Injectable::between(subsort, sort, subsorts))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kast::Label;

    fn production(
        label: Option<&str>,
        sort: &str,
        items: Vec<ProductionItem>,
        keys: &[AttributeKey],
    ) -> Sentence {
        let mut attributes = Attributes::default();
        for key in keys {
            attributes.insert(key.as_str(), serde_json::Value::String(String::new()));
        }
        Sentence::Production {
            label: label.map(Label::new),
            parameters: Vec::new(),
            sort: Sort::new(sort),
            items,
            attributes,
        }
    }

    fn token(label: &str, regex: &str) -> Sentence {
        production(
            Some(label),
            "Id",
            vec![ProductionItem::regex(regex)],
            &[AttributeKey::Token],
        )
    }

    fn generators(
        productions: &[&Sentence],
        sorts: &SortCatalog<'_>,
        sort: &Sort,
    ) -> SortGenerators {
        let catalog = ProductionCatalog::from_visible(productions.iter().copied());
        let subsorts = PartialOrder::new(std::iter::empty()).expect("no subsort cycle");
        SortGenerators::of(&catalog, sorts, &subsorts, sort)
    }

    #[test]
    fn two_labelled_token_productions_contribute_one_domain_values_alternative_in_either_order() {
        let sort = Sort::new("Id");
        let declaration = Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: sort.clone(),
            attributes: Attributes::default(),
        };
        let sorts = SortCatalog::from_visible([&declaration]);
        let lower = token("idLower", "[a-z]+");
        let upper = token("idUpper", "[A-Z]+");
        for order in [[&lower, &upper], [&upper, &lower]] {
            let generated = generators(&order, &sorts, &sort);
            let alternatives = generated.alternatives().collect::<Vec<_>>();
            assert_eq!(
                alternatives,
                [NoJunkAlternative::DomainValues],
                "a labelled token production is never a generator, whatever its position"
            );
        }
    }

    #[test]
    fn domain_values_keep_the_position_of_the_first_token_production() {
        let sort = Sort::new("Id");
        let declaration = Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: sort.clone(),
            attributes: Attributes::default(),
        };
        let sorts = SortCatalog::from_visible([&declaration]);
        let first = production(Some("first"), "Id", Vec::new(), &[]);
        let lexed = token("idLit", "[a-z]+");
        let last = production(Some("last"), "Id", Vec::new(), &[]);
        let relexed = token("idUpper", "[A-Z]+");
        let generated = generators(&[&first, &lexed, &last, &relexed], &sorts, &sort);
        let alternatives = generated.alternatives().collect::<Vec<_>>();
        assert_eq!(
            alternatives,
            [
                NoJunkAlternative::Generator(ProductionId(0)),
                NoJunkAlternative::DomainValues,
                NoJunkAlternative::Generator(ProductionId(2)),
            ]
        );
    }

    #[test]
    fn precedence_keeps_the_later_fact_as_a_field() {
        let function_macro = production(
            Some("f"),
            "Int",
            Vec::new(),
            &[AttributeKey::Function, AttributeKey::Macro],
        );
        assert_eq!(
            ProductionKind::of(&function_macro),
            ProductionKind::Function {
                totality: Totality::Partial,
                macro_like: true,
            }
        );
        let assoc_token = production(
            None,
            "Id",
            vec![ProductionItem::regex("[a-z]+")],
            &[AttributeKey::Token, AttributeKey::Assoc],
        );
        assert_eq!(
            ProductionKind::of(&assoc_token),
            ProductionKind::Token { algebraic: true }
        );
        let bracket = production(
            None,
            "Exp",
            vec![
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("Exp"),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            &[AttributeKey::Bracket],
        );
        assert_eq!(
            ProductionKind::of(&bracket),
            ProductionKind::Bracket(BracketName::Undeclared)
        );
        assert_eq!(
            ProductionKind::of_unbracketed(&bracket),
            ProductionKind::Unlabelled
        );
    }

    /// The syntax declaration of an unlabelled bracket is made under its `bracketLabel`, so the
    /// kind it states is that of a labelled production.
    #[test]
    fn an_unlabelled_bracket_is_classified_under_its_bracket_label_without_the_bracket_test() {
        let bracket = |keys: &[AttributeKey]| {
            let mut bracket = production(
                None,
                "Exp",
                vec![
                    ProductionItem::Terminal("(".into()),
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Exp"),
                        name: None,
                    },
                    ProductionItem::Terminal(")".into()),
                ],
                keys,
            );
            let Sentence::Production { attributes, .. } = &mut bracket else {
                unreachable!()
            };
            attributes.insert(
                AttributeKey::BracketLabel.as_str(),
                serde_json::Value::String("(_)_MAIN_Exp_Exp".into()),
            );
            bracket
        };
        let plain = bracket(&[AttributeKey::Bracket]);
        assert_eq!(
            ProductionKind::of(&plain),
            ProductionKind::Bracket(BracketName::BracketLabel)
        );
        assert_eq!(ProductionKind::of_unbracketed(&plain), ProductionKind::Base);
        assert_eq!(
            ProductionKind::of_unbracketed(&bracket(&[AttributeKey::Bracket, AttributeKey::Assoc])),
            ProductionKind::Algebraic
        );
    }
}
