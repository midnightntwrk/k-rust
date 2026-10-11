//! ```toml algorithm
//! id = "parser.grammar.parametric"
//! name = "concretization of parametric parser productions"
//! sites = ["concretize_parametric_productions", "Grammar::add_parametric_productions"]
//! variable = "S = concrete sorts; P = formal productions; T = traversed sort nodes"
//! counters = []
//! no_counter = "parametric-production concretization has no dedicated counter"
//!
//! [[cost]]
//! mode = "grammar construction"
//! bound = "O(S x P + T)"
//! ```
//!
//! Concretization of parametric productions for Earley parsing.
//!
//! Construction is O(concrete sorts * formal productions), choosing among five formal shapes
//! and closing every candidate over the grammar domain or recognition placeholders.
//! Substitution is linear in the traversed sort tree.

use std::collections::{BTreeMap, BTreeSet};

use crate::definition::production_kind::mentions_parameter;
use crate::definition::regex::Regex as KRegex;
use crate::definition::{
    AttributeKey, Attributes, ProductionCatalog, ProductionItem, Sentence, SortCatalog, SortHead,
};
use crate::kast::{Label, Sort};
use crate::names::BuiltinSort;

use super::grammar::{Placeholder, placeholder_of};
use super::{Grammar, ParametricOrigin, ParseError, ProductionOptions, catalog_production};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParametricInstance {
    sentence: Sentence,
    origin: ParametricOrigin,
}

impl ParametricInstance {
    /// Mint an instance only when every parameter is bound and every parameter-dependent slot
    /// is a sort of the domain or its formal head's recognition placeholder.
    fn close(
        label: &Option<Label>,
        parameters: &[Sort],
        sort: &Sort,
        items: &[ProductionItem],
        attributes: &Attributes,
        mut substitution: BTreeMap<Sort, Sort>,
        domain: &BTreeSet<Sort>,
    ) -> Option<Self> {
        for parameter in parameters {
            substitution
                .entry(parameter.clone())
                .or_insert_with(|| Sort::new("K"));
        }
        for formal in std::iter::once(sort).chain(items.iter().filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort),
            ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
        })) {
            if mentions_parameter(formal, parameters) {
                let written = substitute_sort(formal, &substitution);
                if !domain.contains(&written)
                    && (formal.parameters.is_empty()
                        || written != placeholder_of(&SortHead::from(formal)))
                {
                    return None;
                }
            }
        }
        Some(Self {
            sentence: Sentence::Production {
                label: label.as_ref().map(|label| Label::new(label.name.clone())),
                parameters: Vec::new(),
                sort: substitute_sort(sort, &substitution),
                items: items
                    .iter()
                    .map(|item| substitute_item(item, &substitution))
                    .collect(),
                attributes: attributes.clone(),
            },
            origin: ParametricOrigin {
                label: label.clone(),
                parameters: parameters.to_vec(),
                result: sort.clone(),
                items: items.to_vec(),
                attributes: attributes.clone(),
                substitution,
            },
        })
    }

    pub(crate) fn sentence(&self) -> &Sentence {
        &self.sentence
    }

    pub(crate) fn origin(&self) -> &ParametricOrigin {
        &self.origin
    }

    #[cfg(feature = "cli")]
    pub(crate) fn into_sentence(self) -> Sentence {
        self.sentence
    }
}

/// How a formal production's result and items determine its candidate substitutions.
enum InstanceChoice<'s> {
    /// A result parameter can be any sort of the domain: one candidate `P = C` per sort `C`.
    ResultParameter { parameter: &'s Sort },
    /// A result `H{P}` can be each declared instance `H{a}`: one candidate `P = a` per instance.
    ResultInstance { head: SortHead, parameter: &'s Sort },
    /// A ground-result inclusion enumerates the sorts its item can be. A parameter item uses
    /// the domain except `K`, `KItem` and the result (at or above it); `H{P}` uses declared
    /// instances of `H`; a ground item needs one candidate.
    SubsortItem { item: &'s Sort },
    /// Any other ground result needs one candidate; parameters left unbound become `K`.
    Ground,
    /// A shape outside those admitted by sort checks contributes no candidate.
    Unsupported,
}

impl<'s> InstanceChoice<'s> {
    fn of(
        parameters: &[Sort],
        sort: &'s Sort,
        label: &Option<Label>,
        items: &'s [ProductionItem],
    ) -> Self {
        if parameters.contains(sort) {
            return Self::ResultParameter { parameter: sort };
        }
        if let [argument] = sort.parameters.as_slice()
            && parameters.contains(argument)
        {
            return Self::ResultInstance {
                head: SortHead::from(sort),
                parameter: argument,
            };
        }
        if mentions_parameter(sort, parameters) {
            return Self::Unsupported;
        }
        if is_syntactic_subsort(label, items) {
            let [ProductionItem::NonTerminal { sort: item, .. }] = items else {
                unreachable!("a subsort declaration has one nonterminal")
            };
            if parameters.contains(item)
                || !mentions_parameter(item, parameters)
                || matches!(item.parameters.as_slice(), [argument] if parameters.contains(argument))
            {
                return Self::SubsortItem { item };
            }
            return Self::Unsupported;
        }
        Self::Ground
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParametricFamily<'a> {
    pub(crate) formal_source: &'a Sentence,
    pub(crate) instances: Vec<ParametricInstance>,
}

/// The recognition-only bridge `H{K} ::= H{..}` from a declared instance of the parametric head
/// `head` to its placeholder (`placeholder_of`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParsingOnlySubsort {
    pub(crate) head: SortHead,
    pub(crate) sentence: Sentence,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct ParametricConcretization<'a> {
    pub(crate) families: Vec<ParametricFamily<'a>>,
    pub(crate) parsing_only_subsorts: Vec<ParsingOnlySubsort>,
    /// Every parametric head whose placeholder (`placeholder_of`) some instance's substitution
    /// writes at a result or nonterminal slot: a slot `H{P}` whose parameter `P` has no
    /// parse-time value becomes `H{K}`, whether or not the definition declares an instance of `H`.
    pub(crate) placeholder_heads: BTreeSet<SortHead>,
}

/// Enumerate the concrete parsing productions derived from formal productions.
///
/// The in-process parser and generated parsers share this pure plan so they cannot drift in the
/// five shape choices, the closure gate, or the placeholder subsorts added for parametric heads.
/// Every kept candidate binds all parameters and writes only domain sorts or placeholders at
/// parameter-dependent slots; a candidate writing an unrecognizable sort contributes no parse.
#[deny(clippy::wildcard_enum_match_arm)]
pub(crate) fn concretize_parametric_productions<'a>(
    sentences: &[&'a Sentence],
) -> ParametricConcretization<'a> {
    let catalog = SortCatalog::from_visible(sentences.iter().copied());
    let mut domain = catalog
        .all_sorts()
        .iter()
        .filter(|sort| sort.role().is_k_term_sort())
        .cloned()
        .collect::<BTreeSet<_>>();
    domain.extend([Sort::new("K"), Sort::new("KItem")]);

    let formal_sources = sentences
        .iter()
        .copied()
        .filter(|sentence| {
            matches!(sentence, Sentence::Production { parameters, .. } if !parameters.is_empty())
        })
        .collect::<Vec<_>>();

    let mut families = Vec::new();
    let mut placeholder_heads = BTreeSet::new();
    for sentence in formal_sources {
        let Sentence::Production {
            label,
            parameters,
            sort,
            items,
            attributes,
        } = sentence
        else {
            unreachable!()
        };

        let candidates = match InstanceChoice::of(parameters, sort, label, items) {
            InstanceChoice::ResultParameter { parameter } => domain
                .iter()
                .map(|concrete| BTreeMap::from([(parameter.clone(), concrete.clone())]))
                .collect::<Vec<_>>(),
            InstanceChoice::ResultInstance { head, parameter } => catalog
                .instantiations()
                .get(&head)
                .into_iter()
                .flatten()
                .map(|concrete| {
                    let [value] = concrete.parameters.as_slice() else {
                        unreachable!("a declared instance of an arity-one head has one argument")
                    };
                    BTreeMap::from([(parameter.clone(), value.clone())])
                })
                .collect(),
            InstanceChoice::SubsortItem { item } => {
                if parameters.contains(item) {
                    domain
                        .iter()
                        .filter(|concrete| {
                            concrete.name != BuiltinSort::K.k_name()
                                && concrete.name != BuiltinSort::KItem.k_name()
                                && *concrete != sort
                        })
                        .map(|concrete| BTreeMap::from([(item.clone(), concrete.clone())]))
                        .collect()
                } else if let [parameter] = item.parameters.as_slice()
                    && parameters.contains(parameter)
                {
                    catalog
                        .instantiations()
                        .get(&SortHead::from(item))
                        .into_iter()
                        .flatten()
                        .map(|concrete| {
                            let [value] = concrete.parameters.as_slice() else {
                                unreachable!(
                                    "a declared instance of an arity-one head has one argument"
                                )
                            };
                            BTreeMap::from([(parameter.clone(), value.clone())])
                        })
                        .collect()
                } else {
                    vec![BTreeMap::new()]
                }
            }
            InstanceChoice::Ground => vec![BTreeMap::new()],
            InstanceChoice::Unsupported => {
                debug_assert!(
                    false,
                    "parametric production {sentence:?}: result {sort} is outside the shapes check_sorts admits (a formal parameter nested in an argument, or a head of another arity)"
                );
                Vec::new()
            }
        };

        let instances = candidates
            .into_iter()
            .filter_map(|candidate| {
                ParametricInstance::close(
                    label, parameters, sort, items, attributes, candidate, &domain,
                )
            })
            .collect::<Vec<_>>();
        for instance in &instances {
            placeholder_heads.extend(placeholders_written(
                sort,
                items,
                &instance.origin().substitution,
            ));
        }
        families.push(ParametricFamily {
            formal_source: sentence,
            instances,
        });
    }

    let parsing_only_subsorts = catalog
        .instantiations()
        .iter()
        .flat_map(|(head, instances)| instances.iter().map(move |concrete| (head, concrete)))
        .map(|(head, concrete)| ParsingOnlySubsort {
            head: head.clone(),
            sentence: Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: placeholder_of(head),
                items: vec![ProductionItem::NonTerminal {
                    sort: concrete.clone(),
                    name: None,
                }],
                attributes: Attributes::default(),
            },
        })
        .collect();
    ParametricConcretization {
        families,
        parsing_only_subsorts,
        placeholder_heads,
    }
}

/// The heads of the formal production's result and nonterminal item sorts that `substitution`
/// turns into the head's placeholder: the slots an instance recognizes at `H{K}`.
fn placeholders_written<'s>(
    sort: &'s Sort,
    items: &'s [ProductionItem],
    substitution: &'s BTreeMap<Sort, Sort>,
) -> impl Iterator<Item = SortHead> + 's {
    std::iter::once(sort)
        .chain(items.iter().filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort),
            ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
        }))
        .filter(|formal| !formal.parameters.is_empty())
        .filter_map(move |formal| {
            let head = SortHead::from(formal);
            let substituted = substitute_sort(formal, substitution);
            (substituted != *formal && substituted == placeholder_of(&head)).then_some(head)
        })
}

impl ParsingOnlySubsort {
    /// The declared instance this bridge lets a placeholder slot recognize.
    fn instance(&self) -> &Sort {
        let Sentence::Production { items, .. } = &self.sentence else {
            unreachable!("a bridge is a production")
        };
        let [ProductionItem::NonTerminal { sort, .. }] = items.as_slice() else {
            unreachable!("a bridge has one nonterminal")
        };
        sort
    }
}

impl Grammar {
    /// Register the placeholder of every head whose placeholder the plan writes into a slot, and
    /// of every bridged head, as a declared instance when the plan's declared instances include
    /// its spelling and as scaffolding otherwise. A slot written at `H{K}` is recognized at the
    /// placeholder whether or not any instance of `H` is declared, so the registration does not
    /// depend on the bridges. Heads that share a name share the placeholder spelling
    /// (`placeholder_of`) and so the role.
    pub(super) fn register_placeholders(&mut self, concretization: &ParametricConcretization<'_>) {
        let instances = concretization
            .parsing_only_subsorts
            .iter()
            .map(ParsingOnlySubsort::instance)
            .collect::<BTreeSet<_>>();
        let heads = concretization
            .parsing_only_subsorts
            .iter()
            .map(|bridge| &bridge.head)
            .chain(&concretization.placeholder_heads)
            .collect::<BTreeSet<_>>();
        for head in heads {
            let role = if instances.contains(&placeholder_of(head)) {
                Placeholder::DeclaredInstance
            } else {
                Placeholder::Scaffolding
            };
            self.placeholder_sort(head, role);
        }
    }

    pub(super) fn add_parametric_productions(
        &mut self,
        concretization: ParametricConcretization<'_>,
        lexical: &BTreeMap<String, KRegex>,
        source_catalog: &ProductionCatalog<'_>,
    ) -> Result<(), ParseError> {
        for family in concretization.families {
            let sentence = family.formal_source;
            // The forest identifies all instances of this source as one term production. The
            // first instance is its canonical descriptor; its origin supplies the formal
            // signature for inference, so its concrete parse-time result does not type the term.
            let term_production = self.productions.len();
            let source_production = catalog_production(source_catalog, sentence);
            for instance in family.instances {
                self.add_instantiation(instance, lexical, source_production, term_production)?;
            }
        }

        // Let a concrete instance such as `MInt{6}` be recognized at the placeholder `MInt{K}` of
        // a slot whose parameter has no parse-time value. The bridge states no inclusion, so it
        // is added as a recognition bridge and contributes no subsort pair.
        for bridge in &concretization.parsing_only_subsorts {
            let Sentence::Production { sort, .. } = &bridge.sentence else {
                unreachable!("a bridge is a production")
            };
            self.add_recognition_bridge(sort.clone(), bridge.instance().clone())?;
        }
        Ok(())
    }

    fn add_instantiation(
        &mut self,
        instance: ParametricInstance,
        lexical: &BTreeMap<String, KRegex>,
        source_production: Option<crate::kast::ProductionIdentity>,
        term_production: usize,
    ) -> Result<(), ParseError> {
        let Sentence::Production {
            label,
            sort,
            items,
            attributes,
            ..
        } = instance.sentence()
        else {
            unreachable!()
        };
        let index = self.productions.len();
        let source_production_text = source_production
            .and_then(|production| self.source_production_texts.get(&production))
            .cloned();
        self.add_production_with_lexical(
            sort.clone(),
            items,
            label.clone(),
            ProductionOptions {
                source_production,
                source_production_text: source_production_text.as_ref(),
                source: attributes.source(),
                location: attributes.location(),
                ..production_options(attributes)
            },
            lexical,
        )?;
        self.productions[index].parametric_origin = Some(instance.origin().clone());
        self.productions[index].term_production = Some(term_production);
        Ok(())
    }
}

fn substitute_item(item: &ProductionItem, substitution: &BTreeMap<Sort, Sort>) -> ProductionItem {
    match item {
        ProductionItem::NonTerminal { sort, name } => ProductionItem::NonTerminal {
            sort: substitute_sort(sort, substitution),
            name: name.clone(),
        },
        ProductionItem::RegexTerminal { regex } => ProductionItem::RegexTerminal {
            regex: regex.clone(),
        },
        ProductionItem::Terminal(value) => ProductionItem::Terminal(value.clone()),
    }
}

pub(super) fn substitute_sort(sort: &Sort, substitution: &BTreeMap<Sort, Sort>) -> Sort {
    substitution.get(sort).cloned().unwrap_or_else(|| Sort {
        name: sort.name.clone(),
        parameters: sort
            .parameters
            .iter()
            .map(|parameter| substitute_sort(parameter, substitution))
            .collect(),
    })
}

fn production_options(attributes: &Attributes) -> ProductionOptions<'_> {
    ProductionOptions {
        token: attributes.has(AttributeKey::Token),
        transparent: attributes.has(AttributeKey::Bracket),
        bracket: attributes.has(AttributeKey::Bracket),
        bracket_label: attributes
            .label(AttributeKey::BracketLabel)
            .map(|label| label.name),
        apply_priority: attributes.string(AttributeKey::ApplyPriority),
        function: attributes.has(AttributeKey::Function),
        macro_like: attributes.has_any(&AttributeKey::MACRO_LIKE),
        prefer: attributes.has(AttributeKey::Prefer),
        avoid: attributes.has(AttributeKey::Avoid),
        source_production: None,
        source_production_text: None,
        source: attributes.source(),
        location: attributes.location(),
        user_list: attributes.has(AttributeKey::UserList),
        user_list_nonempty: attributes.string(AttributeKey::UserList) == Some("+"),
        precedence: attributes.string(AttributeKey::Prec),
        hook: attributes.string(AttributeKey::Hook),
    }
}

fn is_syntactic_subsort(label: &Option<Label>, items: &[ProductionItem]) -> bool {
    label.is_none() && matches!(items, [ProductionItem::NonTerminal { .. }])
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    macro_rules! assert_parametric_parse_snapshot {
        ($grammar:expr, $sort:expr, $code:expr) => {{
            let source = indoc::indoc! { $code };
            let expected_sort = $sort;
            let parsed = $grammar.parse(&expected_sort, source);

            insta::with_settings!({
                description => format!("K term parsed as {expected_sort}:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(parsed);
            });
        }};
    }

    fn parametric_sentences() -> Vec<Sentence> {
        let p = Sort::new("P");
        let r = Sort::new("R");
        let s = Sort::new("S");
        let w = Sort::new("W");
        let x = Sort::new("X");
        let mint_w = Sort::with_parameters("MInt", vec![w.clone()]);
        let mint_x = Sort::with_parameters("MInt", vec![x.clone()]);
        let mint_8 = Sort::with_parameters("MInt", vec![Sort::new("8")]);
        let sentences = vec![
            syntax_sort(Vec::new(), Sort::new("Int")),
            syntax_sort(vec![w.clone()], mint_w.clone()),
            syntax_sort(Vec::new(), mint_8.clone()),
            terminal(Sort::new("Int"), "i"),
            terminal(Sort::new("K"), "k"),
            terminal(Sort::with_parameters("MInt", vec![Sort::new("8")]), "m"),
            production(
                vec![p.clone(), r.clone()],
                p.clone(),
                "case1",
                vec![nonterminal(p), nonterminal(r)],
            ),
            production(
                vec![w.clone(), x],
                mint_w.clone(),
                "case2",
                vec![nonterminal(mint_w), nonterminal(mint_x)],
            ),
            Sentence::Production {
                label: None,
                parameters: vec![s.clone()],
                sort: Sort::new("KItem"),
                items: vec![nonterminal(s.clone())],
                attributes: Attributes::default(),
            },
            production(
                vec![s.clone()],
                Sort::new("Int"),
                "case4",
                vec![nonterminal(s)],
            ),
            Sentence::Production {
                label: Some(Label::new("#SemanticCastToMInt{8}")),
                parameters: Vec::new(),
                sort: mint_8.clone(),
                items: vec![
                    nonterminal(mint_8),
                    ProductionItem::Terminal(":MInt{8}".into()),
                ],
                attributes: Attributes::default(),
            },
        ];
        sentences
    }

    fn parametric_grammar() -> Grammar {
        let sentences = parametric_sentences();
        Grammar::from_sentences(&sentences).unwrap()
    }

    #[test]
    fn shared_concretization_families_follow_sentence_order() {
        let sentences = parametric_sentences();
        let references = sentences.iter().collect::<Vec<_>>();
        let expected = concretize_parametric_productions(&references);
        let mut reversed = sentences.clone();
        reversed.reverse();
        let references = reversed.iter().collect::<Vec<_>>();
        let actual = concretize_parametric_productions(&references);

        let mut expected_families = expected.families;
        expected_families.reverse();
        assert_eq!(actual.families, expected_families);
        assert_eq!(actual.parsing_only_subsorts, expected.parsing_only_subsorts);
        assert!(actual.parsing_only_subsorts.iter().all(|bridge| {
            matches!(&bridge.sentence, Sentence::Production { label: None, parameters, attributes, .. }
                if parameters.is_empty() && attributes.wire_entries().next().is_none())
        }));
    }

    #[test]
    fn concretizes_all_parametric_production_shapes() {
        let grammar = parametric_grammar();
        let summary = grammar
            .productions
            .iter()
            .filter_map(|production| {
                let origin = production.parametric_origin.as_ref()?;
                let items = production
                    .items
                    .iter()
                    .map(|item| item.description())
                    .collect::<Vec<_>>()
                    .join(" ");
                let substitution = origin
                    .substitution
                    .iter()
                    .map(|(parameter, concrete)| format!("{parameter}={concrete}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                Some(format!(
                    "{} ::= {items} [{}] from {} parameter(s)",
                    production.result,
                    substitution,
                    origin.parameters.len()
                ))
            })
            .collect::<Vec<_>>();

        assert_eq!(
            summary.iter().map(String::as_str).collect::<Vec<_>>(),
            vec![
                "Int ::= \"case1(\" Int \",\" K \")\" [P=Int, R=K] from 2 parameter(s)",
                "K ::= \"case1(\" K \",\" K \")\" [P=K, R=K] from 2 parameter(s)",
                "KItem ::= \"case1(\" KItem \",\" K \")\" [P=KItem, R=K] from 2 parameter(s)",
                "MInt{8} ::= \"case1(\" MInt{8} \",\" K \")\" [P=MInt{8}, R=K] from 2 parameter(s)",
                "MInt{8} ::= \"case2(\" MInt{8} \",\" MInt{K} \")\" [W=8, X=K] from 2 parameter(s)",
                "KItem ::= Int [S=Int] from 1 parameter(s)",
                "KItem ::= MInt{8} [S=MInt{8}] from 1 parameter(s)",
                "Int ::= \"case4(\" K \")\" [S=K] from 1 parameter(s)",
            ]
        );
        assert!(grammar.productions.iter().any(|production| {
            production.result == Sort::with_parameters("MInt", vec![Sort::new("K")])
                && matches!(
                    production.items.as_slice(),
                    [super::super::Item::NonTerminal(sort)]
                        if sort == &Sort::with_parameters("MInt", vec![Sort::new("8")])
                )
        }));

        assert!(
            grammar.parse(&Sort::new("KItem"), "i").is_ok(),
            "the generated parametric subsort should remain portable"
        );
    }

    #[test]
    fn placeholders_are_registered_and_stay_out_of_both_subsort_relations() {
        let grammar = parametric_grammar();
        let placeholder = Sort::with_parameters("MInt", vec![Sort::new("K")]);
        assert_eq!(
            grammar.placeholders,
            BTreeMap::from([(placeholder.clone(), Placeholder::Scaffolding)])
        );
        for (lesser, greater) in grammar
            .subsort_relations
            .iter()
            .chain(grammar.syntactic_subsort_relations.iter())
        {
            assert!(
                lesser != &placeholder && greater != &placeholder,
                "({lesser}, {greater}) mentions the placeholder"
            );
        }
        // The instance's other unary production is an ordinary subsort.
        let mint_8 = Sort::with_parameters("MInt", vec![Sort::new("8")]);
        assert!(
            grammar
                .subsort_relations
                .contains(&(mint_8, Sort::new("KItem")))
        );
    }

    #[test]
    fn a_declared_placeholder_spelling_keeps_its_own_subsorts_and_only_the_bridges_are_dropped() {
        // `syntax MInt{K}` declares the placeholder spelling as an instance. Its own unary
        // productions (the user's `Thing ::= MInt{K}`, added before the parametric pass, and the
        // generated `KItem ::= MInt{K}`) state inclusions; the bridges into it from `MInt{8}` and
        // from itself do not.
        let mint_k = Sort::with_parameters("MInt", vec![Sort::new("K")]);
        let mint_8 = Sort::with_parameters("MInt", vec![Sort::new("8")]);
        let thing = Sort::new("Thing");
        let mut sentences = parametric_sentences();
        sentences.extend([
            syntax_sort(Vec::new(), mint_k.clone()),
            syntax_sort(Vec::new(), thing.clone()),
            Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: thing.clone(),
                items: vec![nonterminal(mint_k.clone())],
                attributes: Attributes::default(),
            },
        ]);
        let grammar = Grammar::from_sentences(&sentences).unwrap();

        assert_eq!(
            grammar.placeholders,
            BTreeMap::from([(mint_k.clone(), Placeholder::DeclaredInstance)])
        );
        for pair in [
            (mint_k.clone(), thing),
            (mint_k.clone(), Sort::new("KItem")),
            (mint_8.clone(), Sort::new("KItem")),
        ] {
            assert!(grammar.subsort_relations.contains(&pair), "{pair:?}");
            assert!(
                grammar.syntactic_subsort_relations.contains(&pair),
                "{pair:?}"
            );
        }
        for bridge in [
            (mint_8.clone(), mint_k.clone()),
            (mint_k.clone(), mint_k.clone()),
        ] {
            assert!(!grammar.subsort_relations.contains(&bridge), "{bridge:?}");
            assert!(
                !grammar.syntactic_subsort_relations.contains(&bridge),
                "{bridge:?}"
            );
        }
        // The bridge is still there for the recognizer.
        assert!(grammar.productions.iter().any(|production| {
            production.result == mint_k
                && matches!(
                    production.items.as_slice(),
                    [super::super::Item::NonTerminal(sort)] if sort == &mint_8
                )
        }));
    }

    #[test]
    fn a_placeholder_written_into_a_slot_is_registered_without_a_declared_instance() {
        // `syntax {W} Int ::= width(MInt{W})` with no declared instance of `MInt`: case 4 writes
        // the slot at `MInt{K}`, which the plan bridges from nothing. The slot is still recognized
        // at the placeholder, so the placeholder is registered as scaffolding.
        let w = Sort::new("W");
        let mint_w = Sort::with_parameters("MInt", vec![w.clone()]);
        let mint_k = Sort::with_parameters("MInt", vec![Sort::new("K")]);
        let sentences = vec![
            syntax_sort(Vec::new(), Sort::new("Int")),
            syntax_sort(vec![w.clone()], mint_w.clone()),
            production(
                vec![w],
                Sort::new("Int"),
                "width",
                vec![nonterminal(mint_w)],
            ),
        ];
        let references = sentences.iter().collect::<Vec<_>>();
        let concretization = concretize_parametric_productions(&references);
        assert!(concretization.parsing_only_subsorts.is_empty());
        assert_eq!(
            concretization.placeholder_heads,
            BTreeSet::from([SortHead::from(&mint_k)])
        );

        let grammar = Grammar::from_sentences(&sentences).unwrap();

        assert_eq!(
            grammar.placeholders,
            BTreeMap::from([(mint_k, Placeholder::Scaffolding)])
        );
    }

    #[test]
    fn concrete_instances_of_one_family_are_one_production_of_the_parsed_term() {
        // The parse forest names a production by `term_production` (`forest.rs`), so every
        // concrete instance of one formal production must carry the same index, one of the
        // family's own, and instances of different families must not share it. Sort inference
        // relies on this to treat the instances as one reading.
        let grammar = parametric_grammar();
        let mut families: BTreeMap<String, (BTreeSet<usize>, BTreeSet<usize>)> = BTreeMap::new();
        for (index, production) in grammar.productions.iter().enumerate() {
            let Some(origin) = &production.parametric_origin else {
                continue;
            };
            let formal = ParametricOrigin {
                substitution: BTreeMap::new(),
                ..origin.clone()
            };
            let (members, terms) = families.entry(format!("{formal:?}")).or_default();
            members.insert(index);
            terms.insert(
                production
                    .term_production
                    .expect("a concrete instance names its family's production"),
            );
        }
        assert_eq!(families.len(), 4);
        assert!(families.values().any(|(members, _)| members.len() > 1));
        let mut seen = BTreeSet::new();
        for (members, terms) in families.values() {
            let [term] = <[usize; 1]>::try_from(terms.iter().copied().collect::<Vec<_>>())
                .expect("one production index per family");
            assert!(members.contains(&term));
            assert!(seen.insert(term), "two families share a production index");
        }
    }

    #[test]
    fn infers_parameters_when_result_is_a_formal_parameter() {
        let grammar = parametric_grammar();
        assert_parametric_parse_snapshot!(
            grammar,
            Sort::new("Int"),
            r#"
            case1(i,k)
        "#
        );
    }

    #[test]
    fn infers_parameters_in_a_parameterized_result_sort() {
        let grammar = parametric_grammar();
        let expected = Sort::with_parameters("MInt", vec![Sort::new("8")]);
        #[cfg(feature = "z3-inference")]
        assert_parametric_parse_snapshot!(
            grammar,
            expected.clone(),
            r#"
            case2(m,m)
        "#
        );
        #[cfg(not(feature = "z3-inference"))]
        assert_z3_required(grammar.parse(&expected, "case2(m,m)"));
    }

    #[test]
    fn infers_parameters_used_only_by_arguments() {
        let grammar = parametric_grammar();
        assert_parametric_parse_snapshot!(
            grammar,
            Sort::new("Int"),
            r#"
            case4(k)
        "#
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "outside the shapes check_sorts admits")]
    fn a_result_with_a_nested_formal_parameter_is_not_concretized() {
        // `MInt{MInt{W}}` names one sort per `W`, but no declared instance of `MInt` supplies a
        // value for a `W` one level down.
        let w = Sort::new("W");
        let mint = |argument: Sort| Sort::with_parameters("MInt", vec![argument]);
        let sentences = [
            syntax_sort(vec![w.clone()], mint(w.clone())),
            syntax_sort(Vec::new(), mint(Sort::new("8"))),
            production(vec![w.clone()], mint(mint(w)), "mkn", Vec::new()),
        ];
        concretize_parametric_productions(&sentences.iter().collect::<Vec<_>>());
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "outside the shapes check_sorts admits")]
    fn a_result_of_another_arity_is_not_concretized() {
        // `MInt{A, B}` has two formal parameters, so no one argument of a declared instance
        // fixes the result.
        let a = Sort::new("A");
        let b = Sort::new("B");
        let mint_ab = Sort::with_parameters("MInt", vec![a.clone(), b.clone()]);
        let sentences = [
            syntax_sort(vec![a.clone(), b.clone()], mint_ab.clone()),
            syntax_sort(
                Vec::new(),
                Sort::with_parameters("MInt", vec![Sort::new("8"), Sort::new("16")]),
            ),
            production(
                vec![a, b],
                mint_ab,
                "mk",
                vec![nonterminal(Sort::new("Int"))],
            ),
        ];
        concretize_parametric_productions(&sentences.iter().collect::<Vec<_>>());
    }

    #[test]
    fn a_ground_parametric_result_is_concretized_once() {
        // `MInt{8}` is one sort whatever `W` is, so `foo` has one instance, with `W` (which
        // occurs only in an argument) at `K`, however many instances `MInt` has.
        let w = Sort::new("W");
        let k = Sort::new("K");
        let mint = |argument: Sort| Sort::with_parameters("MInt", vec![argument]);
        let sentences = [
            syntax_sort(vec![w.clone()], mint(w.clone())),
            syntax_sort(Vec::new(), mint(Sort::new("8"))),
            syntax_sort(Vec::new(), mint(Sort::new("16"))),
            production(
                vec![w.clone()],
                mint(Sort::new("8")),
                "foo",
                vec![nonterminal(mint(w.clone()))],
            ),
        ];
        let plan = concretize_parametric_productions(&sentences.iter().collect::<Vec<_>>());

        let [family] = plan.families.as_slice() else {
            panic!(
                "one formal production gives one family: {:?}",
                plan.families
            )
        };
        let [instance] = family.instances.as_slice() else {
            panic!("`foo` has {} instances", family.instances.len())
        };
        assert_eq!(
            instance.origin.substitution,
            BTreeMap::from([(w, k.clone())])
        );
        let Sentence::Production { sort, items, .. } = &instance.sentence else {
            unreachable!("an instance is a production")
        };
        assert_eq!(sort, &mint(Sort::new("8")));
        let slots = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(slots, vec![mint(k)]);
    }

    #[test]
    fn a_result_parameter_is_instantiated_only_where_its_slots_are_sorts_of_the_grammar() {
        let t = Sort::new("T");
        let w = Sort::new("W");
        let a = Sort::new("A");
        let k = Sort::new("K");
        let mint = |argument: Sort| Sort::with_parameters("MInt", vec![argument]);
        let sentences = [
            syntax_sort(Vec::new(), Sort::new("Int")),
            syntax_sort(Vec::new(), a.clone()),
            syntax_sort(vec![w.clone()], mint(w)),
            syntax_sort(Vec::new(), mint(a.clone())),
            syntax_sort(Vec::new(), mint(Sort::new("8"))),
            production(
                vec![t.clone()],
                t.clone(),
                "inner",
                vec![ProductionItem::NonTerminal {
                    sort: mint(t),
                    name: Some("x".into()),
                }],
            ),
        ];
        let plan = concretize_parametric_productions(&sentences.iter().collect::<Vec<_>>());
        let [family] = plan.families.as_slice() else {
            panic!("one formal production gives one family")
        };
        let instances = family
            .instances
            .iter()
            .map(|instance| {
                let Sentence::Production { sort, items, .. } = &instance.sentence else {
                    unreachable!("an instance is a production")
                };
                (sort.clone(), items.clone())
            })
            .collect::<Vec<_>>();
        let named = |sort| ProductionItem::NonTerminal {
            sort,
            name: Some("x".into()),
        };
        let expected = [a, k].map(|sort| {
            let Sentence::Production { items, .. } = production(
                Vec::new(),
                sort.clone(),
                "inner",
                vec![named(mint(sort.clone()))],
            ) else {
                unreachable!("the helper builds a production")
            };
            (sort, items)
        });
        assert_eq!(instances, expected);
        assert_eq!(
            plan.placeholder_heads,
            BTreeSet::from([SortHead::from(&mint(Sort::new("K")))])
        );
    }

    #[test]
    fn a_bare_slot_is_not_instantiated_at_a_numeral_argument() {
        let w = Sort::new("W");
        let s = Sort::new("S");
        let a = Sort::new("A");
        let mint = |argument: Sort| Sort::with_parameters("MInt", vec![argument]);
        let sentences = [
            syntax_sort(vec![w.clone()], mint(w)),
            syntax_sort(Vec::new(), a.clone()),
            syntax_sort(Vec::new(), mint(a.clone())),
            syntax_sort(Vec::new(), mint(Sort::new("8"))),
            production(
                vec![s.clone()],
                mint(s.clone()),
                "wrap",
                vec![nonterminal(s)],
            ),
        ];
        let plan = concretize_parametric_productions(&sentences.iter().collect::<Vec<_>>());
        let [family] = plan.families.as_slice() else {
            panic!("one formal production gives one family")
        };
        assert_eq!(
            family
                .instances
                .iter()
                .map(|instance| instance.sentence.clone())
                .collect::<Vec<_>>(),
            vec![production(
                Vec::new(),
                mint(a.clone()),
                "wrap",
                vec![nonterminal(a)]
            )]
        );
    }

    #[test]
    fn a_subsort_declaration_is_instantiated_at_the_sorts_its_item_can_be() {
        let s = Sort::new("S");
        let w = Sort::new("W");
        let a = Sort::new("A");
        let k = Sort::new("K");
        let foo = Sort::new("Foo");
        let eight = Sort::new("8");
        let mint = |argument: Sort| Sort::with_parameters("MInt", vec![argument]);
        let subsort = |parameters, item| Sentence::Production {
            label: None,
            parameters,
            sort: foo.clone(),
            items: vec![nonterminal(item)],
            attributes: Attributes::default(),
        };
        let sentences = [
            syntax_sort(vec![w.clone()], mint(w.clone())),
            syntax_sort(Vec::new(), mint(eight.clone())),
            syntax_sort(Vec::new(), foo.clone()),
            subsort(vec![s.clone(), w.clone()], mint(w.clone())),
            subsort(vec![a.clone(), s.clone()], s.clone()),
        ];
        let plan = concretize_parametric_productions(&sentences.iter().collect::<Vec<_>>());
        let [instance_family, parameter_family] = plan.families.as_slice() else {
            panic!("two formal productions give two families")
        };
        assert_eq!(
            instance_family
                .instances
                .iter()
                .map(|instance| (&instance.sentence, &instance.origin.substitution))
                .collect::<Vec<_>>(),
            vec![(
                &subsort(Vec::new(), mint(eight.clone())),
                &BTreeMap::from([(s.clone(), k.clone()), (w, eight.clone())])
            )]
        );
        // The domain is {Foo, K, KItem, MInt{8}}; only MInt{8} can be included below Foo.
        assert_eq!(
            parameter_family
                .instances
                .iter()
                .map(|instance| (&instance.sentence, &instance.origin.substitution))
                .collect::<Vec<_>>(),
            vec![(
                &subsort(Vec::new(), mint(eight.clone())),
                &BTreeMap::from([(a, k), (s, mint(eight))])
            )]
        );
    }

    #[cfg(not(feature = "z3-inference"))]
    fn assert_z3_required(result: Result<crate::kast::Term, ParseError>) {
        assert!(matches!(
            result,
            Err(ParseError::Z3InferenceRequired {
                parametric_sorts: true,
                ..
            })
        ));
    }

    fn syntax_sort(parameters: Vec<Sort>, sort: Sort) -> Sentence {
        Sentence::SyntaxSort {
            parameters,
            sort,
            attributes: Attributes::default(),
        }
    }

    fn production(
        parameters: Vec<Sort>,
        sort: Sort,
        label: &str,
        arguments: Vec<ProductionItem>,
    ) -> Sentence {
        let mut items = vec![ProductionItem::Terminal(format!("{label}("))];
        for (index, argument) in arguments.into_iter().enumerate() {
            if index != 0 {
                items.push(ProductionItem::Terminal(",".into()));
            }
            items.push(argument);
        }
        items.push(ProductionItem::Terminal(")".into()));
        Sentence::Production {
            label: Some(Label::new(label)),
            parameters,
            sort,
            items,
            attributes: Attributes::default(),
        }
    }

    fn terminal(sort: Sort, value: &str) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(value)),
            parameters: Vec::new(),
            sort,
            items: vec![ProductionItem::Terminal(value.into())],
            attributes: Attributes::default(),
        }
    }

    fn nonterminal(sort: Sort) -> ProductionItem {
        ProductionItem::NonTerminal { sort, name: None }
    }
}
