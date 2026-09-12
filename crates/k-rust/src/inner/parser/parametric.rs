//! Scala-compatible concretization of parametric productions for Earley parsing.

use std::collections::BTreeMap;

use crate::definition::regex::Regex as KRegex;
use crate::definition::{
    Attributes, ProductionCatalog, ProductionItem, Sentence, SortCatalog, SortHead,
    compare_sentences,
};
use crate::kast::{Label, Sort};

use super::{Grammar, ParametricOrigin, ParseError, ProductionOptions, catalog_production};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParametricInstance {
    pub(crate) sentence: Sentence,
    pub(crate) origin: ParametricOrigin,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParametricFamily<'a> {
    pub(crate) formal_source: &'a Sentence,
    pub(crate) instances: Vec<ParametricInstance>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParsingOnlySubsort {
    pub(crate) sentence: Sentence,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct ParametricConcretization<'a> {
    pub(crate) families: Vec<ParametricFamily<'a>>,
    pub(crate) parsing_only_subsorts: Vec<ParsingOnlySubsort>,
}

/// Enumerate the concrete parsing productions derived from formal productions.
///
/// The in-process parser and generated parsers share this pure plan so they cannot drift in the
/// four K concretization cases or in the placeholder subsorts added for parametric sort heads.
pub(crate) fn concretize_parametric_productions<'a>(
    sentences: &[&'a Sentence],
) -> ParametricConcretization<'a> {
    let catalog = SortCatalog::from_visible(sentences.iter().copied());
    let mut all_sorts = catalog
        .all_sorts()
        .iter()
        .filter(|sort| !is_parser_sort(sort) || matches!(sort.name.as_str(), "K" | "KItem"))
        .cloned()
        .collect::<Vec<_>>();
    for builtin in [Sort::new("K"), Sort::new("KItem")] {
        if !all_sorts.contains(&builtin) {
            all_sorts.push(builtin);
        }
    }
    all_sorts.sort();

    let mut formal_sources = sentences
        .iter()
        .copied()
        .filter(|sentence| {
            matches!(sentence, Sentence::Production { parameters, .. } if !parameters.is_empty())
        })
        .collect::<Vec<_>>();
    formal_sources.sort_by(|left, right| {
        compare_sentences(left, right).expect("production sentences have a structural order")
    });

    let mut families = Vec::new();
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

        let substitutions = if parameters.contains(sort) {
            // Case 1: `syntax {P, R} P ::= P "+" R`.
            all_sorts
                .iter()
                .map(|concrete| {
                    parameters
                        .iter()
                        .cloned()
                        .map(|parameter| {
                            let replacement = if &parameter == sort {
                                concrete.clone()
                            } else {
                                Sort::new("K")
                            };
                            (parameter, replacement)
                        })
                        .collect()
                })
                .collect::<Vec<_>>()
        } else if !sort.parameters.is_empty() {
            // Case 2: `syntax {W, X} MInt{W} ::= MInt{W} "+" MInt{X}`.
            let head = SortHead::from(sort);
            catalog
                .instantiations()
                .get(&head)
                .into_iter()
                .flatten()
                .map(|concrete| {
                    let result_parameter = &sort.parameters[0];
                    parameters
                        .iter()
                        .cloned()
                        .map(|parameter| {
                            let replacement = if &parameter == result_parameter {
                                concrete.parameters[0].clone()
                            } else {
                                Sort::new("K")
                            };
                            (parameter, replacement)
                        })
                        .collect()
                })
                .collect()
        } else if is_syntactic_subsort(label, items) {
            // Case 3: `syntax {S} KItem ::= S`.
            all_sorts
                .iter()
                .filter(|concrete| {
                    parameters.contains(sort) || !matches!(concrete.name.as_str(), "K" | "KItem")
                })
                .map(|concrete| BTreeMap::from([(parameters[0].clone(), concrete.clone())]))
                .collect()
        } else {
            // Case 4: parameters which occur only in arguments become `K`.
            vec![
                parameters
                    .iter()
                    .cloned()
                    .map(|parameter| (parameter, Sort::new("K")))
                    .collect(),
            ]
        };

        let instances = substitutions
            .into_iter()
            .map(|substitution| ParametricInstance {
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
                    parameters: parameters.clone(),
                    result: sort.clone(),
                    items: items.clone(),
                    attributes: attributes.clone(),
                    substitution,
                },
            })
            .collect();
        families.push(ParametricFamily {
            formal_source: sentence,
            instances,
        });
    }

    let parsing_only_subsorts = catalog
        .instantiations()
        .values()
        .flatten()
        .map(|concrete| ParsingOnlySubsort {
            sentence: Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: Sort::with_parameters(concrete.name.clone(), vec![Sort::new("K")]),
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
    }
}

impl Grammar {
    pub(super) fn add_parametric_productions(
        &mut self,
        sentences: &[&Sentence],
        lexical: &BTreeMap<String, KRegex>,
        source_catalog: &ProductionCatalog<'_>,
    ) -> Result<(), ParseError> {
        let concretization = concretize_parametric_productions(sentences);
        for family in concretization.families {
            let sentence = family.formal_source;
            // All temporary concrete variants of this source production become the same original
            // production reference in Java's Earley forest. The first variant is our canonical
            // descriptor; its `ParametricOrigin` carries the actual source signature used by
            // inference, so its concrete parse-time result is not semantically observable.
            let term_production = self.productions.len();
            let source_production = catalog_production(source_catalog, sentence);
            for instance in family.instances {
                self.add_instantiation(instance, lexical, source_production, term_production)?;
            }
        }

        // Connect concrete instances such as `MInt{6}` to the placeholder
        // `MInt{K}` used by parameters which lack parse-time sort information. The bridge is a
        // parsing-module production only (RuleGrammarGenerator.java:627-637): the inferencers
        // must not see `MInt{6} <= MInt{K}`, or a production parameter constrained by that slot
        // could be inferred as `K` instead of the declared width its token or cast anchors.
        for bridge in concretization.parsing_only_subsorts {
            let Sentence::Production { sort, items, .. } = bridge.sentence else {
                unreachable!()
            };
            self.add_production_with_lexical(
                sort,
                &items,
                None,
                ProductionOptions {
                    parsing_only_subsort: true,
                    ..ProductionOptions::default()
                },
                &BTreeMap::new(),
            )?;
        }
        Ok(())
    }

    fn add_instantiation(
        &mut self,
        instance: ParametricInstance,
        lexical: &BTreeMap<String, KRegex>,
        source_production: Option<crate::definition::ProductionId>,
        term_production: usize,
    ) -> Result<(), ParseError> {
        let Sentence::Production {
            label,
            sort,
            items,
            attributes,
            ..
        } = instance.sentence
        else {
            unreachable!()
        };
        let index = self.productions.len();
        let source_production_text = source_production
            .and_then(|production| self.source_production_texts.get(&production))
            .cloned();
        self.add_production_with_lexical(
            sort,
            &items,
            label,
            ProductionOptions {
                source_production,
                source_production_text: source_production_text.as_deref(),
                source: attributes.source(),
                location: attributes.location(),
                ..production_options(&attributes)
            },
            lexical,
        )?;
        self.productions[index].parametric_origin = Some(instance.origin);
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
        ProductionItem::RegexTerminal {
            precede_regex,
            regex,
            follow_regex,
        } => ProductionItem::RegexTerminal {
            precede_regex: precede_regex.clone(),
            regex: regex.clone(),
            follow_regex: follow_regex.clone(),
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
        token: attributes.get("token").is_some(),
        transparent: attributes.get("bracket").is_some(),
        bracket: attributes.get("bracket").is_some(),
        bracket_label: attributes.label("bracketLabel").map(|label| label.name),
        apply_priority: attributes.get_str("applyPriority"),
        function: attributes.get("function").is_some(),
        macro_like: ["macro", "macro-rec", "alias", "alias-rec"]
            .iter()
            .any(|key| attributes.get(key).is_some()),
        prefer: attributes.get("prefer").is_some(),
        avoid: attributes.get("avoid").is_some(),
        source_production: None,
        source_production_text: None,
        source: attributes.source(),
        location: attributes.location(),
        user_list: attributes.get("userList").is_some(),
        user_list_nonempty: attributes.get_str("userList") == Some("+"),
        precedence: attributes.get_str("prec"),
        hook: attributes.get_str("hook"),
        parsing_only_subsort: false,
    }
}

fn is_syntactic_subsort(label: &Option<Label>, items: &[ProductionItem]) -> bool {
    label.is_none() && matches!(items, [ProductionItem::NonTerminal { .. }])
}

pub(crate) fn is_parser_sort(sort: &Sort) -> bool {
    matches!(
        sort.name.as_str(),
        "KBott" | "K" | "KLabel" | "KList" | "KItem" | "KConfigVar" | "KString"
    ) || sort.name.starts_with('#')
        || sort.name.parse::<u64>().is_ok()
}

#[cfg(test)]
mod tests {
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
    fn shared_concretization_is_independent_of_sentence_order() {
        let sentences = parametric_sentences();
        let references = sentences.iter().collect::<Vec<_>>();
        let expected = concretize_parametric_productions(&references);
        let mut reversed = sentences.clone();
        reversed.reverse();
        let references = reversed.iter().collect::<Vec<_>>();
        let actual = concretize_parametric_productions(&references);

        assert_eq!(actual, expected);
        assert!(actual.parsing_only_subsorts.iter().all(|bridge| {
            matches!(&bridge.sentence, Sentence::Production { label: None, parameters, attributes, .. }
                if parameters.is_empty() && attributes.entries().is_empty())
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
                "KItem ::= Int [S=Int] from 1 parameter(s)",
                "KItem ::= MInt{8} [S=MInt{8}] from 1 parameter(s)",
                "Int ::= \"case1(\" Int \",\" K \")\" [P=Int, R=K] from 2 parameter(s)",
                "K ::= \"case1(\" K \",\" K \")\" [P=K, R=K] from 2 parameter(s)",
                "KItem ::= \"case1(\" KItem \",\" K \")\" [P=KItem, R=K] from 2 parameter(s)",
                "MInt{8} ::= \"case1(\" MInt{8} \",\" K \")\" [P=MInt{8}, R=K] from 2 parameter(s)",
                "MInt{8} ::= \"case2(\" MInt{8} \",\" MInt{K} \")\" [W=8, X=K] from 2 parameter(s)",
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
