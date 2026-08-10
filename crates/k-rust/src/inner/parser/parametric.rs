//! Scala-compatible concretization of parametric productions for Earley parsing.

use std::collections::BTreeMap;

use crate::definition::regex::Regex as KRegex;
use crate::definition::{
    Attributes, OverloadOrder, ProductionItem, Sentence, SortCatalog, SortHead,
};
use crate::kast::{Label, Sort};

use super::{Grammar, ParametricOrigin, ParseError, ProductionOptions, source_production};

impl Grammar {
    pub(super) fn add_parametric_productions(
        &mut self,
        sentences: &[&Sentence],
        lexical: &BTreeMap<String, KRegex>,
        overloads: &OverloadOrder<'_>,
    ) -> Result<(), ParseError> {
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

        for sentence in sentences {
            let Sentence::Production {
                label,
                parameters,
                sort,
                items,
                attributes,
            } = sentence
            else {
                continue;
            };
            if parameters.is_empty() {
                continue;
            }

            if parameters.contains(sort) {
                // Case 1: `syntax {P, R} P ::= P "+" R`.
                for concrete in &all_sorts {
                    let substitution = parameters
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
                        .collect();
                    self.add_instantiation(
                        label,
                        parameters,
                        sort,
                        items,
                        attributes,
                        substitution,
                        lexical,
                        source_production(overloads, sentence),
                    )?;
                }
            } else if !sort.parameters.is_empty() {
                // Case 2: `syntax {W, X} MInt{W} ::= MInt{W} "+" MInt{X}`.
                let head = SortHead::from(sort);
                for concrete in catalog.instantiations().get(&head).into_iter().flatten() {
                    let result_parameter = &sort.parameters[0];
                    let substitution = parameters
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
                        .collect();
                    self.add_instantiation(
                        label,
                        parameters,
                        sort,
                        items,
                        attributes,
                        substitution,
                        lexical,
                        source_production(overloads, sentence),
                    )?;
                }
            } else if is_syntactic_subsort(label, items) {
                // Case 3: `syntax {S} KItem ::= S`.
                for concrete in &all_sorts {
                    if !parameters.contains(sort) && matches!(concrete.name.as_str(), "K" | "KItem")
                    {
                        continue;
                    }
                    let substitution = BTreeMap::from([(parameters[0].clone(), concrete.clone())]);
                    self.add_instantiation(
                        label,
                        parameters,
                        sort,
                        items,
                        attributes,
                        substitution,
                        lexical,
                        source_production(overloads, sentence),
                    )?;
                }
            } else {
                // Case 4: parameters which occur only in arguments become `K`.
                let substitution = parameters
                    .iter()
                    .cloned()
                    .map(|parameter| (parameter, Sort::new("K")))
                    .collect();
                self.add_instantiation(
                    label,
                    parameters,
                    sort,
                    items,
                    attributes,
                    substitution,
                    lexical,
                    source_production(overloads, sentence),
                )?;
            }
        }

        // Connect concrete instances such as `MInt{6}` to the placeholder
        // `MInt{K}` used by parameters which lack parse-time sort information.
        for instances in catalog.instantiations().values() {
            for concrete in instances {
                let placeholder =
                    Sort::with_parameters(concrete.name.clone(), vec![Sort::new("K")]);
                self.add(
                    placeholder,
                    vec![ProductionItem::NonTerminal {
                        sort: concrete.clone(),
                        name: None,
                    }],
                    None,
                    false,
                    false,
                )?;
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn add_instantiation(
        &mut self,
        label: &Option<Label>,
        parameters: &[Sort],
        result: &Sort,
        items: &[ProductionItem],
        attributes: &Attributes,
        substitution: BTreeMap<Sort, Sort>,
        lexical: &BTreeMap<String, KRegex>,
        source_production: Option<crate::definition::ProductionId>,
    ) -> Result<(), ParseError> {
        let concrete_result = substitute_sort(result, &substitution);
        let concrete_items = items
            .iter()
            .map(|item| substitute_item(item, &substitution))
            .collect::<Vec<_>>();
        let concrete_label = label.as_ref().map(|label| Label::new(label.name.clone()));
        let index = self.productions.len();
        self.add_production_with_lexical(
            concrete_result,
            &concrete_items,
            concrete_label,
            ProductionOptions {
                source_production,
                ..production_options(attributes)
            },
            lexical,
        )?;
        self.productions[index].parametric_origin = Some(ParametricOrigin {
            label: label.clone(),
            parameters: parameters.to_vec(),
            result: result.clone(),
            items: items.to_vec(),
            attributes: attributes.clone(),
            substitution,
        });
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
        bracket_label: attributes.get_str("bracketLabel"),
        apply_priority: attributes.get_str("applyPriority"),
        function: attributes.get("function").is_some(),
        macro_like: ["macro", "macro-rec", "alias", "alias-rec"]
            .iter()
            .any(|key| attributes.get(key).is_some()),
        prefer: attributes.get("prefer").is_some(),
        avoid: attributes.get("avoid").is_some(),
        source_production: None,
        user_list: attributes.get("userList").is_some(),
        precedence: attributes.get_str("prec"),
    }
}

fn is_syntactic_subsort(label: &Option<Label>, items: &[ProductionItem]) -> bool {
    label.is_none() && matches!(items, [ProductionItem::NonTerminal { .. }])
}

fn is_parser_sort(sort: &Sort) -> bool {
    matches!(
        sort.name.as_str(),
        "KBott" | "K" | "KLabel" | "KList" | "KItem" | "KConfigVar" | "KString"
    ) || sort.name.starts_with('#')
        || sort.name.parse::<u64>().is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "z3-inference")]
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

    fn parametric_grammar() -> Grammar {
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
        Grammar::from_sentences(&sentences).unwrap()
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
    fn infers_parameters_when_result_is_a_formal_parameter() {
        let grammar = parametric_grammar();
        #[cfg(feature = "z3-inference")]
        assert_parametric_parse_snapshot!(
            grammar,
            Sort::new("Int"),
            r#"
            case1(i,k)
        "#
        );
        #[cfg(not(feature = "z3-inference"))]
        assert_z3_required(grammar.parse(&Sort::new("Int"), "case1(i,k)"));
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
        #[cfg(feature = "z3-inference")]
        assert_parametric_parse_snapshot!(
            grammar,
            Sort::new("Int"),
            r#"
            case4(k)
        "#
        );
        #[cfg(not(feature = "z3-inference"))]
        assert_z3_required(grammar.parse(&Sort::new("Int"), "case4(k)"));
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
