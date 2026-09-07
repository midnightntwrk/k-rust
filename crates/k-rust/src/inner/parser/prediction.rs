//! Scanner-identity FIRST sets and epsilon-nullability for immutable grammar snapshots.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::{Grammar, Item, Sort};

#[derive(Clone, Copy, Debug)]
enum Symbol {
    NonTerminal(usize),
    Lexical(Option<usize>),
}

#[derive(Clone, Debug)]
pub(super) struct PredictionAnalysis {
    sorts: Vec<Sort>,
    first_items: Vec<Option<Symbol>>,
    epsilon: Vec<bool>,
    first: Vec<BTreeSet<usize>>,
}

impl PredictionAnalysis {
    pub(super) fn new(grammar: &Grammar) -> Self {
        #[cfg(test)]
        super::PREDICTION_ANALYSIS_BUILDS.set(super::PREDICTION_ANALYSIS_BUILDS.get() + 1);
        // Hidden program-list descriptors still exist in `productions` for reconstruction.
        // Only the predictor's active buckets participate in recognition.
        let sorts = grammar
            .by_result
            .keys()
            .cloned()
            .chain(grammar.by_result.values().flatten().flat_map(|index| {
                grammar.productions[*index]
                    .items
                    .iter()
                    .filter_map(|item| match item {
                        Item::NonTerminal(sort) => Some(sort.clone()),
                        _ => None,
                    })
            }))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let sort_ids = sorts
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, sort)| (sort, index))
            .collect::<BTreeMap<_, _>>();
        let mut first_items = vec![None; grammar.productions.len()];
        let productions = grammar
            .by_result
            .values()
            .flatten()
            .map(|index| {
                let production = &grammar.productions[*index];
                let items = production
                    .items
                    .iter()
                    .map(|item| match item {
                        Item::NonTerminal(sort) => Symbol::NonTerminal(sort_ids[sort]),
                        _ => Symbol::Lexical(grammar.scanner.lexeme_id(item)),
                    })
                    .collect::<Vec<_>>();
                first_items[*index] = items.first().copied();
                (sort_ids[&production.result], items)
            })
            .collect::<Vec<_>>();

        // Adapt Java EarleyParser.markNullable: a newly nullable sort wakes its callers.
        // Each nonterminal occurrence counts separately (e.g. S ::= N N).
        // Regexes, including zero-width regexes, are mandatory scanner transitions, not epsilon.
        let mut epsilon = vec![false; sorts.len()];
        let mut remaining = vec![None; productions.len()];
        let mut callers = vec![Vec::new(); sorts.len()];
        let mut pending = VecDeque::new();
        for (index, (result, items)) in productions.iter().enumerate() {
            if items.iter().any(|item| matches!(item, Symbol::Lexical(_))) {
                continue;
            }
            remaining[index] = Some(items.len());
            for item in items {
                let Symbol::NonTerminal(child) = item else {
                    unreachable!()
                };
                callers[*child].push(index);
            }
            if items.is_empty() && !epsilon[*result] {
                epsilon[*result] = true;
                pending.push_back(*result);
            }
        }
        while let Some(sort) = pending.pop_front() {
            for caller in &callers[sort] {
                let count = remaining[*caller]
                    .as_mut()
                    .expect("nonterminal-only caller");
                *count -= 1;
                let result = productions[*caller].0;
                if *count == 0 && !epsilon[result] {
                    epsilon[result] = true;
                    pending.push_back(result);
                }
            }
        }

        // Java computeFirstSet's monotone unions, scheduled only for changed child sorts.
        let mut first = vec![BTreeSet::new(); sorts.len()];
        let mut dependents = vec![BTreeSet::new(); sorts.len()];
        for (result, items) in &productions {
            for item in items {
                match item {
                    Symbol::NonTerminal(child) => {
                        dependents[*child].insert(*result);
                        if !epsilon[*child] {
                            break;
                        }
                    }
                    Symbol::Lexical(lexeme) => {
                        // Unregistered items cannot match Scanner::matches either.
                        first[*result].extend(lexeme);
                        break;
                    }
                }
            }
        }
        let mut queued = first.iter().map(|set| !set.is_empty()).collect::<Vec<_>>();
        pending.extend(
            queued
                .iter()
                .enumerate()
                .filter_map(|(index, queued)| queued.then_some(index)),
        );
        while let Some(sort) = pending.pop_front() {
            queued[sort] = false;
            let tokens = first[sort].clone();
            for parent in &dependents[sort] {
                let previous = first[*parent].len();
                first[*parent].extend(&tokens);
                if previous != first[*parent].len() && !queued[*parent] {
                    queued[*parent] = true;
                    pending.push_back(*parent);
                }
            }
        }
        Self {
            sorts,
            first_items,
            epsilon,
            first,
        }
    }

    pub(super) fn can_filter(&self, production: usize, predicted: &BTreeSet<Sort>) -> bool {
        match self.first_items[production] {
            Some(Symbol::Lexical(_)) => true,
            Some(Symbol::NonTerminal(child)) => {
                // Without this marker, the caller would expand descendants and invalidate
                // snapshots later. Preserve that scheduling even when FIRST proves it dead.
                !self.epsilon[child] && predicted.contains(&self.sorts[child])
            }
            None => false,
        }
    }

    pub(super) fn cannot_start(&self, production: usize, winner: Option<usize>) -> bool {
        match self.first_items[production] {
            Some(Symbol::Lexical(target)) => target.is_none() || target != winner,
            Some(Symbol::NonTerminal(child)) => {
                winner.is_none_or(|winner| !self.first[child].contains(&winner))
            }
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{
        CHART_COMPLETION_CANDIDATES, NONTERMINAL_PREDICTIONS_SKIPPED, PARSE_ATTEMPTS,
        PREDICTION_ANALYSIS_BUILDS, ParseError, ParseProvenance, PredictionMode, SourceId, Term,
        TermMetadata,
    };
    use super::*;
    use crate::definition::{Attributes, ProductionCatalog, ProductionItem, Sentence};
    use crate::kast::Label;

    fn nt(sort: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(sort),
            name: None,
        }
    }

    fn terminal(text: &str) -> ProductionItem {
        ProductionItem::Terminal(text.into())
    }

    fn production(sort: &str, items: Vec<ProductionItem>, label: &str) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(label)),
            parameters: vec![],
            sort: Sort::new(sort),
            items,
            attributes: Attributes::default(),
        }
    }

    fn unfiltered(grammar: &Grammar, input: &str) -> Result<Term, ParseError> {
        grammar.parse_attempt(
            &Sort::new("Start"),
            input,
            false,
            ParseProvenance {
                source: SourceId(7),
                base_offset: 100,
            },
            PredictionMode::Unfiltered,
            &mut false,
        )
    }

    fn filtered(grammar: &Grammar, input: &str) -> Result<Term, ParseError> {
        grammar.parse_with_provenance(&Sort::new("Start"), input, SourceId(7), 100)
    }

    fn metadata(term: &Term) -> Vec<Option<TermMetadata>> {
        let mut result = vec![term.metadata().cloned()];
        if let Term::Apply { arguments, .. } = term.unannotated() {
            for argument in arguments {
                result.extend(metadata(argument));
            }
        }
        result
    }

    #[test]
    fn omits_only_already_considered_impossible_waiters() {
        let mut sentences = vec![
            production("Start", vec![nt("Dead"), terminal("bad")], "bad"),
            production("Start", vec![nt("Wide")], "start"),
            production("Dead", vec![terminal("n")], "n"),
        ];
        for index in 0..32 {
            sentences.push(production(
                "Wide",
                vec![nt("Dead"), terminal(&format!("w{index}"))],
                "dead",
            ));
        }
        sentences.push(production(
            "Wide",
            vec![nt("Empty"), terminal("é"), nt("Empty")],
            "chosen",
        ));
        sentences.push(production("Empty", vec![], "empty"));
        let grammar = Grammar::from_sentences(&sentences).unwrap();
        CHART_COMPLETION_CANDIDATES.set(0);
        let baseline = unfiltered(&grammar, " \né ").unwrap();
        let completions = CHART_COMPLETION_CANDIDATES.get();
        CHART_COMPLETION_CANDIDATES.set(0);
        NONTERMINAL_PREDICTIONS_SKIPPED.set(0);
        PARSE_ATTEMPTS.set(0);
        let parsed = filtered(&grammar, " \né ").unwrap();
        assert_eq!(
            parsed,
            Term::apply(
                "start",
                vec![Term::apply(
                    "chosen",
                    vec![Term::apply("empty", vec![]), Term::apply("empty", vec![])]
                )]
            )
        );
        assert_eq!(parsed, baseline);
        assert_eq!(metadata(&parsed), metadata(&baseline));
        assert_eq!(CHART_COMPLETION_CANDIDATES.get(), completions);
        assert_eq!(NONTERMINAL_PREDICTIONS_SKIPPED.get(), 32);
        assert_eq!(PARSE_ATTEMPTS.get(), 1);

        // Without the earlier caller, the Wide states must remain to initiate Dead's work.
        sentences.remove(0);
        let grammar = Grammar::from_sentences(&sentences).unwrap();
        NONTERMINAL_PREDICTIONS_SKIPPED.set(0);
        assert!(filtered(&grammar, "é").is_ok());
        assert_eq!(NONTERMINAL_PREDICTIONS_SKIPPED.get(), 0);
    }

    #[test]
    fn current_bucket_marker_is_sufficient_without_hiding_cycles() {
        let grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("Dead")], "dead"),
            production("Start", vec![terminal("x")], "x"),
            production("Dead", vec![nt("Dead"), terminal("z")], "recur"),
            production("Dead", vec![terminal("n")], "n"),
        ])
        .unwrap();
        NONTERMINAL_PREDICTIONS_SKIPPED.set(0);
        assert_eq!(filtered(&grammar, "x"), unfiltered(&grammar, "x"));
        assert_eq!(NONTERMINAL_PREDICTIONS_SKIPPED.get(), 1);

        let grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("Dead")], "dead"),
            production("Start", vec![nt("Wide")], "wide"),
            production("Start", vec![terminal("x")], "x"),
            production("Dead", vec![nt("Cycle"), terminal("z")], "dead"),
            production("Wide", vec![nt("Dead"), terminal("w")], "wait"),
            production("Cycle", vec![nt("Cycle")], "wrap"),
            production("Cycle", vec![], "unit"),
        ])
        .unwrap();
        assert_eq!(
            unfiltered(&grammar, "x"),
            Err(ParseError::CyclicParseForest)
        );
        NONTERMINAL_PREDICTIONS_SKIPPED.set(0);
        PARSE_ATTEMPTS.set(0);
        assert_eq!(filtered(&grammar, "x"), Err(ParseError::CyclicParseForest));
        assert_eq!(NONTERMINAL_PREDICTIONS_SKIPPED.get(), 1);
        assert_eq!(PARSE_ATTEMPTS.get(), 2);
    }

    #[test]
    fn fixed_points_distinguish_epsilon_from_zero_width_lexical_items() {
        let mut grammar = Grammar::default();
        for (sort, items) in [
            ("E", vec![nt("F"), nt("F")]),
            ("F", vec![nt("E")]),
            ("F", vec![]),
            ("A", vec![nt("B")]),
            ("B", vec![nt("A")]),
            ("B", vec![terminal("b")]),
            ("NoBase", vec![nt("NoBase")]),
            ("Zero", vec![ProductionItem::regex("z*")]),
            ("Prefix", vec![nt("E"), nt("A")]),
            ("Mandatory", vec![nt("Zero"), terminal("x")]),
        ] {
            grammar
                .add(Sort::new(sort), items, None, false, true)
                .unwrap();
        }
        for (parameter, text) in [("Int", "i"), ("Bool", "t")] {
            grammar
                .add(
                    Sort::with_parameters("Box", vec![Sort::new(parameter)]),
                    vec![terminal(text)],
                    None,
                    false,
                    false,
                )
                .unwrap();
        }
        let analysis = PredictionAnalysis::new(&grammar);
        let id = |sort: &Sort| analysis.sorts.binary_search(sort).unwrap();
        let token = |text: &str| {
            grammar
                .scanner
                .lexeme_id(&Item::Terminal(text.into()))
                .unwrap()
        };
        for sort in ["E", "F"] {
            assert!(analysis.epsilon[id(&Sort::new(sort))]);
        }
        for sort in ["A", "B", "NoBase", "Zero", "Prefix", "Mandatory"] {
            assert!(!analysis.epsilon[id(&Sort::new(sort))]);
        }
        assert!(analysis.first[id(&Sort::new("NoBase"))].is_empty());
        for sort in ["A", "B", "Prefix"] {
            assert_eq!(
                analysis.first[id(&Sort::new(sort))],
                BTreeSet::from([token("b")])
            );
        }
        let zero = grammar.scanner.winner("", 0, &mut None).unwrap().0;
        assert_eq!(
            analysis.first[id(&Sort::new("Mandatory"))],
            BTreeSet::from([zero])
        );
        assert!(!analysis.first[id(&Sort::new("Mandatory"))].contains(&token("x")));
        for (parameter, text) in [("Int", "i"), ("Bool", "t")] {
            assert_eq!(
                analysis.first[id(&Sort::with_parameters("Box", vec![Sort::new(parameter)]))],
                BTreeSet::from([token(text)])
            );
        }
    }

    #[test]
    fn retains_mandatory_zero_width_winners_for_later_callers() {
        let grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("Zero"), terminal("bad")], "bad"),
            production("Start", vec![nt("Later")], "start"),
            production("Later", vec![nt("Zero")], "later"),
            production("Zero", vec![ProductionItem::regex("z*")], "zero"),
        ])
        .unwrap();
        for input in ["", "z"] {
            NONTERMINAL_PREDICTIONS_SKIPPED.set(0);
            let baseline = unfiltered(&grammar, input).unwrap();
            assert_eq!(filtered(&grammar, input).unwrap(), baseline);
            assert_eq!(NONTERMINAL_PREDICTIONS_SKIPPED.get(), 0);
        }
    }

    #[test]
    fn cache_survives_reuse_but_not_clone_mutation_or_failed_registration() {
        let mut grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("Choice")], "start"),
            production("Choice", vec![terminal("a")], "a"),
        ])
        .unwrap();
        PREDICTION_ANALYSIS_BUILDS.set(0);
        assert!(filtered(&grammar, "a").is_ok());
        assert!(filtered(&grammar, "a").is_ok());
        assert_eq!(PREDICTION_ANALYSIS_BUILDS.get(), 1);
        let mut cloned = grammar.clone();
        cloned
            .add(
                Sort::new("Choice"),
                vec![terminal("b")],
                Some(Label::new("b")),
                false,
                false,
            )
            .unwrap();
        assert!(cloned.prediction_analysis.get().is_none());
        assert!(grammar.prediction_analysis.get().is_some());
        assert!(filtered(&cloned, "b").is_ok());
        assert!(filtered(&grammar, "b").is_err());
        assert_eq!(PREDICTION_ANALYSIS_BUILDS.get(), 2);

        // Registration of "ab" succeeds before compilation of the second item fails.
        // The surviving global competitor must change subsequent recognition and IDs remain valid.
        assert!(
            grammar
                .add(
                    Sort::new("Other"),
                    vec![terminal("ab"), ProductionItem::regex("[")],
                    None,
                    false,
                    false
                )
                .is_err()
        );
        assert!(grammar.prediction_analysis.get().is_none());
        assert_eq!(filtered(&grammar, "ab"), unfiltered(&grammar, "ab"));
        assert!(filtered(&grammar, "a").is_ok());
        assert_eq!(PREDICTION_ANALYSIS_BUILDS.get(), 3);

        grammar
            .add_token_with_precedence(Sort::new("Token"), ProductionItem::regex("c+"), "1")
            .unwrap();
        assert!(filtered(&grammar, "a").is_ok());
        assert!(
            grammar
                .add_token_with_precedence(Sort::new("Token"), ProductionItem::regex("c+"), "2")
                .is_err()
        );
        assert!(grammar.prediction_analysis.get().is_none());
        assert!(filtered(&grammar, "a").is_ok());
    }

    #[test]
    fn program_list_analysis_ignores_retained_hidden_descriptors() {
        let mut list = production(
            "List",
            vec![nt("Element"), terminal(","), nt("List")],
            "cons",
        );
        let mut empty = production("List", vec![terminal(".List")], "nil");
        for sentence in [&mut list, &mut empty] {
            let Sentence::Production { attributes, .. } = sentence else {
                unreachable!()
            };
            attributes.insert("userList", serde_json::json!("+"));
        }
        let sentences = vec![production("Element", vec![terminal("a")], "a"), list, empty];
        let catalog = ProductionCatalog::from_visible(&sentences);
        let grammar = Grammar::from_program_sentences(&sentences, &catalog).unwrap();
        assert!(
            grammar
                .productions
                .iter()
                .any(|production| production.result == Sort::new("List")
                    && production.items.is_empty())
        );
        let analysis = PredictionAnalysis::new(&grammar);
        let index = analysis.sorts.binary_search(&Sort::new("List")).unwrap();
        assert!(!analysis.epsilon[index]);
        assert_eq!(
            analysis.first[index],
            BTreeSet::from([grammar
                .scanner
                .lexeme_id(&Item::Terminal("a".into()))
                .unwrap()])
        );
        assert!(grammar.parse(&Sort::new("List"), "").is_err());
        assert!(grammar.parse(&Sort::new("List"), "a").is_ok());
        assert!(grammar.parse(&Sort::new("List"), "a,").is_err());
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn dead_waiters_preserve_nullable_record_names_and_metadata() {
        let mut grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("Dead"), terminal("bad")], "bad"),
            production("Start", vec![nt("Wide")], "start"),
            production("Dead", vec![terminal("n")], "n"),
            production("Wide", vec![nt("Dead"), terminal("w")], "dead"),
            production("Wide", vec![nt("Empty"), nt("Box"), nt("Empty")], "chosen"),
            production("Empty", vec![], "empty"),
            production(
                "Box",
                vec![
                    terminal("box"),
                    terminal("("),
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Int"),
                        name: Some("value".into()),
                    },
                    terminal(")"),
                ],
                "box",
            ),
            production("Int", vec![terminal("1")], "one"),
            // Generated omitted-field variables have K as their default upper bound, as in
            // the normal rule grammar. This focused grammar must declare Int's injection.
            Sentence::Production {
                label: None,
                parameters: vec![],
                sort: Sort::new("K"),
                items: vec![nt("Int")],
                attributes: Attributes::default(),
            },
        ])
        .unwrap();
        crate::inner::config::add_casts(
            &mut grammar,
            Sort::new("K"),
            Sort::new("Int"),
            Sort::new("Int"),
        )
        .unwrap();
        let baseline = unfiltered(&grammar, "box(...)").unwrap();
        assert!(baseline.to_string().contains("_value0"));
        NONTERMINAL_PREDICTIONS_SKIPPED.set(0);
        let parsed = filtered(&grammar, "box(...)").unwrap();
        assert!(NONTERMINAL_PREDICTIONS_SKIPPED.get() > 0);
        assert_eq!(parsed, baseline);
        assert_eq!(metadata(&parsed), metadata(&baseline));
    }
}
