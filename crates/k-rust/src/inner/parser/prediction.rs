//! ```toml algorithm
//! id = "parser.prediction.nullability"
//! name = "epsilon-nullability analysis by worklist"
//! sites = ["PredictionAnalysis::new"]
//! variable = "I = total production items"
//! counters = ["ParserPredictionAnalysisBuilds"]
//!
//! [[cost]]
//! mode = "one grammar"
//! bound = "O(I)"
//! ```
//!
//! ```toml algorithm
//! id = "parser.prediction.first_sets"
//! name = "scanner-identity FIRST-set analysis by monotone propagation"
//! sites = ["PredictionAnalysis::new"]
//! variable = "S = sorts; L = lexemes; R = worklist re-enqueues"
//! counters = ["ParserPredictionAnalysisBuilds"]
//!
//! [[cost]]
//! mode = "one grammar"
//! bound = "O(S x L x R)"
//! ```
//!
//! Epsilon-nullability and scanner-identity FIRST sets for immutable grammar snapshots.
//!
//! Both are monotone worklists. Nullability is O(total production items); FIRST propagation
//! is O(sorts * lexemes * re-enqueues) and runs once per grammar, counted by
//! `Counter::ParserPredictionAnalysisBuilds`. Filtered prediction visits only nonlexical-first
//! productions and the lexical bucket for the scanner winner while retaining declaration order.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use k_rust_kore::measure::{self, Counter};

#[cfg(test)]
use super::Sort;
use super::{Grammar, Item};

/// A set of scanner lexeme ids, one bit per id; ids are dense indexes into the scanner.
#[derive(Clone, Default, Eq, PartialEq)]
struct LexemeSet {
    words: Vec<u64>,
}

impl LexemeSet {
    fn insert(&mut self, id: usize) {
        let (word, bit) = (id / 64, id % 64);
        if self.words.len() <= word {
            self.words.resize(word + 1, 0);
        }
        self.words[word] |= 1 << bit;
    }

    fn contains(&self, id: usize) -> bool {
        self.words
            .get(id / 64)
            .is_some_and(|word| word & (1 << (id % 64)) != 0)
    }

    /// Add every id of `other`; true exactly when the set grew.
    fn union_with(&mut self, other: &Self) -> bool {
        if self.words.len() < other.words.len() {
            self.words.resize(other.words.len(), 0);
        }
        let mut grew = false;
        for (word, added) in self.words.iter_mut().zip(&other.words) {
            grew |= *added & !*word != 0;
            *word |= added;
        }
        grew
    }

    fn is_empty(&self) -> bool {
        self.words.iter().all(|word| *word == 0)
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.words.iter().enumerate().flat_map(|(index, word)| {
            (0..64)
                .filter(move |bit| word & (1 << bit) != 0)
                .map(move |bit| index * 64 + bit)
        })
    }
}

impl std::fmt::Debug for LexemeSet {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_set().entries(self.iter()).finish()
    }
}

#[cfg(test)]
impl PartialEq<BTreeSet<usize>> for LexemeSet {
    fn eq(&self, other: &BTreeSet<usize>) -> bool {
        self.iter().eq(other.iter().copied())
    }
}

#[derive(Clone, Copy, Debug)]
enum Symbol {
    NonTerminal(usize),
    Lexical(Option<usize>),
}

#[derive(Clone, Debug, Default)]
struct PredictionBucket {
    nonlexical_first: Vec<usize>,
    lexical_by_lexeme: BTreeMap<usize, Vec<usize>>,
    lexical_total: usize,
}

pub(super) struct PredictionCandidates<'a> {
    nonlexical: std::slice::Iter<'a, usize>,
    lexical: std::slice::Iter<'a, usize>,
}

impl Iterator for PredictionCandidates<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        match (
            self.nonlexical.as_slice().first(),
            self.lexical.as_slice().first(),
        ) {
            (Some(left), Some(right)) if left < right => self.nonlexical.next().copied(),
            (Some(_), Some(_)) => self.lexical.next().copied(),
            (Some(_), None) => self.nonlexical.next().copied(),
            (None, Some(_)) => self.lexical.next().copied(),
            (None, None) => None,
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct PredictionAnalysis {
    first_items: Vec<Option<Symbol>>,
    epsilon: Vec<bool>,
    first: Vec<LexemeSet>,
    buckets: Vec<PredictionBucket>,
}

impl PredictionAnalysis {
    pub(super) fn new(grammar: &Grammar) -> Self {
        measure::bump(Counter::ParserPredictionAnalysisBuilds);
        // Hidden program-list descriptors still exist in `productions` for reconstruction.
        // Only the predictor's active buckets participate in recognition.
        let mut first_items = vec![None; grammar.productions.len()];
        let productions = grammar
            .by_result
            .iter()
            .flatten()
            .map(|index| {
                let production = &grammar.productions[*index];
                // Prediction follows the recognizer's item sort ids, which can name a wider
                // parse sort than the declared item sort (`Production::item_sort_ids`).
                let items = production
                    .items
                    .iter()
                    .zip(&production.item_sort_ids)
                    .map(|(item, sort_id)| match item {
                        Item::NonTerminal(_) => {
                            Symbol::NonTerminal(sort_id.expect("nonterminal item has a sort id"))
                        }
                        _ => Symbol::Lexical(grammar.scanner.lexeme_id(item)),
                    })
                    .collect::<Vec<_>>();
                first_items[*index] = items.first().copied();
                (production.result_id, items)
            })
            .collect::<Vec<_>>();
        let mut buckets = vec![PredictionBucket::default(); grammar.sorts.len()];
        for (sort_id, indexes) in grammar.by_result.iter().enumerate() {
            let bucket = &mut buckets[sort_id];
            for index in indexes {
                match first_items[*index] {
                    Some(Symbol::Lexical(Some(lexeme))) => {
                        bucket.lexical_total += 1;
                        bucket
                            .lexical_by_lexeme
                            .entry(lexeme)
                            .or_default()
                            .push(*index);
                    }
                    Some(Symbol::Lexical(None)) => bucket.lexical_total += 1,
                    Some(Symbol::NonTerminal(_)) | None => bucket.nonlexical_first.push(*index),
                }
            }
        }

        // Adapt Java EarleyParser.markNullable: a newly nullable sort wakes its callers.
        // Each nonterminal occurrence counts separately (e.g. S ::= N N).
        // Regexes, including zero-width regexes, are mandatory scanner transitions, not epsilon.
        let mut epsilon = vec![false; grammar.sorts.len()];
        let mut remaining = vec![None; productions.len()];
        let mut callers = vec![Vec::new(); grammar.sorts.len()];
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
        // Invariant: every queued sort has just become nullable; each caller's remaining count is
        // the number of child occurrences not yet proved nullable and can only decrease to zero.
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
        let mut first = vec![LexemeSet::default(); grammar.sorts.len()];
        let mut dependents = vec![BTreeSet::new(); grammar.sorts.len()];
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
                        if let Some(lexeme) = lexeme {
                            first[*result].insert(*lexeme);
                        }
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
        // Invariant: each queued sort has new FIRST tokens not yet propagated; all sets grow
        // monotonically and a parent is queued only after its set grows.
        while let Some(sort) = pending.pop_front() {
            queued[sort] = false;
            let tokens = first[sort].clone();
            for parent in &dependents[sort] {
                if first[*parent].union_with(&tokens) && !queued[*parent] {
                    queued[*parent] = true;
                    pending.push_back(*parent);
                }
            }
        }
        Self {
            first_items,
            epsilon,
            first,
            buckets,
        }
    }

    pub(super) fn candidates(
        &self,
        sort: usize,
        winner: Option<usize>,
    ) -> (PredictionCandidates<'_>, usize) {
        let bucket = &self.buckets[sort];
        let lexical = winner
            .and_then(|winner| bucket.lexical_by_lexeme.get(&winner))
            .map_or(&[][..], Vec::as_slice);
        (
            PredictionCandidates {
                nonlexical: bucket.nonlexical_first.iter(),
                lexical: lexical.iter(),
            },
            bucket.lexical_total - lexical.len(),
        )
    }

    pub(super) fn can_filter(&self, production: usize) -> bool {
        match self.first_items[production] {
            Some(Symbol::Lexical(_)) => true,
            Some(Symbol::NonTerminal(child)) => !self.epsilon[child],
            None => false,
        }
    }

    pub(super) fn cannot_start(&self, production: usize, winner: Option<usize>) -> bool {
        match self.first_items[production] {
            Some(Symbol::Lexical(target)) => target.is_none() || target != winner,
            Some(Symbol::NonTerminal(child)) => {
                winner.is_none_or(|winner| !self.first[child].contains(winner))
            }
            None => false,
        }
    }

    #[cfg(test)]
    fn candidates_by_iteration(
        &self,
        grammar: &Grammar,
        sort: &Sort,
        winner: Option<usize>,
    ) -> (Vec<usize>, usize, usize) {
        let mut candidates = Vec::new();
        let mut terminal_skipped = 0;
        let mut nonterminal_skipped = 0;
        for production in grammar.productions_for(sort) {
            if self.can_filter(production) && self.cannot_start(production, winner) {
                if matches!(self.first_items[production], Some(Symbol::NonTerminal(_))) {
                    nonterminal_skipped += 1;
                } else {
                    terminal_skipped += 1;
                }
            } else {
                candidates.push(production);
            }
        }
        (candidates, terminal_skipped, nonterminal_skipped)
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::super::{
        CHART_COMPLETION_CANDIDATES, NONTERMINAL_PREDICTIONS_SKIPPED, PARSE_ATTEMPTS,
        PREDICTION_ANALYSIS_BUILDS, ParseContext, ParseError, ParseProvenance, PredictionMode,
        ScanWinner, SourceId, Term, TermMetadata,
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

    fn indexed_grammar(kinds: &[u8]) -> Grammar {
        let mut sentences = vec![
            production("Start", vec![nt("Choice")], "start"),
            production("Child", vec![terminal("c")], "child-c"),
        ];
        for (index, kind) in kinds.iter().enumerate() {
            let items = match kind % 5 {
                0 => vec![],
                1 => vec![terminal("a")],
                2 => vec![terminal("b")],
                3 => vec![nt("Child")],
                _ => vec![ProductionItem::regex("a*")],
            };
            sentences.push(production("Choice", items, &format!("choice-{index}")));
        }
        Grammar::from_sentences(&sentences).unwrap()
    }

    fn unfiltered(grammar: &Grammar, input: &str) -> Result<Term, ParseError> {
        grammar.parse_attempt(
            &Sort::new("Start"),
            input,
            ParseContext {
                is_anywhere: false,
                provenance: ParseProvenance {
                    source: SourceId(7),
                    base_offset: 100,
                },
                diagnostic_provenance: true,
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

    proptest! {
        #[test]
        fn prediction_fixed_points_match_naive_iteration(
            productions_by_sort in prop::collection::vec(
                prop::collection::vec(
                    prop::collection::vec((any::<bool>(), any::<u8>()), 0..4),
                    0..4,
                ),
                1..6,
            ),
        ) {
            let sort_count = productions_by_sort.len();
            let sorts = (0..sort_count)
                .map(|index| Sort::new(format!("S{index}")))
                .collect::<Vec<_>>();
            let mut grammar = Grammar::default();
            let mut productions = Vec::new();
            for (result, sort_productions) in productions_by_sort.iter().enumerate() {
                for raw_items in sort_productions {
                    let items = raw_items
                        .iter()
                        .map(|(nonterminal, value)| {
                            if *nonterminal {
                                nt(&format!("S{}", usize::from(*value) % sort_count))
                            } else {
                                terminal(&char::from(b'a' + value % 3).to_string())
                            }
                        })
                        .collect::<Vec<_>>();
                    grammar
                        .add(sorts[result].clone(), items.clone(), None, false, true)
                        .unwrap();
                    productions.push((result, items));
                }
            }

            let mut nullable = vec![false; sort_count];
            loop {
                let previous = nullable.clone();
                for (result, items) in &productions {
                    nullable[*result] |= items.iter().all(|item| match item {
                        ProductionItem::NonTerminal { sort, .. } => {
                            let index = sorts.iter().position(|candidate| candidate == sort).unwrap();
                            previous[index]
                        }
                        ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => false,
                    });
                }
                if nullable == previous {
                    break;
                }
            }

            let mut first = vec![BTreeSet::new(); sort_count];
            loop {
                let previous = first.clone();
                for (result, items) in &productions {
                    for item in items {
                        match item {
                            ProductionItem::NonTerminal { sort, .. } => {
                                let index =
                                    sorts.iter().position(|candidate| candidate == sort).unwrap();
                                first[*result].extend(previous[index].iter().copied());
                                if !nullable[index] {
                                    break;
                                }
                            }
                            ProductionItem::Terminal(text) => {
                                first[*result].insert(
                                    grammar.scanner.lexeme_id(&Item::Terminal(text.clone())).unwrap(),
                                );
                                break;
                            }
                            ProductionItem::RegexTerminal { .. } => unreachable!(),
                        }
                    }
                }
                if first == previous {
                    break;
                }
            }

            let analysis = PredictionAnalysis::new(&grammar);
            for (index, sort) in sorts.iter().enumerate() {
                if let Some(actual) = grammar.sort_id(sort) {
                    prop_assert_eq!(analysis.epsilon[actual], nullable[index]);
                    prop_assert_eq!(&analysis.first[actual], &first[index]);
                } else {
                    prop_assert!(!nullable[index]);
                    prop_assert!(first[index].is_empty());
                }
            }
        }
    }

    #[test]
    fn buckets_partition_by_result_in_order() {
        let grammar = Grammar::from_sentences(&[
            production("Choice", vec![], "empty"),
            production("Choice", vec![terminal("a")], "a1"),
            production("Choice", vec![nt("Child")], "child"),
            production("Choice", vec![terminal("b")], "b"),
            production("Choice", vec![terminal("a")], "a2"),
            production("Child", vec![terminal("c")], "c"),
        ])
        .unwrap();
        let analysis = PredictionAnalysis::new(&grammar);
        let sort = Sort::new("Choice");
        let sort_id = grammar.sort_id(&sort).unwrap();
        let winners = [
            None,
            grammar.scanner.lexeme_id(&Item::Terminal("a".into())),
            grammar.scanner.lexeme_id(&Item::Terminal("b".into())),
            grammar.scanner.lexeme_id(&Item::Terminal("c".into())),
        ];
        for winner in winners {
            let (actual, excluded) = analysis.candidates(sort_id, winner);
            let expected = grammar
                .productions_for(&sort)
                .filter(|index| match analysis.first_items[*index] {
                    Some(Symbol::Lexical(target)) => target.is_some() && target == winner,
                    Some(Symbol::NonTerminal(_)) | None => true,
                })
                .collect::<Vec<_>>();
            assert_eq!(actual.collect::<Vec<_>>(), expected);
            assert_eq!(
                excluded,
                grammar
                    .productions_for(&sort)
                    .filter(|index| matches!(
                        analysis.first_items[*index],
                        Some(Symbol::Lexical(_))
                    ))
                    .count()
                    - expected
                        .iter()
                        .filter(|index| {
                            matches!(analysis.first_items[**index], Some(Symbol::Lexical(_)))
                        })
                        .count()
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(128))]

        #[test]
        fn indexed_candidates_match_the_iteration_oracle(
            kinds in prop::collection::vec(0u8..10, 1..20),
            winner_choice in 0u8..4,
        ) {
            let grammar = indexed_grammar(&kinds);
            let analysis = PredictionAnalysis::new(&grammar);
            let sort = Sort::new("Choice");
            let winner = match winner_choice {
                0 => None,
                1 => grammar.scanner.lexeme_id(&Item::Terminal("a".into())),
                2 => grammar.scanner.lexeme_id(&Item::Terminal("b".into())),
                _ => grammar.scanner.lexeme_id(&Item::Terminal("c".into())),
            };
            let (expected, terminal_skipped, nonterminal_skipped) =
                analysis.candidates_by_iteration(&grammar, &sort, winner);
            let (indexed, excluded) = analysis.candidates(grammar.sort_id(&sort).unwrap(), winner);
            let mut actual = Vec::new();
            let mut indexed_nonterminal_skipped = 0;
            for production in indexed {
                if analysis.can_filter(production) && analysis.cannot_start(production, winner)
                {
                    indexed_nonterminal_skipped += 1;
                } else {
                    actual.push(production);
                }
            }
            prop_assert_eq!(actual, expected);
            prop_assert_eq!(excluded, terminal_skipped);
            prop_assert_eq!(indexed_nonterminal_skipped, nonterminal_skipped);
        }

        #[test]
        fn indexed_prediction_matches_unfiltered_recognition(
            kinds in prop::collection::vec(0u8..10, 1..12),
            input in "[abc ]{0,12}",
        ) {
            let grammar = indexed_grammar(&kinds);
            prop_assert_eq!(filtered(&grammar, &input), unfiltered(&grammar, &input));
        }
    }

    #[test]
    fn filters_impossible_waiters_without_a_prior_caller() {
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

        // Filtering remains equivalent even when no earlier caller has populated the bucket.
        sentences.remove(0);
        let grammar = Grammar::from_sentences(&sentences).unwrap();
        NONTERMINAL_PREDICTIONS_SKIPPED.set(0);
        let baseline = unfiltered(&grammar, "é").unwrap();
        let parsed = filtered(&grammar, "é").unwrap();
        assert_eq!(parsed, baseline);
        assert_eq!(metadata(&parsed), metadata(&baseline));
        assert_eq!(NONTERMINAL_PREDICTIONS_SKIPPED.get(), 32);
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
        let id = |sort: &Sort| grammar.sort_id(sort).unwrap();
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
        let Some(ScanWinner::Token { lexeme: zero, .. }) =
            grammar.scanner.winner(&grammar.layout, "", 0, &mut None)
        else {
            panic!("expected the zero-width token to win")
        };
        assert_eq!(
            analysis.first[id(&Sort::new("Mandatory"))],
            BTreeSet::from([zero])
        );
        assert!(!analysis.first[id(&Sort::new("Mandatory"))].contains(token("x")));
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
        let index = grammar.sort_id(&Sort::new("List")).unwrap();
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
