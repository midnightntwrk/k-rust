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
//! variable = "S = sorts; L = lexemes; R = worklist re-enqueues; I = total production items"
//! counters = ["ParserPredictionAnalysisBuilds"]
//!
//! [[cost]]
//! mode = "one grammar"
//! bound = "O(S x L x R) plus O(I x L) for the FIRST sets and nullability of each production's item suffixes"
//! ```
//!
//! Epsilon-nullability and scanner-identity FIRST sets for immutable grammar snapshots.
//!
//! Both are monotone worklists. Nullability is O(total production items); FIRST propagation
//! is O(sorts * lexemes * re-enqueues) and runs once per grammar, counted by
//! `Counter::ParserPredictionAnalysisBuilds`. Filtered prediction visits only nonlexical-first
//! productions and the lexical bucket for the scanner winner while retaining declaration order.
//! The FIRST sets and nullability of each production's item suffixes decide whether an item a
//! completion advances can continue with the next token (`Grammar::advanced_item_useful`).

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use k_rust_kore::measure::{self, Counter};

#[cfg(test)]
use super::Sort;
use super::{Grammar, Item};

/// A set of scanner lexeme ids, one bit per id; ids are dense indexes into the scanner.
#[derive(Clone, Default, Eq, PartialEq)]
pub(super) struct LexemeSet {
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
    /// For each active production and each dot position, what the items from the dot to the end
    /// can begin with; `None` for a production the predictor never adds.
    rests: Vec<Option<ProductionRests>>,
}

/// The FIRST sets and nullability of the suffixes of one production's items.
#[derive(Clone, Debug)]
struct ProductionRests {
    /// `first[dot]`: the lexemes the items from `dot` on can begin with.
    first: Vec<LexemeSet>,
    /// `nullable[dot]`: whether the items from `dot` on can all match the empty string.
    nullable: Vec<bool>,
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

        // Nullable sorts, as a least fixed point: a sort is nullable when one of its productions
        // consists of nullable nonterminals only, so a newly nullable sort wakes only its callers.
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

        // FIRST sets, as a least fixed point of monotone unions over each production's leading
        // items, rescheduled only for the sorts whose child sorts changed.
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
        // The suffix tables, from each production's end backward: a nonterminal adds its FIRST
        // set and passes the rest's on when it is nullable; a lexical item, mandatory even when
        // its match is empty, ends the suffix's FIRST set there.
        let mut rests = vec![None; grammar.productions.len()];
        for (index, (_, items)) in grammar.by_result.iter().flatten().zip(&productions) {
            let mut first_sets = vec![LexemeSet::default(); items.len() + 1];
            let mut nullable = vec![true; items.len() + 1];
            for (dot, item) in items.iter().enumerate().rev() {
                match item {
                    Symbol::NonTerminal(child) => {
                        let mut set = first[*child].clone();
                        if epsilon[*child] {
                            set.union_with(&first_sets[dot + 1]);
                            nullable[dot] = nullable[dot + 1];
                        } else {
                            nullable[dot] = false;
                        }
                        first_sets[dot] = set;
                    }
                    Symbol::Lexical(lexeme) => {
                        if let Some(lexeme) = lexeme {
                            first_sets[dot].insert(*lexeme);
                        }
                        nullable[dot] = false;
                    }
                }
            }
            rests[*index] = Some(ProductionRests {
                first: first_sets,
                nullable,
            });
        }
        Self {
            first_items,
            epsilon,
            first,
            buckets,
            rests,
        }
    }

    /// Whether the items of `production` from `dot` on can begin with the lexeme `winner`, the
    /// token the scanner reads next; `true` for a production the analysis does not cover.
    pub(super) fn rest_can_start_with(
        &self,
        production: usize,
        dot: usize,
        winner: Option<usize>,
    ) -> bool {
        match self.rests.get(production).and_then(Option::as_ref) {
            Some(rests) => winner.is_some_and(|winner| rests.first[dot].contains(winner)),
            None => true,
        }
    }

    /// Whether a phrase of the sort `sort` can begin with the lexeme `lexeme`.
    pub(super) fn sort_can_start_with(&self, sort: usize, lexeme: usize) -> bool {
        self.first[sort].contains(lexeme)
    }

    /// Whether the items of `production` from `dot` on can all match the empty string; `true`
    /// for a production the analysis does not cover.
    pub(super) fn rest_is_nullable(&self, production: usize, dot: usize) -> bool {
        self.rests
            .get(production)
            .and_then(Option::as_ref)
            .is_none_or(|rests| rests.nullable[dot])
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
        CHART_COMPLETION_CANDIDATES, DiagnosticWork, NONTERMINAL_PREDICTIONS_SKIPPED, NoParseInput,
        PARSE_ATTEMPTS, PREDICTION_ANALYSIS_BUILDS, PackedPriorityMemos, PackedTerm, ParseContext,
        ParseError, ParseProvenance, PredictionMode, PriorityFilter, Pruning, Recognition,
        SameSpanCycles, ScanWinner, SourceId, Term, TermMetadata, WorkMeter,
    };
    use super::*;
    use crate::definition::{
        Attributes, ProductionCatalog, ProductionItem, Sentence, SortDenotations,
    };
    use crate::kast::{InternalLabel, Label, TermSpan};
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
        grammar.parse_attempt_explained(
            &Sort::new("Start"),
            input,
            ParseContext {
                is_anywhere: false,
                provenance: ParseProvenance {
                    source: SourceId(7),
                    base_offset: 100,
                },
                diagnostic_provenance: true,
                diagnostic_work: DiagnosticWork::Unlimited,
            },
            PredictionMode::Unfiltered,
            &mut Pruning::default(),
        )
    }

    fn filtered(grammar: &Grammar, input: &str) -> Result<Term, ParseError> {
        grammar.parse_with_provenance(&Sort::new("Start"), input, SourceId(7), 100)
    }

    /// A parse (filtered, and retried when it fails having skipped anything) gives what one
    /// unfiltered recognition gives: the forest, its metadata and the error alike. The one
    /// exception is a same-span cycle the unfiltered recognition meets: it builds every item,
    /// also those no parse of the input contains, and stops at the first cycle among them,
    /// while a recognition that skips those items meets only the cycles of items the input can
    /// continue (as skipped predictions already did), so it may succeed or fail otherwise.
    /// Conversely, a cycle the filtered parse reports is one the unfiltered recognition meets.
    ///
    /// The filtered attempt alone, before any retry, finds a derivation of the input exactly
    /// when the unfiltered recognition does, and then gives its result: a retry, which restores
    /// the skipped work, must not be what makes the two agree.
    fn pruning_agrees_with_unfiltered_recognition(
        grammar: &Grammar,
        input: &str,
    ) -> Result<(), TestCaseError> {
        let filtered = filtered(grammar, input);
        let mut everything = Pruning::default();
        let unfiltered = attempt(grammar, input, PredictionMode::Unfiltered, &mut everything);
        if matches!(unfiltered, Err(ParseError::CyclicDerivation(_))) {
            return Ok(());
        }
        if let (Ok(filtered), Ok(unfiltered)) = (&filtered, &unfiltered) {
            prop_assert_eq!(metadata(filtered), metadata(unfiltered));
        }
        prop_assert_eq!(&filtered, &unfiltered);
        let mut skipped = Pruning::default();
        let alone = attempt(grammar, input, PredictionMode::Filtered, &mut skipped);
        prop_assert_eq!(skipped.furthest.is_none(), everything.furthest.is_none());
        if everything.furthest.is_none() {
            prop_assert_eq!(alone, unfiltered);
        }
        Ok(())
    }

    /// A sentence of the random grammar of the pruning proptests (`(sort, items)` with the item
    /// codes they use), derived from `S0` by taking, at each nonterminal in order, the
    /// production `choices` names next among those of its sort; `None` when the choices run
    /// out before every nonterminal is expanded.
    fn derived_sentence(productions: &[(u8, Vec<u8>)], choices: &[u8]) -> Option<String> {
        let mut choices = choices.iter();
        let mut pending = vec![0u8];
        let mut sentence = Vec::new();
        // Invariant: `pending` holds, last first, the item codes still to expand.
        while let Some(item) = pending.pop() {
            match item {
                0..=2 | 7 => {
                    let sort = if item == 7 { 0 } else { item };
                    let alternatives = productions
                        .iter()
                        .filter(|(result, _)| *result == sort)
                        .collect::<Vec<_>>();
                    if alternatives.is_empty() {
                        return None;
                    }
                    let choice = usize::from(*choices.next()?) % alternatives.len();
                    pending.extend(alternatives[choice].1.iter().rev());
                }
                3 => sentence.push("a"),
                4 => sentence.push("b"),
                5 => sentence.push("c"),
                _ => sentence.push("d"),
            }
        }
        Some(sentence.join(" "))
    }

    /// The case of `completion_pruning_matches_unfiltered_recognition_with_priorities` that
    /// ran a run of the suite out of memory: `S0 ::= S0 S0 | S0 "d" | "d" | "c" "a" "c" "a"`
    /// over thirteen tokens is ambiguous with exponentially many trees: over eight `d`s alone
    /// the grammar has 349,074 trees, an owned tree of 1.1 million nodes, and each further `d`
    /// multiplies both about fourteenfold. Both recognitions report the ambiguity from the
    /// forest, without building the owned tree of its trees (`forest::unpacked_nodes`), which
    /// took memory exponential in the input.
    #[cfg(feature = "z3-inference")]
    #[test]
    fn an_ambiguity_of_exponentially_many_trees_is_reported_from_the_forest() {
        let productions: Vec<(u8, Vec<u8>)> = vec![
            (2, vec![6]),
            (0, vec![7, 0]),
            (0, vec![5, 3, 5, 3]),
            (0, vec![6]),
            (0, vec![0, 6]),
            (2, vec![]),
            (2, vec![3, 6]),
            (2, vec![0, 5, 4, 4]),
        ];
        let mut sentences = vec![production("Start", vec![nt("S0")], "start")];
        for (index, (result, items)) in productions.iter().enumerate() {
            let items = items
                .iter()
                .map(|item| match item {
                    0..=2 => nt(&format!("S{item}")),
                    3 => terminal("a"),
                    4 => terminal("b"),
                    5 => terminal("c"),
                    6 => terminal("d"),
                    _ => nt("S0"),
                })
                .collect();
            sentences.push(production(
                &format!("S{result}"),
                items,
                &format!("p{index}"),
            ));
        }
        sentences.push(Sentence::SyntaxPriority {
            priorities: vec![
                vec!["p1".to_string(), "p3".to_string()],
                vec!["p5".to_string()],
                vec!["p7".to_string()],
            ],
            attributes: Attributes::default(),
        });
        let grammar = Grammar::from_sentences(&sentences).unwrap();
        let input = "d d c a c a d d d d d d d";

        super::super::forest::reset_unpacked_nodes();
        pruning_agrees_with_unfiltered_recognition(&grammar, input).unwrap();
        let parsed = filtered(&grammar, input);
        assert!(
            matches!(parsed, Err(ParseError::Ambiguous { .. })),
            "{parsed:?}"
        );
        assert_eq!(super::super::forest::unpacked_nodes(), 0);
    }

    fn attempt(
        grammar: &Grammar,
        input: &str,
        mode: PredictionMode,
        pruning: &mut Pruning,
    ) -> Result<Term, ParseError> {
        grammar.parse_attempt_explained(
            &Sort::new("Start"),
            input,
            ParseContext {
                is_anywhere: false,
                provenance: ParseProvenance {
                    source: SourceId(7),
                    base_offset: 100,
                },
                diagnostic_provenance: true,
                diagnostic_work: DiagnosticWork::Unlimited,
            },
            mode,
            pruning,
        )
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

        /// Skipping completions that cannot contribute to a parse keeps every parse and every
        /// error: on random recursive grammars with associativity declarations, a parse
        /// (filtered, and retried when it fails having skipped anything) gives what one
        /// unfiltered recognition gives, the forest, its metadata, and the error alike.
        #[test]
        fn completion_pruning_matches_unfiltered_recognition(
            productions in prop::collection::vec(
                (0u8..3, prop::collection::vec(0u8..6, 0..4), 0u8..4),
                1..9,
            ),
            input in "[ab ]{0,9}",
        ) {
            let mut sentences = vec![production("Start", vec![nt("S0")], "start")];
            for (index, (result, items, associativity)) in productions.iter().enumerate() {
                let label = format!("p{index}");
                let items = items
                    .iter()
                    .map(|item| match item {
                        0..=2 => nt(&format!("S{item}")),
                        3 => terminal("a"),
                        4 => terminal("b"),
                        _ => nt("S0"),
                    })
                    .collect();
                sentences.push(production(&format!("S{result}"), items, &label));
                let associativity = match associativity {
                    0 => continue,
                    1 => crate::definition::Associativity::Left,
                    2 => crate::definition::Associativity::Right,
                    _ => crate::definition::Associativity::NonAssoc,
                };
                sentences.push(Sentence::SyntaxAssociativity {
                    associativity,
                    tags: vec![label],
                    attributes: Attributes::default(),
                });
            }
            let Ok(grammar) = Grammar::from_sentences(&sentences) else {
                return Ok(());
            };
            pruning_agrees_with_unfiltered_recognition(&grammar, &input)?;
        }

        /// The same with associativity declared over groups of productions of different sorts,
        /// where a production's node can be forbidden under another sort's production: a
        /// recognition that skips such nodes before they are completed must still report the
        /// violation, or the chart, that an unfiltered one reports.
        #[test]
        fn completion_pruning_matches_unfiltered_recognition_with_grouped_associativity(
            productions in prop::collection::vec(
                (0u8..3, prop::collection::vec(0u8..7, 0..5)),
                1..9,
            ),
            groups in prop::collection::vec(
                (0u8..3, prop::collection::btree_set(0usize..9, 1..4)),
                1..3,
            ),
            input in "[abc ]{0,11}",
        ) {
            let mut sentences = vec![production("Start", vec![nt("S0")], "start")];
            for (index, (result, items)) in productions.iter().enumerate() {
                let items = items
                    .iter()
                    .map(|item| match item {
                        0..=2 => nt(&format!("S{item}")),
                        3 => terminal("a"),
                        4 => terminal("b"),
                        5 => terminal("c"),
                        _ => nt("S0"),
                    })
                    .collect();
                sentences.push(production(&format!("S{result}"), items, &format!("p{index}")));
            }
            for (associativity, members) in &groups {
                let tags = members
                    .iter()
                    .filter(|member| **member < productions.len())
                    .map(|member| format!("p{member}"))
                    .collect::<Vec<_>>();
                if tags.is_empty() {
                    continue;
                }
                sentences.push(Sentence::SyntaxAssociativity {
                    associativity: match associativity {
                        0 => crate::definition::Associativity::Left,
                        1 => crate::definition::Associativity::Right,
                        _ => crate::definition::Associativity::NonAssoc,
                    },
                    tags,
                    attributes: Attributes::default(),
                });
            }
            let Ok(grammar) = Grammar::from_sentences(&sentences) else {
                return Ok(());
            };
            pruning_agrees_with_unfiltered_recognition(&grammar, &input)?;
        }

        /// The same with priority declarations and terminals the input may lack: a recognition
        /// that skips the items whose node a priority forbids wherever it could sit, or whose
        /// callers need a token that no longer occurs in the input, keeps every parse and every
        /// error of an unfiltered one.
        #[test]
        fn completion_pruning_matches_unfiltered_recognition_with_priorities(
            productions in prop::collection::vec(
                (0u8..3, prop::collection::vec(0u8..8, 0..5)),
                1..9,
            ),
            levels in prop::collection::btree_map(0usize..9, 0u8..3, 1..7),
            associativity in prop::collection::vec((0u8..4, 0usize..9), 0..3),
            random_input in "[abc ]{0,11}",
            choices in prop::collection::vec(any::<u8>(), 0..24),
        ) {
            let mut sentences = vec![production("Start", vec![nt("S0")], "start")];
            for (index, (result, items)) in productions.iter().enumerate() {
                let items = items
                    .iter()
                    .map(|item| match item {
                        0..=2 => nt(&format!("S{item}")),
                        3 => terminal("a"),
                        4 => terminal("b"),
                        5 => terminal("c"),
                        6 => terminal("d"),
                        _ => nt("S0"),
                    })
                    .collect();
                sentences.push(production(&format!("S{result}"), items, &format!("p{index}")));
            }
            // Most random inputs have no derivation, which the retry explains; a sentence of
            // the grammar, derived by `choices` when they derive one, is what exercises the
            // items skipped from parses that exist.
            let input = derived_sentence(&productions, &choices).unwrap_or(random_input);
            let label = |member: &usize| (*member < productions.len()).then(|| format!("p{member}"));
            // Each production is at most at one level, so the declaration has no cycle.
            let priorities = (0u8..3)
                .map(|level| {
                    levels
                        .iter()
                        .filter(|(_, at)| **at == level)
                        .filter_map(|(member, _)| label(member))
                        .collect::<Vec<_>>()
                })
                .filter(|group| !group.is_empty())
                .collect::<Vec<_>>();
            if priorities.len() >= 2 {
                sentences.push(Sentence::SyntaxPriority {
                    priorities,
                    attributes: Attributes::default(),
                });
            }
            for (associativity, member) in &associativity {
                let Some(tag) = label(member) else {
                    continue;
                };
                sentences.push(Sentence::SyntaxAssociativity {
                    associativity: match associativity {
                        0 => continue,
                        1 => crate::definition::Associativity::Left,
                        2 => crate::definition::Associativity::Right,
                        _ => crate::definition::Associativity::NonAssoc,
                    },
                    tags: vec![tag],
                    attributes: Attributes::default(),
                });
            }
            let Ok(grammar) = Grammar::from_sentences(&sentences) else {
                return Ok(());
            };
            pruning_agrees_with_unfiltered_recognition(&grammar, &input)?;
        }

        /// With the relations ignored, a recognition whose every node is one stand-in node has
        /// the items of the forest-building recognition in every chart, and finds a derivation
        /// of the whole input exactly when it does: a failed parse's explanation reads only
        /// that (`Grammar::explain_violation`).
        #[test]
        fn a_stand_in_recognition_has_the_items_of_the_forest_building_one(
            productions in prop::collection::vec(
                (0u8..3, prop::collection::vec(0u8..7, 0..5)),
                1..9,
            ),
            input in "[abc ]{0,11}",
            filtered in any::<bool>(),
        ) {
            let mut sentences = vec![production("Start", vec![nt("S0")], "start")];
            for (index, (result, items)) in productions.iter().enumerate() {
                let items = items
                    .iter()
                    .map(|item| match item {
                        0..=2 => nt(&format!("S{item}")),
                        3 => terminal("a"),
                        4 => terminal("b"),
                        5 => terminal("c"),
                        _ => nt("S0"),
                    })
                    .collect();
                sentences.push(production(&format!("S{result}"), items, &format!("p{index}")));
            }
            let Ok(grammar) = Grammar::from_sentences(&sentences) else {
                return Ok(());
            };
            if !SameSpanCycles::new(&grammar).is_empty() {
                return Ok(());
            }
            let start_sort = Sort::new("Start");
            let start = grammar.sort_denotations.denote(&start_sort);
            let start_id = grammar.sort_id(start).unwrap();
            let mode = if filtered {
                PredictionMode::Filtered
            } else {
                PredictionMode::Unfiltered
            };
            let stand_in = PackedTerm::leaf(Term::Token {
                token: String::new(),
                sort: Sort::new("K"),
            });
            let recognize = |stand_in: Option<&std::rc::Rc<PackedTerm>>| {
                let mut scanner_cache = vec![None; input.len() + 1];
                let start_position = grammar.canonical_position(&input, 0, &mut scanner_cache);
                grammar.recognize(
                    start_id,
                    start_position,
                    &input,
                    ParseProvenance {
                        source: SourceId(0),
                        base_offset: 0,
                    },
                    mode,
                    PriorityFilter::Ignored,
                    stand_in,
                    false,
                    &mut false,
                    &mut WorkMeter::unlimited(),
                    &mut scanner_cache,
                    &std::cell::RefCell::new(PackedPriorityMemos::default()),
                )
            };
            let items = |recognition: &Recognition| {
                recognition
                    .charts
                    .iter()
                    .map(|chart| chart.states.keys().copied().collect::<BTreeSet<_>>())
                    .collect::<Vec<_>>()
            };
            match (recognize(Some(&stand_in)), recognize(None)) {
                (Ok(stood_in), Ok(built)) => {
                    prop_assert_eq!(items(&stood_in), items(&built));
                    prop_assert_eq!(stood_in.parses.is_empty(), built.parses.is_empty());
                }
                (stood_in, built) => {
                    prop_assert_eq!(stood_in.err(), built.err());
                }
            }
        }

        /// The same in a grammar with productions labelled `#KRewrite`, `#KSequence` or `#let`:
        /// a node of one below an operator is a scope error, which drops the reading at
        /// completion like every other violation, so skipping the items that would build one
        /// loses no parse (`Grammar::boundary_admits`); and an ambiguity prefers its readings
        /// rooted at such a node, which the skipped items must leave unchanged.
        #[test]
        fn completion_pruning_matches_unfiltered_recognition_with_rewrites_sequences_and_lets(
            productions in prop::collection::vec(
                (0u8..3, prop::collection::vec(0u8..8, 0..5)),
                1..9,
            ),
            levels in prop::collection::btree_map(0usize..9, 0u8..3, 1..7),
            associativity in prop::collection::vec((0u8..4, 0usize..9), 0..3),
            scoped in prop::collection::btree_map(0usize..9, 0u8..3, 1..4),
            random_input in "[abc ]{0,11}",
            choices in prop::collection::vec(any::<u8>(), 0..24),
        ) {
            let scoped_label = |index: usize| scoped.get(&index).map(|kind| match kind {
                0 => "#KRewrite",
                1 => "#KSequence",
                _ => "#let",
            });
            let mut sentences = vec![production("Start", vec![nt("S0")], "start")];
            for (index, (result, items)) in productions.iter().enumerate() {
                let items = items
                    .iter()
                    .map(|item| match item {
                        0..=2 => nt(&format!("S{item}")),
                        3 => terminal("a"),
                        4 => terminal("b"),
                        5 => terminal("c"),
                        6 => terminal("d"),
                        _ => nt("S0"),
                    })
                    .collect();
                let label = scoped_label(index).map_or_else(|| format!("p{index}"), str::to_owned);
                sentences.push(production(&format!("S{result}"), items, &label));
            }
            let input = derived_sentence(&productions, &choices).unwrap_or(random_input);
            let label = |member: &usize| (*member < productions.len() && scoped_label(*member).is_none()).then(|| format!("p{member}"));
            let priorities = (0u8..3)
                .map(|level| {
                    levels
                        .iter()
                        .filter(|(_, at)| **at == level)
                        .filter_map(|(member, _)| label(member))
                        .collect::<Vec<_>>()
                })
                .filter(|group| !group.is_empty())
                .collect::<Vec<_>>();
            if priorities.len() >= 2 {
                sentences.push(Sentence::SyntaxPriority {
                    priorities,
                    attributes: Attributes::default(),
                });
            }
            for (associativity, member) in &associativity {
                let Some(tag) = label(member) else {
                    continue;
                };
                sentences.push(Sentence::SyntaxAssociativity {
                    associativity: match associativity {
                        0 => continue,
                        1 => crate::definition::Associativity::Left,
                        2 => crate::definition::Associativity::Right,
                        _ => crate::definition::Associativity::NonAssoc,
                    },
                    tags: vec![tag],
                    attributes: Attributes::default(),
                });
            }
            let Ok(grammar) = Grammar::from_sentences(&sentences) else {
                return Ok(());
            };
            pruning_agrees_with_unfiltered_recognition(&grammar, &input)?;
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

    /// `b a` under `S0 ::= "" | S2 | "" [#KRewrite] | S0 S1 [p6]`, `S1 ::= S1 S0 [p4] | "b"
    /// [p7]`, `S2 ::= "a" | "a"` with `p4 p6 > p7` is derived only as `p6(ε, p4(p7(b), a))`
    /// (and with more empty `S0` in it), so every derivation breaks `p4 > p7` and the input is
    /// grammatical: the error is that violation. A recognition that builds every item also
    /// meets `p6(ε, p7(b))` over `b`, which breaks `p6 > p7` but which no derivation contains
    /// (nothing can follow it with `a`); the explanation's recognition with the relations
    /// ignored meets a same-span repetition (`S1 ::= S1 S0` over an empty `S0`), and the
    /// violation that recognition met first was reported in its place, so the error depended on
    /// which items the recognition skipped. The explanation cuts the repetition and reports the
    /// violation of the input's derivations, whatever was skipped.
    #[test]
    fn a_failed_parse_reports_a_violation_of_a_derivation_of_the_input() {
        let grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("S0")], "start"),
            production("S0", vec![], "p0"),
            production("S0", vec![nt("S2")], "p1"),
            production("S0", vec![], InternalLabel::KRewrite.as_str()),
            production("S2", vec![terminal("a")], "p3"),
            production("S1", vec![nt("S1"), nt("S0")], "p4"),
            production("S2", vec![terminal("a")], "p5"),
            production("S0", vec![nt("S0"), nt("S1")], "p6"),
            production("S1", vec![terminal("b")], "p7"),
            Sentence::SyntaxPriority {
                priorities: vec![
                    vec!["p4".to_owned(), "p6".to_owned()],
                    vec!["p7".to_owned()],
                ],
                attributes: Attributes::default(),
            },
        ])
        .unwrap();
        let expected = Err(ParseError::Priority {
            parent: "p4".to_owned(),
            child: "p7".to_owned(),
        });
        assert_eq!(unfiltered(&grammar, "b a"), expected);
        assert_eq!(
            attempt(
                &grammar,
                "b a",
                PredictionMode::Filtered,
                &mut Pruning::default()
            ),
            expected
        );
        assert_eq!(filtered(&grammar, "b a"), expected);
    }

    /// `a + a * b c` has one derivation, `plus(a, q(a))`, and the left associativity of the
    /// group `plus q` forbids `q` as the right operand of `plus`: the input is grammatical and
    /// the error is that violation. `a + a * b b` has no derivation; the longest prefix of a
    /// sentence is `a + a * b`, which `q` would continue with `c`. The first attempt skips `q`'s
    /// items, whose node the relation forbids where it could sit; the failed parse is then
    /// recognized again for its diagnostic, which must not skip them.
    #[test]
    fn a_failed_parse_reports_the_grammars_violation_or_longest_prefix() {
        let sentences = [
            production("Start", vec![nt("E")], "start"),
            production("E", vec![nt("E"), terminal("+"), nt("F")], "plus"),
            production("E", vec![terminal("a")], "ea"),
            production(
                "E",
                vec![
                    nt("E"),
                    terminal("+"),
                    terminal("a"),
                    terminal("*"),
                    terminal("d"),
                ],
                "other",
            ),
            production("F", vec![terminal("a")], "fa"),
            production(
                "F",
                vec![nt("F"), terminal("*"), terminal("b"), terminal("c")],
                "q",
            ),
            Sentence::SyntaxAssociativity {
                associativity: crate::definition::Associativity::Left,
                tags: vec!["plus".to_owned(), "q".to_owned()],
                attributes: Attributes::default(),
            },
        ];
        let grammar = Grammar::from_sentences(&sentences).unwrap();

        let violation = filtered(&grammar, "a + a * b c");
        assert_eq!(violation, unfiltered(&grammar, "a + a * b c"));
        assert!(
            matches!(
                &violation,
                Err(ParseError::Associativity { parent, child, side })
                    if parent == "plus" && child == "q" && *side == "right"
            ),
            "{violation:?}"
        );

        let no_parse = filtered(&grammar, "a + a * b b");
        assert_eq!(no_parse, unfiltered(&grammar, "a + a * b b"));
        assert!(
            matches!(
                &no_parse,
                Err(ParseError::NoParse { expected, .. }) if **expected == ["\"c\"".to_owned()]
            ),
            "{no_parse:?}"
        );
    }

    /// A same-span cycle is reported when an item the input can continue reaches it, and not
    /// when only items no parse contains do: under `S1 ::= S1 | ""`, the empty input as an
    /// `S1` has infinitely many parses; the empty input as an `S0` whose only route to the
    /// cycle needs an `a` has one; and `caa`, whose only route to the cycle is an item that
    /// cannot be continued by the `a` that follows, has none, and fails where its longest
    /// viable prefix ends.
    #[test]
    fn a_cycle_is_reported_only_where_the_input_can_reach_it() {
        let grammar = |productions: &[(&str, Vec<ProductionItem>)]| {
            let mut sentences = vec![production("Start", vec![nt("S0")], "start")];
            for (index, (result, items)) in productions.iter().enumerate() {
                sentences.push(production(result, items.clone(), &format!("p{index}")));
            }
            Grammar::from_sentences(&sentences).unwrap()
        };

        let in_the_parse = grammar(&[("S0", vec![nt("S0")]), ("S0", vec![])]);
        assert!(matches!(
            filtered(&in_the_parse, ""),
            Err(ParseError::CyclicDerivation(_))
        ));
        assert_eq!(filtered(&in_the_parse, ""), unfiltered(&in_the_parse, ""));

        let behind_a_token = grammar(&[
            ("S1", vec![nt("S2"), terminal("a")]),
            ("S0", vec![nt("S1")]),
            ("S0", vec![]),
            ("S2", vec![nt("S2")]),
            ("S2", vec![]),
        ]);
        assert_eq!(
            filtered(&behind_a_token, "").map(|term| term.to_string()),
            Ok("start(p2(.KList))".to_owned())
        );
        assert!(matches!(
            unfiltered(&behind_a_token, ""),
            Err(ParseError::CyclicDerivation(_))
        ));
        // The same dead cycle beside an ambiguity: the error is the ambiguity of the two empty
        // readings, which the forest decides, not the cycle that no reading of the input contains.
        let ambiguous_beside_it = grammar(&[
            ("S1", vec![nt("S2"), terminal("a")]),
            ("S0", vec![nt("S1")]),
            ("S0", vec![]),
            ("S2", vec![nt("S2")]),
            ("S2", vec![]),
            ("S0", vec![]),
        ]);
        PARSE_ATTEMPTS.set(0);
        let ambiguity = filtered(&ambiguous_beside_it, "");
        assert!(
            matches!(
                &ambiguity,
                Err(ParseError::Ambiguous { alternatives, .. }) if alternatives.len() == 2
            ),
            "{ambiguity:?}"
        );
        assert_eq!(PARSE_ATTEMPTS.get(), 1);
        // The same dead cycle where the input has no derivation: `b` fails at its first
        // character, before which an `a` could come. The failure is recognized again for its
        // diagnostic, making every prediction, which meets the cycle; the cycle is still part of
        // no reading of the input.
        PARSE_ATTEMPTS.set(0);
        let no_parse = filtered(&behind_a_token, "b");
        assert!(
            matches!(
                &no_parse,
                Err(ParseError::NoParse {
                    position: 0,
                    input: NoParseInput::UnrecognizedInput { .. },
                    expected,
                    ..
                }) if expected.contains(&"\"a\"".to_owned())
            ),
            "{no_parse:?}"
        );
        assert_eq!(PARSE_ATTEMPTS.get(), 2);
        // A retry that meets a productive unary cycle still builds its first lap. Under
        // `S1 ::= S3 "a"`, `S3 ::= S2`, `S2 ::= S3 | ""`, the only `S3` over the empty prefix is
        // the one `S3 ::= S2` builds, and it is what lets `S1 ::= S3 "a"` expect the `a`. The
        // first attempt does not predict `S1` before `b`, which no `S1` can begin, and fails
        // there; the retry, which makes every prediction and reads the chart's items, must offer
        // the `a`; the cycle's second lap is the repetition it cuts.
        let unary_cycle_behind_a_token = grammar(&[
            ("S1", vec![nt("S3"), terminal("a")]),
            ("S0", vec![nt("S1")]),
            ("S0", vec![]),
            ("S3", vec![nt("S2")]),
            ("S2", vec![nt("S3")]),
            ("S2", vec![]),
        ]);
        PARSE_ATTEMPTS.set(0);
        let no_parse = filtered(&unary_cycle_behind_a_token, "b");
        assert!(
            matches!(
                &no_parse,
                Err(ParseError::NoParse {
                    position: 0,
                    input: NoParseInput::UnrecognizedInput { .. },
                    expected,
                    ..
                }) if expected.contains(&"\"a\"".to_owned())
            ),
            "{no_parse:?}"
        );
        assert_eq!(PARSE_ATTEMPTS.get(), 2);

        let behind_a_dead_item = grammar(&[
            ("S1", vec![nt("S1")]),
            ("S0", vec![nt("S2"), nt("S2"), nt("S2")]),
            ("S1", vec![]),
            ("S0", vec![terminal("c"), nt("S2"), nt("S1")]),
            ("S2", vec![terminal("a"), nt("S0")]),
            ("S0", vec![]),
        ]);
        let no_parse = filtered(&behind_a_dead_item, "caa");
        assert!(
            matches!(
                &no_parse,
                Err(ParseError::NoParse {
                    position: 3,
                    input: NoParseInput::EndOfInput,
                    ..
                })
            ),
            "{no_parse:?}"
        );
        assert!(matches!(
            unfiltered(&behind_a_dead_item, "caa"),
            Err(ParseError::CyclicDerivation(_))
        ));
    }

    /// In a grammar with a rewrite, a rewrite below an operator is a scope error, which drops
    /// the node holding it at completion like every other violation, and a filtered
    /// recognition skips the items that would build such a node. Under
    /// `S2 ::= "a" | S0 "c" | S2 S0 "c" [#KRewrite]` and `S0 ::= S2 S0 | ""`, `a c c c` is
    /// ambiguous. The report is a function of the readings (the smallest subterm outside which
    /// they all agree, and where they differ), not of how a forest packs them, so the filtered
    /// attempt, the full parse and an unfiltered recognition report the same ambiguity.
    #[test]
    fn an_ambiguity_beside_a_rewrite_below_an_operator_is_reported_by_its_readings() {
        let grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("S0")], "start"),
            production("S1", vec![], "p0"),
            production("S2", vec![terminal("a")], "p1"),
            production("S2", vec![nt("S0"), terminal("c")], "p2"),
            production(
                "S2",
                vec![nt("S2"), nt("S0"), terminal("c")],
                InternalLabel::KRewrite.as_str(),
            ),
            production("S0", vec![nt("S2"), nt("S0")], "p4"),
            production("S0", vec![], "p5"),
        ])
        .unwrap();

        // The readings differ at both children of the root's `S2 S0`, so the whole input is
        // reported, with those two subterms.
        let (start, end) = (100, 107);
        let expected = unfiltered(&grammar, "a c c c");
        assert!(
            matches!(
                &expected,
                Err(ParseError::Ambiguous {
                    alternatives,
                    span: Some(TermSpan {
                        start: reported_start,
                        end: reported_end,
                        ..
                    }),
                    places,
                }) if alternatives.is_empty()
                    && places
                        .iter()
                        .map(|place| place.alternatives.len())
                        .eq([2, 2])
                    && (*reported_start, *reported_end) == (start, end)
            ),
            "{expected:?}"
        );
        let mut pruning = Pruning::default();
        assert_eq!(
            attempt(&grammar, "a c c c", PredictionMode::Filtered, &mut pruning),
            expected
        );
        assert_eq!(filtered(&grammar, "a c c c"), expected);
    }

    /// A reading with a rewrite below an operator denotes nothing, so it is dropped when its
    /// node completes and is no candidate for the preference among the readings of the root.
    /// `Start ::= S` passes its child through, so the readings of `S` are the readings of the
    /// root, among which the preference, once every relation has judged them, keeps those
    /// rooted at a rewrite. `S ::= A "=>" X` is a
    /// rewrite and `S ::= A "=>" Y [imp]` an ordinary production over the same token; `X`
    /// derives only `Q "*" A [times]`, with the nested rewrite `Q ::= A "=>" A` as its first
    /// child, and `times > plus`. In `a => a => a * a + a` the only `X` is
    /// `times(rewrite(a, a), plus(a, a))`, which breaks two relations (the rewrite below
    /// `times`, the sum below `times`) and is dropped, so `S` has no reading rooted at a
    /// rewrite and its one reading, `imp(a, ytail(a, a, plus(a, a)))`, is the parse, whichever
    /// of the two violations is met first.
    #[test]
    fn a_reading_with_a_rewrite_below_an_operator_is_no_candidate_for_the_preference() {
        let grammar = Grammar::from_sentences(&[
            Sentence::Production {
                label: None,
                parameters: vec![],
                sort: Sort::new("Start"),
                items: vec![nt("S")],
                attributes: Attributes::default(),
            },
            production("A", vec![terminal("a")], "atom"),
            production("A", vec![nt("A"), terminal("+"), nt("A")], "plus"),
            production(
                "S",
                vec![nt("A"), terminal("=>"), nt("X")],
                InternalLabel::KRewrite.as_str(),
            ),
            production("S", vec![nt("A"), terminal("=>"), nt("Y")], "imp"),
            production("X", vec![nt("Q"), terminal("*"), nt("A")], "times"),
            production(
                "Q",
                vec![nt("A"), terminal("=>"), nt("A")],
                InternalLabel::KRewrite.as_str(),
            ),
            production(
                "Y",
                vec![nt("A"), terminal("=>"), nt("A"), terminal("*"), nt("A")],
                "ytail",
            ),
            Sentence::SyntaxPriority {
                priorities: vec![vec!["times".to_owned()], vec!["plus".to_owned()]],
                attributes: Attributes::default(),
            },
        ])
        .unwrap();
        let input = "a => a => a * a + a";
        let expected = unfiltered(&grammar, input);
        assert!(
            matches!(&expected, Ok(term) if matches!(
                term.unannotated(),
                Term::Apply { label, .. } if label.name == "imp"
            )),
            "{expected:?}"
        );
        assert_eq!(filtered(&grammar, input), expected);
        pruning_agrees_with_unfiltered_recognition(&grammar, input).unwrap();
    }

    /// An operator whose operands are recognized at a sort that derives the operator's own sort
    /// through an unlabelled production (`R ::= E`, as a rule grammar's `#RuleE ::= E` where
    /// argument positions admit rewrites) holds the operand node itself: that production adds
    /// no node to the forest, so the relations judge the sum at the `+`. Root reachability must
    /// judge it there too, or no partial sum of a left-associative chain is skipped: the
    /// completions grew fourfold with each doubling of the operands (2,552, 10,102 and 40,202 at
    /// 50, 100 and 200), where they now grow in proportion (200, 400 and 800).
    #[test]
    fn a_chain_through_an_operand_that_passes_its_node_through_skips_forbidden_sums() {
        let grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("E")], "start"),
            production("E", vec![nt("R"), terminal("+"), nt("R")], "plus"),
            production("E", vec![terminal("a")], "a"),
            Sentence::Production {
                label: None,
                parameters: vec![],
                sort: Sort::new("R"),
                items: vec![nt("E")],
                attributes: Attributes::default(),
            },
            Sentence::SyntaxAssociativity {
                associativity: crate::definition::Associativity::Left,
                tags: vec!["plus".to_owned()],
                attributes: Attributes::default(),
            },
        ])
        .unwrap();
        let [at_50, at_100, at_200] = [50, 100, 200].map(|length| {
            let input = vec!["a"; length].join(" + ");
            CHART_COMPLETION_CANDIDATES.set(0);
            let parsed = filtered(&grammar, &input);
            assert!(parsed.is_ok(), "{parsed:?}");
            CHART_COMPLETION_CANDIDATES.get()
        });
        println!("{at_50}, {at_100} and {at_200} completions at 50, 100 and 200 operands");
        assert!(
            at_200 - at_100 <= (at_100 - at_50) * 5 / 2,
            "{at_50}, {at_100} and {at_200} completions at 50, 100 and 200 operands"
        );
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
        let error = unfiltered(&grammar, "x").unwrap_err();
        let ParseError::CyclicDerivation(cycle) = &error else {
            panic!("expected a cyclic derivation, got {error:?}");
        };
        assert_eq!(cycle.sort, Sort::new("Cycle"));
        assert_eq!(cycle.productions.len(), 1);
        assert!(cycle.empty.is_empty());
        NONTERMINAL_PREDICTIONS_SKIPPED.set(0);
        PARSE_ATTEMPTS.set(0);
        assert_eq!(filtered(&grammar, "x"), Err(error));
        assert_eq!(NONTERMINAL_PREDICTIONS_SKIPPED.get(), 1);
        assert_eq!(PARSE_ATTEMPTS.get(), 1);
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
        let grammar =
            Grammar::from_program_sentences(&sentences, &catalog, SortDenotations::default())
                .unwrap();
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
        let sentences = [
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
        ];
        let mut grammar = Grammar::from_sentences(&sentences).unwrap();
        // `box(...)` completes the `Int` field through a cast; `Int` is a sort the test sentences
        // give a position, so its casts come from its universe member.
        let visible = sentences.iter().collect::<Vec<_>>();
        let universe = crate::inner::sort_universe::SortUniverse::new(
            &visible,
            &crate::definition::SortSynonyms::of(visible.iter().copied()),
        );
        let int = universe
            .member(&Sort::new("Int"))
            .expect("Int is a sort of the test sentences");
        crate::inner::config::add_casts(
            &mut grammar,
            &crate::inner::sort_universe::CastTarget::member(&int),
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

    /// A production of the pruning proptests' item codes with an optional label and attributes.
    fn coded_production(
        result: u8,
        items: &[u8],
        label: Option<String>,
        attributes: Attributes,
    ) -> Sentence {
        Sentence::Production {
            label: label.map(Label::new),
            parameters: vec![],
            sort: Sort::new(format!("S{result}")),
            items: items
                .iter()
                .map(|item| match item {
                    0..=2 => nt(&format!("S{item}")),
                    3 => terminal("a"),
                    4 => terminal("b"),
                    5 => terminal("c"),
                    6 => terminal("d"),
                    _ => nt("S0"),
                })
                .collect(),
            attributes,
        }
    }

    proptest! {
        /// Class test for the parser-proptest ticket: the pruning proptests above build every
        /// production labelled and attribute-free, so they never reach the shapes the pruning
        /// and the relations treat specially. This one generates, beside the same priorities,
        /// unlabelled pass-throughs (`S1 ::= S2`), `applyPriority` positions, deliberate
        /// duplicates of a production under another label, and associativity groups of several
        /// tags; recognition with pruning must still agree with the unfiltered one.
        #[test]
        fn completion_pruning_matches_unfiltered_recognition_beyond_labelled_productions(
            productions in prop::collection::vec(
                (0u8..3, prop::collection::vec(0u8..8, 0..5)),
                1..9,
            ),
            unlabelled in prop::collection::btree_set(0usize..9, 0..3),
            apply in prop::collection::btree_map(0usize..9, 1u8..3, 0..3),
            duplicates in prop::collection::btree_set(0usize..9, 0..3),
            levels in prop::collection::btree_map(0usize..18, 0u8..3, 1..7),
            associativity in prop::collection::vec(
                (1u8..4, prop::collection::btree_set(0usize..18, 1..3)),
                0..3,
            ),
            random_input in "[abc ]{0,11}",
            choices in prop::collection::vec(any::<u8>(), 0..24),
        ) {
            let mut sentences = vec![production("Start", vec![nt("S0")], "start")];
            // A tag names `p{i}` for production `i < 9` and the duplicate `q{i}` for `9 + i`.
            let mut tags = BTreeSet::new();
            for (index, (result, items)) in productions.iter().enumerate() {
                let pass_through = items.len() == 1 && matches!(items[0], 0..=2 | 7);
                let label = (!(pass_through && unlabelled.contains(&index)))
                    .then(|| format!("p{index}"));
                let attributes = apply.get(&index).map_or_else(Attributes::default, |position| {
                    Attributes::new(std::collections::BTreeMap::from([(
                        "applyPriority".to_owned(),
                        serde_json::json!(position.to_string()),
                    )]))
                });
                if let Some(label) = &label {
                    tags.insert((index, label.clone()));
                }
                sentences.push(coded_production(*result, items, label, attributes.clone()));
                if duplicates.contains(&index) {
                    tags.insert((9 + index, format!("q{index}")));
                    sentences.push(coded_production(
                        *result,
                        items,
                        Some(format!("q{index}")),
                        attributes,
                    ));
                }
            }
            let input = derived_sentence(&productions, &choices).unwrap_or(random_input);
            let tag = |member: &usize| {
                tags.iter()
                    .find(|(index, _)| index == member)
                    .map(|(_, tag)| tag.clone())
            };
            let priorities = (0u8..3)
                .map(|level| {
                    levels
                        .iter()
                        .filter(|(_, at)| **at == level)
                        .filter_map(|(member, _)| tag(member))
                        .collect::<Vec<_>>()
                })
                .filter(|group| !group.is_empty())
                .collect::<Vec<_>>();
            if priorities.len() >= 2 {
                sentences.push(Sentence::SyntaxPriority {
                    priorities,
                    attributes: Attributes::default(),
                });
            }
            for (associativity, members) in &associativity {
                let group = members.iter().filter_map(tag).collect::<Vec<_>>();
                if group.is_empty() {
                    continue;
                }
                sentences.push(Sentence::SyntaxAssociativity {
                    associativity: match associativity {
                        1 => crate::definition::Associativity::Left,
                        2 => crate::definition::Associativity::Right,
                        _ => crate::definition::Associativity::NonAssoc,
                    },
                    tags: group,
                    attributes: Attributes::default(),
                });
            }
            let Ok(grammar) = Grammar::from_sentences(&sentences) else {
                return Ok(());
            };
            pruning_agrees_with_unfiltered_recognition(&grammar, &input)?;
        }
    }

    /// The operator grammar of the end-position tests: `F ::= a | F "+" F [plus]` (and the
    /// duplicate `plustwo` when asked), `E ::= F` without a label, which builds no node, and
    /// `E ::= <left> "#" E [hash]`, with `applyPriority(2)` when asked, under
    /// `syntax right hash plus`. With `left` = `E` a sum reaches `hash`'s left position through
    /// the pass-through; with `left` = `F` it is there directly. Both derive the same trees for
    /// `a + a # a`.
    fn end_position_grammar(left: &str, apply_priority: bool, plustwo: bool) -> Grammar {
        let mut sentences = vec![
            production("Start", vec![nt("E")], "start"),
            production("F", vec![terminal("a")], "fa"),
            production("F", vec![nt("F"), terminal("+"), nt("F")], "plus"),
            Sentence::Production {
                label: None,
                parameters: vec![],
                sort: Sort::new("E"),
                items: vec![nt("F")],
                attributes: Attributes::default(),
            },
            Sentence::Production {
                label: Some(Label::new("hash")),
                parameters: vec![],
                sort: Sort::new("E"),
                items: vec![nt(left), terminal("#"), nt("E")],
                attributes: if apply_priority {
                    Attributes::new(std::collections::BTreeMap::from([(
                        "applyPriority".to_owned(),
                        serde_json::json!("2"),
                    )]))
                } else {
                    Attributes::default()
                },
            },
            Sentence::SyntaxAssociativity {
                associativity: crate::definition::Associativity::Right,
                tags: vec!["hash".into(), "plus".into()],
                attributes: Attributes::default(),
            },
        ];
        if plustwo {
            sentences.push(production(
                "F",
                vec![nt("F"), terminal("+"), nt("F")],
                "plustwo",
            ));
        }
        Grammar::from_sentences(&sentences).unwrap()
    }

    /// A parse result as the end-position tests compare it: the term, the readings of an
    /// ambiguity, or a rejection.
    fn parse_outcome(result: Result<Term, ParseError>) -> String {
        match result {
            Ok(term) => term.to_string(),
            Err(ParseError::Ambiguous { alternatives, .. }) => format!(
                "ambiguous {:?}",
                alternatives
                    .into_iter()
                    .map(|alternative| alternative.term)
                    .collect::<BTreeSet<_>>()
            ),
            Err(_) => "rejected".to_owned(),
        }
    }

    /// The pruned recognition agrees with the unfiltered one where a sum and its duplicate
    /// reach `hash`'s left position through an unlabelled pass-through, which packs them into
    /// one node set before `hash` holds it.
    #[test]
    fn pruning_agrees_with_unfiltered_recognition_through_an_unlabelled_pass_through() {
        let grammar = end_position_grammar("E", true, true);
        pruning_agrees_with_unfiltered_recognition(&grammar, "a + a # a").unwrap();
    }

    /// An unlabelled pass-through builds no node, so the grammars with `hash`'s left operand
    /// written `E` (through `E ::= F`) and written `F` derive the same trees for `a + a # a`,
    /// and a parse is a function of the trees the grammar derives: each of the pruned and the
    /// unfiltered parser gives both grammars one outcome, the same term or the same rejection.
    /// Whether a reading is accepted must not depend on which other readings it is packed with.
    #[test]
    fn a_pass_through_that_builds_no_node_does_not_change_the_parse() {
        let mut failures = Vec::new();
        for plustwo in [true, false] {
            let a = end_position_grammar("E", true, plustwo);
            let b = end_position_grammar("F", true, plustwo);
            for (mode, parse) in [
                (
                    "pruned",
                    filtered as fn(&Grammar, &str) -> Result<Term, ParseError>,
                ),
                ("unfiltered", unfiltered),
            ] {
                let (in_a, in_b) = (
                    parse_outcome(parse(&a, "a + a # a")),
                    parse_outcome(parse(&b, "a + a # a")),
                );
                if in_a != in_b {
                    failures.push(format!(
                        "plustwo {plustwo}, {mode}: through E {in_a}, directly {in_b}"
                    ));
                }
            }
        }
        assert!(failures.is_empty(), "{failures:#?}");
    }

    /// Associativity is judged at the positions priority is judged at: a node's
    /// `applyPriority` names the child positions the relations check, and associativity, which
    /// applies only at the two ends, is checked at an end only when that end is named. So
    /// under `applyPriority(2)` the sum is admitted as `hash`'s left child (and, with the
    /// duplicate `plustwo`, the two sums are two readings), whether it reaches that position
    /// through a pass-through or directly; without the attribute both ends are checked, `right`
    /// forbids the sum on the left, and only the duplicate outside the group is left.
    #[test]
    fn associativity_is_judged_at_the_positions_apply_priority_names() {
        let both = r#"ambiguous {"plus(fa(.KList),fa(.KList))", "plustwo(fa(.KList),fa(.KList))"}"#;
        let plus = "start(hash(plus(fa(.KList),fa(.KList)),fa(.KList)))";
        let cases = [
            ("E", true, true, both),
            ("F", true, true, both),
            ("E", true, false, plus),
            ("F", true, false, plus),
            (
                "F",
                false,
                true,
                "start(hash(plustwo(fa(.KList),fa(.KList)),fa(.KList)))",
            ),
            ("F", false, false, "rejected"),
        ];
        let mut failures = Vec::new();
        for (left, apply_priority, plustwo, expected) in cases {
            let grammar = end_position_grammar(left, apply_priority, plustwo);
            for (mode, parse) in [
                (
                    "pruned",
                    filtered as fn(&Grammar, &str) -> Result<Term, ParseError>,
                ),
                ("unfiltered", unfiltered),
            ] {
                let outcome = parse_outcome(parse(&grammar, "a + a # a"));
                if outcome != expected {
                    failures.push(format!(
                        "{left}, applyPriority {apply_priority}, plustwo {plustwo}, {mode}: \
                         {outcome}"
                    ));
                }
            }
        }
        assert!(failures.is_empty(), "{failures:#?}");
    }

    /// A labelled syntactic subsort (one nonterminal, no terminal) builds a node that the
    /// relation filter judges by its own label, but the filter checks no child below it. So
    /// `wrap` admits a sum below it even though `syntax right wrap plus` would forbid the sum as
    /// its left child at a checked position, in the pruned and the unfiltered parser alike.
    #[test]
    fn a_labelled_syntactic_subsort_judges_no_child() {
        let grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("E")], "start"),
            production("F", vec![terminal("a")], "fa"),
            production("F", vec![nt("F"), terminal("+"), nt("F")], "plus"),
            production("E", vec![nt("F")], "wrap"),
            Sentence::SyntaxAssociativity {
                associativity: crate::definition::Associativity::Right,
                tags: vec!["wrap".into(), "plus".into()],
                attributes: Attributes::default(),
            },
        ])
        .unwrap();
        pruning_agrees_with_unfiltered_recognition(&grammar, "a + a").unwrap();
        assert_eq!(
            parse_outcome(filtered(&grammar, "a + a")),
            "start(wrap(plus(fa(.KList),fa(.KList))))"
        );
    }

    /// One operator of the structured generator's grammars ([`operator_grammar`]), as
    /// `(result, form, left, right, token, applyPriority, duplicate, scope)`:
    /// - `result`, `left`, `right` pick `S0` or `S1` for the result and the operands;
    /// - `form` 0 is infix (`left token right`), 1 prefix (`token right`), 2 postfix
    ///   (`left token`), 3 a labelled unary production `S1 ::= S0`, 4 a circumfix
    ///   (`"[" left "]"`), whose operand is not at an end, so that a rewrite or sequence may
    ///   stand below it unless its `applyPriority` names that operand;
    /// - `token` picks one of `+ * # -`;
    /// - `applyPriority` 1 or 2 names that one position of an infix operator, 0 none;
    /// - `duplicate` adds the same items under another label;
    /// - `scope` 1 makes an infix operator a rewrite (`=>`, labelled `#KRewrite`), 2 a
    ///   sequence (`~>`, labelled `#KSequence`), 0 neither.
    type GeneratedOperator = (u8, u8, u8, u8, u8, u8, bool, u8);

    const OPERATOR_TOKENS: [&str; 4] = ["+", "*", "#", "-"];

    /// The items of a generated operator, and the tokens of the language it is part of.
    fn operator_items(operator: &GeneratedOperator) -> Vec<ProductionItem> {
        let &(_, form, left, right, token, _, _, scope) = operator;
        let operand = |sort: u8| nt(&format!("S{}", sort % 2));
        let token = match scope {
            1 => "=>",
            2 => "~>",
            _ => OPERATOR_TOKENS[usize::from(token % 4)],
        };
        match (form % 5, scope) {
            (_, 1 | 2) | (0, _) => vec![operand(left), terminal(token), operand(right)],
            (1, _) => vec![terminal(token), operand(right)],
            (2, _) => vec![operand(left), terminal(token)],
            (4, _) => vec![terminal("["), operand(left), terminal("]")],
            _ => vec![nt("S0")],
        }
    }

    fn operator_result(operator: &GeneratedOperator) -> String {
        let &(result, form, _, _, _, _, _, scope) = operator;
        if form % 5 == 3 && scope == 0 {
            // A unary production in the direction of `S1 ::= S0`, so that it closes no cycle.
            "S1".to_owned()
        } else {
            format!("S{}", result % 2)
        }
    }

    /// The label of operator `index`, or of its duplicate.
    fn operator_label(operators: &[GeneratedOperator], index: usize, duplicate: bool) -> String {
        match (operators[index].7, duplicate) {
            (1, false) => InternalLabel::KRewrite.as_str().to_owned(),
            (2, false) => InternalLabel::KSequence.as_str().to_owned(),
            (_, false) => format!("o{index}"),
            (_, true) => format!("d{index}"),
        }
    }

    /// The structured generator's operator grammar: `Start ::= S1`, labelled `start` when
    /// `labelled_start` (so that the parse's root is that node) and else a pass-through (so
    /// that the parse is rooted at its sentence's own root, as a rule body is), `S1 ::= S0`
    /// without a label, `S0 ::= "a"`, the operators, their duplicates, and the priorities and
    /// associativity groups over the operators' labels (`levels` and `groups` name operator
    /// `i` as `i` and its duplicate as `i + operators.len()`, modulo twice that length). With `inlined` = `(i, k)`, the
    /// `k`-th nonterminal of operator `i` is written through a fresh sort `P` whose only
    /// production is the unlabelled `P ::= S`: a pass-through, which builds no node, so the
    /// grammar derives the same trees as without it.
    fn operator_grammar(
        operators: &[GeneratedOperator],
        levels: &BTreeMap<usize, u8>,
        groups: &[(u8, BTreeSet<usize>)],
        labelled_start: bool,
        inlined: Option<(usize, usize)>,
    ) -> Option<Grammar> {
        let start = if labelled_start {
            production("Start", vec![nt("S1")], "start")
        } else {
            Sentence::Production {
                label: None,
                parameters: vec![],
                sort: Sort::new("Start"),
                items: vec![nt("S1")],
                attributes: Attributes::default(),
            }
        };
        let mut sentences = vec![
            start,
            production("S0", vec![terminal("a")], "atom"),
            Sentence::Production {
                label: None,
                parameters: vec![],
                sort: Sort::new("S1"),
                items: vec![nt("S0")],
                attributes: Attributes::default(),
            },
        ];
        let count = operators.len();
        let mut tags = BTreeMap::new();
        for (index, operator) in operators.iter().enumerate() {
            let mut items = operator_items(operator);
            if let Some((at, position)) = inlined
                && at == index
            {
                let slot = items
                    .iter_mut()
                    .filter(|item| matches!(item, ProductionItem::NonTerminal { .. }))
                    .nth(position)?;
                let ProductionItem::NonTerminal { sort, .. } = slot else {
                    unreachable!("a nonterminal was selected")
                };
                sentences.push(Sentence::Production {
                    label: None,
                    parameters: vec![],
                    sort: Sort::new("P"),
                    items: vec![nt(&sort.name)],
                    attributes: Attributes::default(),
                });
                *slot = nt("P");
            }
            let attributes = match (operator.5 % 3, items.len()) {
                (position @ 1..=2, 3) => Attributes::new(BTreeMap::from([(
                    "applyPriority".to_owned(),
                    serde_json::json!(position.to_string()),
                )])),
                _ => Attributes::default(),
            };
            let label = operator_label(operators, index, false);
            tags.insert(index, label.clone());
            sentences.push(Sentence::Production {
                label: Some(Label::new(label)),
                parameters: vec![],
                sort: Sort::new(operator_result(operator)),
                items: items.clone(),
                attributes: attributes.clone(),
            });
            if operator.6 && operator.7 == 0 {
                let label = operator_label(operators, index, true);
                tags.insert(count + index, label.clone());
                sentences.push(Sentence::Production {
                    label: Some(Label::new(label)),
                    parameters: vec![],
                    sort: Sort::new(operator_result(operator)),
                    items,
                    attributes,
                });
            }
        }
        // A member index names a tag modulo the number of tags an operator and its duplicate
        // can have, so that the relations hold the grammar's operators whatever their count.
        let member = |index: &usize| tags.get(&(index % (2 * count))).cloned();
        let mut leveled = BTreeMap::new();
        for (index, level) in levels {
            if let Some(tag) = member(index) {
                leveled.entry(tag).or_insert(*level);
            }
        }
        let priorities = (0u8..3)
            .map(|level| {
                leveled
                    .iter()
                    .filter(|(_, at)| **at == level)
                    .map(|(tag, _)| tag.clone())
                    .collect::<Vec<_>>()
            })
            .filter(|group| !group.is_empty())
            .collect::<Vec<_>>();
        if priorities.len() >= 2 {
            sentences.push(Sentence::SyntaxPriority {
                priorities,
                attributes: Attributes::default(),
            });
        }
        for (associativity, members) in groups {
            let group = members
                .iter()
                .filter_map(member)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            if group.is_empty() {
                continue;
            }
            sentences.push(Sentence::SyntaxAssociativity {
                associativity: match associativity % 3 {
                    0 => crate::definition::Associativity::Left,
                    1 => crate::definition::Associativity::Right,
                    _ => crate::definition::Associativity::NonAssoc,
                },
                tags: group,
                attributes: Attributes::default(),
            });
        }
        Grammar::from_sentences(&sentences).ok()
    }

    /// A sentence of an operator grammar, derived from `S1` by taking, at each nonterminal in
    /// order, the alternative `choices` names next; `None` when the choices run out first.
    fn operator_sentence(operators: &[GeneratedOperator], choices: &[u8]) -> Option<String> {
        let mut choices = choices.iter();
        let mut pending = vec![nt("S1")];
        let mut sentence = Vec::new();
        // Invariant: `pending` holds, last first, the items still to expand.
        while let Some(item) = pending.pop() {
            match item {
                ProductionItem::NonTerminal { sort, .. } => {
                    let mut alternatives = operators
                        .iter()
                        .filter(|operator| operator_result(operator) == sort.name)
                        .map(operator_items)
                        .collect::<Vec<_>>();
                    alternatives.push(if sort.name == "S0" {
                        vec![terminal("a")]
                    } else {
                        vec![nt("S0")]
                    });
                    let choice = usize::from(*choices.next()?) % alternatives.len();
                    pending.extend(alternatives.swap_remove(choice).into_iter().rev());
                }
                ProductionItem::Terminal(text) => sentence.push(text),
                ProductionItem::RegexTerminal { .. } => unreachable!("operators have no regex"),
            }
        }
        Some(sentence.join(" "))
    }

    /// The cases of the structured generator: enough that a run finds the defect of judging
    /// associativity at an end `applyPriority` leaves unjudged, the shape the generator was
    /// built to reach (`a + a + a` under a non-associative `S0 ::= S0 "+" S0
    /// [applyPriority(1)]`). With that defect seeded and no saved failure, 20 of 20 seeded runs
    /// found it at this count, 19 at half of it and 11 at an eighth.
    const OPERATOR_GRAMMAR_CASES: u32 = 2048;

    /// The parse of `input` by an operator grammar and by its pass-through pair, the same
    /// grammar with the operand `inlined` = `(i, k)` written through `P ::= S`
    /// ([`operator_grammar`]); `None` when either grammar is not built.
    ///
    /// In each grammar the pruned recognition agrees with the unfiltered one. The pass-through
    /// builds no node, so both grammars derive the same trees under the same labels, priorities
    /// and associativity, and where operator `i` has a label of its own nothing else the parse
    /// reads differs: then the two grammars give one outcome, pruned and unfiltered, the term
    /// or the whole error. An error names productions by their text, which in the pair writes
    /// `P` for the operand's own sort; it is compared with that sort written back. Two rewrite
    /// or two sequence operators share one label: they are overloads, which the overload filter
    /// orders by their argument sorts, and `P ::= S` makes `P` a supersort of `S` and not a
    /// subsort, so writing an operand of an overload through it can change that order and with
    /// it the parse; such a pair is not the same grammar and is not compared. The outcome is
    /// returned as [`parse_outcome`] writes it.
    fn pass_through_pair_outcome(
        operators: &[GeneratedOperator],
        levels: &BTreeMap<usize, u8>,
        groups: &[(u8, BTreeSet<usize>)],
        labelled_start: bool,
        inlined: (usize, usize),
        input: &str,
    ) -> Result<Option<String>, TestCaseError> {
        let Some(original) = operator_grammar(operators, levels, groups, labelled_start, None)
        else {
            return Ok(None);
        };
        let Some(passed) =
            operator_grammar(operators, levels, groups, labelled_start, Some(inlined))
        else {
            return Ok(None);
        };
        pruning_agrees_with_unfiltered_recognition(&original, input)?;
        pruning_agrees_with_unfiltered_recognition(&passed, input)?;
        let (at, position) = inlined;
        let scope = operators[at].7;
        let overloaded = scope != 0
            && operators
                .iter()
                .filter(|operator| operator.7 == scope)
                .count()
                > 1;
        if !overloaded {
            let operand = operator_items(&operators[at])
                .into_iter()
                .filter_map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => Some(sort.name.clone()),
                    _ => None,
                })
                .nth(position)
                .expect("the pair was built, so the operand exists");
            let pass_through_sort = regex::Regex::new(r"\bP\b").expect("a valid pattern");
            // A failure without a derivation names the sorts expected where it stops, as a set;
            // `P` is expected exactly where its operand's sort is, so written back it names
            // nothing more.
            let outcome = |result: Result<Term, ParseError>, pair: bool| {
                let text = match result {
                    Ok(term) => term.to_string(),
                    Err(ParseError::NoParse {
                        position,
                        expected,
                        input,
                        previous,
                        notes,
                        span,
                        work_limit,
                    }) => {
                        let expected = expected
                            .iter()
                            .map(|name| if pair && name == "P" { &operand } else { name })
                            .collect::<BTreeSet<_>>();
                        format!(
                            "NoParse {position} {expected:?} {input:?} {previous:?} {notes:?} {span:?} {work_limit:?}"
                        )
                    }
                    Err(error) => format!("{error:?}"),
                };
                if pair {
                    pass_through_sort
                        .replace_all(&text, operand.as_str())
                        .into_owned()
                } else {
                    text
                }
            };
            // A build without Z3 declines to type an ambiguous forest outside its decision
            // (`Z3InferenceRequired`: too many trees, or no greatest typing), which is no
            // outcome of the parse. `P` is a sort of its own, so the forest the pair hands to
            // sort inference can differ in those respects where the readings are the same; such
            // a pair is not compared.
            let declined = |result: &Result<Term, ParseError>| {
                matches!(result, Err(ParseError::Z3InferenceRequired { .. }))
            };
            for (mode, recognize) in [
                (
                    "pruned",
                    filtered as fn(&Grammar, &str) -> Result<Term, ParseError>,
                ),
                ("unfiltered", unfiltered),
            ] {
                let (pair, single) = (recognize(&passed, input), recognize(&original, input));
                if !declined(&pair) && !declined(&single) {
                    prop_assert_eq!(outcome(pair, true), outcome(single, false), "{}", mode);
                }
            }
        }
        Ok(Some(parse_outcome(filtered(&original, input))))
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(OPERATOR_GRAMMAR_CASES))]

        /// The structured pruning generator: an operator grammar (infix, prefix and postfix
        /// operators over two sorts, labelled unary productions, circumfix productions,
        /// duplicates of an operator under another label, `applyPriority` naming one operand,
        /// priorities, associativity groups, and rewrites and sequences, which are scope errors
        /// at an end of an operator and may stand inside a circumfix, below the parse's root,
        /// where the choice of the rewrite or sequence reading is made as at the root), with a
        /// labelled start production or a pass-through one, and its metamorphic pair, the same grammar
        /// with one operand of one operator written through an unlabelled pass-through
        /// (`P ::= S`): both parse alike and prune alike ([`pass_through_pair_outcome`]). The
        /// input is a sentence of the grammar when `choices` derive one; with two rewrite or
        /// sequence operators it can hold two or more of their tokens. The choices are few
        /// enough that a sentence has a handful of operators: under duplicates and labelled
        /// unary productions a longer one has exponentially many readings, which the tree
        /// sort inference reads copies out (`docs/compatibility.md`, the ambiguity report): with
        /// up to 24 choices, single cases of five to nine operators took from seconds to over
        /// two minutes.
        #[test]
        fn an_operator_grammar_and_its_pass_through_pair_parse_alike(
            operators in prop::collection::vec(
                (0u8..2, 0u8..5, 0u8..2, 0u8..2, 0u8..4, 0u8..3, any::<bool>(), 0u8..3),
                1..6,
            ),
            levels in prop::collection::btree_map(0usize..12, 0u8..3, 0..6),
            groups in prop::collection::vec(
                (0u8..3, prop::collection::btree_set(0usize..12, 1..4)),
                0..3,
            ),
            labelled_start in any::<bool>(),
            inlined in (any::<prop::sample::Index>(), 0usize..2),
            choices in prop::collection::vec(any::<u8>(), 0..12),
            random_input in prop::collection::vec(0usize..9, 0..9),
        ) {
            let tokens = ["a", "+", "*", "#", "-", "=>", "~>", "[", "]"];
            let input = operator_sentence(&operators, &choices).unwrap_or_else(|| {
                random_input
                    .iter()
                    .map(|token| tokens[*token])
                    .collect::<Vec<_>>()
                    .join(" ")
            });
            let at = inlined.0.index(operators.len());
            pass_through_pair_outcome(
                &operators,
                &levels,
                &groups,
                labelled_start,
                (at, inlined.1),
                &input,
            )?;
        }
    }

    /// Under `S0 ::= "+" S1 [o2]` and `S1 ::= S0 [o0]`, non-associative together, with
    /// `S1 ::= S0` also a pass-through, every reading of `+ + a` breaks `o2`'s right edge,
    /// below it `o0` or `o2`. Writing `o0`'s operand through `P ::= S0` numbers the productions
    /// differently and changes no tree, so it changes no reported violation either
    /// (`canonical_packed_error`).
    #[test]
    fn a_reported_violation_does_not_depend_on_a_pass_through_renumbering_productions() {
        let operators: Vec<GeneratedOperator> = vec![
            (0, 3, 0, 0, 0, 0, false, 0),
            (1, 0, 0, 0, 0, 0, false, 0),
            (0, 1, 0, 1, 0, 0, false, 0),
            (0, 0, 0, 0, 0, 0, false, 0),
            (1, 0, 0, 0, 0, 0, false, 0),
        ];
        let groups = [(2, BTreeSet::from([2, 10]))];
        pass_through_pair_outcome(
            &operators,
            &BTreeMap::new(),
            &groups,
            false,
            (0, 0),
            "+ + a",
        )
        .unwrap();
        let original =
            operator_grammar(&operators, &BTreeMap::new(), &groups, false, None).unwrap();
        assert_eq!(
            filtered(&original, "+ + a"),
            Err(ParseError::Associativity {
                parent: "o2".to_owned(),
                child: "o0".to_owned(),
                side: "right",
            })
        );
    }

    /// Under `S0 ::= S0 "=>" S1` (a rewrite), `S1 ::= "+" S0 [o3]` and three sequences
    /// (`S0 ::= S0 "~>" S0`, `S0 ::= S0 "~>" S1`, `S1 ::= S1 "~>" S1`), every reading of
    /// `+ a => a ~> + a` puts a rewrite or a sequence below `o3`. Writing the rewrite's right
    /// operand through `P ::= S1` changes no tree, and the same scope error is reported.
    #[test]
    fn a_reported_scope_error_does_not_depend_on_a_pass_through_below_a_rewrite() {
        let operators: Vec<GeneratedOperator> = vec![
            (0, 0, 0, 0, 0, 0, false, 2),
            (0, 0, 0, 1, 0, 0, false, 1),
            (0, 0, 0, 1, 0, 0, false, 2),
            (1, 1, 0, 0, 0, 0, false, 0),
            (1, 0, 1, 1, 0, 0, false, 2),
        ];
        let input = "+ a => a ~> + a";
        pass_through_pair_outcome(&operators, &BTreeMap::new(), &[], false, (1, 1), input).unwrap();
        let original = operator_grammar(&operators, &BTreeMap::new(), &[], false, None).unwrap();
        assert_eq!(
            filtered(&original, input),
            Err(ParseError::Scope {
                parent: "o3".to_owned(),
                child: InternalLabel::KRewrite.as_str().to_owned(),
            })
        );
    }

    /// Under `S1 ::= S1 "~>" S0` (a sequence) and `S1 ::= S0 "+" S1 [applyPriority(1)]`,
    /// `a + a ~> a ~> a` has three readings: sequences of three items and of two, and a sum
    /// whose right operand, which `applyPriority(1)` leaves unjudged, is a sequence. Below the
    /// labelled start the sequence is chosen over the sum; then the outer sequence's left
    /// operand, `a + a ~> a`, is a sequence or a sum, and the sequence is chosen there too
    /// ([`Grammar::prefer_structural_readings`]). With the sequence's left operand written
    /// through `P ::= S1` the trees are the same, and so is the choice.
    #[test]
    fn an_ambiguity_report_does_not_depend_on_a_pass_through_below_a_sequence() {
        let operators: Vec<GeneratedOperator> =
            vec![(1, 0, 1, 0, 0, 0, false, 2), (1, 0, 0, 1, 0, 1, false, 0)];
        let outcome = pass_through_pair_outcome(
            &operators,
            &BTreeMap::new(),
            &[],
            true,
            (0, 0),
            "a + a ~> a ~> a",
        )
        .unwrap();
        assert_eq!(
            outcome.as_deref(),
            Some("start(o1(atom(.KList),atom(.KList))~>atom(.KList)~>atom(.KList))")
        );
    }

    /// Under `S0 ::= S0 "=>" S1` (a rewrite), `S1 ::= S0 [o1]`, `S1 ::= S0 [o2]` and
    /// `S1 ::= S1 "+" S0 [o3]`, `a => a => a + a` has readings rooted at the rewrite and at
    /// `o1`, `o2` and `o3` (`o3(o1(a => a => a), a)`: `o1` and `o2`, syntactic subsorts, judge no
    /// child). Below the labelled start the readings rooted at the rewrite are chosen; they
    /// split the text at either `=>`, so they share no position below the root and stay an
    /// ambiguity, reported at the places they differ. Below the rewrite, at the right side of
    /// `a => (a => a + a)`, the inner rewrite read through the unlabelled pass-through ranks
    /// after its readings through `o1` and `o2`, which are rooted at those labels. Writing
    /// `o3`'s left operand through `P ::= S1` changes no tree and no entry of the report.
    #[test]
    fn an_ambiguity_report_does_not_depend_on_a_pass_through_above_a_rewrite() {
        let operators: Vec<GeneratedOperator> = vec![
            (0, 0, 0, 1, 0, 0, false, 1),
            (0, 3, 0, 0, 0, 0, false, 0),
            (0, 3, 0, 0, 0, 0, false, 0),
            (1, 0, 1, 0, 0, 0, false, 0),
        ];
        let outcome = pass_through_pair_outcome(
            &operators,
            &BTreeMap::new(),
            &[],
            true,
            (3, 0),
            "a => a => a + a",
        )
        .unwrap();
        assert_eq!(outcome.as_deref(), Some("ambiguous {}"));
        let original = operator_grammar(&operators, &BTreeMap::new(), &[], true, None).unwrap();
        let Err(ParseError::Ambiguous { places, .. }) = filtered(&original, "a => a => a + a")
        else {
            panic!("`a => a => a + a` has two rewrite readings");
        };
        let terms = places
            .iter()
            .map(|place| {
                place
                    .alternatives
                    .iter()
                    .map(|entry| entry.term.as_str())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            terms,
            [
                vec!["atom(.KList)=>atom(.KList)", "atom(.KList)"],
                vec![
                    "o1(atom(.KList)=>o3(atom(.KList),atom(.KList)))",
                    "o2(atom(.KList)=>o3(atom(.KList),atom(.KList)))",
                    "o3(atom(.KList),atom(.KList))"
                ],
            ]
        );
    }

    /// Under `S1 ::= S1 "+" S1 [o0]`, `S0 ::= S0 "=>" S0` (a rewrite) and `S1 ::= S0 [o2]`,
    /// the rewrite of `a => a + a` cannot stand directly below `o0`, a scope error, but it can
    /// below `o2`, a syntactic subsort, which judges no child. Two readings are left,
    /// `o0(o2(a => a), a)` and `o0(o2(a => a), o2(a))`, which differ at the last `a` only, and
    /// both grammars report that ambiguity, with `o0`'s left operand written through `P ::= S1`
    /// or not.
    #[test]
    fn a_rejection_does_not_depend_on_a_pass_through_above_a_rewrite() {
        let operators: Vec<GeneratedOperator> = vec![
            (1, 0, 1, 1, 0, 0, false, 0),
            (0, 0, 0, 0, 0, 0, false, 1),
            (0, 3, 0, 0, 0, 0, false, 0),
        ];
        let outcome = pass_through_pair_outcome(
            &operators,
            &BTreeMap::new(),
            &[],
            true,
            (0, 0),
            "a => a + a",
        )
        .unwrap();
        assert_eq!(
            outcome.as_deref(),
            Some(r#"ambiguous {"atom(.KList)", "o2(atom(.KList))"}"#)
        );
    }

    /// Under `S0 ::= S0 "=>" S0` (a rewrite) and `S0 ::= S0 "~>" S0 [applyPriority(2)]` (a
    /// sequence, whose left operand is unjudged), `a => a ~> a` has two readings, the rewrite of
    /// `a` to `a ~> a` and the sequence of `a => a` and `a`. The reading rooted at the rewrite is
    /// chosen ([`Grammar::prefer_structural_readings`]), whether the parse is rooted at the
    /// sentence (a pass-through start production, as a rule body is) or the sentence is the
    /// operand of a labelled start production, below the parse's root. The choice is made per
    /// tree, so writing the rewrite's right operand through `P ::= S0` changes neither.
    #[test]
    fn a_rewrite_reading_does_not_depend_on_a_pass_through_at_its_operand() {
        let operators: Vec<GeneratedOperator> =
            vec![(0, 0, 0, 0, 0, 0, false, 1), (0, 0, 0, 0, 0, 2, false, 2)];
        let outcome = |labelled_start| {
            pass_through_pair_outcome(
                &operators,
                &BTreeMap::new(),
                &[],
                labelled_start,
                (0, 1),
                "a => a ~> a",
            )
            .unwrap()
        };
        assert_eq!(
            outcome(false).as_deref(),
            Some("atom(.KList)=>atom(.KList)~>atom(.KList)")
        );
        assert_eq!(
            outcome(true).as_deref(),
            Some("start(atom(.KList)=>atom(.KList)~>atom(.KList))")
        );
    }

    /// Inside a circumfix `S0 ::= "[" S0 "]" [o0]`, whose operand is not at an end, a rewrite and
    /// a sequence may stand, so `[ a => a ~> a ]` has the same two readings as `a => a ~> a`
    /// below `o0`, and the reading rooted at the rewrite is chosen there, below the parse's root.
    /// Writing the circumfix's operand through `P ::= S0` puts a pass-through above both readings
    /// and changes nothing.
    #[test]
    fn a_rewrite_reading_below_the_root_does_not_depend_on_a_pass_through_above_it() {
        let operators: Vec<GeneratedOperator> = vec![
            (0, 4, 0, 0, 0, 0, false, 0),
            (0, 0, 0, 0, 0, 0, false, 1),
            (0, 0, 0, 0, 0, 2, false, 2),
        ];
        for labelled_start in [false, true] {
            let outcome = pass_through_pair_outcome(
                &operators,
                &BTreeMap::new(),
                &[],
                labelled_start,
                (0, 0),
                "[ a => a ~> a ]",
            )
            .unwrap();
            let expected = "o0(atom(.KList)=>atom(.KList)~>atom(.KList))";
            let expected = if labelled_start {
                format!("start({expected})")
            } else {
                expected.to_owned()
            };
            assert_eq!(outcome.as_deref(), Some(expected.as_str()));
        }
    }

    /// Two rewrites of one label, `S0 ::= S0 "=>" S1` and `S0 ::= S1 "=>" S0`, beside
    /// `S1 ::= S0 [o0]`: in `a => a => a`, each `a => a` is the one term `a => a` built by either
    /// rewrite, and the report's entry for it names the production of the least text, whatever
    /// order the forest lists the two in, so writing `o0`'s operand through `P ::= S0` changes
    /// no entry.
    #[test]
    fn an_ambiguity_entry_names_one_production_of_overloads_building_one_term() {
        let operators: Vec<GeneratedOperator> = vec![
            (0, 3, 0, 0, 0, 0, false, 0),
            (0, 0, 0, 1, 0, 0, false, 1),
            (0, 0, 1, 0, 0, 0, false, 1),
        ];
        let outcome = pass_through_pair_outcome(
            &operators,
            &BTreeMap::new(),
            &[],
            false,
            (0, 0),
            "a => a => a",
        )
        .unwrap();
        assert_eq!(outcome.as_deref(), Some("ambiguous {}"));
        let original = operator_grammar(&operators, &BTreeMap::new(), &[], false, None).unwrap();
        let Err(ParseError::Ambiguous { places, .. }) = filtered(&original, "a => a => a") else {
            panic!("`a => a => a` is ambiguous at both rewrites");
        };
        let named = places
            .iter()
            .flat_map(|place| &place.alternatives)
            .filter(|entry| entry.term == "atom(.KList)=>atom(.KList)")
            .map(|entry| entry.production.as_deref())
            .collect::<Vec<_>>();
        assert_eq!(named, [Some(r#"syntax S0 ::= S0 "=>" S1"#); 2]);
    }

    /// A postfix `S1 ::= S1 "+" [o2]` beside a rewrite, written `S1 ::= P "+"` through
    /// `P ::= S1`: on `a => a +` every reading puts the rewrite below `o2`, a scope error, and
    /// the pruned recognition, which drops such a node where it completes, finds no derivation
    /// exactly when the unfiltered one finds none, and reports that scope error alike.
    #[test]
    fn a_pass_through_below_a_postfix_operator_keeps_the_first_attempts_derivation() {
        let operators: Vec<GeneratedOperator> = vec![
            (1, 1, 1, 0, 3, 0, true, 0),
            (1, 0, 0, 0, 3, 1, true, 1),
            (1, 2, 1, 0, 0, 0, false, 0),
            (1, 0, 1, 1, 2, 2, false, 0),
            (1, 0, 0, 0, 3, 1, true, 1),
        ];
        let levels = BTreeMap::from([(3, 1), (6, 0), (7, 2), (11, 1)]);
        let groups = [(1, BTreeSet::from([2, 8, 11]))];
        let passed = operator_grammar(&operators, &levels, &groups, true, Some((2, 0))).unwrap();
        pruning_agrees_with_unfiltered_recognition(&passed, "a => a +").unwrap();
        assert_eq!(
            filtered(&passed, "a => a +"),
            Err(ParseError::Scope {
                parent: "o2".to_owned(),
                child: InternalLabel::KRewrite.as_str().to_owned(),
            })
        );
    }

    /// Class test for the inference-engine ticket: the Z3 and portable engines implement one
    /// decision (which readings of a forest are the parse), so on one forest they reject alike:
    /// the same error, the same reported ambiguity, span and subterms. The forest is
    /// the one `an_ambiguity_beside_a_rewrite_below_an_operator_is_reported_by_its_readings`
    /// pins per engine; both engines are
    /// run on it in one build, after the same recognition and pre-inference passes.
    #[cfg(feature = "z3-inference")]
    #[test]
    fn both_inference_engines_reject_one_ambiguous_forest_alike() {
        let grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("S0")], "start"),
            production("S1", vec![], "p0"),
            production("S2", vec![terminal("a")], "p1"),
            production("S2", vec![nt("S0"), terminal("c")], "p2"),
            production(
                "S2",
                vec![nt("S2"), nt("S0"), terminal("c")],
                InternalLabel::KRewrite.as_str(),
            ),
            production("S0", vec![nt("S2"), nt("S0")], "p4"),
            production("S0", vec![], "p5"),
        ])
        .unwrap();
        let input = "a c c c";
        let start_sort = Sort::new("Start");
        let start = grammar.sort_id(grammar.sort_denotations.denote(&start_sort));
        let mut scanner_cache = vec![None; input.len() + 1];
        let start_position = grammar.canonical_position(input, 0, &mut scanner_cache);
        let memos = std::cell::RefCell::new(PackedPriorityMemos::default());
        let recognition = grammar
            .recognize(
                start.unwrap(),
                start_position,
                input,
                ParseProvenance {
                    source: SourceId(7),
                    base_offset: 100,
                },
                PredictionMode::Unfiltered,
                PriorityFilter::Enforced,
                None,
                false,
                &mut false,
                &mut WorkMeter::unlimited(),
                &mut scanner_cache,
                &memos,
            )
            .unwrap();
        let forest = grammar
            .prepare_packed_forest(PackedTerm::ambiguity(recognition.parses), &memos)
            .unwrap();
        let lower = |tree| grammar.lower_inferred(tree, &start_sort);
        let portable = grammar.infer_ambiguous_sorts_portable(&forest, &start_sort, false, &lower);
        let z3 = grammar
            .infer_packed_sorts_z3(std::rc::Rc::clone(&forest), &start_sort, false)
            .and_then(&lower);
        assert_eq!(portable, z3);
    }

    /// The forest of `S ::= S S | S "d" | "d"` over `d`^n holds, for every span of `L >= 2`
    /// tokens, one ambiguity of a `S S` node per split, `L - 1`, and one `S "d"` node, and
    /// nothing else: C(n + 1, 3) + C(n, 2) alternatives in all. A chart that
    /// completes a longer span before the shorter spans below it are complete builds a version
    /// of its nodes per growth of those spans, and the ambiguities above keep every version
    /// beside the latest, so the count then grows with the number of versions, exponentially in
    /// n.
    #[test]
    fn the_forest_of_an_ambiguous_chain_has_one_node_per_split_of_each_span() {
        use std::collections::HashSet;

        use super::super::forest::PackedNode;

        let grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("S")], "start"),
            production("S", vec![nt("S"), nt("S")], "pair"),
            production("S", vec![nt("S"), terminal("d")], "post"),
            production("S", vec![terminal("d")], "d"),
        ])
        .unwrap();
        let n = 12;
        let input = vec!["d"; n].join(" ");
        let start = grammar
            .sort_id(grammar.sort_denotations.denote(&Sort::new("Start")))
            .unwrap();
        let mut scanner_cache = vec![None; input.len() + 1];
        let start_position = grammar.canonical_position(&input, 0, &mut scanner_cache);
        let memos = std::cell::RefCell::new(PackedPriorityMemos::default());
        let recognition = grammar
            .recognize(
                start,
                start_position,
                &input,
                ParseProvenance {
                    source: SourceId(7),
                    base_offset: 100,
                },
                PredictionMode::Unfiltered,
                PriorityFilter::Enforced,
                None,
                false,
                &mut false,
                &mut WorkMeter::unlimited(),
                &mut scanner_cache,
                &memos,
            )
            .unwrap();
        // Ambiguities told apart by structure, so that equal copies count once.
        let mut ambiguities = BTreeSet::new();
        let mut seen = HashSet::new();
        let mut pending: Vec<_> = recognition.parses.into_iter().collect();
        while let Some(node) = pending.pop() {
            if !seen.insert(std::rc::Rc::as_ptr(&node)) {
                continue;
            }
            match &node.node {
                PackedNode::Production { children, .. }
                | PackedNode::InstantiatedProduction { children, .. } => {
                    pending.extend(children.iter().cloned());
                }
                PackedNode::Ambiguity(nodes) => {
                    pending.extend(nodes.iter().cloned());
                    ambiguities.insert(node);
                }
                PackedNode::Term(_) => {}
            }
        }
        let alternatives: usize = ambiguities
            .iter()
            .map(|ambiguity| match &ambiguity.node {
                PackedNode::Ambiguity(nodes) => nodes.len(),
                _ => unreachable!("only ambiguities are kept"),
            })
            .sum();
        assert_eq!(ambiguities.len(), n * (n - 1) / 2);
        assert_eq!(alternatives, (n + 1) * n * (n - 1) / 6 + n * (n - 1) / 2);
    }

    /// The preference for K's own constructs chooses once per node of the forest and place.
    /// Under `S ::= "" | "c" S S S | "c" "c"`, over `c`^n, many alternatives of an ambiguity apply
    /// one production over one split (the empty `S` reached from several items), so the choice
    /// merges them into one node per position, whose children are the union of theirs. Built
    /// anew per merge, equal unions were new nodes that the memo, keyed by identity, never met
    /// again, and the choice below them was made once per path down to them: at n = 16, 32 s and
    /// 3.9 GB in the test build, where the forest had 7,000 nodes.
    #[test]
    fn the_structural_preference_chooses_once_per_node_and_place() {
        use std::collections::HashSet;

        use super::super::disambiguation::PREFERENCE_CHOICES;
        use super::super::forest::PackedNode;

        let grammar = Grammar::from_sentences(&[
            production("Start", vec![nt("S")], "start"),
            production("S", vec![], "empty"),
            production(
                "S",
                vec![terminal("c"), nt("S"), nt("S"), nt("S")],
                "triple",
            ),
            production("S", vec![terminal("c"), terminal("c")], "pair"),
        ])
        .unwrap();
        let n = 14;
        let input = vec!["c"; n].join(" ");
        let start = grammar
            .sort_id(grammar.sort_denotations.denote(&Sort::new("Start")))
            .unwrap();
        let mut scanner_cache = vec![None; input.len() + 1];
        let start_position = grammar.canonical_position(&input, 0, &mut scanner_cache);
        let memos = std::cell::RefCell::new(PackedPriorityMemos::default());
        let recognition = grammar
            .recognize(
                start,
                start_position,
                &input,
                ParseProvenance {
                    source: SourceId(7),
                    base_offset: 100,
                },
                PredictionMode::Unfiltered,
                PriorityFilter::Enforced,
                None,
                false,
                &mut false,
                &mut WorkMeter::unlimited(),
                &mut scanner_cache,
                &memos,
            )
            .unwrap();
        let forest = PackedTerm::ambiguity(recognition.parses);
        let mut seen = HashSet::new();
        let mut pending = vec![std::rc::Rc::clone(&forest)];
        while let Some(node) = pending.pop() {
            if !seen.insert(std::rc::Rc::as_ptr(&node)) {
                continue;
            }
            match &node.node {
                PackedNode::Production { children, .. }
                | PackedNode::InstantiatedProduction { children, .. } => {
                    pending.extend(children.iter().cloned());
                }
                PackedNode::Ambiguity(nodes) => pending.extend(nodes.iter().cloned()),
                PackedNode::Term(_) => {}
            }
        }
        PREFERENCE_CHOICES.with(|count| count.set(0));
        grammar.prefer_structural_readings(forest);
        let choices = PREFERENCE_CHOICES.with(std::cell::Cell::get);
        // One choice per node and place, the nodes being the forest's and the unions of its
        // merged positions: 586 for 3,890 nodes, where one per path down to a union made 584,141.
        assert!(
            choices <= 2 * seen.len(),
            "{choices} choices for {} nodes",
            seen.len()
        );
    }
}
