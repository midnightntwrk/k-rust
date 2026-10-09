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
use crate::kast::InternalLabel;

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
    /// The productions the predictor adds that build a rewrite, a sequence or a `#let`, whose
    /// scope errors the priority filter defers, as the tokens their nodes contain.
    deferred_scopes: DeferredScopes,
}

/// Where a node whose scope error the priority filter defers (one built by a production
/// labelled `#KRewrite`, `#KSequence` or `#let`) can lie in the input.
#[derive(Clone, Debug)]
pub(super) enum DeferredScopes {
    /// The grammar builds no such node.
    Absent,
    /// Every such node contains a token of one of these lexemes (each production's first
    /// lexical item), so a span without one contains none.
    Witnessed(LexemeSet),
    /// Some such production has no lexical item, so any span may contain its node.
    Unwitnessed,
}

impl DeferredScopes {
    /// Whether a token of `lexeme` witnesses a deferred node (`Witnessed` only).
    pub(super) fn witnesses(&self, lexeme: usize) -> bool {
        matches!(self, Self::Witnessed(lexemes) if lexemes.contains(lexeme))
    }
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
        let deferred = |index: usize| {
            grammar.productions[index]
                .parse_label
                .as_deref()
                .is_some_and(|label| {
                    [
                        InternalLabel::KRewrite,
                        InternalLabel::KSequence,
                        InternalLabel::Let,
                    ]
                    .iter()
                    .any(|deferred| label == deferred.as_str())
                })
        };
        let mut deferred_scopes = DeferredScopes::Absent;
        for index in grammar.by_result.iter().flatten() {
            let production = &grammar.productions[*index];
            if !deferred(*index) && !production.term_production.is_some_and(deferred) {
                continue;
            }
            let witness = production
                .items
                .iter()
                .filter(|item| !matches!(item, Item::NonTerminal(_)))
                .find_map(|item| grammar.scanner.lexeme_id(item));
            deferred_scopes = match (deferred_scopes, witness) {
                (DeferredScopes::Unwitnessed, _) | (_, None) => DeferredScopes::Unwitnessed,
                (DeferredScopes::Absent, Some(lexeme)) => {
                    let mut lexemes = LexemeSet::default();
                    lexemes.insert(lexeme);
                    DeferredScopes::Witnessed(lexemes)
                }
                (DeferredScopes::Witnessed(mut lexemes), Some(lexeme)) => {
                    lexemes.insert(lexeme);
                    DeferredScopes::Witnessed(lexemes)
                }
            };
        }
        Self {
            first_items,
            epsilon,
            first,
            buckets,
            rests,
            deferred_scopes,
        }
    }

    /// Where the nodes whose scope errors the priority filter defers can lie
    /// (`Grammar::boundary_admits`).
    pub(super) fn deferred_scopes(&self) -> &DeferredScopes {
        &self.deferred_scopes
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
        CHART_COMPLETION_CANDIDATES, DiagnosticWork, DoomedEdges, NONTERMINAL_PREDICTIONS_SKIPPED,
        NoParseInput, PARSE_ATTEMPTS, PREDICTION_ANALYSIS_BUILDS, PackedPriorityMemos, PackedTerm,
        ParseContext, ParseError, ParseProvenance, PredictionMode, PriorityFilter, Pruning,
        Recognition, SameSpanCycles, ScanWinner, SourceId, Term, TermMetadata, WorkMeter,
    };
    use super::*;
    use crate::definition::{
        Attributes, ProductionCatalog, ProductionItem, Sentence, SortDenotations,
    };
    use crate::kast::{Label, TermSpan};
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
                    DoomedEdges::Kept,
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

        /// The same in a grammar with productions labelled `#KRewrite`, `#KSequence` or `#let`,
        /// whose scope errors below an operator the priority filter defers: the doomed nodes
        /// it keeps can be read by the preference among the readings of the root, so skipping
        /// items must keep every one it can read (`Grammar::priority_admits`), and an attempt
        /// that skipped the others and failed is made again keeping them (`DoomedEdges`).
        #[test]
        fn completion_pruning_matches_unfiltered_recognition_with_deferred_scopes(
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
            matches!(&ambiguity, Err(ParseError::Ambiguous { parses: 2, .. })),
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

    /// In a grammar with a rewrite, the priority filter keeps a node whose child is a rewrite
    /// below an operator: the scope error is deferred, so that a reading rooted at the rewrite
    /// can be preferred over it, and until then the doomed node, with every edge below it, is
    /// part of the forest. Under `S2 ::= "a" | S0 "c" | S2 S0 "c" [#KRewrite]` and
    /// `S0 ::= S2 S0 | ""`, `a c c c` is ambiguous. A first attempt that skipped every item
    /// whose edge the filter rejects, the deferred ones included, built a smaller forest than an
    /// unfiltered recognition, and in the `z3-inference` build reported the ambiguity at
    /// 104-107 instead of 102-106. Where an ambiguity is reported is decided by sort inference
    /// after recognition, so the reported error is pinned per engine, and the forests are
    /// compared directly. The input holds three `c`, each a token a rewrite node can hold, so
    /// the full parse skips no edge to a doomed node either (`DoomedEdges`).
    #[test]
    fn edges_below_a_deferred_scope_error_are_kept() {
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
        let forest = |mode: PredictionMode| {
            let input = "a c c c";
            let start = grammar.sort_id(grammar.sort_denotations.denote(&Sort::new("Start")));
            let mut scanner_cache = vec![None; input.len() + 1];
            let start_position = grammar.canonical_position(input, 0, &mut scanner_cache);
            grammar
                .recognize(
                    start.unwrap(),
                    start_position,
                    input,
                    ParseProvenance {
                        source: SourceId(7),
                        base_offset: 100,
                    },
                    mode,
                    PriorityFilter::Enforced,
                    None,
                    false,
                    DoomedEdges::Kept,
                    &mut false,
                    &mut WorkMeter::unlimited(),
                    &mut scanner_cache,
                    &std::cell::RefCell::new(PackedPriorityMemos::default()),
                )
                .map(|recognition| recognition.parses)
        };
        let unfiltered_forest = forest(PredictionMode::Unfiltered);
        assert!(
            unfiltered_forest
                .as_ref()
                .is_ok_and(|parses| !parses.is_empty()),
            "{unfiltered_forest:?}"
        );
        assert_eq!(forest(PredictionMode::Filtered), unfiltered_forest);

        #[cfg(feature = "z3-inference")]
        let (parses, start, end) = (2, 102, 106);
        #[cfg(not(feature = "z3-inference"))]
        let (parses, start, end) = (14, 100, 107);
        let expected = unfiltered(&grammar, "a c c c");
        assert!(
            matches!(
                &expected,
                Err(ParseError::Ambiguous {
                    parses: reported,
                    span: Some(TermSpan {
                        start: reported_start,
                        end: reported_end,
                        ..
                    }),
                    ..
                }) if (*reported, *reported_start, *reported_end) == (parses, start, end)
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
}
