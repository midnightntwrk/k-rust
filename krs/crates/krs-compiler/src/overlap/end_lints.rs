//! The lints on declared ends (`#[k::end(..)]`).
//!
//! An end is a set of states, stated as a function of the configuration that is true where the
//! end's pattern matches under its condition.
//! Nothing in the transition system reads it: the rules apply where they apply, whatever the ends
//! say.
//! So an end may be true at a state where a rule applies, and a reader that takes "the end holds"
//! for "the run is over" (a claim whose target is a class) is then wrong at that state.
//! The lints below report the cases of that, and of two neighbouring mistakes, that the patterns
//! decide by themselves.
//!
//! - `krs::analysis::end-not-terminal`: an end and a rule are shown to hold of one state.
//! - `krs::analysis::end-classes-overlap`: two ends of different classes are shown to hold of one
//!   state.
//! - `krs::analysis::end-catch-all`: a rule that goes after the others takes any head and gives a
//!   state of a `refused` end.
//!
//! # What "shown" means
//!
//! Each finding is one of three facts about two sides (an end's clause and a rule's left side, or
//! two ends' clauses), each fact decided exactly.
//!
//! - *Covers*: the first side has no condition, and its pattern matches every state the second
//!   side's pattern matches, so the first holds wherever the second does.
//!   The second side's condition is not read: the statement is about the states where it holds,
//!   whichever they are.
//! - *Meets*: neither side has a condition, and the two patterns have a common instance, which is
//!   then a state both hold of.
//!
//! A condition is never judged satisfiable or not.
//! Two sides that both have a condition are therefore never reported, whatever their patterns: a
//! clause separated from a rule by its condition is silent, and so is one that is not separated
//! but whose condition this module does not read.
//!
//! A pattern is read only where matching it is syntactic: variables, tokens, applications of
//! free constructors, and a computation cell's items with or without a rest.
//! A map, list or set pattern, a function's application, an or-pattern on the side that must
//! cover, a whole group cell, an optional cell or a collection instance on a side that must be
//! matched as a whole: each makes the pair silent, since the overlap check's unification of them
//! is an over-approximation and answers "may match", which is no finding.
//!
//! "A rule applies" is said of the state, not of the rule named: where a rule's left side
//! matches and its condition holds, that rule or one of a higher priority applies.
//! The rules read are the transitions: a heating or cooling step, a context and an `anywhere`
//! rule are not, so an end at a state only those leave is not reported.

use std::collections::{BTreeMap, BTreeSet};

use krs_diagnostic::{Diagnostic, Label, Location, Severity, codes};
use krs_ir::{
    ApplicationRef, BuiltinSort, CellContentFrame, CellPost, ConfigurationClause, EndClass,
    EndForm, EndRole, SemanticId, SentenceKind, StableItemId,
};
use krs_ir_levels::{
    RuleBodyRef, SemanticModule, SemanticRule, SemanticSortRef, SemanticTerm, SemanticTermKind,
};

use super::{
    Choice, DEFAULT_PRIORITY, Pattern, StaticSubjects, Unifier, VariableCatalog, VariableKey,
    WITNESS_DEPTH, choices, count_variables, instance, or_nodes, pattern, splices,
};
use crate::ends::{EndMark, own_function, semantic_mark};

/// The `warning[krs::analysis::end-not-terminal]`, `warning[krs::analysis::end-classes-overlap]`
/// and `warning[krs::analysis::end-catch-all]` diagnostics of a lowered theory's modules (the
/// module documentation): none for a definition that declares no end.
#[must_use]
pub fn end_warnings(modules: &[SemanticModule]) -> Vec<Diagnostic> {
    let marks = modules
        .iter()
        .flat_map(SemanticModule::productions)
        .filter_map(|production| Some((production.id(), semantic_mark(production)?)))
        .collect::<BTreeMap<_, _>>();
    if marks.is_empty() {
        return Vec::new();
    }
    let judge = Judge::of(modules);
    let ends = judge.ends(modules, &marks);
    let rules = judge.rules(modules);
    let mut warnings = Vec::new();
    for end in &ends {
        warnings.extend(judge.not_terminal(end, &rules));
    }
    for (index, later) in ends.iter().enumerate() {
        for earlier in &ends[..index] {
            warnings.extend(judge.classes_overlap(earlier, later));
        }
    }
    for rule in &rules {
        warnings.extend(judge.catch_all(rule, &ends));
    }
    warnings
}

/// One cell's pattern as its sentence writes it.
#[derive(Clone, Copy)]
struct Raw<'m> {
    cell: &'m SemanticId,
    term: &'m SemanticTerm,
    frame: RawFrame<'m>,
}

/// What a pattern leaves out of its cell's content.
#[derive(Clone, Copy)]
enum RawFrame<'m> {
    /// Nothing.
    Exact,
    /// The rest of the computation after the pattern's items, with the name that binds it.
    Rest(Option<&'m SemanticId>),
    /// A map's or a list's remainder, which this module does not read.
    Unread,
}

impl<'m> RawFrame<'m> {
    const fn of(frame: &'m CellContentFrame) -> Self {
        match frame {
            CellContentFrame::Exact => Self::Exact,
            CellContentFrame::KSequenceTail { binding, .. } => Self::Rest(binding.as_ref()),
            CellContentFrame::MapRemainder { .. }
            | CellContentFrame::ListRemainder { .. }
            | CellContentFrame::MovedMapRemainder { .. } => Self::Unread,
        }
    }
}

/// One cell's content as a side requires it.
enum Shape {
    /// A computation: these items, then nothing (`open` false) or any rest.
    Sequence { items: Vec<Pattern>, open: bool },
    /// The whole content as one term.
    Single(Pattern),
    /// A content this module does not read.
    Unread,
}

struct Content<'m> {
    cell: &'m SemanticId,
    shape: Shape,
    /// The variable a named rest binds.
    rest: Option<VariableKey>,
}

/// The patterns one sentence places on the cells every state holds once, under one choice of its
/// or-patterns' alternatives.
struct Side<'m> {
    contents: Vec<Content<'m>>,
    /// How often each variable occurs in the patterns.
    counts: BTreeMap<VariableKey, usize>,
    /// Whether a variable may be constrained where `counts` does not see it: an `alias @ pattern`
    /// binds the alias to the pattern, and a `k::matches!` or a `let` hides its names.
    hidden_binders: bool,
}

impl<'m> Side<'m> {
    fn content(&self, cell: &SemanticId) -> Option<&Content<'m>> {
        self.contents.iter().find(|content| content.cell == cell)
    }

    /// Whether `key` occurs once in the side's patterns: nothing but its own place constrains
    /// it.
    fn once(&self, key: VariableKey) -> bool {
        !self.hidden_binders && self.counts.get(&key) == Some(&1)
    }
}

/// One clause of a declared end: the states its `holds` function is true at.
struct EndView<'m> {
    rule: &'m SemanticRule,
    mark: EndMark<'m>,
    raws: Vec<Raw<'m>>,
    guarded: bool,
}

/// One transition.
struct RuleView<'m> {
    rule: &'m SemanticRule,
    /// Its patterns on cells every state holds once.
    raws: Vec<Raw<'m>>,
    /// Whether its left side also matches an optional cell or a collection's instances, which
    /// `raws` leaves out.
    partial: bool,
    guarded: bool,
    priority: u32,
    owise: bool,
}

/// How two sides are shown to hold of one state.
enum Shown {
    /// The first side holds wherever the second does.
    FirstCovers,
    /// The second side holds wherever the first does.
    SecondCovers,
    /// Both hold of every state with these contents, where they are written.
    Meet(Option<String>),
}

struct Judge<'m> {
    subjects: StaticSubjects,
    /// The main computation cell, in a configuration that has one outside every optional cell
    /// and collection.
    main: Option<SemanticId>,
    /// Each leaf cell's declared sort and K name.
    cells: BTreeMap<&'m SemanticId, (&'m SemanticSortRef, &'m str)>,
}

impl<'m> Judge<'m> {
    fn of(modules: &'m [SemanticModule]) -> Self {
        fn leaves<'c>(
            cells: &'c [krs_ir::FixedCell<SemanticSortRef, SemanticId>],
            output: &mut BTreeMap<&'c SemanticId, (&'c SemanticSortRef, &'c str)>,
        ) {
            for cell in cells {
                match cell.content() {
                    krs_ir::FixedCellContent::Term { sort, .. } => {
                        output.insert(cell.id(), (sort, cell.name()));
                    }
                    krs_ir::FixedCellContent::Children { children } => leaves(children, output),
                }
            }
        }
        let mut cells = BTreeMap::new();
        if let Some(configuration) = modules.iter().find_map(SemanticModule::configuration) {
            leaves(configuration.cells(), &mut cells);
        }
        let keys = crate::instance_keys::InstanceKeys::of(modules);
        Self {
            subjects: StaticSubjects::of(modules),
            main: keys
                .main()
                .filter(|main| keys.enclosing(&main.cell).is_empty())
                .map(|main| main.cell.clone()),
            cells,
        }
    }

    /// The clauses of the ends `marks` names, in module and sentence order: each end's own
    /// equation whose result is `true`, with the cells it reads.
    fn ends(
        &self,
        modules: &'m [SemanticModule],
        marks: &BTreeMap<&'m StableItemId, EndMark<'m>>,
    ) -> Vec<EndView<'m>> {
        let mut ends = Vec::new();
        for rule in modules.iter().flat_map(SemanticModule::rules) {
            let Some(function) = own_function(rule, marks) else {
                continue;
            };
            let mark = marks[function];
            if mark.role != EndRole::Holds || rule.id().item_name() != mark.item {
                continue;
            }
            let RuleBodyRef::Term(body) = rule.relational_body() else {
                continue;
            };
            let mut raws = Vec::new();
            if let Some(context) = rule.function_context() {
                for cell in context.cells().cells() {
                    raws.push(Raw {
                        cell: cell.cell(),
                        term: cell.pattern(),
                        frame: RawFrame::of(cell.frame()),
                    });
                }
            }
            if mark.form == EndForm::Constructor {
                // The function's one argument is the head of the main computation cell.
                let (Some(main), SemanticTermKind::Application { arguments, .. }) =
                    (self.main_cell(), body.from().kind())
                else {
                    continue;
                };
                let [head] = arguments.as_slice() else {
                    continue;
                };
                raws.push(Raw {
                    cell: main,
                    term: head,
                    frame: RawFrame::Rest(None),
                });
            }
            ends.push(EndView {
                rule,
                mark,
                raws,
                guarded: rule.requires().is_some(),
            });
        }
        ends
    }

    /// The main cell, by the identity the configuration's cells have in `self.cells`.
    fn main_cell(&self) -> Option<&'m SemanticId> {
        let main = self.main.as_ref()?;
        self.cells.keys().copied().find(|cell| *cell == main)
    }

    /// The transitions of the definition's modules, in module and sentence order.
    fn rules(&self, modules: &'m [SemanticModule]) -> Vec<RuleView<'m>> {
        let mut rules = Vec::new();
        for module in modules.iter().filter(|module| !module.is_spec()) {
            for rule in module.rules() {
                if rule.kind() != SentenceKind::Transition
                    || rule.anywhere().is_some()
                    || rule.evaluation().is_some()
                {
                    continue;
                }
                let mut raws = Vec::new();
                let mut partial = false;
                match rule.relational_body() {
                    RuleBodyRef::Term(body) => {
                        // A term rule runs at the head of the main computation cell.
                        let Some(main) = self.main_cell() else {
                            continue;
                        };
                        raws.push(Raw {
                            cell: main,
                            term: body.from(),
                            frame: RawFrame::Rest(None),
                        });
                    }
                    RuleBodyRef::Configuration { body, .. } => {
                        let mut whole = false;
                        for clause in body.clauses() {
                            match clause {
                                ConfigurationClause::Fixed(clause) => {
                                    whole |= !clause.kind().is_content();
                                    raws.push(Raw {
                                        cell: clause.cell(),
                                        term: clause.before(),
                                        frame: RawFrame::of(clause.frame()),
                                    });
                                }
                                ConfigurationClause::Optional(_)
                                | ConfigurationClause::Instances(_) => partial = true,
                            }
                        }
                        // A whole group cell constrains the leaves below it, which no clause
                        // names.
                        if whole {
                            continue;
                        }
                    }
                    RuleBodyRef::Predicate(_) => continue,
                }
                rules.push(RuleView {
                    rule,
                    raws,
                    partial,
                    guarded: rule.requires().is_some(),
                    priority: rule
                        .priority()
                        .map_or(DEFAULT_PRIORITY, krs_ir_levels::SemanticRulePriority::value),
                    owise: rule
                        .priority()
                        .is_some_and(krs_ir_levels::SemanticRulePriority::is_owise),
                });
            }
        }
        rules
    }

    /// Every choice of one alternative at each or-pattern of `raws`.
    fn alternatives(raws: &[Raw<'_>]) -> Vec<Choice> {
        let mut nodes = Vec::new();
        for raw in raws {
            or_nodes(raw.term, &mut nodes);
        }
        choices(&nodes)
    }

    /// `raws` as the side `index` of a pair, under `choice`.
    fn side(&self, raws: &[Raw<'m>], index: usize, choice: &Choice) -> Side<'m> {
        let mut catalog = VariableCatalog::default();
        catalog.choices[index] = choice.clone();
        let mut counts = BTreeMap::new();
        let mut hidden_binders = false;
        let mut contents = Vec::new();
        for raw in raws {
            let read = pattern(raw.term, index, &mut catalog);
            count(&read, &mut counts, &mut hidden_binders);
            let computation = self.cells.get(raw.cell).is_some_and(|(sort, _)| {
                **sort == SemanticSortRef::Builtin(BuiltinSort::KSequence)
            });
            let items = |read: Pattern| match read {
                Pattern::KSequence { items, .. } => items,
                read => vec![read],
            };
            let (shape, rest) = match raw.frame {
                RawFrame::Unread => (Shape::Unread, None),
                RawFrame::Rest(binding) => {
                    let rest = binding.map(|binding| catalog.key(index, binding));
                    if let Some(rest) = rest {
                        *counts.entry(rest).or_default() += 1;
                    }
                    (
                        Shape::Sequence {
                            items: items(read),
                            open: true,
                        },
                        rest,
                    )
                }
                RawFrame::Exact => match read {
                    Pattern::KSequence { items, .. } => {
                        (Shape::Sequence { items, open: false }, None)
                    }
                    read if computation && !splices(&read) => (
                        Shape::Sequence {
                            items: vec![read],
                            open: false,
                        },
                        None,
                    ),
                    read => (Shape::Single(read), None),
                },
            };
            contents.push(Content {
                cell: raw.cell,
                shape,
                rest,
            });
        }
        hidden_binders |= !catalog.aliases.is_empty();
        Side {
            contents,
            counts,
            hidden_binders,
        }
    }

    fn graph(&self) -> &super::SortGraph {
        &self.subjects.graph
    }

    /// Whether `general` matches every term `specific` matches.
    fn term_covers(&self, general: &Pattern, side: &Side<'_>, specific: &Pattern) -> bool {
        match (general, specific) {
            // A variable that nothing else constrains stands for every term of its sort.
            (Pattern::Variable { key, sort }, specific) => {
                side.once(*key) && self.graph().is_subsort(specific.sort(), sort)
            }
            (
                Pattern::Application {
                    application: ApplicationRef::Declared(general),
                    arguments: general_arguments,
                    instance: general_instance,
                    ..
                },
                Pattern::Application {
                    application: ApplicationRef::Declared(specific),
                    arguments: specific_arguments,
                    instance: specific_instance,
                    ..
                },
            ) => {
                general == specific
                    && general_instance == specific_instance
                    && self.graph().free_constructor(general)
                    && general_arguments.len() == specific_arguments.len()
                    && general_arguments
                        .iter()
                        .zip(specific_arguments)
                        .all(|(general, specific)| self.term_covers(general, side, specific))
            }
            (
                Pattern::Token {
                    sort: general_sort,
                    value: general,
                },
                Pattern::Token {
                    sort: specific_sort,
                    value: specific,
                },
            ) => general_sort == specific_sort && general == specific,
            _ => false,
        }
    }

    /// Whether `general` requires nothing of its cell.
    fn requires_nothing(&self, general: &Content<'_>, side: &Side<'_>) -> bool {
        let rest_free = general.rest.is_none_or(|rest| side.once(rest));
        match &general.shape {
            Shape::Single(Pattern::Variable { key, sort }) => {
                side.once(*key)
                    && self
                        .cells
                        .get(general.cell)
                        .is_some_and(|(declared, _)| self.graph().is_subsort(declared, sort))
            }
            Shape::Sequence { items, open: true } => items.is_empty() && rest_free,
            Shape::Sequence { .. } | Shape::Single(_) | Shape::Unread => false,
        }
    }

    /// Whether `general` matches every content `specific` matches.
    fn content_covers(
        &self,
        general: &Content<'_>,
        side: &Side<'_>,
        specific: &Content<'_>,
    ) -> bool {
        match (&general.shape, &specific.shape) {
            (Shape::Single(general), Shape::Single(specific)) => {
                self.term_covers(general, side, specific)
            }
            (
                Shape::Sequence {
                    items: general_items,
                    open: general_open,
                },
                Shape::Sequence {
                    items: specific_items,
                    open: specific_open,
                },
            ) => {
                // An item that splices may stand for no item or for several, so the items of a
                // sequence that holds one are at no fixed place.
                let fixed = |items: &[Pattern]| !items.iter().any(splices);
                let lengths = if *general_open {
                    general_items.len() <= specific_items.len()
                        && fixed(&specific_items[..general_items.len()])
                } else {
                    general_items.len() == specific_items.len()
                        && !specific_open
                        && fixed(specific_items)
                };
                lengths
                    && fixed(general_items)
                    && general.rest.is_none_or(|rest| side.once(rest))
                    && general_items
                        .iter()
                        .zip(specific_items)
                        .all(|(general, specific)| self.term_covers(general, side, specific))
            }
            _ => false,
        }
    }

    /// Whether `general`'s patterns match every state `specific`'s patterns match.
    fn covers(&self, general: &Side<'_>, specific: &Side<'_>) -> bool {
        general.contents.iter().all(|content| {
            self.requires_nothing(content, general)
                || specific
                    .content(content.cell)
                    .is_some_and(|other| self.content_covers(content, general, other))
        })
    }

    /// Whether every pattern of `side` is matched syntactically: variables, tokens and free
    /// constructors, in a computation's items or as a cell's whole content.
    fn syntactic(&self, side: &Side<'_>) -> bool {
        fn term(judge: &Judge<'_>, pattern: &Pattern) -> bool {
            match pattern {
                Pattern::Variable { .. } | Pattern::Token { .. } => true,
                Pattern::Application {
                    application: ApplicationRef::Declared(production),
                    arguments,
                    ..
                } => {
                    judge.graph().free_constructor(production)
                        && arguments.iter().all(|argument| term(judge, argument))
                }
                _ => false,
            }
        }
        !side.hidden_binders
            && side.contents.iter().all(|content| {
                content.rest.is_none_or(|rest| side.once(rest))
                    && match &content.shape {
                        Shape::Single(pattern) => term(self, pattern),
                        Shape::Sequence { items, .. } => {
                            items.iter().all(|item| !splices(item) && term(self, item))
                        }
                        Shape::Unread => false,
                    }
            })
    }

    /// Unifies two terms of syntactic sides: `true` exactly when they have a common instance.
    fn unify(&self, unifier: &mut Unifier<'_>, left: &Pattern, right: &Pattern) -> bool {
        match (
            unifier.resolve(left.clone()),
            unifier.resolve(right.clone()),
        ) {
            (
                Pattern::Variable {
                    key: left,
                    sort: left_sort,
                },
                Pattern::Variable {
                    key: right,
                    sort: right_sort,
                },
            ) => {
                if !unifier.unify_variables(left, left_sort, right, right_sort) {
                    return false;
                }
                // The terms both variables stand for are those of a sort below every sort
                // required of them. With a least one among the required sorts, that is this
                // sort's terms; without, it is the terms of sorts below several, which are not
                // shown to exist.
                let root = left.min(right);
                unifier.requirements.get(&root).is_some_and(|required| {
                    required.iter().any(|least| {
                        required
                            .iter()
                            .all(|other| self.graph().is_subsort(least, other))
                    })
                })
            }
            (Pattern::Variable { key, sort }, term) | (term, Pattern::Variable { key, sort }) => {
                unifier.bind(key, sort, term)
            }
            (
                Pattern::Application {
                    application: left,
                    arguments: left_arguments,
                    instance: left_instance,
                    ..
                },
                Pattern::Application {
                    application: right,
                    arguments: right_arguments,
                    instance: right_instance,
                    ..
                },
            ) => {
                left == right
                    && left_instance == right_instance
                    && left_arguments.len() == right_arguments.len()
                    && left_arguments
                        .iter()
                        .zip(&right_arguments)
                        .all(|(left, right)| self.unify(unifier, left, right))
            }
            (
                Pattern::Token {
                    sort: left_sort,
                    value: left,
                },
                Pattern::Token {
                    sort: right_sort,
                    value: right,
                },
            ) => left_sort == right_sort && left == right,
            _ => false,
        }
    }

    /// The common instance of two sides' patterns, when both are syntactic and have one: `None`
    /// where they have none or are not shown to, and otherwise the contents of the cells both
    /// read, where they can be written.
    fn meet(&self, left: &Side<'_>, right: &Side<'_>) -> Option<Shown> {
        if !self.syntactic(left) || !self.syntactic(right) {
            return None;
        }
        let mut unifier = Unifier::new(self.graph());
        let mut shared = Vec::new();
        for content in &left.contents {
            let Some(other) = right.content(content.cell) else {
                continue;
            };
            match (&content.shape, &other.shape) {
                (Shape::Single(left), Shape::Single(right)) => {
                    if !self.unify(&mut unifier, left, right) {
                        return None;
                    }
                    shared.push((content.cell, vec![left.clone()], None));
                }
                (
                    Shape::Sequence {
                        items: left_items,
                        open: left_open,
                    },
                    Shape::Sequence {
                        items: right_items,
                        open: right_open,
                    },
                ) => {
                    // The shorter sequence's rest holds the longer one's further items.
                    let fits = match left_items.len().cmp(&right_items.len()) {
                        std::cmp::Ordering::Equal => true,
                        std::cmp::Ordering::Less => *left_open,
                        std::cmp::Ordering::Greater => *right_open,
                    };
                    if !fits
                        || !left_items
                            .iter()
                            .zip(right_items)
                            .all(|(left, right)| self.unify(&mut unifier, left, right))
                    {
                        return None;
                    }
                    let (longer, open) = if left_items.len() >= right_items.len() {
                        (left_items, *left_open && *right_open)
                    } else {
                        (right_items, *left_open && *right_open)
                    };
                    shared.push((content.cell, longer.clone(), Some(open)));
                }
                _ => return None,
            }
        }
        Some(Shown::Meet(self.witness(&unifier, &shared)))
    }

    /// The contents `shared` under `unifier`, as `cell: term` and `cell: [items, ..]`.
    fn witness(
        &self,
        unifier: &Unifier<'_>,
        shared: &[(&SemanticId, Vec<Pattern>, Option<bool>)],
    ) -> Option<String> {
        if shared.is_empty() {
            return None;
        }
        let instances = shared
            .iter()
            .map(|(cell, items, open)| {
                let items = items
                    .iter()
                    .map(|item| instance(unifier, item, WITNESS_DEPTH))
                    .collect::<Option<Vec<_>>>()?;
                Some((*cell, items, *open))
            })
            .collect::<Option<Vec<_>>>()?;
        let mut occurrences = BTreeMap::new();
        for (_, items, _) in &instances {
            for item in items {
                count_variables(item, &mut occurrences);
            }
        }
        let mut names = BTreeMap::new();
        let mut written = Vec::new();
        for (cell, items, open) in &instances {
            let mut terms = items
                .iter()
                .map(|item| {
                    self.subjects
                        .render(unifier, item, None, &occurrences, &mut names)
                })
                .collect::<Option<Vec<_>>>()?;
            let name = self.cells.get(cell).map_or("?", |(_, name)| name);
            written.push(match open {
                None => format!("{name}: {}", terms.join(", ")),
                Some(open) => {
                    if *open {
                        terms.push("..".to_owned());
                    }
                    format!("{name}: [{}]", terms.join(", "))
                }
            });
        }
        Some(written.join(", "))
    }

    /// How an end's clause and another sentence's patterns are shown to hold of one state.
    ///
    /// `second_whole` says whether `second` is all the second sentence's left side requires: a
    /// side that leaves requirements out is still covered where its patterns are, and is not
    /// shown to cover or to meet anything.
    fn shown(
        &self,
        first: &[Raw<'m>],
        first_guarded: bool,
        second: &[Raw<'m>],
        second_guarded: bool,
        second_whole: bool,
    ) -> Option<Shown> {
        let [first_choices, second_choices] = [first, second].map(Self::alternatives);
        // An end's clause holds no or-pattern in what this module reads of it: with one, its
        // alternatives are several clauses, which are not judged.
        let [first_choice] = first_choices.as_slice() else {
            return None;
        };
        let first_side = self.side(first, 0, first_choice);
        let seconds = second_choices
            .iter()
            .map(|choice| self.side(second, 1, choice))
            .collect::<Vec<_>>();
        if !first_guarded
            && seconds
                .iter()
                .all(|second| self.covers(&first_side, second))
        {
            return Some(Shown::FirstCovers);
        }
        if second_guarded || !second_whole {
            return None;
        }
        if seconds
            .iter()
            .any(|second| self.covers(second, &first_side))
        {
            return Some(Shown::SecondCovers);
        }
        if first_guarded {
            return None;
        }
        seconds
            .iter()
            .find_map(|second| self.meet(&first_side, second))
    }

    /// `krs::analysis::end-not-terminal`: one warning for `end`, about the first rule shown to
    /// apply at its states, with the others named.
    fn not_terminal(&self, end: &EndView<'m>, rules: &[RuleView<'m>]) -> Option<Diagnostic> {
        let mut found = rules.iter().filter_map(|rule| {
            let shown = self.shown(
                &end.raws,
                end.guarded,
                &rule.raws,
                rule.guarded,
                !rule.partial,
            )?;
            Some((rule, shown))
        });
        let (rule, shown) = found.next()?;
        let name = end.mark.item;
        let by = rule.rule.id().item_name();
        let message = match &shown {
            Shown::FirstCovers => format!(
                "the end `{name}` holds at every state the rule `{by}` applies to: `{name}` has no condition, and its pattern matches every state the left side of `{by}` matches. A rule applies at those states, so the run is not over there, and `{name}` is true at states that are not ends"
            ),
            Shown::SecondCovers => format!(
                "a rule applies at every state of the end `{name}`: the rule `{by}` has no condition, and its left side matches every state the pattern of `{name}` matches, so `{by}` or a rule that goes before it applies there. `{name}` is true at no state where the run is over"
            ),
            Shown::Meet(witness) => format!(
                "the end `{name}` holds at states where a rule applies: neither `{name}` nor the rule `{by}` has a condition, and {}. `{by}` or a rule that goes before it applies there, so the run is not over, and `{name}` is true at states that are not ends",
                match witness {
                    Some(witness) => format!(
                        "the pattern of `{name}` and the left side of `{by}` both match every state with `{witness}`"
                    ),
                    None => format!(
                        "the pattern of `{name}` and the left side of `{by}` read no cell in common, so both match one state"
                    ),
                }
            ),
        };
        let mut warning = self.warning(codes::analysis::END_NOT_TERMINAL, message, end.rule);
        if let Some(range) = rule.rule.origin().origin().exact_authored_range() {
            warning = warning.with_secondary(
                Label::new(Location::Source(range)).with_message(format!("the rule `{by}`")),
            );
        }
        let others = found
            .map(|(rule, _)| format!("`{}`", rule.rule.id().item_name()))
            .collect::<BTreeSet<_>>();
        if !others.is_empty() {
            warning = warning.with_note(format!(
                "rules shown to apply at states of `{name}` in the same way or another: {}",
                others.into_iter().collect::<Vec<_>>().join(", ")
            ));
        }
        Some(warning.with_help(match (end.mark.form, &shown) {
            (EndForm::Constructor, Shown::FirstCovers) => format!(
                "`{name}` is declared on a constructor, so it holds wherever the main computation cell starts with that constructor, whatever the other cells hold, and `{by}` takes the constructor there. An end states where no rule applies: declare it with `#[k::end({})]` on a `fn` whose `k::cells!` pattern and `#[k::requires]` state the states `{by}` leaves, in the package that holds `{by}`",
                end.mark.class.word(),
            ),
            (EndForm::Constructor, _) => format!(
                "`{name}` is declared on a constructor, so it holds wherever the main computation cell starts with that constructor, whatever the other cells hold. Declare it with `#[k::end({})]` on a `fn` whose `k::cells!` pattern and `#[k::requires]` leave out the states `{by}` applies to",
                end.mark.class.word(),
            ),
            (EndForm::Clause, _) => format!(
                "narrow the pattern of `{name}`, or give it a `#[k::requires]` that is false wherever `{by}` applies"
            ),
        }))
    }

    /// `krs::analysis::end-classes-overlap`: two ends of different classes shown to hold of one
    /// state, reported at the later one.
    fn classes_overlap(&self, earlier: &EndView<'m>, later: &EndView<'m>) -> Option<Diagnostic> {
        if earlier.mark.class == later.mark.class {
            return None;
        }
        let shown = self.shown(
            &later.raws,
            later.guarded,
            &earlier.raws,
            earlier.guarded,
            true,
        )?;
        let class = |end: &EndView<'_>| end.mark.class.word();
        let covering = |general: &EndView<'_>, specific: &EndView<'_>| {
            format!(
                "the end `{}` ({}) holds at every state of the end `{}` ({}): `{0}` has no condition, and its pattern matches every state the pattern of `{2}` matches",
                general.mark.item,
                class(general),
                specific.mark.item,
                class(specific),
            )
        };
        let fact = match &shown {
            Shown::FirstCovers => covering(later, earlier),
            Shown::SecondCovers => covering(earlier, later),
            Shown::Meet(witness) => format!(
                "the ends `{}` ({}) and `{}` ({}) both hold at one state: neither has a condition, and {}",
                earlier.mark.item,
                class(earlier),
                later.mark.item,
                class(later),
                match witness {
                    Some(witness) => {
                        format!("their patterns both match every state with `{witness}`")
                    }
                    None => "their patterns read no cell in common".to_owned(),
                }
            ),
        };
        let mut warning = self.warning(
            codes::analysis::END_CLASSES_OVERLAP,
            format!(
                "{fact}. A state where the run is over is in one class, and this one is in both, so the definition contradicts itself there"
            ),
            later.rule,
        );
        if let Some(range) = earlier.rule.origin().origin().exact_authored_range() {
            warning = warning.with_secondary(
                Label::new(Location::Source(range))
                    .with_message(format!("the end `{}`", earlier.mark.item)),
            );
        }
        Some(warning.with_help(
            "state in each end's pattern or `#[k::requires]` what keeps its states out of the other",
        ))
    }

    /// The head of `rule`'s subject in the main computation cell, and what its result puts
    /// there: the items, and whether the subject's rest follows them.
    fn main_rewrite(
        &self,
        rule: &'m SemanticRule,
    ) -> Option<(&'m SemanticTerm, Vec<&'m SemanticTerm>, bool)> {
        fn items(term: &SemanticTerm) -> Vec<&SemanticTerm> {
            match term.kind() {
                SemanticTermKind::KSequence { items, .. } => items.iter().collect(),
                _ => vec![term],
            }
        }
        let main = self.main_cell()?;
        match rule.relational_body() {
            RuleBodyRef::Term(body) => Some((*items(body.from()).first()?, items(body.to()), true)),
            RuleBodyRef::Configuration { body, .. } => {
                let clause = body
                    .clauses()
                    .iter()
                    .filter_map(ConfigurationClause::as_fixed)
                    .find(|clause| clause.cell() == main && clause.kind().is_content())?;
                let open = match clause.frame() {
                    CellContentFrame::Exact => false,
                    CellContentFrame::KSequenceTail { .. } => true,
                    _ => return None,
                };
                let before = items(clause.before());
                let head = *before.first()?;
                match clause.after() {
                    CellPost::Replace { term } => Some((head, items(term), open)),
                    // A rewrite written in place: the head's own, with the items after it
                    // kept.
                    CellPost::Local => match head.kind() {
                        SemanticTermKind::Rewrite { from, to } => Some((
                            from,
                            std::iter::once(&**to)
                                .chain(before[1..].iter().copied())
                                .collect(),
                            open,
                        )),
                        _ => None,
                    },
                    CellPost::Preserve => None,
                }
            }
            RuleBodyRef::Predicate(_) => None,
        }
    }

    /// `krs::analysis::end-catch-all`: `rule` goes after the default priority, its subject's
    /// head is a binder, and the state it gives is in a `refused` end, whatever the head was.
    fn catch_all(&self, rule: &RuleView<'m>, ends: &[EndView<'m>]) -> Option<Diagnostic> {
        if !rule.owise && rule.priority <= DEFAULT_PRIORITY {
            return None;
        }
        let main = self.main_cell()?;
        let (head, result, open) = self.main_rewrite(rule.rule)?;
        let SemanticTermKind::Variable { .. } = head.kind() else {
            return None;
        };
        // A binder of sort `K` stands for any number of items, the empty computation among
        // them, and is no head.
        if *head.sort() == SemanticSortRef::Builtin(BuiltinSort::KSequence) {
            return None;
        }
        let mut catalog = VariableCatalog::default();
        let written = Content {
            cell: main,
            shape: Shape::Sequence {
                items: result
                    .iter()
                    .map(|item| pattern(item, 1, &mut catalog))
                    .collect(),
                open,
            },
            rest: None,
        };
        let end = ends.iter().find(|end| {
            if end.mark.class != EndClass::Refused || end.guarded {
                return false;
            }
            let alternatives = Self::alternatives(&end.raws);
            let [choice] = alternatives.as_slice() else {
                return false;
            };
            let side = self.side(&end.raws, 0, choice);
            // The end reads the main cell alone, so the state the rule gives is in it by what
            // the rule writes there.
            side.content(main)
                .is_some_and(|content| self.content_covers(content, &side, &written))
                && side
                    .contents
                    .iter()
                    .all(|content| content.cell == main || self.requires_nothing(content, &side))
        })?;
        let name = rule.rule.id().item_name();
        let after = if rule.owise {
            "`owise`, so it applies where no other rule does".to_owned()
        } else {
            format!(
                "at priority {}, so it applies where no rule at the default priority {DEFAULT_PRIORITY} does",
                rule.priority
            )
        };
        let condition = if rule.guarded {
            ", where its condition holds"
        } else {
            ""
        };
        Some(
            self.warning(
                codes::analysis::END_CATCH_ALL,
                format!(
                    "the rule `{name}` makes a state of the refused end `{}` out of every head of sort `{}` no other rule takes: the head of its subject in the main computation cell is a binder of that sort, it is {after}{condition}, and the state it gives is in `{0}`. A head the definition has no rule for by omission is then refused like one it refuses on purpose, and no run ends at it outside the declared ends",
                    end.mark.item,
                    crate::partition::sort_display(head.sort()),
                ),
                rule.rule,
            )
            .with_help(format!(
                "a refusal is stated, not inferred from the absence of a rule: write a rule to `{}` for each head that is refused, or declare the end on a `fn` whose `k::cells!` pattern names it, and leave the other heads without a rule, where a run ends at no declared end",
                end.mark.item,
            )),
        )
    }

    /// A warning at the sentence `at`.
    fn warning(
        &self,
        code: krs_diagnostic::Code,
        message: String,
        at: &SemanticRule,
    ) -> Diagnostic {
        let _ = self;
        let mut warning = match at.origin().origin().exact_authored_range() {
            Some(range) => Diagnostic::error(code, message, Location::Source(range)),
            None => Diagnostic::error(code, message, Location::None).with_item(at.id().to_string()),
        };
        warning.severity = Severity::Warning;
        warning
    }
}

/// Counts each variable's occurrences in `pattern`, and says whether it holds names the count
/// does not see.
fn count(pattern: &Pattern, counts: &mut BTreeMap<VariableKey, usize>, hidden: &mut bool) {
    match pattern {
        Pattern::Variable { key, .. } => *counts.entry(*key).or_default() += 1,
        Pattern::Application { arguments, .. }
        | Pattern::KSequence {
            items: arguments, ..
        }
        | Pattern::Map { arguments, .. }
        | Pattern::List { arguments, .. }
        | Pattern::Set { arguments, .. }
        | Pattern::Cell {
            children: arguments,
            ..
        } => {
            for argument in arguments {
                count(argument, counts, hidden);
            }
        }
        Pattern::Matches { .. } | Pattern::Opaque { .. } => *hidden = true,
        Pattern::Token { .. } => {}
    }
}
