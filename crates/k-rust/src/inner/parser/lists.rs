//! ```toml algorithm
//! id = "parser.grammar.lists"
//! name = "generation and reconstruction of implicit user lists"
//! sites = ["Grammar::initialize_user_lists", "Grammar::program_list_terminator"]
//! variable = "L = list declarations; R = productions in the grammar"
//! counters = []
//! no_counter = "implicit-list processing has no dedicated counter"
//!
//! [[cost]]
//! mode = "grammar insertion"
//! bound = "O(R + L x R)"
//!
//! [[cost]]
//! mode = "program-list terminator lookup"
//! bound = "O(L) per child, plus the structural ordering of the terminator alternatives of an ambiguity at a list's tail"
//! ```
//!
//! ```toml algorithm
//! id = "parser.disambiguation.insert_empty_lists"
//! name = "insertion of implicit empty user lists"
//! sites = ["Grammar::add_packed_empty_lists", "Grammar::complete_packed_lists", "Grammar::complete_packed_list_child", "Grammar::wrap_packed_list_child", "Grammar::packed_list_sort", "Grammar::list_instantiation", "Grammar::singleton_list"]
//! variable = "N = session nodes reachable from the forest, with the singleton lists the pass builds; E = their child edges; S = distinct sorts a node is expected at; C = candidate list instantiations"
//! counters = []
//! no_counter = "empty-list insertion has no dedicated counter"
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one packed forest"
//! bound = "O((N + E) x S x C), each node's result, wrapping and list sort computed once per expected sort, plus one PartialOrder::new over the subsort relations the first time a grammar needs its order, and the structural ordering of an ambiguity's alternatives only where they fail or two results are equal as terms"
//! ```
//!
//! The constructors and terminators a user-list declaration (`List{S, ","}`) implies, and the
//! reconstruction of list terms from their parses.
//!
//! Grammar insertion is O(productions + list declarations * productions); list reconstruction
//! is O(session nodes * expected sorts * candidate instantiations) and recursively preserves
//! declared child sorts.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use k_rust_kore::measure::{self, Algorithm};

use crate::definition::{PartialOrder, ProductionItem};
use crate::kast::{FrontendSort, GeneratedLabel, InternalLabel, Sort, Term};
use crate::names::BuiltinSort;

use super::disambiguation::collect_in_structural_order;
use super::parametric::substitute_sort;
use super::{
    Grammar, Item, LoweringSession, PackedNode, PackedTerm, ParametricOrigin, ParseError,
    ParserRole, ProductionOptions, StructuralOrder, TermMetadata,
};
#[cfg(test)]
use super::{ParsedParts, ParsedTerm};

/// The list sorts ([`Grammar::list_sort`]) computed for one node of a tree that list completion
/// is reading, by expected sort, and those of the node's children, kept beside the node as
/// [`Grammar::add_empty_lists_with_order`] takes the tree apart so that no node is
/// instantiated twice for one expected sort. Results are attached to the node they were
/// computed for, not looked up by its address: completion moves each child out of its parent
/// before it inspects it.
#[cfg(test)]
#[derive(Debug, Default)]
struct ListSorts {
    by_expected: Vec<(Option<Sort>, Sort)>,
    children: Vec<ListSorts>,
}

#[derive(Clone, Debug)]
pub(super) struct UserList {
    child_sort: Sort,
    list_production: usize,
    terminator_production: usize,
    left_associative: bool,
}

impl Grammar {
    /// Recognize each lowered `userList` pair and add the temporary
    /// `ListSort ::= ElementSort` injection used by K's rule grammar.
    pub(super) fn initialize_user_lists(&mut self) -> Result<(), ParseError> {
        self.invalidate_prediction_analysis();
        let mut grouped = BTreeMap::<Sort, Vec<usize>>::new();
        for (index, production) in self.productions.iter().enumerate() {
            if production.user_list {
                grouped
                    .entry(production.result.clone())
                    .or_default()
                    .push(index);
            }
        }

        let mut lists = BTreeMap::new();
        for (sort, productions) in grouped {
            let recursive = productions
                .iter()
                .copied()
                .filter(|production| nonterminal_sorts(&self.productions[*production]).len() == 2)
                .collect::<Vec<_>>();
            let terminators = productions
                .iter()
                .copied()
                .filter(|production| nonterminal_sorts(&self.productions[*production]).is_empty())
                .collect::<Vec<_>>();
            let ([list_production], [terminator_production]) =
                (recursive.as_slice(), terminators.as_slice())
            else {
                return Err(list_error(format!(
                    "expected exactly one recursive and one terminator production for user list sort {sort}"
                )));
            };
            let arguments = nonterminal_sorts(&self.productions[*list_production]);
            let (child_sort, left_associative) = match arguments.as_slice() {
                [list, child] if *list == &sort => ((*child).clone(), true),
                [child, list] if *list == &sort => ((*child).clone(), false),
                _ => {
                    return Err(list_error(format!(
                        "recursive production for user list sort {sort} must contain the list sort on exactly one side"
                    )));
                }
            };
            lists.insert(
                sort,
                UserList {
                    child_sort,
                    list_production: *list_production,
                    terminator_production: *terminator_production,
                    left_associative,
                },
            );
        }

        // A program grammar parses the empty list as the empty string. K's program grammar
        // then splits each list with a visible separator into K's own shape,
        //
        //     Xs ::= Ne#Xs | ""        Ne#Xs ::= X sep Ne#Xs | X
        //
        // so the empty list is only ever the whole list, never the tail after a separator
        // (`1,2,` does not parse). The `Ne#Xs` productions are parse-time only: their forest
        // nodes carry the source list production's identity, exactly like the temporary
        // concrete variants of parametric productions.
        //
        // When the separator is also empty, `X sep Xs` with an empty tail already derives
        // every lone element for `List`; neither the split nor the singleton injection is
        // needed there. `NeList` hides its empty terminator, however, so it needs the
        // singleton injection to retain that derivation without admitting an empty list.
        let mut injections = Vec::new();
        let mut splits = Vec::new();
        let mut nonempty_terminators = Vec::new();
        for (sort, list) in &lists {
            let terminator = &self.productions[list.terminator_production];
            let recursive = &self.productions[list.list_production];
            if terminator.items.is_empty() {
                if terminator.user_list_nonempty {
                    nonempty_terminators.push((sort.clone(), list.terminator_production));
                }
                if has_visible_terminal(recursive) {
                    splits.push((sort.clone(), list.clone()));
                } else if terminator.user_list_nonempty {
                    // With an empty separator, the recursive production has no base once
                    // the NeList terminator is hidden, so retain its singleton injection.
                    injections.push((sort.clone(), list.child_sort.clone()));
                }
            } else {
                injections.push((sort.clone(), list.child_sort.clone()));
            }
        }
        self.user_lists = lists;
        // The erased terminator still provides the empty-list production needed by `List`,
        // but `NeList` must not retain that `Sort ::= ""` alternative. Keep its production
        // identity for list reconstruction while removing it from the parse index.
        for (sort, terminator) in nonempty_terminators {
            if let Some(indices) = self
                .sort_id(&sort)
                .and_then(|id| self.by_result.get_mut(id))
            {
                indices.retain(|index| *index != terminator);
            }
        }
        for (sort, list) in splits {
            self.split_program_list(&sort, &list)?;
        }
        for (sort, child_sort) in injections {
            // The injection writes a lone element as the list of it, as a program writes that
            // list, so it is program text exactly when the list is.
            let list_production = self.user_lists[&sort].list_production;
            let program_text = self.productions[list_production].program_text;
            let exists = self.productions.iter().any(|production| {
                production.result == sort
                    && production.label.is_none()
                    && matches!(
                        production.items.as_slice(),
                        [Item::NonTerminal(child)] if child == &child_sort
                    )
            });
            if !exists {
                let injection = self.productions.len();
                self.add(
                    sort,
                    vec![ProductionItem::NonTerminal {
                        sort: child_sort,
                        name: None,
                    }],
                    None,
                    false,
                    true,
                )?;
                self.productions[injection].program_text = program_text;
            }
        }
        Ok(())
    }

    /// Replace a program-grammar list with a visible separator by K's non-empty split.
    fn split_program_list(&mut self, sort: &Sort, list: &UserList) -> Result<(), ParseError> {
        self.invalidate_prediction_analysis();
        let nonempty = Sort::with_parameters(format!("Ne#{}", sort.name), sort.parameters.clone());
        let terminator_sort =
            Sort::with_parameters(format!("{}#Terminator", sort.name), sort.parameters.clone());
        let recursive = self.productions[list.list_production].clone();
        let terminator = self.productions[list.terminator_production].clone();
        let label = recursive.label.clone();
        let source_production = recursive.source_production;
        let items = recursive
            .items
            .iter()
            .map(|item| match item {
                Item::NonTerminal(child) if child == sort => Ok(ProductionItem::NonTerminal {
                    sort: nonempty.clone(),
                    name: None,
                }),
                Item::NonTerminal(child) => Ok(ProductionItem::NonTerminal {
                    sort: child.clone(),
                    name: None,
                }),
                Item::Terminal(text) => Ok(ProductionItem::Terminal(text.clone())),
                Item::Regex { .. } => Err(list_error(format!(
                    "user list sort {sort} has a regular-expression separator"
                ))),
            })
            .collect::<Result<Vec<_>, _>>()?;

        // The source production no longer parses directly; only its `Ne#` variant does.
        if let Some(indices) = self.sort_id(sort).and_then(|id| self.by_result.get_mut(id)) {
            indices.retain(|index| *index != list.list_production);
        }
        let split = self.productions.len();
        self.add_production_with_lexical(
            nonempty.clone(),
            &items,
            label,
            ProductionOptions {
                program_text: recursive.program_text,
                source_production,
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )?;
        self.productions[split].term_production = Some(list.list_production);

        // K's program grammar does not make the singleton branch a transparent
        // `Ne#Xs ::= X` injection. It generates `Xs#Terminator ::= ""` and parses
        // the singleton as the original list constructor over `X` and that hidden
        // terminator. Retaining both original production identities here prevents a
        // transparent enclosing start sort from erasing the list node altogether.
        let hidden_terminator = self.productions.len();
        self.add_production_with_lexical(
            terminator_sort.clone(),
            &[ProductionItem::Terminal(String::new())],
            terminator.label.clone(),
            ProductionOptions {
                program_text: recursive.program_text,
                source_production: terminator.source_production,
                source_production_text: terminator.source_production_text.as_ref(),
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )?;
        self.productions[hidden_terminator].term_production = Some(list.terminator_production);

        let child = ProductionItem::NonTerminal {
            sort: list.child_sort.clone(),
            name: None,
        };
        let hidden_terminator = ProductionItem::NonTerminal {
            sort: terminator_sort,
            name: None,
        };
        let singleton_items = if list.left_associative {
            vec![hidden_terminator, child]
        } else {
            vec![child, hidden_terminator]
        };
        let singleton = self.productions.len();
        self.add_production_with_lexical(
            nonempty.clone(),
            &singleton_items,
            recursive.label.clone(),
            ProductionOptions {
                program_text: recursive.program_text,
                source_production: recursive.source_production,
                source_production_text: recursive.source_production_text.as_ref(),
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )?;
        self.productions[singleton].term_production = Some(list.list_production);
        // The former transparent singleton production also made the element a
        // temporary subsort of `Ne#Xs`. K's generated singleton is a real list
        // constructor, but its user-list metadata provides the equivalent relation
        // to sort inference. Preserve that relation without adding a competing parse.
        self.subsort_relations
            .insert((list.child_sort.clone(), nonempty.clone()));
        self.syntactic_subsort_relations
            .insert((list.child_sort.clone(), nonempty.clone()));
        let injection = self.productions.len();
        self.add(
            sort.clone(),
            vec![ProductionItem::NonTerminal {
                sort: nonempty,
                name: None,
            }],
            None,
            false,
            true,
        )?;
        self.productions[injection].program_text = recursive.program_text;
        Ok(())
    }

    /// Keep an empty-separator program list's own terminator when it is the direct tail of that
    /// list's recursive production. Overload resolution may otherwise replace the tail with the
    /// shared least terminator, even though K's program parser preserves the enclosing list's
    /// concrete representation.
    ///
    /// `child` is the input node at that position: the terminator itself, or the structurally
    /// first alternative of an ambiguity there that is one, kept as it is.
    pub(super) fn program_list_terminator(
        &self,
        order: &mut StructuralOrder,
        parent: usize,
        child_index: usize,
        child: &Rc<PackedTerm>,
    ) -> Option<Rc<PackedTerm>> {
        let terminator = self.program_list_tail_terminator(parent, child_index)?;
        let is_terminator = |term: &Rc<PackedTerm>| {
            matches!(&term.node, PackedNode::Production { production, children, .. }
                if *production == terminator && children.is_empty())
        };
        match &child.node {
            PackedNode::Ambiguity(alternatives) => alternatives
                .iter()
                .filter(|term| is_terminator(term))
                .min_by(|left, right| order.cmp(left, right))
                .cloned(),
            _ if is_terminator(child) => Some(Rc::clone(child)),
            _ => None,
        }
    }

    /// The terminator production of the empty-separator program list whose recursive production
    /// is `parent`, when `child_index` is that production's tail position.
    fn program_list_tail_terminator(&self, parent: usize, child_index: usize) -> Option<usize> {
        if self.role != ParserRole::Program {
            return None;
        }
        let list = self
            .user_lists
            .values()
            .find(|list| list.list_production == parent)?;
        let tail_index = usize::from(!list.left_associative);
        (child_index == tail_index).then_some(list.terminator_production)
    }

    /// The owned-tree form of [`Self::program_list_terminator`], for the tests' owned-tree
    /// terminator resolution.
    #[cfg(test)]
    pub(super) fn program_list_terminator_tree(
        &self,
        parent: usize,
        child_index: usize,
        child: &ParsedTerm,
    ) -> Option<ParsedTerm> {
        let terminator = self.program_list_tail_terminator(parent, child_index)?;
        let is_terminator = |term: &ParsedTerm| {
            matches!(term, ParsedTerm::Production { production, children, .. }
                if *production == terminator && children.is_empty())
        };
        match child {
            ParsedTerm::Ambiguity(alternatives) => alternatives
                .iter()
                .find(|term| is_terminator(term))
                .cloned(),
            _ if is_terminator(child) => Some(child.clone()),
            _ => None,
        }
    }

    /// Reconstruct the real list nodes of an owned tree; see [`Self::add_packed_empty_lists`],
    /// which this runs on the tree's packed form.
    #[cfg(test)]
    pub(super) fn add_empty_lists(
        &self,
        term: ParsedTerm,
        expected: &Sort,
    ) -> Result<ParsedTerm, ParseError> {
        let tree = self.add_empty_lists_tree(term.clone(), expected);
        let mut session = LoweringSession::default();
        let packed = session.intern_parsed(&term);
        drop(term);
        let completed = self
            .add_packed_empty_lists(&mut session, &packed, expected)
            .map(|completed| completed.unpack());
        assert!(
            match (&completed, &tree) {
                (Ok(completed), Ok(tree)) => completed.identical(tree),
                (Err(completed), Err(tree)) => completed == tree,
                _ => false,
            },
            "completing the lists of the packed tree differs from the owned tree:\n\
             {completed:?}\n{tree:?}"
        );
        completed
    }

    /// Reconstruct real list nodes after inference has consumed the temporary singleton-list
    /// subsorts: a child expected at a user-list sort whose own sort is below the list's
    /// element sort becomes the singleton list of it, the list's constructor over the child and
    /// a terminator ([`Self::singleton_list`]). `expected` is the sort the root is expected at.
    ///
    /// What a node becomes is a function of the node and the sort its position expects: the
    /// expected sort of each child is decided at the node from its production, its
    /// instantiation for that expected sort and the sorts of its input children, and whether a
    /// child is wrapped is decided from the child and its expected sort. So the result is
    /// computed once per session node and expected sort, for the nodes of the forest and for
    /// the singleton lists the pass builds alike, and an ambiguity, whose alternatives are
    /// completed at its own expected sort and never wrapped, keeps their results as they come,
    /// even when two become equal. The error is the first a depth-first walk meets: at a
    /// node, the instantiation of an instantiated one, then the number of its children, then
    /// each child left to right, its wrapping before what lies below it; at an ambiguity, its
    /// alternatives in structural order.
    pub(super) fn add_packed_empty_lists(
        &self,
        session: &mut LoweringSession,
        term: &Rc<PackedTerm>,
        expected: &Sort,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let _span = measure::algorithm_span(Algorithm::ParserDisambiguationInsertEmptyLists);
        let subsorts =
            self.subsort_relations
                .order()
                .map_err(|cycle| ParseError::CircularSubsorts {
                    path: cycle.path.clone(),
                })?;
        let mut lists = PackedLists::default();
        self.complete_packed_lists(session, &mut lists, subsorts, term, expected)
    }

    /// The node `term` becomes at a position expected at `expected`
    /// ([`Self::add_packed_empty_lists`]), memoized in `lists`.
    fn complete_packed_lists(
        &self,
        session: &mut LoweringSession,
        lists: &mut PackedLists,
        subsorts: &PartialOrder<Sort>,
        term: &Rc<PackedTerm>,
        expected: &Sort,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        if let Some(known) = PackedLists::known(&lists.completed, term, expected) {
            return known;
        }
        let result = crate::stack::guarded(|| {
            self.complete_packed_lists_node(session, lists, subsorts, term, expected)
        });
        lists
            .completed
            .entry(Rc::as_ptr(term))
            .or_default()
            .push((expected.clone(), result.clone()));
        result
    }

    fn complete_packed_lists_node(
        &self,
        session: &mut LoweringSession,
        lists: &mut PackedLists,
        subsorts: &PartialOrder<Sort>,
        term: &Rc<PackedTerm>,
        expected: &Sort,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        match &term.node {
            PackedNode::Term(_) => Ok(Rc::clone(term)),
            PackedNode::Ambiguity(alternatives) => {
                let results = alternatives
                    .iter()
                    .map(|alternative| {
                        let result = self.complete_packed_lists(
                            session,
                            lists,
                            subsorts,
                            alternative,
                            expected,
                        );
                        (Rc::clone(alternative), result)
                    })
                    .collect::<Vec<_>>();
                if results.iter().any(|(_, result)| result.is_err()) {
                    let mut failed = results
                        .into_iter()
                        .filter_map(|(alternative, result)| Some((alternative, result.err()?)))
                        .collect::<Vec<_>>();
                    failed.sort_by(|(left, _), (right, _)| session.order.cmp(left, right));
                    let (_, first) = failed.swap_remove(0);
                    return Err(first);
                }
                let results = results
                    .into_iter()
                    .map(|(alternative, result)| (alternative, result.expect("checked above")))
                    .collect::<Vec<_>>();
                if results
                    .iter()
                    .all(|(alternative, result)| Rc::ptr_eq(alternative, result))
                {
                    return Ok(Rc::clone(term));
                }
                let alternatives = collect_in_structural_order(&mut session.order, results);
                Ok(session.intern(PackedTerm::alternatives(alternatives)))
            }
            PackedNode::Production {
                production,
                children,
                metadata,
            } => {
                let descriptor = &self.productions[*production];
                let expected_children = nonterminal_sorts(descriptor);
                check_list_arity(descriptor, expected_children.len(), children.len())?;
                let wraps = !shields_children(descriptor);
                let rewrite_sort = self.rewrite_list_sort(
                    descriptor,
                    children.iter().map(|child| packed_parsed_sort(self, child)),
                );
                let mut completed = Vec::with_capacity(children.len());
                for (child, expected_child) in children.iter().zip(expected_children) {
                    let expected_child = rewrite_sort.as_ref().unwrap_or(expected_child);
                    completed.push(self.complete_packed_list_child(
                        session,
                        lists,
                        subsorts,
                        child,
                        expected_child,
                        wraps,
                    )?);
                }
                if packed_children_unchanged(children, &completed) {
                    return Ok(Rc::clone(term));
                }
                Ok(session.intern(PackedTerm::production(
                    *production,
                    completed,
                    metadata.clone(),
                )))
            }
            PackedNode::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => {
                let descriptor = &self.productions[*production];
                // Children are completed against the production instantiated from the node's
                // expected sort and its children's sorts, not against the parser's inferred
                // parameters: a parameter stands for the sort of every position it occupies,
                // so it is the least sort that holds them all. The two differ for a binder
                // position such as `#let X = e #in ...`: inference leaves the child-only
                // `Sort2` at `K`, while the binder equates `X` and `e`, so `Sort2` is
                // `lub(sort(X), sort(e))`, and an element-sorted `X` bound to a user list is
                // completed to the singleton list `X .Xs` before ResolveFun reads the binder.
                let expected_children = if let Some(origin) = &descriptor.parametric_origin {
                    self.list_instantiation(
                        origin,
                        parameters,
                        Some(expected),
                        children.len(),
                        subsorts,
                        |index, child_expected| {
                            self.packed_list_sort(lists, subsorts, &children[index], child_expected)
                        },
                    )?
                    .0
                } else {
                    nonterminal_sorts(descriptor).into_iter().cloned().collect()
                };
                check_list_arity(descriptor, expected_children.len(), children.len())?;
                let rewrite_sort = self.rewrite_list_sort(
                    descriptor,
                    children.iter().map(|child| packed_parsed_sort(self, child)),
                );
                let mut completed = Vec::with_capacity(children.len());
                for (child, expected_child) in children.iter().zip(&expected_children) {
                    let expected_child = rewrite_sort.as_ref().unwrap_or(expected_child);
                    completed.push(self.complete_packed_list_child(
                        session,
                        lists,
                        subsorts,
                        child,
                        expected_child,
                        true,
                    )?);
                }
                if packed_children_unchanged(children, &completed) {
                    return Ok(Rc::clone(term));
                }
                Ok(session.intern(PackedTerm::instantiated_production(
                    *production,
                    parameters.clone(),
                    completed,
                    metadata.clone(),
                )))
            }
        }
    }

    /// What the child `child` of a node becomes at its position, expected at `expected`: the
    /// singleton list of it when `wraps` and the position needs one, then completed below.
    fn complete_packed_list_child(
        &self,
        session: &mut LoweringSession,
        lists: &mut PackedLists,
        subsorts: &PartialOrder<Sort>,
        child: &Rc<PackedTerm>,
        expected: &Sort,
        wraps: bool,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let child = if wraps && self.user_lists.contains_key(expected) {
            match PackedLists::known(&lists.wrapped, child, expected) {
                Some(known) => known?,
                None => {
                    let wrapped =
                        self.wrap_packed_list_child(session, lists, subsorts, child, expected);
                    lists
                        .wrapped
                        .entry(Rc::as_ptr(child))
                        .or_default()
                        .push((expected.clone(), wrapped.clone()));
                    wrapped?
                }
            }
        } else {
            Rc::clone(child)
        };
        self.complete_packed_lists(session, lists, subsorts, &child, expected)
    }

    /// `child`, or the singleton list of it that its position at the user-list sort
    /// `expected` needs, interned.
    fn wrap_packed_list_child(
        &self,
        session: &mut LoweringSession,
        lists: &mut PackedLists,
        subsorts: &PartialOrder<Sort>,
        child: &Rc<PackedTerm>,
        expected: &Sort,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let child_sort = self.packed_list_sort(lists, subsorts, child, Some(expected))?;
        let bracket = matches!(&child.node, PackedNode::Production { production, .. }
            if self.productions[*production].bracket);
        let Some((list, terminator)) =
            self.singleton_list(bracket, &child_sort, expected, subsorts)?
        else {
            return Ok(Rc::clone(child));
        };
        let terminator = session.intern(PackedTerm::production(
            terminator,
            Vec::new(),
            TermMetadata::default(),
        ));
        let children = if list.left_associative {
            vec![terminator, Rc::clone(child)]
        } else {
            vec![Rc::clone(child), terminator]
        };
        Ok(session.intern(PackedTerm::production(
            list.list_production,
            children,
            TermMetadata::default(),
        )))
    }

    /// The list sort of a session node at `expected`, as [`Self::list_instantiation`] and
    /// [`packed_parsed_sort`] give it (see the owned form, `list_sort`), computed once per node
    /// and expected sort: a nesting of instances is then instantiated once per level, however
    /// often list completion asks.
    fn packed_list_sort(
        &self,
        lists: &mut PackedLists,
        subsorts: &PartialOrder<Sort>,
        term: &Rc<PackedTerm>,
        expected: Option<&Sort>,
    ) -> Result<Sort, ParseError> {
        let PackedNode::InstantiatedProduction {
            production,
            parameters,
            children,
            ..
        } = &term.node
        else {
            return Ok(packed_parsed_sort(self, term));
        };
        let Some(origin) = &self.productions[*production].parametric_origin else {
            return Ok(self.productions[*production].result.clone());
        };
        let k = Sort::new("K");
        let expected = list_sort_expectation(expected, &k, subsorts);
        if let Some((_, known)) = lists
            .sorts
            .get(&Rc::as_ptr(term))
            .and_then(|known| known.iter().find(|(known, _)| known.as_ref() == expected))
        {
            return known.clone();
        }
        let sort = crate::stack::guarded(|| {
            self.list_instantiation(
                origin,
                parameters,
                expected,
                children.len(),
                subsorts,
                |index, child_expected| {
                    self.packed_list_sort(lists, subsorts, &children[index], child_expected)
                },
            )
        })
        .map(|(_, sort)| sort);
        lists
            .sorts
            .entry(Rc::as_ptr(term))
            .or_default()
            .push((expected.cloned(), sort.clone()));
        sort
    }

    /// The single sort of a user list among the parsed sorts of a `#KRewrite` node's sides,
    /// at which both sides are then expected: rewrite operands are parsed through generic K
    /// productions, but sort inference still requires both sides to share the function result
    /// sort, so when one side is a user list a singleton element on the other side receives its
    /// real recursive constructor and terminator. `None` for any other production.
    fn rewrite_list_sort(
        &self,
        descriptor: &super::Production,
        children_sorts: impl Iterator<Item = Sort>,
    ) -> Option<Sort> {
        if !descriptor
            .label
            .as_ref()
            .is_some_and(|label| label.is(InternalLabel::KRewrite))
        {
            return None;
        }
        let sorts = children_sorts
            .filter(|sort| self.user_lists.contains_key(sort))
            .collect::<BTreeSet<_>>();
        (sorts.len() == 1).then(|| sorts.into_iter().next().expect("one sort"))
    }

    /// The user list and terminator production of the singleton list that a child of list sort
    /// `child_sort` needs at a position expected at the user-list sort `expected`: `None` when
    /// the child is a list there already, is a bracket, has no sort (`K`) or is not strictly
    /// below `expected`. The list is the least user list whose elements hold the child and
    /// which fits `expected`; its terminator is its own in a program, and otherwise the
    /// terminator of the least user list that fits `expected`.
    fn singleton_list(
        &self,
        bracket: bool,
        child_sort: &Sort,
        expected: &Sort,
        subsorts: &PartialOrder<Sort>,
    ) -> Result<Option<(&UserList, usize)>, ParseError> {
        if self.user_lists.contains_key(child_sort) && subsorts.less_than_eq(child_sort, expected) {
            return Ok(None);
        }
        if bracket
            || child_sort.name == BuiltinSort::K.k_name()
            || !subsorts.less_than(child_sort, expected)
        {
            return Ok(None);
        }

        let candidates = self
            .user_lists
            .iter()
            .filter_map(|(sort, list)| {
                (subsorts.less_than_eq(child_sort, &list.child_sort)
                    && subsorts.less_than_eq(sort, expected))
                .then_some(sort.clone())
            })
            .collect::<BTreeSet<_>>();
        let least = subsorts.minimal(candidates.iter());
        if least.len() != 1 {
            return Err(ParseError::OverloadedTerminator {
                possible_sorts: least.into_iter().collect(),
            });
        }
        let list_sort = least.first().expect("length was checked above");
        let list = &self.user_lists[list_sort];

        let terminator_production = if self.role == ParserRole::Program {
            list.terminator_production
        } else {
            let terminator_candidates = self
                .user_lists
                .keys()
                .filter(|sort| subsorts.less_than_eq(sort, expected))
                .cloned()
                .collect::<BTreeSet<_>>();
            let least_terminators = subsorts.minimal(terminator_candidates.iter());
            if least_terminators.len() != 1 {
                return Err(ParseError::ListTerminator {
                    possible_sorts: least_terminators.into_iter().collect(),
                });
            }
            let terminator_sort = least_terminators.first().expect("length was checked above");
            self.user_lists[terminator_sort].terminator_production
        };
        Ok(Some((list, terminator_production)))
    }

    /// The owned-tree form of [`Self::add_packed_empty_lists`], which the tests check the packed
    /// pass against.
    #[cfg(test)]
    pub(super) fn add_empty_lists_tree(
        &self,
        term: ParsedTerm,
        expected: &Sort,
    ) -> Result<ParsedTerm, ParseError> {
        let subsorts =
            self.subsort_relations
                .order()
                .map_err(|cycle| ParseError::CircularSubsorts {
                    path: cycle.path.clone(),
                })?;
        self.add_empty_lists_with_order(term, expected, subsorts, ListSorts::default())
    }

    /// Complete the lists of `term` at `expected`; `sorts` holds the list sorts already
    /// computed for `term` and below it.
    #[cfg(test)]
    fn add_empty_lists_with_order(
        &self,
        term: ParsedTerm,
        expected: &Sort,
        subsorts: &PartialOrder<Sort>,
        sorts: ListSorts,
    ) -> Result<ParsedTerm, ParseError> {
        crate::stack::guarded(|| {
            match term.into_parts() {
                ParsedParts::Term(leaf) => Ok(ParsedTerm::Term(leaf)),
                ParsedParts::Ambiguity(alternatives) => Ok(ParsedTerm::Ambiguity(
                    alternatives
                        .into_iter()
                        .map(|alternative| {
                            self.add_empty_lists_with_order(
                                alternative,
                                expected,
                                subsorts,
                                ListSorts::default(),
                            )
                        })
                        .collect::<Result<_, _>>()?,
                )),
                ParsedParts::Production {
                    production,
                    children,
                    metadata,
                } => {
                    let descriptor = &self.productions[production];
                    let expected_children = nonterminal_sorts(descriptor);
                    if expected_children.len() != children.len() {
                        return Err(list_error(format!(
                            "production {:?} has {} nonterminals but its parse node has {} children",
                            descriptor.parse_label,
                            expected_children.len(),
                            children.len()
                        )));
                    }
                    let shields_children = descriptor.label.as_ref().is_some_and(|label| {
                        label.is(InternalLabel::SyntacticCast)
                            || label.is(InternalLabel::SyntacticCastBraced)
                            || matches!(
                                label.generated(),
                                Some(GeneratedLabel::SemanticCast { .. })
                            )
                    });
                    // Rewrite operands are parsed through generic K productions, but sort inference
                    // still requires both sides to share the function result sort. Preserve that
                    // context when one side is a user list so a singleton element on the other side
                    // receives its real recursive constructor and terminator.
                    let rewrite_list_sort = descriptor
                        .label
                        .as_ref()
                        .is_some_and(|label| label.is(InternalLabel::KRewrite))
                        .then(|| {
                            children
                                .iter()
                                .map(|child| parsed_sort(self, child))
                                .filter(|sort| self.user_lists.contains_key(sort))
                                .collect::<BTreeSet<_>>()
                        })
                        .and_then(|sorts| {
                            (sorts.len() == 1).then(|| sorts.into_iter().next().unwrap())
                        });
                    let mut child_sorts = sorts.children.into_iter();
                    let children = children
                        .into_iter()
                        .zip(expected_children)
                        .map(|(child, expected_child)| {
                            let expected_child =
                                rewrite_list_sort.as_ref().unwrap_or(expected_child);
                            let sorts = child_sorts.next().unwrap_or_default();
                            let (child, sorts) = if shields_children {
                                (child, sorts)
                            } else {
                                self.wrap_list_child(child, expected_child, subsorts, sorts)?
                            };
                            self.add_empty_lists_with_order(child, expected_child, subsorts, sorts)
                        })
                        .collect::<Result<_, _>>()?;
                    Ok(ParsedTerm::Production {
                        production,
                        children,
                        metadata,
                    })
                }
                ParsedParts::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    metadata,
                } => {
                    let descriptor = &self.productions[production];
                    // Children are completed against the production instantiated from the node's
                    // expected sort and its children's sorts, not against the parser's inferred
                    // parameters: a parameter stands for the sort of every position it occupies, so
                    // it is the least sort that holds them all. The two differ for a binder position
                    // such as `#let X = e #in ...`: inference leaves the child-only `Sort2` at `K`,
                    // while the binder equates `X` and `e`, so `Sort2` is `lub(sort(X), sort(e))`,
                    // and an element-sorted `X` bound to a user list is completed to the singleton
                    // list `X .Xs` before ResolveFun reads the binder.
                    let mut child_sorts = sorts.children;
                    let expected_children = if let Some(origin) = &descriptor.parametric_origin {
                        if child_sorts.len() < children.len() {
                            child_sorts.resize_with(children.len(), ListSorts::default);
                        }
                        self.list_instantiation(
                            origin,
                            &parameters,
                            Some(expected),
                            children.len(),
                            subsorts,
                            |index, child_expected| {
                                self.list_sort(
                                    &children[index],
                                    child_expected,
                                    subsorts,
                                    &mut child_sorts[index],
                                )
                            },
                        )?
                        .0
                    } else {
                        nonterminal_sorts(descriptor).into_iter().cloned().collect()
                    };
                    if expected_children.len() != children.len() {
                        return Err(list_error(format!(
                            "production {:?} has {} nonterminals but its parse node has {} children",
                            descriptor.parse_label,
                            expected_children.len(),
                            children.len()
                        )));
                    }
                    let rewrite_list_sort = descriptor
                        .label
                        .as_ref()
                        .is_some_and(|label| label.is(InternalLabel::KRewrite))
                        .then(|| {
                            children
                                .iter()
                                .map(|child| parsed_sort(self, child))
                                .filter(|sort| self.user_lists.contains_key(sort))
                                .collect::<BTreeSet<_>>()
                        })
                        .and_then(|sorts| {
                            (sorts.len() == 1).then(|| sorts.into_iter().next().unwrap())
                        });
                    let mut child_sorts = child_sorts.into_iter();
                    let children = children
                        .into_iter()
                        .zip(&expected_children)
                        .map(|(child, expected_child)| {
                            let expected_child =
                                rewrite_list_sort.as_ref().unwrap_or(expected_child);
                            let sorts = child_sorts.next().unwrap_or_default();
                            let (child, sorts) =
                                self.wrap_list_child(child, expected_child, subsorts, sorts)?;
                            self.add_empty_lists_with_order(child, expected_child, subsorts, sorts)
                        })
                        .collect::<Result<_, _>>()?;
                    Ok(ParsedTerm::InstantiatedProduction {
                        production,
                        parameters,
                        children,
                        metadata,
                    })
                }
            }
        })
    }

    /// `child`, or the singleton list of it that its position at `expected` needs, with the
    /// list sorts computed for what is returned (`sorts` are `child`'s).
    #[cfg(test)]
    fn wrap_list_child(
        &self,
        child: ParsedTerm,
        expected: &Sort,
        subsorts: &PartialOrder<Sort>,
        mut sorts: ListSorts,
    ) -> Result<(ParsedTerm, ListSorts), ParseError> {
        if !self.user_lists.contains_key(expected) {
            return Ok((child, sorts));
        }
        let child_sort = self.list_sort(&child, Some(expected), subsorts, &mut sorts)?;
        let bracket = matches!(
            child,
            ParsedTerm::Production { production, .. } if self.productions[production].bracket
        );
        let Some((list, terminator_production)) =
            self.singleton_list(bracket, &child_sort, expected, subsorts)?
        else {
            return Ok((child, sorts));
        };
        let terminator = ParsedTerm::Production {
            production: terminator_production,
            children: Vec::new(),
            metadata: super::TermMetadata::default(),
        };
        let (children, children_sorts) = if list.left_associative {
            (vec![terminator, child], vec![ListSorts::default(), sorts])
        } else {
            (vec![child, terminator], vec![sorts, ListSorts::default()])
        };
        Ok((
            ParsedTerm::Production {
                production: list.list_production,
                children,
                metadata: super::TermMetadata::default(),
            },
            ListSorts {
                by_expected: Vec::new(),
                children: children_sorts,
            },
        ))
    }
}

impl Grammar {
    /// Instantiate a parametric production from the expected sort of its node and the sorts of
    /// its children, for list completion: each parameter is the least sort that holds every
    /// position it occupies. A parameter that neither the expected sort nor any child constrains
    /// is not determined by the node and keeps the parser's inferred instantiation. A parameter
    /// with bounds must have a unique least upper bound; otherwise no one instantiation is the
    /// least that holds them.
    /// Returns the instantiated nonterminal sorts and the instantiated result sort.
    /// The node has `arity` children; `child_sort(index, expected)` is the list sort of the
    /// child at `index` at the sort its position expects, `None` where that sort mentions a
    /// parameter. Children are asked left to right, and the first failure is returned.
    fn list_instantiation(
        &self,
        origin: &ParametricOrigin,
        inferred: &[Sort],
        expected: Option<&Sort>,
        arity: usize,
        subsorts: &PartialOrder<Sort>,
        mut child_sort: impl FnMut(usize, Option<&Sort>) -> Result<Sort, ParseError>,
    ) -> Result<(Vec<Sort>, Sort), ParseError> {
        let fresh = origin
            .parameters
            .iter()
            .map(|parameter| {
                (*parameter == origin.result)
                    .then(|| expected.cloned())
                    .flatten()
            })
            .collect::<Vec<_>>();
        let fresh_substitution = origin
            .parameters
            .iter()
            .zip(&fresh)
            .filter_map(|(parameter, sort)| Some((parameter.clone(), sort.clone()?)))
            .collect::<BTreeMap<_, _>>();
        let declared = origin
            .items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort),
                ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
            })
            .collect::<Vec<_>>();
        let mut bounds = BTreeMap::<Sort, Vec<Sort>>::new();
        for (index, declared_sort) in declared.iter().take(arity).enumerate() {
            let child_expected = substitute_sort(declared_sort, &fresh_substitution);
            let child_expected = (!mentions_parameter(&child_expected, &origin.parameters))
                .then_some(child_expected);
            let actual = child_sort(index, child_expected.as_ref())?;
            match_parameters(origin, declared_sort, &actual, &mut bounds, subsorts);
        }
        let result_only_parameter = origin.parameters.iter().any(|parameter| {
            let parameter = std::slice::from_ref(parameter);
            mentions_parameter(&origin.result, parameter)
                && !declared
                    .iter()
                    .any(|sort| mentions_parameter(sort, parameter))
        });
        if result_only_parameter && let Some(expected) = expected {
            match_parameters(origin, &origin.result, expected, &mut bounds, subsorts);
        }
        let mut arguments = Vec::with_capacity(origin.parameters.len());
        for (index, (parameter, fresh)) in origin.parameters.iter().zip(&fresh).enumerate() {
            // A parameter without bounds takes its fresh sort (the expected sort for the result
            // parameter); a bounded one takes the lub of its bounds, where the fresh sort only
            // filters the candidate upper bounds and never joins them.
            // `1 => foo(1)` at a user-list position therefore instantiates `#KRewrite` at `Int`
            // and the parent wraps the whole rewrite, as K does.
            let entries = bounds.get(parameter).cloned().unwrap_or_default();
            let argument = if entries.is_empty() {
                fresh
                    .clone()
                    .or_else(|| inferred.get(index).cloned())
                    .unwrap_or_else(|| parameter.clone())
            } else {
                least_upper_bound(&entries, fresh.as_ref(), subsorts).ok_or_else(|| {
                    ParseError::SortInference {
                        message: format!(
                            "could not compute a unique least upper bound for parametric production bounds: {}",
                            entries
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    }
                })?
            };
            arguments.push(argument);
        }
        let instantiation = origin
            .parameters
            .iter()
            .cloned()
            .zip(arguments)
            .collect::<BTreeMap<_, _>>();
        Ok((
            declared
                .iter()
                .map(|sort| substitute_sort(sort, &instantiation))
                .collect(),
            substitute_sort(&origin.result, &instantiation),
        ))
    }

    /// The sort of a parse node as list completion sees it (the owned form of
    /// [`Self::packed_list_sort`]). An instance of a parametric production is instantiated from
    /// its expected sort and its children ([`Grammar::list_instantiation`]), an expected sort
    /// above `K` counting as `K` ([`list_sort_expectation`]). Any other node has the sort of
    /// its production, token or variable, and `K` when it carries none.
    ///
    /// The sort of an instance depends only on the node and its expected sort, so it is kept in
    /// `sorts` (those of `term`) and computed once per expected sort. The recursion through
    /// nested instances checks the remaining stack at every level.
    #[cfg(test)]
    fn list_sort(
        &self,
        term: &ParsedTerm,
        expected: Option<&Sort>,
        subsorts: &PartialOrder<Sort>,
        sorts: &mut ListSorts,
    ) -> Result<Sort, ParseError> {
        let ParsedTerm::InstantiatedProduction {
            production,
            parameters,
            children,
            ..
        } = term
        else {
            return Ok(parsed_sort(self, term));
        };
        let Some(origin) = &self.productions[*production].parametric_origin else {
            return Ok(self.productions[*production].result.clone());
        };
        let k = Sort::new("K");
        let expected = list_sort_expectation(expected, &k, subsorts);
        if let Some((_, sort)) = sorts
            .by_expected
            .iter()
            .find(|(known, _)| known.as_ref() == expected)
        {
            return Ok(sort.clone());
        }
        if sorts.children.len() < children.len() {
            sorts
                .children
                .resize_with(children.len(), ListSorts::default);
        }
        let children_sorts = &mut sorts.children;
        let sort = crate::stack::guarded(|| {
            self.list_instantiation(
                origin,
                parameters,
                expected,
                children.len(),
                subsorts,
                |index, child_expected| {
                    self.list_sort(
                        &children[index],
                        child_expected,
                        subsorts,
                        &mut children_sorts[index],
                    )
                },
            )
        })?
        .1;
        sorts.by_expected.push((expected.cloned(), sort.clone()));
        Ok(sort)
    }
}

/// Record which concrete sorts flow into each parameter of `origin` when a nonterminal declared
/// as `declared` holds a child of sort `actual`. A parameter declared as the whole sort is
/// bounded by `actual`, and a sort without parameters records nothing. A sort that applies a head
/// to parameters, such as `MInt{Width}`, is matched argument by argument against each instance of
/// that head among `actual` and the sorts below it, the instances a value of sort `actual` in
/// that position can belong to.
fn match_parameters(
    origin: &ParametricOrigin,
    declared: &Sort,
    actual: &Sort,
    bounds: &mut BTreeMap<Sort, Vec<Sort>>,
    subsorts: &PartialOrder<Sort>,
) {
    if origin.parameters.contains(declared) {
        bounds
            .entry(declared.clone())
            .or_default()
            .push(actual.clone());
        return;
    }
    if declared.parameters.is_empty() {
        return;
    }
    let candidates = std::iter::once(actual.clone())
        .chain(subsorts.lower_bounds([actual]))
        .collect::<BTreeSet<_>>();
    for candidate in candidates {
        if candidate.name == declared.name
            && candidate.parameters.len() == declared.parameters.len()
        {
            for (declared, actual) in declared.parameters.iter().zip(&candidate.parameters) {
                match_parameters(origin, declared, actual, bounds, subsorts);
            }
        }
    }
}

fn mentions_parameter(sort: &Sort, parameters: &[Sort]) -> bool {
    parameters.contains(sort)
        || sort
            .parameters
            .iter()
            .any(|parameter| mentions_parameter(parameter, parameters))
}

/// The least upper bound of `sorts` in the parser's subsort order: the unique minimal common
/// upper bound that is neither below `KBott` nor above `K`, the range of sorts a term can have.
/// A non-parametric `expected` sort discards candidates that do not fit below it, since the
/// node's value must also be a value of the sort its position expects. These admissibility
/// filters apply even when deduplication leaves one input bound.
fn least_upper_bound(
    sorts: &[Sort],
    expected: Option<&Sort>,
    subsorts: &PartialOrder<Sort>,
) -> Option<Sort> {
    let unique = sorts.iter().cloned().collect::<BTreeSet<_>>();
    let k = Sort::new("K");
    let k_bottom = Sort::frontend(FrontendSort::KBott);
    let admissible = |bound: &Sort| {
        !subsorts.less_than_eq(bound, &k_bottom)
            && !subsorts.greater_than(bound, &k)
            && expected
                .filter(|expected| expected.parameters.is_empty())
                .is_none_or(|expected| subsorts.less_than_eq(bound, expected))
    };
    if unique.len() == 1
        && let Some(bound) = unique.first()
        && admissible(bound)
    {
        return Some(bound.clone());
    }
    let bounds = subsorts
        .upper_bounds(unique.iter())
        .into_iter()
        .filter(admissible)
        .collect::<BTreeSet<_>>();
    let minimal = subsorts.minimal(bounds.iter());
    (minimal.len() == 1).then(|| minimal.into_iter().next().expect("one minimum"))
}

fn has_visible_terminal(production: &super::Production) -> bool {
    production.items.iter().any(|item| match item {
        Item::Terminal(text) => !text.is_empty(),
        Item::Regex { .. } => true,
        Item::NonTerminal(_) => false,
    })
}

fn nonterminal_sorts(production: &super::Production) -> Vec<&Sort> {
    production
        .items
        .iter()
        .filter_map(|item| match item {
            Item::NonTerminal(sort) => Some(sort),
            Item::Terminal(_) | Item::Regex { .. } => None,
        })
        .collect()
}

/// The sort list completion reads off an owned node that it does not instantiate.
#[cfg(test)]
fn parsed_sort(grammar: &Grammar, term: &ParsedTerm) -> Sort {
    match term {
        ParsedTerm::Production { production, .. } => {
            grammar.productions[*production].result.clone()
        }
        ParsedTerm::InstantiatedProduction { production, .. } => {
            grammar.productions[*production].result.clone()
        }
        ParsedTerm::Term(term) => match term.unannotated() {
            Term::Token { sort, .. }
            | Term::Variable {
                sort: Some(sort), ..
            } => sort.clone(),
            _ => Sort::new("K"),
        },
        ParsedTerm::Ambiguity(_) => Sort::new("K"),
    }
}

/// The sort list completion reads off a packed node that it does not instantiate: that of its
/// production, of a token or a sorted variable, and `K` for anything else, an ambiguity
/// included.
fn packed_parsed_sort(grammar: &Grammar, term: &PackedTerm) -> Sort {
    match &term.node {
        PackedNode::Production { production, .. }
        | PackedNode::InstantiatedProduction { production, .. } => {
            grammar.productions[*production].result.clone()
        }
        PackedNode::Term(term) => match term.unannotated() {
            Term::Token { sort, .. }
            | Term::Variable {
                sort: Some(sort), ..
            } => sort.clone(),
            _ => Sort::new("K"),
        },
        PackedNode::Ambiguity(_) => Sort::new("K"),
    }
}

/// The expected sort at which a parametric node's list sort is computed: an expected sort
/// above `K` counts as `K` (`k`), the largest sort a term can have.
fn list_sort_expectation<'a>(
    expected: Option<&'a Sort>,
    k: &'a Sort,
    subsorts: &PartialOrder<Sort>,
) -> Option<&'a Sort> {
    expected.map(|sort| {
        if subsorts.greater_than(sort, k) {
            k
        } else {
            sort
        }
    })
}

/// Whether the children of a node of `production` keep their own sorts at its positions: a
/// cast's child is read at the sort the cast names, so it is never wrapped into a list.
fn shields_children(production: &super::Production) -> bool {
    production.label.as_ref().is_some_and(|label| {
        label.is(InternalLabel::SyntacticCast)
            || label.is(InternalLabel::SyntacticCastBraced)
            || matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
    })
}

/// The error of a parse node whose number of children differs from the number of nonterminals
/// (`expected`) of its production as list completion reads it.
fn check_list_arity(
    production: &super::Production,
    expected: usize,
    children: usize,
) -> Result<(), ParseError> {
    if expected == children {
        return Ok(());
    }
    Err(list_error(format!(
        "production {:?} has {} nonterminals but its parse node has {} children",
        production.parse_label, expected, children
    )))
}

/// Whether completion left every child of a node as it was (`completed` holds their results).
fn packed_children_unchanged(children: &[Rc<PackedTerm>], completed: &[Rc<PackedTerm>]) -> bool {
    children
        .iter()
        .zip(completed)
        .all(|(child, completed)| Rc::ptr_eq(child, completed))
}

/// What one packed list completion keeps by session node (each a node the session keeps
/// alive): its list sort by expected sort, the node its position's wrapping makes of it by
/// expected sort, and what it completes to by expected sort. A node meets few expected sorts,
/// so each is a short list.
#[derive(Default)]
struct PackedLists {
    sorts: rustc_hash::FxHashMap<*const PackedTerm, Vec<PackedListSort>>,
    wrapped: PackedListResults,
    completed: PackedListResults,
}

/// A list sort computed for a node, with the expected sort it was computed at.
type PackedListSort = (Option<Sort>, Result<Sort, ParseError>);

type PackedListResults =
    rustc_hash::FxHashMap<*const PackedTerm, Vec<(Sort, Result<Rc<PackedTerm>, ParseError>)>>;

impl PackedLists {
    fn known(
        results: &PackedListResults,
        term: &Rc<PackedTerm>,
        expected: &Sort,
    ) -> Option<Result<Rc<PackedTerm>, ParseError>> {
        results
            .get(&Rc::as_ptr(term))?
            .iter()
            .find(|(known, _)| known == expected)
            .map(|(_, result)| result.clone())
    }
}

fn list_error(message: impl Into<String>) -> ParseError {
    ParseError::UserList {
        message: message.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::{Attributes, Sentence, SortDenotations};
    use crate::kast::{Label, TermMetadata};
    use serde_json::json;

    macro_rules! assert_list_parse_snapshot {
        ($grammar:expr, $source:expr) => {{
            let source = indoc::indoc! { $source };
            let parsed = $grammar
                .parse(&Sort::new("Box"), source)
                .expect("list term should parse")
                .to_string();
            insta::with_settings!({
                description => source,
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_snapshot!(parsed);
            });
        }};
    }

    fn nonterminal(sort: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(sort),
            name: None,
        }
    }

    fn production(
        result: &str,
        items: Vec<ProductionItem>,
        label: Option<&str>,
        user_list: bool,
    ) -> Sentence {
        let mut attributes = Attributes::default();
        if user_list {
            attributes.insert("userList", json!("*"));
        }
        Sentence::Production {
            label: label.map(Label::new),
            parameters: Vec::new(),
            sort: Sort::new(result),
            items,
            attributes,
        }
    }

    fn injection(result: &str, child: &str) -> Sentence {
        production(result, vec![nonterminal(child)], None, false)
    }

    fn list(result: &str, child: &str, left: bool) -> [Sentence; 2] {
        let arguments = if left {
            vec![
                nonterminal(result),
                ProductionItem::Terminal(",".into()),
                nonterminal(child),
            ]
        } else {
            vec![
                nonterminal(child),
                ProductionItem::Terminal(",".into()),
                nonterminal(result),
            ]
        };
        [
            production(result, arguments, Some("cons"), true),
            production(
                result,
                vec![ProductionItem::Terminal(format!(".{result}"))],
                Some("nil"),
                true,
            ),
        ]
    }

    fn list_grammar(left: bool) -> Grammar {
        let [recursive, terminator] = list("Exps", "Exp", left);
        Grammar::from_sentences(&[
            production(
                "Exp",
                vec![ProductionItem::Terminal("a".into())],
                Some("a"),
                false,
            ),
            recursive,
            terminator,
            production(
                "Box",
                vec![ProductionItem::Terminal("box".into()), nonterminal("Exps")],
                Some("box"),
                false,
            ),
        ])
        .unwrap()
    }

    #[test]
    fn inserts_a_right_associative_singleton_list() {
        let grammar = list_grammar(false);
        assert_list_parse_snapshot!(grammar, "box a");
    }

    #[test]
    fn reconstructs_a_right_associative_recursive_list() {
        let grammar = list_grammar(false);
        assert_list_parse_snapshot!(grammar, "box a,a");
    }

    #[test]
    fn preserves_an_explicit_list_terminator() {
        let grammar = list_grammar(false);
        assert_list_parse_snapshot!(grammar, "box .Exps");
    }

    #[test]
    fn inserts_a_left_associative_singleton_list() {
        let grammar = list_grammar(true);
        assert_list_parse_snapshot!(grammar, "box a");
    }

    #[test]
    fn filters_singleton_completion_bounds_before_selecting_the_lub() {
        let k_bottom = Sort::new("KBott");
        let int = Sort::new("Int");
        let bool_sort = Sort::new("Bool");
        let k = Sort::new("K");
        let order = PartialOrder::new([
            (k_bottom.clone(), int.clone()),
            (k_bottom.clone(), bool_sort.clone()),
            (int.clone(), k.clone()),
            (bool_sort, k),
        ])
        .unwrap();

        assert_eq!(least_upper_bound(&[k_bottom], None, &order), None);
        let relation_free = Sort::new("RelationFree");
        assert_eq!(
            least_upper_bound(std::slice::from_ref(&relation_free), None, &order),
            Some(relation_free.clone())
        );
        assert_eq!(
            least_upper_bound(&[relation_free], Some(&int), &order),
            None
        );
    }

    #[test]
    fn propagates_nested_parametric_completion_failures() {
        let parameter = Sort::new("P");
        let grammar = Grammar::from_sentences(&[
            production(
                "A",
                vec![ProductionItem::Terminal("a".into())],
                Some("a"),
                false,
            ),
            production(
                "B",
                vec![ProductionItem::Terminal("b".into())],
                Some("b"),
                false,
            ),
            Sentence::Production {
                label: Some(Label::new("pair")),
                parameters: vec![parameter.clone()],
                sort: Sort::new("R"),
                items: vec![
                    ProductionItem::NonTerminal {
                        sort: parameter.clone(),
                        name: None,
                    },
                    ProductionItem::NonTerminal {
                        sort: parameter,
                        name: None,
                    },
                ],
                attributes: Attributes::default(),
            },
        ])
        .unwrap();
        let find = |label: &str| {
            grammar
                .productions
                .iter()
                .position(|production| {
                    production
                        .label
                        .as_ref()
                        .is_some_and(|candidate| candidate.name == label)
                })
                .unwrap()
        };
        let leaf = |production| ParsedTerm::Production {
            production,
            children: Vec::new(),
            metadata: TermMetadata::default(),
        };
        let pair = grammar
            .productions
            .iter()
            .position(|production| {
                production
                    .parametric_origin
                    .as_ref()
                    .and_then(|origin| origin.label.as_ref())
                    .is_some_and(|label| label.name == "pair")
            })
            .unwrap();
        let term = ParsedTerm::InstantiatedProduction {
            production: pair,
            parameters: vec![Sort::new("K")],
            children: vec![leaf(find("a")), leaf(find("b"))],
            metadata: TermMetadata::default(),
        };
        let order = PartialOrder::new(grammar.subsort_relations.iter().cloned()).unwrap();

        assert!(matches!(
            grammar.list_sort(
                &term,
                Some(&Sort::new("R")),
                &order,
                &mut ListSorts::default()
            ),
            Err(ParseError::SortInference { message }) if message.contains("least upper bound")
        ));
    }

    #[test]
    fn reports_ambiguous_list_and_terminator_sorts() {
        let atom = production(
            "Atom",
            vec![ProductionItem::Terminal("atom".into())],
            Some("atom"),
            false,
        );
        let [first_list, first_terminator] = list("Firsts", "First", false);
        let [second_list, second_terminator] = list("Seconds", "Second", false);
        let [general_list, general_terminator] = list("General", "GeneralElement", false);
        let base = vec![
            atom.clone(),
            injection("First", "Atom"),
            first_list.clone(),
            first_terminator.clone(),
            second_list.clone(),
            second_terminator.clone(),
            general_list,
            general_terminator,
            injection("General", "Firsts"),
            injection("General", "Seconds"),
            production(
                "Holder",
                vec![nonterminal("General")],
                Some("holder"),
                false,
            ),
        ];

        let mut ambiguous_lists = base.clone();
        ambiguous_lists.insert(2, injection("Second", "Atom"));
        let ambiguous_lists = Grammar::from_sentences(&ambiguous_lists).unwrap();
        let atom_term = |grammar: &Grammar| ParsedTerm::Production {
            production: grammar
                .productions
                .iter()
                .position(|production| {
                    production
                        .label
                        .as_ref()
                        .is_some_and(|label| label.name == "atom")
                })
                .unwrap(),
            children: Vec::new(),
            metadata: TermMetadata::default(),
        };
        let held_atom = |grammar: &Grammar| ParsedTerm::Production {
            production: grammar
                .productions
                .iter()
                .position(|production| {
                    production
                        .label
                        .as_ref()
                        .is_some_and(|label| label.name == "holder")
                })
                .unwrap(),
            children: vec![atom_term(grammar)],
            metadata: TermMetadata::default(),
        };
        let list_error = ambiguous_lists
            .add_empty_lists(held_atom(&ambiguous_lists), &Sort::new("Holder"))
            .unwrap_err();

        let ambiguous_terminators = Grammar::from_sentences(&base).unwrap();
        let terminator_error = ambiguous_terminators
            .add_empty_lists(held_atom(&ambiguous_terminators), &Sort::new("Holder"))
            .unwrap_err();

        assert_eq!(
            list_error,
            ParseError::OverloadedTerminator {
                possible_sorts: vec![Sort::new("Firsts"), Sort::new("Seconds")],
            }
        );
        assert_eq!(
            terminator_error,
            ParseError::ListTerminator {
                possible_sorts: vec![Sort::new("Firsts"), Sort::new("Seconds")],
            }
        );

        let source_catalog = crate::definition::ProductionCatalog::from_visible(&base);
        let program =
            Grammar::from_program_sentences(&base, &source_catalog, SortDenotations::default())
                .unwrap();
        let completed = program
            .add_empty_lists(held_atom(&program), &Sort::new("Holder"))
            .unwrap();
        let ParsedParts::Production { children, .. } = completed.into_parts() else {
            unreachable!()
        };
        let [
            ParsedTerm::Production {
                production,
                children: list_children,
                ..
            },
        ] = children.as_slice()
        else {
            panic!("program list should be reconstructed under the holder");
        };
        assert_eq!(program.productions[*production].result, Sort::new("Firsts"));
        assert!(list_children.iter().any(|child| matches!(child,
            ParsedTerm::Production { production, children, .. }
                if program.productions[*production].result == Sort::new("Firsts")
                    && children.is_empty())));
    }

    /// `Exps ::= List{Exp, ","}` with `Exp ::= "a" | "f" Exps | "g" Exps | "h" Exp | Exp "+" Exp`,
    /// and the indexes of the productions labelled `a`, `f`, `g` and `h`.
    fn nested_list_grammar() -> (Grammar, [usize; 4]) {
        let [recursive, terminator] = list("Exps", "Exp", false);
        let terminal = |text: &str| ProductionItem::Terminal(text.into());
        let grammar = Grammar::from_sentences(&[
            production("Exp", vec![terminal("a")], Some("a"), false),
            production(
                "Exp",
                vec![terminal("f"), nonterminal("Exps")],
                Some("f"),
                false,
            ),
            production(
                "Exp",
                vec![terminal("g"), nonterminal("Exps")],
                Some("g"),
                false,
            ),
            production(
                "Exp",
                vec![terminal("h"), nonterminal("Exp")],
                Some("h"),
                false,
            ),
            production(
                "Exp",
                vec![nonterminal("Exp"), terminal("+"), nonterminal("Exp")],
                Some("plus"),
                false,
            ),
            recursive,
            terminator,
        ])
        .unwrap();
        let find = |name: &str| {
            grammar
                .productions
                .iter()
                .position(|production| {
                    production
                        .label
                        .as_ref()
                        .is_some_and(|label| label.name == name)
                })
                .unwrap()
        };
        let labels = [find("a"), find("f"), find("g"), find("h")];
        (grammar, labels)
    }

    #[test]
    fn completing_the_lists_of_a_forest_of_exponentially_many_trees_visits_each_node_once() {
        let (grammar, [a, f, g, h]) = nested_list_grammar();
        let list = &grammar.user_lists[&Sort::new("Exps")];
        let mut session = LoweringSession::default();
        let node = |session: &mut LoweringSession, production, children| {
            session.intern(PackedTerm::production(
                production,
                children,
                TermMetadata::default(),
            ))
        };
        let forest_and_expected = |session: &mut LoweringSession, wrapped: bool| {
            let nil = node(session, list.terminator_production, Vec::new());
            // Level k + 1 is `f(h(level k))` or `g(h(level k))`: 2^64 trees. `h(level k)` is
            // expected at `Exps` there, so it becomes the singleton list `h(level k), .Exps`.
            let mut level = node(session, a, Vec::new());
            for _ in 0..64 {
                let mut child = node(session, h, vec![level]);
                if wrapped {
                    child = node(session, list.list_production, vec![child, Rc::clone(&nil)]);
                }
                let alternatives = BTreeSet::from([
                    node(session, f, vec![Rc::clone(&child)]),
                    node(session, g, vec![child]),
                ]);
                level = session.intern(PackedTerm::alternatives(alternatives));
            }
            level
        };
        let forest = forest_and_expected(&mut session, false);
        let expected = forest_and_expected(&mut session, true);
        super::super::forest::reset_unpacked_nodes();

        let completed = grammar
            .add_packed_empty_lists(&mut session, &forest, &Sort::new("Exp"))
            .unwrap();

        assert!(Rc::ptr_eq(&completed, &expected));
        assert_eq!(super::super::forest::unpacked_nodes(), 0);
    }

    /// Two alternatives of an ambiguity that both fail: the error is that of the structurally
    /// first, the one the owned tree's depth-first walk meets first, whichever order the packed
    /// ambiguity holds them in.
    #[test]
    fn the_list_error_of_an_ambiguity_is_its_structurally_first_alternatives() {
        let (grammar, [_, f, g, _]) = nested_list_grammar();
        let childless = |production| ParsedTerm::Production {
            production,
            children: Vec::new(),
            metadata: TermMetadata::default(),
        };
        let ambiguity = ParsedTerm::Ambiguity(BTreeSet::from([childless(f), childless(g)]));
        let first = grammar.productions[f.min(g)].parse_label.clone();

        let error = grammar
            .add_empty_lists(ambiguity, &Sort::new("Exp"))
            .unwrap_err();

        assert_eq!(
            error,
            list_error(format!(
                "production {first:?} has 1 nonterminals but its parse node has 0 children"
            ))
        );
    }

    /// The trees of `g a + g a + ... + g a` are every bracketing of the sum, and each `a`
    /// becomes the singleton list `a, .Exps` below its `g`. The ambiguity is reported from the
    /// inferred forest with its lists completed, without unpacking its trees.
    #[cfg(feature = "z3-inference")]
    #[test]
    fn an_ambiguity_whose_lists_are_completed_is_reported_from_the_forest() {
        let (grammar, _) = nested_list_grammar();
        let input = ["g a"; 12].join(" + ");
        super::super::forest::reset_unpacked_nodes();

        let parsed = grammar.parse(&Sort::new("Exp"), &input);

        assert!(
            matches!(parsed, Err(ParseError::Ambiguous { .. })),
            "{parsed:?}"
        );
        assert_eq!(super::super::forest::unpacked_nodes(), 0);
    }

    /// The singleton list of `atom` at `General` could be a `Firsts` or a `Seconds`, neither
    /// below the other, in each of the bracketings of `w atom + ... + w atom`. The error is
    /// reported from the inferred forest, without unpacking its trees.
    #[cfg(feature = "z3-inference")]
    #[test]
    fn an_ambiguous_singleton_list_in_a_forest_is_reported_from_the_forest() {
        let atom = production(
            "Atom",
            vec![ProductionItem::Terminal("atom".into())],
            Some("atom"),
            false,
        );
        let [first_list, first_terminator] = list("Firsts", "First", false);
        let [second_list, second_terminator] = list("Seconds", "Second", false);
        let [general_list, general_terminator] = list("General", "GeneralElement", false);
        let grammar = Grammar::from_sentences(&[
            atom,
            injection("First", "Atom"),
            injection("Second", "Atom"),
            first_list,
            first_terminator,
            second_list,
            second_terminator,
            general_list,
            general_terminator,
            injection("General", "Firsts"),
            injection("General", "Seconds"),
            production(
                "Atom",
                vec![ProductionItem::Terminal("w".into()), nonterminal("General")],
                Some("w"),
                false,
            ),
            production(
                "Atom",
                vec![
                    nonterminal("Atom"),
                    ProductionItem::Terminal("+".into()),
                    nonterminal("Atom"),
                ],
                Some("plus"),
                false,
            ),
        ])
        .unwrap();
        let input = ["w atom"; 12].join(" + ");
        super::super::forest::reset_unpacked_nodes();

        let parsed = grammar.parse(&Sort::new("Atom"), &input);

        assert_eq!(
            parsed.map(|term| term.to_string()),
            Err(ParseError::OverloadedTerminator {
                possible_sorts: vec![Sort::new("Firsts"), Sort::new("Seconds")],
            })
        );
        assert_eq!(super::super::forest::unpacked_nodes(), 0);
    }
}
