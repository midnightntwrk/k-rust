//! Scala-compatible insertion of implicit user-list constructors and terminators.

use std::collections::{BTreeMap, BTreeSet};

use crate::definition::{PartialOrder, ProductionItem};
use crate::kast::{Sort, Term};

use super::parametric::substitute_sort;
use super::{
    Grammar, Item, ParametricOrigin, ParseError, ParsedTerm, ParserRole, ProductionOptions,
};

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
            if let Some(indices) = self.by_result.get_mut(&sort) {
                indices.retain(|index| *index != terminator);
            }
        }
        for (sort, list) in splits {
            self.split_program_list(&sort, &list)?;
        }
        for (sort, child_sort) in injections {
            let exists = self.productions.iter().any(|production| {
                production.result == sort
                    && production.label.is_none()
                    && matches!(
                        production.items.as_slice(),
                        [Item::NonTerminal(child)] if child == &child_sort
                    )
            });
            if !exists {
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
            }
        }
        Ok(())
    }

    /// Replace a program-grammar list with a visible separator by K's non-empty split.
    fn split_program_list(&mut self, sort: &Sort, list: &UserList) -> Result<(), ParseError> {
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
        if let Some(indices) = self.by_result.get_mut(sort) {
            indices.retain(|index| *index != list.list_production);
        }
        let split = self.productions.len();
        self.add_production_with_lexical(
            nonempty.clone(),
            &items,
            label,
            ProductionOptions {
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
                source_production: terminator.source_production,
                source_production_text: terminator.source_production_text.as_deref(),
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
                source_production: recursive.source_production,
                source_production_text: recursive.source_production_text.as_deref(),
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
        self.add(
            sort.clone(),
            vec![ProductionItem::NonTerminal {
                sort: nonempty,
                name: None,
            }],
            None,
            false,
            true,
        )
    }

    /// Keep an empty-separator program list's own terminator when it is the direct tail of that
    /// list's recursive production. Overload resolution may otherwise replace the tail with the
    /// shared least terminator, even though K's program parser preserves the enclosing list's
    /// concrete representation.
    pub(super) fn program_list_terminator(
        &self,
        parent: usize,
        child_index: usize,
        child: &ParsedTerm,
    ) -> Option<ParsedTerm> {
        if self.role != ParserRole::Program {
            return None;
        }
        let list = self
            .user_lists
            .values()
            .find(|list| list.list_production == parent)?;
        let tail_index = usize::from(!list.left_associative);
        if child_index != tail_index {
            return None;
        }
        let terminator = list.terminator_production;
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

    /// Reconstruct real list nodes after inference has consumed the temporary
    /// singleton-list subsorts.
    pub(super) fn add_empty_lists(
        &self,
        term: ParsedTerm,
        expected: &Sort,
    ) -> Result<ParsedTerm, ParseError> {
        let subsorts = PartialOrder::new(self.subsort_relations.iter().cloned())
            .map_err(|cycle| ParseError::CircularSubsorts { path: cycle.path })?;
        self.add_empty_lists_with_order(term, expected, &subsorts)
    }

    fn add_empty_lists_with_order(
        &self,
        term: ParsedTerm,
        expected: &Sort,
        subsorts: &PartialOrder<Sort>,
    ) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Term(_) => Ok(term),
            ParsedTerm::Ambiguity(alternatives) => Ok(ParsedTerm::Ambiguity(
                alternatives
                    .into_iter()
                    .map(|alternative| {
                        self.add_empty_lists_with_order(alternative, expected, subsorts)
                    })
                    .collect::<Result<_, _>>()?,
            )),
            ParsedTerm::Production {
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
                    label.name == "#SyntacticCast"
                        || label.name == "#SyntacticCastBraced"
                        || label.name.starts_with("#SemanticCastTo")
                });
                // Rewrite operands are parsed through generic K productions, but sort inference
                // still requires both sides to share the function result sort. Preserve that
                // context when one side is a user list so a singleton element on the other side
                // receives its real recursive constructor and terminator.
                let rewrite_list_sort = descriptor
                    .label
                    .as_ref()
                    .is_some_and(|label| label.name == "#KRewrite")
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
                let children = children
                    .into_iter()
                    .zip(expected_children)
                    .map(|(child, expected_child)| {
                        let expected_child = rewrite_list_sort.as_ref().unwrap_or(expected_child);
                        let child = if shields_children {
                            child
                        } else {
                            self.wrap_list_child(child, expected_child, subsorts)?
                        };
                        self.add_empty_lists_with_order(child, expected_child, subsorts)
                    })
                    .collect::<Result<_, _>>()?;
                Ok(ParsedTerm::Production {
                    production,
                    children,
                    metadata,
                })
            }
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => {
                let descriptor = &self.productions[production];
                // Java's `AddEmptyLists.apply` completes children against the production that
                // `AddSortInjections.substituteProd` instantiates from the node's expected sort
                // and its children's sorts, not against the parser's inferred parameters. The
                // two differ for a binder position such as `#let X = e #in ...`: inference
                // leaves the child-only `Sort2` at `K`, while the reference instantiates it to
                // `lub(sort(X), sort(e))`, so an element-sorted `X` bound to a user list is
                // completed to the singleton list `X .Xs` before ResolveFun reads the binder.
                let expected_children = descriptor
                    .parametric_origin
                    .as_ref()
                    .map(|origin| {
                        self.list_instantiation(
                            origin,
                            &parameters,
                            Some(expected),
                            &children,
                            subsorts,
                        )
                        .0
                    })
                    .unwrap_or_else(|| {
                        nonterminal_sorts(descriptor).into_iter().cloned().collect()
                    });
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
                    .is_some_and(|label| label.name == "#KRewrite")
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
                let children = children
                    .into_iter()
                    .zip(&expected_children)
                    .map(|(child, expected_child)| {
                        let expected_child = rewrite_list_sort.as_ref().unwrap_or(expected_child);
                        let child = self.wrap_list_child(child, expected_child, subsorts)?;
                        self.add_empty_lists_with_order(child, expected_child, subsorts)
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
    }

    fn wrap_list_child(
        &self,
        child: ParsedTerm,
        expected: &Sort,
        subsorts: &PartialOrder<Sort>,
    ) -> Result<ParsedTerm, ParseError> {
        if !self.user_lists.contains_key(expected) {
            return Ok(child);
        }
        let child_sort = self.list_sort(&child, Some(expected), subsorts);
        if self.user_lists.contains_key(&child_sort) && subsorts.less_than_eq(&child_sort, expected)
        {
            return Ok(child);
        }
        if matches!(
            child,
            ParsedTerm::Production { production, .. } if self.productions[production].bracket
        ) || child_sort.name == "K"
            || !subsorts.less_than(&child_sort, expected)
        {
            return Ok(child);
        }

        let candidates = self
            .user_lists
            .iter()
            .filter_map(|(sort, list)| {
                (subsorts.less_than_eq(&child_sort, &list.child_sort)
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
        let terminator = ParsedTerm::Production {
            production: terminator_production,
            children: Vec::new(),
            metadata: super::TermMetadata::default(),
        };
        let children = if list.left_associative {
            vec![terminator, child]
        } else {
            vec![child, terminator]
        };
        Ok(ParsedTerm::Production {
            production: list.list_production,
            children,
            metadata: super::TermMetadata::default(),
        })
    }
}

impl Grammar {
    /// Port of `AddSortInjections.substituteProd` as `AddEmptyLists` uses it: instantiate a
    /// parametric production from the expected sort of its node and the sorts of its children.
    /// A parameter that neither the expected sort nor any child constrains keeps the parser's
    /// inferred instantiation, where Java would keep a fresh sort parameter; so does a parameter
    /// whose bounds have no unique least upper bound, where Java reports an internal error.
    /// Returns the instantiated nonterminal sorts and the instantiated result sort.
    fn list_instantiation(
        &self,
        origin: &ParametricOrigin,
        inferred: &[Sort],
        expected: Option<&Sort>,
        children: &[ParsedTerm],
        subsorts: &PartialOrder<Sort>,
    ) -> (Vec<Sort>, Sort) {
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
        for (declared_sort, child) in declared.iter().zip(children) {
            let child_expected = substitute_sort(declared_sort, &fresh_substitution);
            let child_expected = (!mentions_parameter(&child_expected, &origin.parameters))
                .then_some(child_expected);
            let actual = self.list_sort(child, child_expected.as_ref(), subsorts);
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
        let arguments = origin
            .parameters
            .iter()
            .zip(&fresh)
            .enumerate()
            .map(|(index, (parameter, fresh))| {
                let mut entries = bounds.get(parameter).cloned().unwrap_or_default();
                entries.extend(fresh.clone());
                if entries.is_empty() {
                    None
                } else {
                    least_upper_bound(&entries, subsorts)
                }
                .or_else(|| inferred.get(index).cloned())
                .unwrap_or_else(|| parameter.clone())
            })
            .collect::<Vec<_>>();
        let instantiation = origin
            .parameters
            .iter()
            .cloned()
            .zip(arguments)
            .collect::<BTreeMap<_, _>>();
        (
            declared
                .iter()
                .map(|sort| substitute_sort(sort, &instantiation))
                .collect(),
            substitute_sort(&origin.result, &instantiation),
        )
    }

    /// Port of `AddEmptyLists.getSort`: the sort of a parse node as the completion pass sees
    /// it, instantiating a parametric node against its expected sort.
    fn list_sort(
        &self,
        term: &ParsedTerm,
        expected: Option<&Sort>,
        subsorts: &PartialOrder<Sort>,
    ) -> Sort {
        let k = Sort::new("K");
        let expected = expected.map(|sort| {
            if subsorts.greater_than(sort, &k) {
                &k
            } else {
                sort
            }
        });
        match term {
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                ..
            } => match &self.productions[*production].parametric_origin {
                Some(origin) => {
                    self.list_instantiation(origin, parameters, expected, children, subsorts)
                        .1
                }
                None => self.productions[*production].result.clone(),
            },
            _ => parsed_sort(self, term),
        }
    }
}

/// Port of `AddSortInjections.match`: record which concrete sorts flow into each parameter of
/// `origin` when a nonterminal declared as `declared` holds a child of sort `actual`.
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

/// Port of `AddSortInjections.lub` over the parser's subsort order: the unique minimal common
/// upper bound that is neither below `KBott` nor above `K`.
fn least_upper_bound(sorts: &[Sort], subsorts: &PartialOrder<Sort>) -> Option<Sort> {
    let unique = sorts.iter().cloned().collect::<BTreeSet<_>>();
    if unique.len() == 1 {
        return unique.into_iter().next();
    }
    let k = Sort::new("K");
    let k_bottom = Sort::new("KBott");
    let bounds = subsorts
        .upper_bounds(unique.iter())
        .into_iter()
        .filter(|bound| {
            !subsorts.less_than_eq(bound, &k_bottom) && !subsorts.greater_than(bound, &k)
        })
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

fn list_error(message: impl Into<String>) -> ParseError {
    ParseError::UserList {
        message: message.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::{Attributes, Sentence};
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
        let program = Grammar::from_program_sentences(&base, &source_catalog).unwrap();
        let completed = program
            .add_empty_lists(held_atom(&program), &Sort::new("Holder"))
            .unwrap();
        let ParsedTerm::Production { children, .. } = completed else {
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
}
