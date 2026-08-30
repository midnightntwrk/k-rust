//! Scala-compatible insertion of implicit user-list constructors and terminators.

use std::collections::{BTreeMap, BTreeSet};

use crate::definition::{PartialOrder, ProductionItem};
use crate::kast::{Sort, Term};

use super::parametric::substitute_sort;
use super::{Grammar, Item, ParseError, ParsedTerm, ParserRole, ProductionOptions};

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
        // every lone element, so neither the split nor the singleton injection is needed;
        // both would make each element parse twice (as `X` and as `[X]`).
        let mut injections = Vec::new();
        let mut splits = Vec::new();
        for (sort, list) in &lists {
            let terminator = &self.productions[list.terminator_production];
            let recursive = &self.productions[list.list_production];
            if !terminator.items.is_empty() {
                injections.push((sort.clone(), list.child_sort.clone()));
            } else if has_visible_terminal(recursive) {
                splits.push((sort.clone(), list.clone()));
            }
        }
        self.user_lists = lists;
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
        let nonempty = Sort::new(format!("Ne#{sort}"));
        let recursive = &self.productions[list.list_production];
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
        self.add(
            nonempty.clone(),
            vec![ProductionItem::NonTerminal {
                sort: list.child_sort.clone(),
                name: None,
            }],
            None,
            false,
            true,
        )?;
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
        _expected: &Sort,
        subsorts: &PartialOrder<Sort>,
    ) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Term(_) => Ok(term),
            ParsedTerm::Ambiguity(alternatives) => Ok(ParsedTerm::Ambiguity(
                alternatives
                    .into_iter()
                    .map(|alternative| {
                        self.add_empty_lists_with_order(alternative, _expected, subsorts)
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
                let expected_children = descriptor
                    .parametric_origin
                    .as_ref()
                    .map(|origin| {
                        let substitution = origin
                            .parameters
                            .iter()
                            .cloned()
                            .zip(parameters.iter().cloned())
                            .collect::<BTreeMap<_, _>>();
                        origin
                            .items
                            .iter()
                            .filter_map(|item| match item {
                                ProductionItem::NonTerminal { sort, .. } => {
                                    Some(substitute_sort(sort, &substitution))
                                }
                                ProductionItem::Terminal(_)
                                | ProductionItem::RegexTerminal { .. } => None,
                            })
                            .collect::<Vec<_>>()
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
        let child_sort = parsed_sort(self, &child);
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
