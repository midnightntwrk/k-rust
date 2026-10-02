//! Sort synonym denotations are closed in each module's full view before application to productions.
//! Cost is one scan of each module's view for synonym declarations and their closure, plus the existing `ResolvedDefinition::resolve` and `ResolvedDefinition::update`; `KompileResolveCalls`, `KompileResolveUpdates`, and `KompileSentenceCopies` count the resolve, update and local sentence copies.

use std::collections::{BTreeMap, BTreeSet};

use petgraph::algo::tarjan_scc;
use petgraph::graph::DiGraph;

use crate::kast::Sort;

use super::{Definition, ModuleId, ProductionItem, ResolveError, ResolvedDefinition, Sentence};

/// What a whole sort spelling denotes in a view.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Spelling<'s> {
    /// No visible synonym has this alias: the spelling names a sort, declared or not.
    Sort,
    /// A visible alias whose chain ends at `denotes`, which is never an alias in this view.
    Synonym { denotes: &'s Sort },
    /// A visible alias on a cycle, ambiguous, or referring to an alias without a denotation.
    /// [`super::check_sort_synonyms`] reports its root declaration defect.
    Undenoted,
}

/// A root defect that prevents synonym declarations from naming one sort.
#[derive(Clone, Debug)]
pub enum SynonymDefect<'a> {
    /// The declarations within one cyclic strongly connected component, in visible order.
    /// A self-loop is a cycle too.
    Cycle { declarations: Vec<&'a Sentence> },
    /// An alias whose referents all denote sorts, but those denotations differ.
    /// Each declaration is paired with its denotation, in visible order.
    Ambiguous {
        alias: Sort,
        declarations: Vec<(&'a Sentence, Sort)>,
    },
}

/// Closed denotations of the synonym equations in one view, with whole sorts as keys.
/// A defined alias denotes the common end of all its chains, never another alias.
/// Cycles, ambiguity and their dependent aliases are undenoted; a dangling referent
/// still denotes that undeclared sort, whose uses the sort checks reject.
#[derive(Clone, Debug, Default)]
pub struct SortSynonyms<'a> {
    denotations: BTreeMap<Sort, Sort>,
    undenoted: BTreeSet<Sort>,
    defects: Vec<SynonymDefect<'a>>,
}

impl<'a> SortSynonyms<'a> {
    /// Close all visible synonym equations, keeping the first declaration of each
    /// `(alias, referent)` pair. No synonym declarations means no allocation.
    pub fn of(visible: impl IntoIterator<Item = &'a Sentence>) -> Self {
        let mut seen = BTreeSet::new();
        let mut equations = Vec::new();
        for sentence in visible {
            if let Sentence::SortSynonym {
                new_sort, old_sort, ..
            } = sentence
                && seen.insert((new_sort, old_sort))
            {
                equations.push((new_sort, old_sort, sentence));
            }
        }
        let mut closed = Self::default();
        if !equations.is_empty() {
            let mut graph = DiGraph::<&Sort, ()>::new();
            let mut nodes = BTreeMap::new();
            let mut declarations = BTreeMap::<_, Vec<_>>::new();
            for (order, &(alias, referent, sentence)) in equations.iter().enumerate() {
                nodes.entry(alias).or_insert_with(|| graph.add_node(alias));
                declarations
                    .entry(alias)
                    .or_default()
                    .push((order, referent, sentence));
            }
            for &(alias, referent, _) in &equations {
                if let Some(&target) = nodes.get(referent) {
                    graph.add_edge(nodes[alias], target, ());
                }
            }
            // Edges point to dependencies, so SCC postorder visits every referent before
            // its dependent alias. A cyclic component has no denotation regardless of exits.
            for component in tarjan_scc(&graph) {
                let cyclic = component.len() > 1 || graph.contains_edge(component[0], component[0]);
                if cyclic {
                    let members = component
                        .iter()
                        .map(|&node| graph[node])
                        .collect::<BTreeSet<_>>();
                    let mut cycle = Vec::new();
                    for &alias in &members {
                        closed.undenoted.insert(alias.clone());
                        cycle.extend(
                            declarations[alias]
                                .iter()
                                .filter(|(_, referent, _)| members.contains(referent))
                                .copied(),
                        );
                    }
                    cycle.sort_by_key(|&(order, _, _)| order);
                    closed.defects.push(SynonymDefect::Cycle {
                        declarations: cycle.into_iter().map(|(_, _, sentence)| sentence).collect(),
                    });
                    continue;
                }
                let alias = graph[component[0]];
                let mut denotations = Vec::new();
                let mut undenoted = false;
                for &(_, referent, sentence) in &declarations[alias] {
                    match closed.spelling(referent) {
                        Spelling::Sort => denotations.push((sentence, referent.clone())),
                        Spelling::Synonym { denotes } => {
                            denotations.push((sentence, denotes.clone()))
                        }
                        Spelling::Undenoted => undenoted = true,
                    }
                }
                if undenoted {
                    closed.undenoted.insert(alias.clone());
                } else if denotations
                    .iter()
                    .any(|(_, denotes)| denotes != &denotations[0].1)
                {
                    closed.undenoted.insert(alias.clone());
                    closed.defects.push(SynonymDefect::Ambiguous {
                        alias: alias.clone(),
                        declarations: denotations,
                    });
                } else {
                    closed
                        .denotations
                        .insert(alias.clone(), denotations[0].1.clone());
                }
            }
        }
        debug_assert!(
            closed
                .denotations
                .values()
                .all(|denotes| !closed.denotations.contains_key(denotes)
                    && !closed.undenoted.contains(denotes))
        );
        closed
    }

    /// Close the equations of a module's full view, including private imports.
    pub fn of_module(resolved: &'a ResolvedDefinition, module: ModuleId) -> Self {
        Self::of(resolved.sentences(module))
    }

    /// Decide the denotation of one whole spelling; sort arguments are not rewritten.
    pub fn spelling(&self, sort: &Sort) -> Spelling<'_> {
        if let Some(denotes) = self.denotations.get(sort) {
            Spelling::Synonym { denotes }
        } else if self.undenoted.contains(sort) {
            Spelling::Undenoted
        } else {
            Spelling::Sort
        }
    }

    /// Root cycle and ambiguity defects; dependent aliases introduce no additional defect.
    pub fn defects(&self) -> &[SynonymDefect<'a>] {
        &self.defects
    }

    /// Whether this view contains no synonym aliases, denoted or undenoted.
    pub fn is_empty(&self) -> bool {
        self.denotations.is_empty() && self.undenoted.is_empty()
    }
}

/// Replace each production's result and nonterminal sorts by their denotations in its module's full view.
/// Chains are followed to their end; spellings bound by the production's parameters stay as written.
/// Undenoted aliases stay in place for [`super::check_sort_synonyms`] to report their declaration defects.
/// Sort arguments, parameters and synonym declarations are unchanged.
pub fn apply_sort_synonyms(definition: &Definition) -> Result<Definition, ResolveError> {
    apply_sort_synonyms_with_resolved(definition).map(|(transformed, _)| transformed)
}

/// Apply sort synonyms and retain the resolved graph for callers that immediately need derived
/// views of the transformed definition.
pub(crate) fn apply_sort_synonyms_with_resolved(
    definition: &Definition,
) -> Result<(Definition, ResolvedDefinition), ResolveError> {
    let resolved = ResolvedDefinition::resolve(definition)?;
    let mut transformed = definition.clone();

    for module in &mut transformed.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("every flat module was added to the resolved definition");
        let synonyms = SortSynonyms::of_module(&resolved, module_id);

        for sentence in &mut module.local_sentences {
            apply_to_sentence(crate::definition::sentence_mut(sentence), &synonyms);
        }
    }

    let resolved = resolved.update(definition, &transformed)?;
    Ok((transformed, resolved))
}

pub(crate) struct UnappliedSynonym {
    pub module: String,
    pub sentence: usize,
    pub synonym: Sort,
    pub sort: Sort,
}

/// Find the first production that is not a fixpoint of synonym application.
/// Re-applying a copy checks exactly the positions application rewrites, including after
/// application is widened. The recursive name prefilter only avoids unnecessary view builds
/// and copies; it does not decide whether a production has been applied.
pub(crate) fn first_unapplied_synonym(
    definition: &Definition,
    resolved: &ResolvedDefinition,
) -> Option<UnappliedSynonym> {
    let names = definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| match &**sentence {
            Sentence::SortSynonym { new_sort, .. } => Some(new_sort),
            Sentence::SyntaxSort { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => None,
        })
        .collect::<BTreeSet<_>>();
    if names.is_empty() {
        return None;
    }

    fn mentions_name(sort: &Sort, names: &BTreeSet<&Sort>) -> bool {
        names.contains(sort)
            || sort
                .parameters
                .iter()
                .any(|sort| mentions_name(sort, names))
    }

    for module in &definition.modules {
        let mut synonyms = None;
        for (index, sentence) in module.local_sentences.iter().enumerate() {
            let Sentence::Production {
                parameters,
                sort,
                items,
                ..
            } = &**sentence
            else {
                continue;
            };
            let operands = || {
                std::iter::once(sort).chain(items.iter().filter_map(|item| {
                    if let ProductionItem::NonTerminal { sort, .. } = item {
                        Some(sort)
                    } else {
                        None
                    }
                }))
            };
            if !operands()
                .chain(parameters)
                .any(|sort| mentions_name(sort, &names))
            {
                continue;
            }
            let synonyms = synonyms.get_or_insert_with(|| {
                let id = resolved
                    .module_id(&module.name)
                    .expect("every flat module was added to the resolved definition");
                SortSynonyms::of_module(resolved, id)
            });
            let mut applied = (**sentence).clone();
            apply_to_sentence(&mut applied, synonyms);
            if applied != **sentence {
                let (synonym, sort) = operands()
                    .filter(|sort| !parameters.contains(sort))
                    .find_map(|sort| match synonyms.spelling(sort) {
                        Spelling::Synonym { denotes } => Some((sort, denotes)),
                        Spelling::Sort | Spelling::Undenoted => None,
                    })
                    .expect("a changed production has an unbound synonym operand");
                return Some(UnappliedSynonym {
                    module: module.name.clone(),
                    sentence: index,
                    synonym: synonym.clone(),
                    sort: sort.clone(),
                });
            }
        }
    }
    None
}

fn apply_to_sentence(sentence: &mut Sentence, synonyms: &SortSynonyms<'_>) {
    let Sentence::Production {
        parameters,
        sort,
        items,
        ..
    } = sentence
    else {
        return;
    };
    for sort in std::iter::once(sort).chain(items.iter_mut().filter_map(|item| {
        if let ProductionItem::NonTerminal { sort, .. } = item {
            Some(sort)
        } else {
            None
        }
    })) {
        if parameters.contains(sort) {
            continue;
        }
        match synonyms.spelling(sort) {
            Spelling::Synonym { denotes } => *sort = denotes.clone(),
            Spelling::Sort | Spelling::Undenoted => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::Attributes;

    fn synonym(alias: &str, referent: &str) -> Sentence {
        Sentence::SortSynonym {
            new_sort: Sort::new(alias),
            old_sort: Sort::new(referent),
            attributes: Attributes::default(),
        }
    }

    fn lowered_definition(text: &str) -> Definition {
        crate::outer::lower(&crate::outer::parse("synonyms.k", text).unwrap(), "MAIN").unwrap()
    }

    #[test]
    fn unapplied_result_and_nonterminal_synonyms_are_reported() {
        for production in ["syntax Num ::= \"num\"", "syntax Foo ::= g(Num)"] {
            let definition = lowered_definition(&format!(
                "module MAIN\nsyntax Num = Int\n{production}\nendmodule\n"
            ));
            let resolved = ResolvedDefinition::resolve(&definition).unwrap();
            let found = first_unapplied_synonym(&definition, &resolved).unwrap();
            assert_eq!(found.module, "MAIN");
            assert_eq!(found.sentence, 1);
            assert_eq!(found.synonym, Sort::new("Num"));
            assert_eq!(found.sort, Sort::new("Int"));
            let applied = apply_sort_synonyms(&definition).unwrap();
            let resolved = ResolvedDefinition::resolve(&applied).unwrap();
            assert!(first_unapplied_synonym(&applied, &resolved).is_none());
        }
    }

    #[test]
    fn a_definition_without_synonyms_is_a_fixpoint() {
        let definition = lowered_definition("module MAIN\nsyntax Foo ::= \"foo\"\nendmodule\n");
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        assert!(first_unapplied_synonym(&definition, &resolved).is_none());
    }

    #[test]
    fn prefilter_hits_do_not_reject_bound_or_nested_synonyms() {
        let definition = lowered_definition(
            "module MAIN\nsyntax Num = Int\nsyntax {Num} Num ::= id(Num)\nsyntax Foo ::= g(MInt{Num})\nendmodule\n",
        );
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        assert!(first_unapplied_synonym(&definition, &resolved).is_none());
    }

    #[test]
    fn a_chain_denotes_its_end() {
        let declarations = [synonym("C", "B"), synonym("B", "A"), synonym("A", "Int")];
        let synonyms = SortSynonyms::of(&declarations);
        for alias in ["C", "B", "A"] {
            assert_eq!(
                synonyms.spelling(&Sort::new(alias)),
                Spelling::Synonym {
                    denotes: &Sort::new("Int")
                }
            );
        }
        for sort in ["Int", "Foo"] {
            assert_eq!(synonyms.spelling(&Sort::new(sort)), Spelling::Sort);
        }
        assert!(synonyms.defects().is_empty());
    }

    #[test]
    fn a_cycle_denotes_nothing_and_is_one_defect() {
        let declarations = [synonym("A", "B"), synonym("B", "A"), synonym("C", "A")];
        let synonyms = SortSynonyms::of(&declarations);
        for alias in ["A", "B", "C"] {
            assert_eq!(synonyms.spelling(&Sort::new(alias)), Spelling::Undenoted);
        }
        assert_eq!(synonyms.defects().len(), 1);
        match &synonyms.defects()[0] {
            SynonymDefect::Cycle {
                declarations: cycle,
            } => assert_eq!(cycle, &[&declarations[0], &declarations[1]]),
            SynonymDefect::Ambiguous { .. } => panic!("a cycle is not an ambiguity"),
        }
    }

    #[test]
    fn a_self_synonym_is_a_cycle() {
        let declarations = [synonym("A", "A")];
        let synonyms = SortSynonyms::of(&declarations);
        assert_eq!(synonyms.spelling(&Sort::new("A")), Spelling::Undenoted);
        assert_eq!(synonyms.defects().len(), 1);
        match &synonyms.defects()[0] {
            SynonymDefect::Cycle {
                declarations: cycle,
            } => assert_eq!(cycle, &[&declarations[0]]),
            SynonymDefect::Ambiguous { .. } => panic!("a self-loop is not an ambiguity"),
        }
    }

    #[test]
    fn different_denotations_are_ambiguous() {
        let declarations = [synonym("A", "Int"), synonym("A", "Bool")];
        let synonyms = SortSynonyms::of(&declarations);
        assert_eq!(synonyms.spelling(&Sort::new("A")), Spelling::Undenoted);
        assert_eq!(synonyms.defects().len(), 1);
        match &synonyms.defects()[0] {
            SynonymDefect::Ambiguous {
                alias,
                declarations: ambiguous,
            } => {
                assert_eq!(alias, &Sort::new("A"));
                assert_eq!(
                    ambiguous,
                    &vec![
                        (&declarations[0], Sort::new("Int")),
                        (&declarations[1], Sort::new("Bool"))
                    ]
                );
            }
            SynonymDefect::Cycle { .. } => panic!("distinct terminal sorts do not form a cycle"),
        }
    }

    #[test]
    fn declarations_that_agree_have_one_denotation() {
        let declarations = [synonym("A", "B"), synonym("B", "Int"), synonym("A", "Int")];
        let synonyms = SortSynonyms::of(&declarations);
        assert_eq!(
            synonyms.spelling(&Sort::new("A")),
            Spelling::Synonym {
                denotes: &Sort::new("Int")
            }
        );
        assert!(synonyms.defects().is_empty());
    }

    #[test]
    fn a_parametric_alias_matches_only_itself() {
        let declaration = Sentence::SortSynonym {
            new_sort: Sort::with_parameters("Alias", vec![Sort::new("Int")]),
            old_sort: Sort::new("Target"),
            attributes: Attributes::default(),
        };
        let synonyms = SortSynonyms::of([&declaration]);
        assert_eq!(
            synonyms.spelling(&Sort::with_parameters("Alias", vec![Sort::new("Int")])),
            Spelling::Synonym {
                denotes: &Sort::new("Target")
            }
        );
        assert_eq!(
            synonyms.spelling(&Sort::with_parameters("Alias", vec![Sort::new("Bool")])),
            Spelling::Sort
        );
    }

    #[test]
    fn duplicate_equations_keep_the_first_declaration_and_ambiguity_propagates() {
        let declarations = [
            synonym("A", "Int"),
            synonym("A", "Int"),
            synonym("A", "Bool"),
            synonym("C", "A"),
        ];
        let synonyms = SortSynonyms::of(&declarations);
        assert_eq!(synonyms.spelling(&Sort::new("C")), Spelling::Undenoted);
        assert_eq!(synonyms.defects().len(), 1);
        match &synonyms.defects()[0] {
            SynonymDefect::Ambiguous {
                declarations: ambiguous,
                ..
            } => {
                assert_eq!(ambiguous.len(), 2);
                assert!(std::ptr::eq(ambiguous[0].0, &declarations[0]));
                assert!(std::ptr::eq(ambiguous[1].0, &declarations[2]));
            }
            SynonymDefect::Cycle { .. } => panic!("distinct terminal sorts do not form a cycle"),
        }
    }

    #[test]
    fn an_empty_view_has_no_aliases_or_defects() {
        let synonyms = SortSynonyms::of([]);
        assert!(synonyms.is_empty());
        assert!(synonyms.defects().is_empty());
        assert_eq!(synonyms.spelling(&Sort::new("A")), Spelling::Sort);
        assert!(!SortSynonyms::of([&synonym("A", "A")]).is_empty());
    }
}
