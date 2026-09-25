//! ```toml algorithm
//! id = "definition.catalog.sort"
//! name = "sort-catalog construction"
//! sites = ["SortCatalog", "SortCatalog::new", "SortCatalog::from_visible"]
//! variable = "V = visible sentences"
//! counters = []
//! no_counter = "sort-catalog construction has no dedicated counter"
//! consumes = [{ type = "k_rust::definition::ResolvedDefinition", role = "resolved definition" }]
//! produces = [{ type = "k_rust::definition::SortCatalog<'a>", role = "sort lookup" }]
//!
//! [[cost]]
//! mode = "one catalog"
//! bound = "O(V log V)"
//! ```
//!
//! Sort catalogs group visible declarations and instantiated sort heads in declaration order.
//! Construction is O(V log V) in visible sentences V: it scans every visible sentence, since productions also feed the instantiations, defined heads, token sorts, and list sorts, and the log factor comes from the BTree inserts; no dedicated counter.
//!
//! Deterministic indexes over the sorts visible from a resolved module.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::{Attributes, Sentence};
use super::catalog::SortHead;
use super::resolve::{ModuleId, ResolvedDefinition};
use crate::definition::AttributeKey;
use crate::kast::Sort;
use crate::names::BuiltinSort;

#[derive(Clone, Debug)]
pub struct SortCatalog<'a> {
    declarations: Vec<&'a Sentence>,
    declarations_by_head: BTreeMap<SortHead, Vec<&'a Sentence>>,
    synonyms: Vec<&'a Sentence>,
    synonym_map: BTreeMap<Sort, Sort>,
    defined_heads: BTreeSet<SortHead>,
    instantiations: BTreeMap<SortHead, BTreeSet<Sort>>,
    all_sorts: BTreeSet<Sort>,
    local_sorts: BTreeSet<Sort>,
    attributes_by_head: BTreeMap<SortHead, Attributes>,
    hooks: BTreeMap<String, String>,
    token_sorts: BTreeSet<Sort>,
    parametric_token_sorts: Vec<(Sort, Vec<Sort>)>,
    list_sorts: BTreeSet<Sort>,
}

impl<'a> SortCatalog<'a> {
    pub fn new(
        visible_sentences: impl IntoIterator<Item = &'a Sentence>,
        imported_sorts: impl IntoIterator<Item = Sort>,
    ) -> Self {
        let sentences = visible_sentences.into_iter().collect::<Vec<_>>();
        let declarations = sentences
            .iter()
            .copied()
            .filter(|sentence| matches!(sentence, Sentence::SyntaxSort { .. }))
            .collect::<Vec<_>>();
        let synonyms = sentences
            .iter()
            .copied()
            .filter(|sentence| matches!(sentence, Sentence::SortSynonym { .. }))
            .collect::<Vec<_>>();

        let mut declarations_by_head = BTreeMap::<SortHead, Vec<&Sentence>>::new();
        for declaration in &declarations {
            let Sentence::SyntaxSort { sort, .. } = declaration else {
                unreachable!()
            };
            declarations_by_head
                .entry(SortHead::from(sort))
                .or_default()
                .push(declaration);
        }

        let mut synonym_map = BTreeMap::new();
        for synonym in &synonyms {
            let Sentence::SortSynonym {
                new_sort, old_sort, ..
            } = synonym
            else {
                unreachable!()
            };
            synonym_map.insert(new_sort.clone(), old_sort.clone());
        }

        let instantiations = compute_instantiations(&sentences, &declarations);
        let defined_heads = compute_defined_heads(&sentences, &declarations, &instantiations);
        let all_sorts = defined_heads
            .iter()
            .filter(|head| !instantiations.contains_key(*head))
            .map(|head| {
                assert_eq!(head.parameters(), 0);
                Sort::new(head.as_str())
            })
            .chain(instantiations.values().flatten().cloned())
            .collect::<BTreeSet<_>>();
        let imported_sorts = imported_sorts.into_iter().collect::<BTreeSet<_>>();
        let local_sorts = all_sorts.difference(&imported_sorts).cloned().collect();

        let mut attributes_by_head = BTreeMap::new();
        let all_heads = all_sorts
            .iter()
            .map(SortHead::from)
            .chain(declarations_by_head.keys().cloned())
            .collect::<BTreeSet<_>>();
        for head in all_heads {
            let attributes = declarations_by_head
                .get(&head)
                .into_iter()
                .flatten()
                .map(|declaration| declaration.attributes());
            attributes_by_head.insert(
                head,
                Attributes::merge(attributes).unwrap_or_else(|error| error.merged),
            );
        }
        let hooks = attributes_by_head
            .iter()
            .filter_map(|(head, attributes)| {
                attributes
                    .string(AttributeKey::Hook)
                    .map(|hook| (head.as_str().to_owned(), hook.to_owned()))
            })
            .collect();

        let token_sorts = sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::Production {
                    sort, attributes, ..
                }
                | Sentence::SyntaxSort {
                    sort, attributes, ..
                } if attributes.has(AttributeKey::Token) => Some(sort.clone()),
                _ => None,
            })
            .collect();
        let parametric_token_sorts = sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::Production {
                    sort,
                    parameters,
                    attributes,
                    ..
                }
                | Sentence::SyntaxSort {
                    sort,
                    parameters,
                    attributes,
                    ..
                } if !parameters.is_empty() && attributes.has(AttributeKey::Token) => {
                    Some((sort.clone(), parameters.clone()))
                }
                _ => None,
            })
            .collect();
        let list_sorts = sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::Production {
                    sort, attributes, ..
                } if attributes.has(AttributeKey::UserList) => Some(sort.clone()),
                _ => None,
            })
            .collect();

        Self {
            declarations,
            declarations_by_head,
            synonyms,
            synonym_map,
            defined_heads,
            instantiations,
            all_sorts,
            local_sorts,
            attributes_by_head,
            hooks,
            token_sorts,
            parametric_token_sorts,
            list_sorts,
        }
    }

    pub fn from_visible(sentences: impl IntoIterator<Item = &'a Sentence>) -> Self {
        Self::new(sentences, std::iter::empty())
    }

    pub fn declarations(&self) -> impl ExactSizeIterator<Item = &'a Sentence> + '_ {
        self.declarations.iter().copied()
    }

    pub fn declarations_by_head(&self) -> &BTreeMap<SortHead, Vec<&'a Sentence>> {
        &self.declarations_by_head
    }

    pub fn declarations_for(&self, head: &SortHead) -> &[&'a Sentence] {
        self.declarations_by_head
            .get(head)
            .map_or(&[], Vec::as_slice)
    }

    pub fn synonyms(&self) -> impl ExactSizeIterator<Item = &'a Sentence> + '_ {
        self.synonyms.iter().copied()
    }

    pub fn synonym_map(&self) -> &BTreeMap<Sort, Sort> {
        &self.synonym_map
    }

    pub fn defined_heads(&self) -> &BTreeSet<SortHead> {
        &self.defined_heads
    }

    pub fn instantiations(&self) -> &BTreeMap<SortHead, BTreeSet<Sort>> {
        &self.instantiations
    }

    pub fn all_sorts(&self) -> &BTreeSet<Sort> {
        &self.all_sorts
    }

    pub fn local_sorts(&self) -> &BTreeSet<Sort> {
        &self.local_sorts
    }

    pub fn sorted_defined_heads(&self) -> impl ExactSizeIterator<Item = &SortHead> {
        self.defined_heads.iter()
    }

    pub fn sorted_all_sorts(&self) -> impl ExactSizeIterator<Item = &Sort> {
        self.all_sorts.iter()
    }

    pub fn attributes_by_head(&self) -> &BTreeMap<SortHead, Attributes> {
        &self.attributes_by_head
    }

    pub fn attributes_for(&self, head: &SortHead) -> Option<&Attributes> {
        self.attributes_by_head.get(head)
    }

    pub fn hooks(&self) -> &BTreeMap<String, String> {
        &self.hooks
    }

    pub fn token_sorts(&self) -> &BTreeSet<Sort> {
        &self.token_sorts
    }

    /// Whether a term of this sort can denote a domain value in this module.
    pub fn admits_domain_value(&self, sort: &Sort) -> bool {
        self.token_sorts.contains(sort)
            || self.parametric_token_sorts.iter().any(|(declared, formals)| {
                matches_token_sort(declared, sort, formals, &mut BTreeMap::new())
            })
            || self.hooks.contains_key(&sort.name)
            // Truth values and configuration-map keys have intrinsic domains even in a
            // minimal structured definition without their usual syntax declarations.
            || sort.is_builtin(BuiltinSort::Bool)
            || sort.is_builtin(BuiltinSort::KConfigVar)
    }

    pub fn list_sorts(&self) -> &BTreeSet<Sort> {
        &self.list_sorts
    }
}

fn matches_token_sort(
    declared: &Sort,
    actual: &Sort,
    formals: &[Sort],
    substitution: &mut BTreeMap<Sort, Sort>,
) -> bool {
    if formals.contains(declared) {
        return substitution
            .entry(declared.clone())
            .or_insert_with(|| actual.clone())
            == actual;
    }
    declared.name == actual.name
        && declared.parameters.len() == actual.parameters.len()
        && declared
            .parameters
            .iter()
            .zip(&actual.parameters)
            .all(|(declared, actual)| matches_token_sort(declared, actual, formals, substitution))
}

impl ResolvedDefinition {
    /// Compute the sort catalog for a module.
    ///
    /// This accessor recomputes on every call; use `DefinitionViews` inside a loop.
    pub fn sort_catalog(&self, module: ModuleId) -> SortCatalog<'_> {
        // Invariant: the collected set holds the `all_sorts` of the visible-sentence catalog of every entry of `self.direct_imports(module)` already consumed; the pass consumes one direct import per step and rebuilds its catalog with `SortCatalog::from_visible`.
        let imported_sorts = self
            .direct_imports(module)
            .into_iter()
            .flat_map(|import| {
                SortCatalog::from_visible(self.sentences(import.module))
                    .all_sorts
                    .into_iter()
            })
            .collect::<BTreeSet<_>>();
        SortCatalog::new(self.sentences(module), imported_sorts)
    }
}

fn compute_instantiations(
    sentences: &[&Sentence],
    declarations: &[&Sentence],
) -> BTreeMap<SortHead, BTreeSet<Sort>> {
    let mut nonempty = BTreeMap::<SortHead, BTreeSet<Sort>>::new();
    let mut heads = BTreeSet::new();
    // Invariant: `heads` holds the head of every parametric production sort among the entries of `sentences` before `sentence`, and `nonempty` maps each such head to those sorts that mention none of their production's `parameters`; each iteration consumes one sentence.
    for sentence in sentences {
        let Sentence::Production {
            parameters, sort, ..
        } = sentence
        else {
            continue;
        };
        if !sort.parameters.is_empty() {
            let head = SortHead::from(sort);
            heads.insert(head.clone());
            if !parameters.contains(sort)
                && sort
                    .parameters
                    .iter()
                    .all(|parameter| !parameters.contains(parameter))
            {
                nonempty.entry(head).or_default().insert(sort.clone());
            }
        }
    }
    for declaration in declarations {
        let Sentence::SyntaxSort {
            parameters, sort, ..
        } = declaration
        else {
            unreachable!()
        };
        if !sort.parameters.is_empty() {
            let head = SortHead::from(sort);
            heads.insert(head.clone());
            if parameters.is_empty() {
                nonempty.entry(head).or_default().insert(sort.clone());
            }
        }
    }
    heads
        .into_iter()
        .map(|head| {
            let instances = nonempty.remove(&head).unwrap_or_default();
            (head, instances)
        })
        .collect()
}

fn compute_defined_heads(
    sentences: &[&Sentence],
    declarations: &[&Sentence],
    instantiations: &BTreeMap<SortHead, BTreeSet<Sort>>,
) -> BTreeSet<SortHead> {
    let mut defined = BTreeSet::new();
    // Invariant: `defined` holds the head of every production sort among the entries of `sentences` before `sentence` that is not one of its production's `parameters`; each iteration consumes one sentence.
    for sentence in sentences {
        let Sentence::Production {
            parameters, sort, ..
        } = sentence
        else {
            continue;
        };
        if !parameters.contains(sort) {
            defined.insert(SortHead::from(sort));
        }
    }
    for declaration in declarations {
        let Sentence::SyntaxSort {
            parameters, sort, ..
        } = declaration
        else {
            unreachable!()
        };
        if parameters.is_empty() {
            defined.insert(SortHead::from(sort));
        }
    }
    defined.extend(
        instantiations
            .values()
            .flatten()
            .flat_map(|sort| &sort.parameters)
            .filter(|sort| sort.name.parse::<i32>().is_ok())
            .map(SortHead::from),
    );
    defined
}
