//! The sorts cell completion gives the cell-fragment variables of a typed sentence.
//!
//! Cell completion (`kompile::passes::concretize_cells`) runs before injection, and it rewrites
//! every occurrence of a cell-fragment variable: a variable without a cell sort written directly
//! in the body of a cell with children, as an item of the body or as a side of a rewrite item.
//! The rule parser reads such a variable at `Bag` (it writes `#SemanticCastToBag(X)`), so the
//! loaded sentence has it at `Bag` everywhere.
//! Completion's analysis (`Concretizer::analyze_fragments`) decides which children of the cell
//! the variable stands for, and keeps the value sort of each in the variable's
//! `FragmentInfo::split`.
//! Completion then builds (`Concretizer::sort_cells_level`, `order_children`,
//! `fragment_replacement`):
//! - at each occurrence in a cell body, the variable itself at the value sort of its one child
//!   (`AccountCellMap` for a `multiplicity="*"` child, the cell sort for any other), or one fresh
//!   variable per child when it stands for none or several;
//! - for its sort predicate (`isBag(X)`, `isPCellFragment(X)`), the sort predicates of those
//!   parts;
//! - at every other occurrence, in the body, the requires or the ensures, the fragment term
//!   `<p>-fragment(..)`, whose sort is the cell's fragment sort (`AccountsCellFragment`).
//!
//! [`complete`] reads the variables and their parts from completion's own analysis
//! ([`CellCompletion::fragment_variables`]), on the resolved sentence with its anonymous
//! variables named as compilation names them, and gives each occurrence the sort of the term
//! completion builds there.
//! The term shape is unchanged (a variable stays a variable), so the loaded and resolved walks
//! stay aligned.
//! An occurrence in a body that completion replaces by its parts, or by none, is left without a
//! sort: the compiled term has no one term there, and each part is placed in its own child at
//! its own sort.
//! A sort predicate's argument is given the sort of the variable's one part, or none either.
//! The re-sorted variable keeps no cast: the walk reports the requirement of the position the
//! cast stood at for it ([`Completed::contains`]).
//!
//! Cost: one walk of the sentence to find a variable in a cell body; and, when there is one, a
//! copy of the sentence, compilation's completion of its cells up to that analysis, and one
//! more walk of the sentence and of the copy.
//! The cell model is built once per typer and model module.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::definition::{LabelHead, ModuleId, ResolvedDefinition, Sentence};
use crate::kast::{InternalLabel, Sort, Term};
use crate::kompile::passes::{CellCompletion, FragmentVariable, resolve_anon_vars_in_sentence};

use super::super::SortInjector;

/// The occurrences of cell-fragment variables a typed sentence's completion re-sorts, and the
/// cell model that completes the sentence (none for a sentence without an authored cell).
#[derive(Default)]
pub(super) struct Completed {
    pub(super) completion: Option<Arc<CellCompletion>>,
    /// The address of each re-sorted occurrence, as a node of the resolved sentence.
    nodes: BTreeSet<usize>,
    /// The cell-fragment variables with a name of their own in the typed sentence, by name.
    pub(super) variables: BTreeMap<String, FragmentVariable>,
}

impl Completed {
    fn new(completion: Arc<CellCompletion>) -> Self {
        Self {
            completion: Some(completion),
            nodes: BTreeSet::new(),
            variables: BTreeMap::new(),
        }
    }

    /// Whether completion re-sorts no occurrence.
    pub(super) fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Whether `name` is a cell-fragment variable of the typed sentence.
    pub(super) fn mentions(&self, name: &str) -> bool {
        self.variables.contains_key(name)
    }

    /// Whether `node`, a node of the resolved sentence, is an occurrence completion re-sorts:
    /// it has no cast in the compiled term, so it occupies the position of a cast above it.
    pub(super) fn contains(&self, node: &Term) -> bool {
        self.nodes.contains(&std::ptr::from_ref(node).addr())
    }
}

/// Give each occurrence of a cell-fragment variable of `sentence`, a resolved rule or claim of
/// `module`, and of `values`, the values its local functions are applied to in it, the sort of
/// the term completion builds there; or completion's error for the sentence.
///
/// The terms are changed in place, so the addresses [`Completed`] records are those of their
/// nodes for as long as they are not moved.
pub(super) fn complete(
    sentence: &mut Sentence,
    values: Vec<&mut Term>,
    completion: Arc<CellCompletion>,
    definition: &ResolvedDefinition,
    module: ModuleId,
    injector: &SortInjector<'_, '_>,
) -> Result<Completed, String> {
    let (Sentence::Rule {
        body,
        requires,
        ensures,
        ..
    }
    | Sentence::Claim {
        body,
        requires,
        ensures,
        ..
    }) = &*sentence
    else {
        return Ok(Completed::new(completion));
    };
    if ![body, requires, ensures]
        .into_iter()
        .any(|root| has_body_variable(root, &completion))
    {
        return Ok(Completed::new(completion));
    }
    let (named, _) = resolve_anon_vars_in_sentence(sentence.clone());
    let fragments = completion.fragment_variables(definition, module, named.clone())?;
    if fragments.is_empty() {
        return Ok(Completed::new(completion));
    }
    let mut sorts = BTreeMap::new();
    for (name, variable) in &fragments {
        let production = injector
            .productions
            .productions_for(&LabelHead::from(&variable.fragment))
            .first()
            .map(|id| injector.productions.production(*id));
        let Some(Sentence::Production { sort, .. }) = production else {
            return Err(format!(
                "cell completion writes {} for the cell fragment variable {name}, and no production declares it",
                variable.fragment.name
            ));
        };
        sorts.insert(name.clone(), sort.clone());
    }
    let model = Arc::clone(&completion);
    let mut resort = Resort {
        completion: &model,
        fragments: &fragments,
        sorts: &sorts,
        completed: Completed::new(completion),
    };
    let (
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        },
        Sentence::Rule {
            body: named_body,
            requires: named_requires,
            ensures: named_ensures,
            ..
        }
        | Sentence::Claim {
            body: named_body,
            requires: named_requires,
            ensures: named_ensures,
            ..
        },
    ) = (sentence, &named)
    else {
        unreachable!("naming anonymous variables keeps the sentence kind")
    };
    resort.term(body, named_body);
    resort.term(requires, named_requires);
    resort.term(ensures, named_ensures);
    // A value is a term of the enclosing scope written outside its cells; its anonymous
    // variables are none of the sentence's.
    for value in values {
        let named = value.clone();
        resort.term(value, &named);
    }
    Ok(resort.completed)
}

/// Where completion meets an occurrence of a cell-fragment variable.
#[derive(Clone, Copy)]
enum Place {
    /// In the body of a cell with children, or as the argument of the variable's sort
    /// predicate: completion writes the variable's parts there.
    Parts,
    /// Anywhere else: completion writes the fragment term there.
    Fragment,
}

struct Resort<'c> {
    completion: &'c CellCompletion,
    fragments: &'c BTreeMap<String, FragmentVariable>,
    /// The sort of each variable's fragment term.
    sorts: &'c BTreeMap<String, Sort>,
    completed: Completed,
}

impl Resort<'_> {
    /// Re-sort the occurrences in `term`, a node of the typed sentence, whose copy with its
    /// anonymous variables named is `named`.
    // Invariant: each call recurses into the direct subterms of `term` and `named`, which have
    // the same shape; their depth bounds the recursion.
    fn term(&mut self, term: &mut Term, named: &Term) {
        if matches!(term.unannotated(), Term::Variable { .. }) {
            self.variable(term, named, Place::Fragment);
            return;
        }
        match (unannotated_mut(term), named.unannotated()) {
            (
                Term::Apply { label, arguments },
                Term::Apply {
                    arguments: named_arguments,
                    ..
                },
            ) => {
                if self.completion.is_parent(label) {
                    for (argument, named) in arguments.iter_mut().zip(named_arguments) {
                        self.body_item(argument, named);
                    }
                } else if let ([argument], [named]) =
                    (arguments.as_mut_slice(), named_arguments.as_slice())
                    && let Term::Variable { name, .. } = named.unannotated()
                    && self.fragments.get(name).is_some_and(|variable| {
                        variable
                            .predicates
                            .iter()
                            .any(|predicate| predicate.name == label.name)
                    })
                {
                    self.variable(argument, named, Place::Parts);
                } else {
                    for (argument, named) in arguments.iter_mut().zip(named_arguments) {
                        self.term(argument, named);
                    }
                }
            }
            (
                Term::Rewrite { left, right },
                Term::Rewrite {
                    left: named_left,
                    right: named_right,
                },
            ) => {
                self.term(left, named_left);
                self.term(right, named_right);
            }
            (
                Term::As { pattern, alias },
                Term::As {
                    pattern: named_pattern,
                    alias: named_alias,
                },
            ) => {
                self.term(pattern, named_pattern);
                self.term(alias, named_alias);
            }
            (Term::Sequence(items), Term::Sequence(named_items)) => {
                for (item, named) in items.iter_mut().zip(named_items) {
                    self.term(item, named);
                }
            }
            (
                Term::Apply { .. }
                | Term::Rewrite { .. }
                | Term::As { .. }
                | Term::Sequence(_)
                | Term::Variable { .. }
                | Term::Token { .. }
                | Term::InjectedLabel(_)
                | Term::Annotated { .. },
                _,
            ) => {}
        }
    }

    /// Re-sort the occurrences in `term`, an argument of a cell with children: an item of its
    /// body (through `#cells`) or a side of a rewrite item that is a variable is one of the
    /// occurrences completion writes the parts of (`collect_direct_fragment_variables`).
    fn body_item(&mut self, term: &mut Term, named: &Term) {
        if matches!(term.unannotated(), Term::Variable { .. }) {
            self.variable(term, named, Place::Parts);
            return;
        }
        match (unannotated_mut(term), named.unannotated()) {
            (
                Term::Apply { label, arguments },
                Term::Apply {
                    arguments: named_arguments,
                    ..
                },
            ) if label.is(InternalLabel::Cells) => {
                for (argument, named) in arguments.iter_mut().zip(named_arguments) {
                    self.body_item(argument, named);
                }
            }
            (
                Term::Rewrite { left, right },
                Term::Rewrite {
                    left: named_left,
                    right: named_right,
                },
            ) => {
                self.body_item(left, named_left);
                self.body_item(right, named_right);
            }
            (
                other @ (Term::Apply { .. }
                | Term::Rewrite { .. }
                | Term::As { .. }
                | Term::Sequence(_)
                | Term::Variable { .. }
                | Term::Token { .. }
                | Term::InjectedLabel(_)
                | Term::Annotated { .. }),
                named,
            ) => self.term(other, named),
        }
    }

    /// Give `term`, a variable whose copy is `named`, the sort of what completion writes for
    /// it at `place`, when it is a cell-fragment variable.
    fn variable(&mut self, term: &mut Term, named: &Term, place: Place) {
        let Term::Variable { name, .. } = named.unannotated() else {
            unreachable!("the copy of a variable is a variable")
        };
        let Some(variable) = self.fragments.get(name) else {
            return;
        };
        let sort = match place {
            Place::Parts => match variable.parts.as_slice() {
                [part] => Some(part.clone()),
                _ => None,
            },
            Place::Fragment => Some(self.sorts[name].clone()),
        };
        self.completed
            .nodes
            .insert(std::ptr::from_ref::<Term>(term).addr());
        // A part is a variable of its own, without the occurrence's metadata; the fragment term
        // keeps the occurrence's metadata.
        let mut node = &mut *term;
        loop {
            match node {
                Term::Annotated {
                    term: inner,
                    metadata,
                } => {
                    if matches!(place, Place::Parts) {
                        metadata.sort = None;
                    }
                    node = inner;
                }
                Term::Variable {
                    name: written,
                    sort: own,
                } => {
                    *own = sort;
                    if written == name {
                        self.completed
                            .variables
                            .insert(name.clone(), variable.clone());
                    }
                    return;
                }
                Term::Apply { .. }
                | Term::Rewrite { .. }
                | Term::As { .. }
                | Term::Sequence(_)
                | Term::Token { .. }
                | Term::InjectedLabel(_) => unreachable!("a variable"),
            }
        }
    }
}

/// Whether some cell with children in `term` has, in its body, a variable without a cell sort:
/// a candidate cell-fragment variable (`collect_fragment_observations`).
pub(super) fn has_body_variable(term: &Term, completion: &CellCompletion) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        if let Term::Apply { label, arguments } = term.unannotated()
            && completion.is_parent(label)
        {
            found |= arguments
                .iter()
                .any(|argument| body_variable(argument, completion));
        }
    });
    found
}

/// Whether `term`, an argument of a cell with children, has an item or rewrite side that is a
/// variable without a cell sort.
fn body_variable(term: &Term, completion: &CellCompletion) -> bool {
    match term.unannotated() {
        Term::Variable { sort, .. } => !sort
            .as_ref()
            .is_some_and(|sort| completion.is_cell_sort(sort)),
        Term::Apply { label, arguments } if label.is(InternalLabel::Cells) => arguments
            .iter()
            .any(|argument| body_variable(argument, completion)),
        Term::Rewrite { left, right } => {
            body_variable(left, completion) || body_variable(right, completion)
        }
        Term::Apply { .. }
        | Term::As { .. }
        | Term::Sequence(_)
        | Term::Token { .. }
        | Term::InjectedLabel(_)
        | Term::Annotated { .. } => false,
    }
}

fn unannotated_mut(term: &mut Term) -> &mut Term {
    match term {
        Term::Annotated { term, .. } => unannotated_mut(term),
        other @ (Term::Apply { .. }
        | Term::Rewrite { .. }
        | Term::As { .. }
        | Term::Sequence(_)
        | Term::Variable { .. }
        | Term::Token { .. }
        | Term::InjectedLabel(_)) => other,
    }
}
