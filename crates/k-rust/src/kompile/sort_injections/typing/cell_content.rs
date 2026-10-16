//! The sorts cell completion gives the cell-fragment and one-cell alias variables of a typed
//! sentence.
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
//! Before that, it gives the variable `V` of each alias `P #as V` of one cell that cell's sort,
//! at every occurrence (`sort_one_cell_aliases`).
//!
//! [`complete`] reads the alias sorts, the fragment variables and their parts from completion's
//! own analysis ([`CellCompletion::alias_sorts`], [`CellCompletion::fragment_variables`]), and
//! gives each occurrence the sort of the term completion builds there.
//! Compilation lowers local functions first, so the analysis reads the sentence with each
//! local function's stand-in replaced by the application compilation writes there, its value
//! and its closure variables as arguments, and with its anonymous variables named as
//! compilation names them; the values are re-sorted with the sentence, as terms of its scope.
//! The term shape is unchanged (a variable stays a variable), so the loaded and resolved walks
//! stay aligned.
//! An occurrence in a body that completion replaces by its parts, or by none, is left without a
//! sort: the compiled term has no one term there, and each part is placed in its own child at
//! its own sort.
//! A sort predicate's argument is given the sort of the variable's one part, or none either.
//! The re-sorted variable keeps no cast: the walk reports the requirement of the position the
//! cast stood at for it ([`Completed::contains`]).
//!
//! Cost: one walk of the sentence and its values for the alias sorts and one to find a variable
//! in a cell body; and, when there is one, a copy of the sentence, compilation's completion of
//! its cells up to that analysis, and one more walk of the sentence and of the copy.
//! The cell model is built once per typer and model module.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::definition::{LabelHead, ModuleId, ResolvedDefinition, Sentence};
use crate::kast::{InternalLabel, Label, Sort, Term};
use crate::kompile::passes::{CellCompletion, FragmentVariable, resolve_anon_vars_in_sentence};

use super::super::SortInjector;
use super::local_functions::Locals;

/// The occurrences a typed sentence's completion re-sorts, and the cell model that completes
/// the sentence (none for a sentence without an authored cell).
#[derive(Default)]
pub(super) struct Completed {
    pub(super) completion: Option<Arc<CellCompletion>>,
    /// The address of each re-sorted occurrence, as a node of the resolved sentence or of a
    /// local function's value.
    nodes: BTreeSet<usize>,
    /// The cell-fragment variables with a name of their own in the typed sentence, by name.
    pub(super) variables: BTreeMap<String, FragmentVariable>,
    /// The sort of the fragment term of each of them.
    pub(super) fragment_sorts: BTreeMap<String, Sort>,
    /// The cell sort of each one-cell alias variable.
    pub(super) aliases: BTreeMap<String, Sort>,
    /// The local functions applied in the sentence's own scope (not in an equation), by
    /// stand-in name.
    pub(super) enclosing: BTreeSet<String>,
    /// Whether a local function is written as an item of the body of a cell with children.
    pub(super) local_in_body: bool,
    /// The re-sorted nodes a walk looked up, which must be all of them.
    #[cfg(debug_assertions)]
    looked_up: std::cell::RefCell<BTreeSet<usize>>,
}

impl Completed {
    fn new(completion: Arc<CellCompletion>) -> Self {
        Self {
            completion: Some(completion),
            ..Self::default()
        }
    }

    /// Whether `node`, a node of the resolved sentence or of a local function's value, is an
    /// occurrence completion re-sorts: it has no cast in the compiled term, so it occupies the
    /// position of a cast above it.
    pub(super) fn contains(&self, node: &Term) -> bool {
        let address = std::ptr::from_ref(node).addr();
        let contained = self.nodes.contains(&address);
        #[cfg(debug_assertions)]
        if contained {
            self.looked_up.borrow_mut().insert(address);
        }
        contained
    }

    /// Check, in a debug build, that the walks looked up every re-sorted node: a node that was
    /// moved or copied after [`complete`] recorded it would keep a requirement it does not have.
    pub(super) fn assert_all_looked_up(&self) {
        #[cfg(debug_assertions)]
        debug_assert_eq!(
            *self.looked_up.borrow(),
            self.nodes,
            "a re-sorted occurrence was not met at its recorded address"
        );
    }
}

/// Give each occurrence of a cell-fragment or one-cell alias variable of `sentence`, a resolved
/// rule or claim of `module`, and of the values its `locals` are applied to, the sort of the
/// term completion builds there; or completion's error for the sentence.
///
/// The terms are changed in place, so the addresses [`Completed`] records are those of their
/// nodes for as long as they are not moved.
pub(super) fn complete(
    sentence: &mut Sentence,
    locals: &mut Locals,
    completion: Arc<CellCompletion>,
    definition: &ResolvedDefinition,
    module: ModuleId,
    injector: &SortInjector<'_, '_>,
) -> Result<Completed, String> {
    let mut completed = Completed::new(Arc::clone(&completion));
    let aliases = {
        let expanded = expanded(sentence, locals);
        completion.alias_sorts(&roots(&expanded))?
    };
    completed.aliases.clone_from(&aliases);
    if !aliases.is_empty() {
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
        }) = &mut *sentence
        else {
            return Ok(completed);
        };
        for term in [body, requires, ensures]
            .into_iter()
            .chain(locals.values_mut().map(|local| &mut local.argument))
        {
            sort_aliases(term, &aliases, &completion, &mut completed.nodes);
        }
    }
    let named = resolve_anon_vars_in_sentence(expanded(sentence, locals)).0;
    if !roots(&named)
        .into_iter()
        .any(|root| has_body_variable(root, &completion))
    {
        return Ok(completed);
    }
    let fragments = completion.fragment_variables(definition, module, named.clone())?;
    if fragments.is_empty() {
        return Ok(completed);
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
    let mut resort = Resort {
        completion: &completion,
        fragments: &fragments,
        sorts: &sorts,
        values: locals
            .iter_mut()
            .map(|(name, local)| (name.clone(), &mut local.argument))
            .collect(),
        completed,
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
        [named_body, named_requires, named_ensures],
    ) = (sentence, roots(&named))
    else {
        unreachable!("naming anonymous variables keeps the sentence kind")
    };
    resort.term(body, named_body);
    resort.term(requires, named_requires);
    resort.term(ensures, named_ensures);
    Ok(resort.completed)
}

/// The body, requires and ensures of `sentence`, a rule or claim.
fn roots(sentence: &Sentence) -> [&Term; 3] {
    match sentence {
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
        } => [body, requires, ensures],
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => unreachable!("the typer completes rules and claims"),
    }
}

/// A copy of `sentence`, a rule or claim, with each stand-in variable of `locals` replaced by
/// the application compilation's lowering writes there: the stand-in label applied to the
/// value and the closure variables.
fn expanded(sentence: &Sentence, locals: &Locals) -> Sentence {
    let mut copy = sentence.clone();
    if locals.is_empty() {
        return copy;
    }
    if let Sentence::Rule {
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
    } = &mut copy
    {
        for term in [body, requires, ensures] {
            expand(term, locals);
        }
    }
    copy
}

// Invariant: each call recurses into the direct subterms of `term`, and into the value of a
// stand-in it replaces, which lowering built from a strict subterm of the loaded sentence; the
// sentence's depth bounds the recursion.
fn expand(term: &mut Term, locals: &Locals) {
    if let Term::Variable { name, .. } = term.unannotated()
        && let Some(local) = locals.get(name)
    {
        let mut value = local.argument.clone();
        expand(&mut value, locals);
        let mut arguments = vec![value];
        arguments.extend(local.closure.iter().cloned());
        *term = Term::Apply {
            label: Label::new(name.clone()),
            arguments,
        };
        return;
    }
    match unannotated_mut(term) {
        Term::Apply { arguments, .. } => {
            for argument in arguments {
                expand(argument, locals);
            }
        }
        Term::Rewrite { left, right } => {
            expand(left, locals);
            expand(right, locals);
        }
        Term::As { pattern, alias } => {
            expand(pattern, locals);
            expand(alias, locals);
        }
        Term::Sequence(items) => {
            for item in items {
                expand(item, locals);
            }
        }
        Term::Variable { .. }
        | Term::Token { .. }
        | Term::InjectedLabel(_)
        | Term::Annotated { .. } => {}
    }
}

/// Give each variable of `term` that `aliases` sorts, and that completion does not read at a
/// cell sort already, its alias sort, recording the node.
// Invariant: each call recurses into the direct subterms of `term`; its depth bounds the
// recursion.
fn sort_aliases(
    term: &mut Term,
    aliases: &BTreeMap<String, Sort>,
    completion: &CellCompletion,
    nodes: &mut BTreeSet<usize>,
) {
    if let Term::Variable { name, .. } = term.unannotated()
        && let Some(sort) = aliases.get(name)
    {
        if !completion.has_cell_sort(term) {
            nodes.insert(std::ptr::from_ref::<Term>(term).addr());
            if let Term::Variable { sort: own, .. } = unannotated_mut(term) {
                *own = Some(sort.clone());
            }
        }
        return;
    }
    match unannotated_mut(term) {
        Term::Apply { arguments, .. } => {
            for argument in arguments {
                sort_aliases(argument, aliases, completion, nodes);
            }
        }
        Term::Rewrite { left, right } => {
            sort_aliases(left, aliases, completion, nodes);
            sort_aliases(right, aliases, completion, nodes);
        }
        Term::As { pattern, alias } => {
            sort_aliases(pattern, aliases, completion, nodes);
            sort_aliases(alias, aliases, completion, nodes);
        }
        Term::Sequence(items) => {
            for item in items {
                sort_aliases(item, aliases, completion, nodes);
            }
        }
        Term::Variable { .. }
        | Term::Token { .. }
        | Term::InjectedLabel(_)
        | Term::Annotated { .. } => {}
    }
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

struct Resort<'c, 'v> {
    completion: &'c CellCompletion,
    fragments: &'c BTreeMap<String, FragmentVariable>,
    /// The sort of each variable's fragment term.
    sorts: &'c BTreeMap<String, Sort>,
    /// The value of each local function not met yet, by stand-in name.
    values: BTreeMap<String, &'v mut Term>,
    completed: Completed,
}

impl Resort<'_, '_> {
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
            // A stand-in variable, whose copy is the application compilation writes there: its
            // value is a term of this scope.
            let (Term::Variable { name, .. }, Term::Apply { arguments, .. }) =
                (term.unannotated(), named.unannotated())
            else {
                unreachable!("the copy of a variable is a variable or a local function")
            };
            self.completed.enclosing.insert(name.clone());
            self.completed.local_in_body |= matches!(place, Place::Parts);
            if let Some(value) = self.values.remove(name) {
                self.term(value, &arguments[0]);
            }
            return;
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
                        self.completed
                            .fragment_sorts
                            .insert(name.clone(), self.sorts[name].clone());
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
