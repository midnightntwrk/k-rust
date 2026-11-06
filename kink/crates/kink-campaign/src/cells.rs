//! The cell projection: an end's configuration without the content of the cells a slot leaves
//! uncompared ([`CellProjection`], the state projection [`crate::StateProjection::Cells`]), and
//! where a compiled configuration's cells sit in its KORE terms ([`CellLayout`]).
//!
//! A cell application's arguments are its production's non-terminals, in order, so the argument
//! that holds a child cell is the same in every end. Through cells of multiplicity `1` the path
//! from `<generatedTop>` to a cell is therefore one list of argument indices. The walk along it
//! checks the symbol of each cell on the path, and at the position that the subterm there has the
//! position's sort under the baseline's declarations ([`UnobservedPosition::heads`]); only then
//! does it replace the subterm. In every end of the baseline's shape it reaches the cell, and an
//! end of another shape on the path or at the position (a mutant that reshapes the configuration)
//! has no such position there, and the walk leaves it as it is.
//!
//! A position inside a `?` or `*` cell is fixed relative to the instance that holds it, so the
//! walk reaches it in each instance:
//! - a `?` cell's position holds its one instance, the cell's own application, or another term
//!   when the cell is absent; the path goes on through the instance as through a cell of
//!   multiplicity `1`, and an absent cell has no position below it;
//! - a `*` cell's position holds a collection ([`Collection`]): its elements and the rest folded
//!   by the collection's concatenation. The walk goes on through the instance in each element
//!   ([`Through`]). The elements of a Set or Map are then sorted, so that the projection of the
//!   collection is a function of the multiset of its projected elements, whatever order the end
//!   wrote them in; a List keeps its order, which is its instances' identity. A Set is never
//!   re-read as a set, which would merge instances the projection made equal.
//!
//! A Map holds each instance by its key, the instance's key cell, which the element also holds as
//! its first argument; a position at or inside the key is refused
//! ([`CellLayoutRefusal::MapKeyLeftOut`]), since the walk goes on through the instance alone and
//! the element's key argument would still carry the content left out, so the projection could not
//! honour the declaration. A `?` or `*` cell's own position can be left out too: the projection
//! then leaves out the whole optional cell or collection.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use k_rust::backend::counter_erased;
use k_rust::definition::ResolvedDefinition;
use k_rust::definition::configuration::{CellMultiplicity, declared_cells};
use k_rust::kore::ast::{Definition as KoreDefinition, Pattern, Sentence, Sort};
use k_rust::kore::parser::parse_definition;
use k_rust::names::KoreAttribute;
use kink_native::ValidatedDefinition;

use crate::OracleFailureKind;
use crate::oracle::OracleFailure;

/// The KORE symbol of a compiled configuration's top cell, the head of every end.
const GENERATED_TOP: &str = "Lbl'-LT-'generatedTop'-GT-'";

/// How a `*` cell's collection holds its instances: the symbols `definition.kore` declares at
/// the collection sort with the collection hooks (`MAP.element`, `MAP.concat`, `MAP.unit`, and
/// likewise `SET.` and `LIST.`).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Collection {
    pub kind: CollectionKind,
    /// The element symbol (`LblThreadCellMapItem`).
    pub element: String,
    /// The element's argument that holds the instance, the cell's own application: the second
    /// of a Map element, whose first is the key cell, and the only one otherwise.
    pub instance: u32,
    /// The concatenation symbol (`Lbl'Unds'ThreadCellMap'Unds'`).
    pub concat: String,
    /// The unit symbol (`Lbl'Stop'ThreadCellMap`).
    pub unit: String,
}

/// The kind of a cell collection, its hook's prefix (`MAP`, `SET`, `LIST`).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum CollectionKind {
    Map,
    Set,
    List,
}

impl CollectionKind {
    /// Whether the collection's elements are unordered: those of a Map or a Set.
    #[must_use]
    pub const fn unordered(self) -> bool {
        matches!(self, Self::Map | Self::Set)
    }
}

/// A `*` cell on the path of an [`UnobservedPosition`]: the walk reaches its collection after
/// [`Self::at`] steps of the path, and goes on with the rest of the path from the instance of
/// each element.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Through {
    /// The number of steps of the path that reach the collection: `path[..at]` leads from the
    /// end's top application to it, and `path[at..]` from each instance, whose symbol is
    /// `symbols[at]`.
    pub at: u32,
    /// The `*` cell's K name, for reports.
    pub cell: String,
    /// The collection sort.
    pub sort: Sort,
    /// The symbols `definition.kore` declares without sort parameters and with [`Self::sort`]
    /// as their result sort, sorted ([`UnobservedPosition::heads`]).
    pub heads: Vec<String>,
    pub collection: Collection,
}

impl Through {
    /// Whether `term` has the collection sort ([`UnobservedPosition::has_sort`]).
    fn has_sort(&self, term: &Pattern) -> bool {
        has_sort(term, &self.sort, &self.heads)
    }

    /// The instance `component` holds, when it is an element of the collection.
    fn instance<'a>(&self, component: &'a Pattern) -> Option<&'a Pattern> {
        match component {
            Pattern::Application { symbol, arguments }
                if symbol.name == self.collection.element && symbol.sort_parameters.is_empty() =>
            {
                arguments.get(usize::try_from(self.collection.instance).ok()?)
            }
            _ => None,
        }
    }

    /// [`Self::instance`], mutably.
    fn instance_mut<'a>(&self, component: &'a mut Pattern) -> Option<&'a mut Pattern> {
        match component {
            Pattern::Application { symbol, arguments }
                if symbol.name == self.collection.element && symbol.sort_parameters.is_empty() =>
            {
                arguments.get_mut(usize::try_from(self.collection.instance).ok()?)
            }
            _ => None,
        }
    }

    /// Whether `term` is an application of the concatenation.
    fn concatenation<'a>(&self, term: &'a Pattern) -> Option<&'a [Pattern]> {
        match term {
            Pattern::Application { symbol, arguments }
                if symbol.name == self.collection.concat
                    && symbol.sort_parameters.is_empty()
                    && arguments.len() == 2 =>
            {
                Some(arguments)
            }
            _ => None,
        }
    }

    /// The components of the collection `term`: the terms its concatenations fold, left to right.
    /// Iterative, so a long collection needs no deep stack.
    fn components<'a>(&self, term: &'a Pattern) -> Vec<&'a Pattern> {
        let mut components = Vec::new();
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            match self.concatenation(term) {
                Some(arguments) => pending.extend(arguments.iter().rev()),
                None => components.push(term),
            }
        }
        components
    }

    /// [`Self::components`], taking `term` apart.
    fn take_components(&self, term: Pattern) -> Vec<Pattern> {
        let mut components = Vec::new();
        let mut pending = vec![term];
        while let Some(mut term) = pending.pop() {
            if self.concatenation(&term).is_some()
                && let Pattern::Application { arguments, .. } = &mut term
                && let (Some(right), Some(left)) = (arguments.pop(), arguments.pop())
            {
                pending.push(right);
                pending.push(left);
                continue;
            }
            components.push(term);
        }
        components
    }

    /// The collection of `components`, right-nested by the concatenation; one component is
    /// itself. `components` is not empty.
    fn rebuild(&self, components: Vec<Pattern>) -> Pattern {
        let mut components = components.into_iter().rev();
        let last = components.next().unwrap_or_else(|| Pattern::Application {
            symbol: k_rust::kore::ast::Symbol {
                name: self.collection.unit.clone(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        });
        components.fold(last, |rest, component| Pattern::Application {
            symbol: k_rust::kore::ast::Symbol {
                name: self.collection.concat.clone(),
                sort_parameters: Vec::new(),
            },
            arguments: vec![component, rest],
        })
    }
}

/// Whether `term` has the sort `sort`, whose parameterless symbols are `heads`: an application
/// of one of them, an injection `inj{_, sort}`, a variable of the sort, or `\top` of the sort.
fn has_sort(term: &Pattern, sort: &Sort, heads: &[String]) -> bool {
    match term {
        Pattern::Application { symbol, .. } | Pattern::AssociativeApplication { symbol, .. } => {
            match symbol.name.as_str() {
                "inj" => symbol.sort_parameters.len() == 2 && symbol.sort_parameters[1] == *sort,
                name => symbol.sort_parameters.is_empty() && heads.iter().any(|head| head == name),
            }
        }
        Pattern::Variable(variable) => variable.sort == *sort,
        Pattern::Top { sort: top } => top == sort,
        _ => false,
    }
}

/// One position of an end that a cell projection leaves uncompared.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct UnobservedPosition {
    /// KORE argument indices from the end's top application to the position, where a `*` cell
    /// of [`Self::through`] passes from its collection to each instance. First, so that
    /// positions order by path.
    pub path: Vec<u32>,
    /// The KORE symbol of the application each step of [`Self::path`] leaves: `symbols[0]` is
    /// the top cell's (`Lbl'-LT-'generatedTop'-GT-'`), `symbols[i]` the application at
    /// `path[..i]` (in each instance, below a `*` cell of [`Self::through`]).
    pub symbols: Vec<String>,
    /// The K name of the cell at the position, for reports (`w` for `<w>`).
    pub cell: String,
    /// The KORE sort of the position, the sort of its `\top` placeholder: the cell sort for a cell
    /// of multiplicity `1` or `?`, the collection sort for a `*` cell.
    pub sort: Sort,
    /// The KORE symbols `definition.kore` declares without sort parameters and with
    /// [`Self::sort`] as their result sort, sorted: the cell's own symbol (and for a `?` cell its
    /// unit), or the collection sort's constructors and functions for a `*` cell. A subterm at the
    /// position has the position's sort when it is an application of one of them, an injection
    /// `inj{_, sort}` into the sort, a variable of the sort, or `\top` of the sort (a placeholder
    /// already there); only such a subterm is replaced.
    pub heads: Vec<String>,
    /// The `*` cells the path passes through, outermost first; empty for a position whose
    /// enclosing cells all have multiplicity `1` or `?`.
    pub through: Vec<Through>,
}

impl UnobservedPosition {
    fn placeholder(&self) -> Pattern {
        Pattern::Top {
            sort: self.sort.clone(),
        }
    }

    /// The number of path steps that reach the collection `through[next]`, or the position when
    /// the path passes through no further collection.
    fn stop(&self, next: usize) -> usize {
        self.through
            .get(next)
            .and_then(|through| usize::try_from(through.at).ok())
            .unwrap_or(self.path.len())
    }

    /// The subterm `path[from..to]` leads to from `term`, through applications of
    /// `symbols[from..to]` that have the argument the path names.
    fn walk<'a>(&self, term: &'a Pattern, from: usize, to: usize) -> Option<&'a Pattern> {
        self.path
            .get(from..to)?
            .iter()
            .zip(self.symbols.get(from..to)?)
            .try_fold(term, |term, (step, symbol)| match term {
                Pattern::Application {
                    symbol: head,
                    arguments,
                } if head.name == *symbol => arguments.get(usize::try_from(*step).ok()?),
                _ => None,
            })
    }

    /// [`Self::walk`], mutably.
    fn walk_mut<'a>(
        &self,
        term: &'a mut Pattern,
        from: usize,
        to: usize,
    ) -> Option<&'a mut Pattern> {
        let path = self.path.get(from..to)?;
        let symbols = self.symbols.get(from..to)?;
        path.iter()
            .zip(symbols)
            .try_fold(term, |term, (step, symbol)| match term {
                Pattern::Application {
                    symbol: head,
                    arguments,
                } if head.name == *symbol => arguments.get_mut(usize::try_from(*step).ok()?),
                _ => None,
            })
    }

    /// Whether `term` has the position's sort under the baseline's declarations
    /// ([`Self::heads`]). Any other pattern is not the position's content: the end has another
    /// shape there.
    fn has_sort(&self, term: &Pattern) -> bool {
        has_sort(term, &self.sort, &self.heads)
    }

    /// Whether [`Self::project_from`] changes `term`, the subterm reached after `from` steps of
    /// the path and `next` collections of [`Self::through`]: some subterm at the position it
    /// reaches is not yet the placeholder, or some unordered collection it passes through is not
    /// sorted.
    fn changes(&self, term: &Pattern, from: usize, next: usize) -> bool {
        let to = self.stop(next);
        let Some(at) = self.walk(term, from, to) else {
            return false;
        };
        let Some(through) = self.through.get(next) else {
            return self.has_sort(at) && *at != self.placeholder();
        };
        if !through.has_sort(at) {
            return false;
        }
        let components = through.components(at);
        components.iter().any(|component| {
            through
                .instance(component)
                .is_some_and(|instance| self.changes(instance, to, next + 1))
        }) || (through.collection.kind.unordered()
            && !components.windows(2).all(|pair| pair[0] <= pair[1]))
    }

    /// Projects `term`, the subterm reached after `from` steps of the path and `next`
    /// collections of [`Self::through`]: walks the path to the position and replaces the subterm
    /// there by `\top` of its sort, in each instance of each collection on the way, and sorts the
    /// components of each unordered collection it passes through. Leaves alone a subterm where
    /// the walk does not reach the position (another symbol on the path, a missing argument, a
    /// subterm without the sort of the position or of the collection, a component of a
    /// collection that is not an element).
    fn project_from(&self, term: &mut Pattern, from: usize, next: usize) {
        let to = self.stop(next);
        let Some(at) = self.walk_mut(term, from, to) else {
            return;
        };
        let Some(through) = self.through.get(next) else {
            if self.has_sort(at) {
                *at = self.placeholder();
            }
            return;
        };
        if !through.has_sort(at) {
            return;
        }
        let whole = std::mem::replace(
            at,
            Pattern::Top {
                sort: through.sort.clone(),
            },
        );
        let mut components = through.take_components(whole);
        for component in &mut components {
            if let Some(instance) = through.instance_mut(component) {
                self.project_from(instance, to, next + 1);
            }
        }
        if through.collection.kind.unordered() {
            components.sort();
        }
        *at = through.rebuild(components);
    }
}

/// The ends' configurations without the content of their uncompared cells: the state projection
/// [`crate::StateProjection::Cells`].
///
/// Two ends have equal projections exactly when they are equal outside the `<generatedCounter>`
/// content and outside the content of the uncompared positions, each unordered collection on a
/// position's path read as the multiset of its components: where both ends have a position,
/// both placeholders are `\top` of its sort and the rest is compared; where neither has it,
/// nothing is replaced; where one has it and the other does not, they differ at or above the
/// position (a symbol on the path, an arity, whether the subterm at the path has the position's
/// sort, or a collection's components), and one projection holds `\top` of the sort where the
/// other holds a subterm that is not that placeholder. Two collections of a Map or a Set with
/// equal multisets of projected components project to one term, since the components are sorted;
/// a Map's components keep their keys, so that is the map from each key to its projected
/// instance; a List's are compared in order. So a slot projecting them distinguishes only by a
/// difference some compared cell shows (an instance's presence, key or position included), never
/// by a difference in an uncompared one. The projection is defined on every pattern, which the
/// one-sided kill needs ([`crate::OneSided`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellProjection {
    positions: Vec<UnobservedPosition>,
}

impl CellProjection {
    /// Requires at least one position, each path nonempty with one symbol per step, each
    /// collection the path passes through reached after at least one step and before the last,
    /// in path order, and the paths sorted and prefix-free (as term paths are), so that no
    /// position lies inside another.
    pub fn new(positions: Vec<UnobservedPosition>) -> Result<Self, OracleFailure> {
        let invalid = |detail: &str| {
            Err(OracleFailure::new(
                OracleFailureKind::InvalidDeclaration,
                detail,
            ))
        };
        if positions.is_empty() {
            return invalid("a cell projection leaves out at least one position");
        }
        if positions.iter().any(|position| position.path.is_empty()) {
            return invalid("an uncompared position is below the top cell (a nonempty path)");
        }
        if positions
            .iter()
            .any(|position| position.symbols.len() != position.path.len())
        {
            return invalid("an uncompared position names one symbol per step of its path");
        }
        let steps_in_order = |position: &UnobservedPosition| {
            let mut previous = 0;
            position.through.iter().all(|through| {
                let at = usize::try_from(through.at).unwrap_or(usize::MAX);
                let ordered = previous < at && at < position.path.len();
                previous = at;
                ordered
            })
        };
        if !positions.iter().all(steps_in_order) {
            return invalid(
                "a collection on an uncompared position's path is reached after a step of the \
                 path and before its last, in path order",
            );
        }
        let ordered = positions
            .windows(2)
            .all(|pair| pair[0].path < pair[1].path && !pair[1].path.starts_with(&pair[0].path));
        if !ordered {
            return invalid("uncompared positions must be sorted and prefix-free");
        }
        Ok(Self { positions })
    }

    /// The uncompared positions, sorted by path.
    #[must_use]
    pub fn positions(&self) -> &[UnobservedPosition] {
        &self.positions
    }

    /// `end` with its `<generatedCounter>` content erased ([`counter_erased`], as the whole-term
    /// projection erases it), then, at each position the walk reaches (in each instance of each
    /// collection on its path), the subterm replaced by `\top` of the position's sort, and the
    /// components of each unordered collection on its path sorted. A position `end` does not have
    /// (another symbol on the path, a missing argument, a subterm there that does not have the
    /// position's sort, a component of a collection that is not an element) is left as it is.
    /// Total.
    ///
    /// The walk replaces only a subterm of the position's sort, so `\top{S}()` stands where a
    /// pattern of sort `S` stood and the projection is well-sorted wherever the end is; it is
    /// ground, and it reads as "any value of `S`", which is what an uncompared position is; no sort
    /// has a canonical constant to use instead.
    #[must_use]
    pub fn project<'a>(&self, end: &'a Pattern) -> Cow<'a, Pattern> {
        let mut projected = counter_erased(end);
        for position in &self.positions {
            if position.changes(&projected, 0, 0) {
                position.project_from(projected.to_mut(), 0, 0);
            }
        }
        projected
    }
}

/// One cell of a compiled configuration, placed in the tree of `<generatedTop>`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LaidOutCell {
    /// The cell's K name, `w` for `<w>`.
    pub name: String,
    /// The KORE symbol of the cell's application.
    pub kore_symbol: String,
    pub multiplicity: CellMultiplicity,
    /// Whether the declaration writes `unobservable`: no use of the definition may observe the
    /// cell's content.
    pub unobservable: bool,
    /// The parent's index in [`CellLayout::cells`]; `None` for the top cell.
    pub parent: Option<usize>,
    /// The argument of the parent's application that holds the cell (`0` for the top cell).
    pub index: u32,
    /// The KORE sort of that argument: the cell sort, or for a `*` cell the collection sort.
    pub sort: Sort,
    /// The KORE symbols `definition.kore` declares without sort parameters and with [`Self::sort`]
    /// as their result sort, sorted ([`UnobservedPosition::heads`]).
    pub heads: Vec<String>,
    /// For a `*` cell, how its collection holds its instances; `None` for any other cell, and
    /// for a `*` cell whose collection sort `definition.kore` declares no element, concatenation
    /// and unit for (no position below it can then be reached).
    pub collection: Option<Collection>,
    /// For a `*` cell of a Map, the index in [`CellLayout::cells`] of its key: the child whose
    /// sort is the Map element's first argument sort, which the element holds beside the
    /// instance.
    pub key: Option<usize>,
}

/// Where a compiled configuration's cells sit in its KORE terms: the cells of the tree of
/// `<generatedTop>`, in configuration preorder (a parent before its children, children in
/// argument order), the top cell first.
///
/// Read from the compiled execution definition's cell productions (k-rust `declared_cells`),
/// each checked against the symbol `definition.kore` declares. The tree is the top cell and,
/// recursively, the cells an argument of a cell in it holds; only those holders count. A cell no
/// cell of the tree holds (a `cell` production written outside any configuration, which may hold
/// cells of the configuration) has no position in any end and is not in the layout; such a cell
/// declared `unobservable` is refused
/// ([`CellLayoutRefusal::UnobservableCellOutsideConfiguration`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellLayout {
    cells: Vec<LaidOutCell>,
}

impl CellLayout {
    /// The layout of `compiled`'s configuration, in its main module.
    ///
    /// Refused ([`CellLayoutRefusal::Layout`]) when the configuration's cells cannot be placed:
    /// no top cell, the top cell held by a cell of its tree, a cell held at two arguments of cells
    /// of the tree, a cell of the tree whose KORE symbol is not declared with its production's
    /// argument sorts. None of these happens for a configuration compilation generated, since
    /// expansion admits no `cell` production of a declared cell's sort beside the generated one;
    /// the check keeps the projection from resting on an ordering convention. Refused
    /// ([`CellLayoutRefusal::UnobservableCellOutsideConfiguration`]) when a cell outside the tree
    /// is declared unobservable.
    pub fn of(compiled: &ValidatedDefinition) -> Result<Self, CellLayoutRefusal> {
        let kore = parse_definition(&compiled.artifacts().definition_kore).map_err(|error| {
            CellLayoutRefusal::Layout {
                cell: None,
                detail: format!("definition.kore: {error}"),
            }
        })?;
        Self::of_parsed(compiled, &kore)
    }

    /// [`Self::of`] with `compiled`'s `definition.kore` already parsed as `kore`, for a caller
    /// that parses it anyway.
    pub fn of_parsed(
        compiled: &ValidatedDefinition,
        kore: &KoreDefinition,
    ) -> Result<Self, CellLayoutRefusal> {
        let layout = |cell: Option<&str>, detail: String| CellLayoutRefusal::Layout {
            cell: cell.map(str::to_owned),
            detail,
        };
        let resolved = ResolvedDefinition::resolve(&compiled.artifacts().execution_definition)
            .map_err(|error| layout(None, format!("the compiled definition: {error}")))?;
        let declared = declared_cells(&resolved, resolved.main_module_id());
        let mut signatures = BTreeMap::new();
        // The symbols without sort parameters of each result sort, sorted.
        let mut heads = BTreeMap::<&Sort, BTreeSet<&str>>::new();
        // The collection symbols of each result sort, by hook (`MAP.element`, ...).
        let mut hooked = BTreeMap::<&Sort, Vec<(&str, &str, &[Sort])>>::new();
        for module in &kore.modules {
            for sentence in &module.sentences {
                if let Sentence::SymbolDeclaration {
                    symbol,
                    argument_sorts,
                    result_sort,
                    attributes,
                    ..
                } = sentence
                {
                    signatures.insert(symbol.name.as_str(), (argument_sorts, result_sort));
                    if symbol.sort_parameters.is_empty() {
                        heads
                            .entry(result_sort)
                            .or_default()
                            .insert(symbol.name.as_str());
                        if let Ok(Some(hook)) = attributes.string(KoreAttribute::Hook) {
                            hooked.entry(result_sort).or_default().push((
                                hook,
                                symbol.name.as_str(),
                                argument_sorts,
                            ));
                        }
                    }
                }
            }
        }

        let Some(root) = declared
            .iter()
            .position(|cell| cell.kore_symbol == GENERATED_TOP)
        else {
            return Err(layout(None, "the configuration has no top cell".to_owned()));
        };
        // The cells `parent` holds, each with the argument that holds it.
        let held_by = |parent: usize| {
            let mut held = Vec::new();
            for (index, sort) in declared[parent].child_kore_sorts.iter().enumerate() {
                for (child, candidate) in declared.iter().enumerate() {
                    if candidate.position_kore_sort == *sort {
                        held.push((child, index));
                    }
                }
            }
            held
        };
        // The tree: the top cell and every cell a cell of the tree holds. A cell production
        // outside it may hold cells of the configuration too, and does not count as their holder.
        let mut in_tree = vec![false; declared.len()];
        in_tree[root] = true;
        let mut reach = vec![root];
        while let Some(parent) = reach.pop() {
            for (child, _) in held_by(parent) {
                if !in_tree[child] {
                    in_tree[child] = true;
                    reach.push(child);
                }
            }
        }
        // Each cell's holders among the cells of the tree, and where.
        let mut holders = vec![Vec::new(); declared.len()];
        for parent in (0..declared.len()).filter(|&parent| in_tree[parent]) {
            for (child, index) in held_by(parent) {
                holders[child].push((parent, index));
            }
        }
        if !holders[root].is_empty() {
            return Err(layout(
                Some(&declared[root].name),
                "the top cell is held by another cell".to_owned(),
            ));
        }

        let mut cells = Vec::new();
        // The key sort of each laid-out cell that is a Map's `*` cell, by layout index.
        let mut keys = Vec::new();
        // (declared index, parent's layout index, argument index), visited in preorder.
        let mut pending = vec![(root, None, 0_u32)];
        while let Some((at, parent, index)) = pending.pop() {
            let cell = &declared[at];
            let cell_sort = match signatures.get(cell.kore_symbol.as_str()) {
                Some((arguments, result)) if **arguments == cell.child_kore_sorts => *result,
                Some((arguments, _)) => {
                    return Err(layout(
                        Some(&cell.name),
                        format!(
                            "{} takes the arguments ({}) in definition.kore, and its production \
                             the arguments ({})",
                            cell.kore_symbol,
                            sorts(arguments),
                            sorts(&cell.child_kore_sorts)
                        ),
                    ));
                }
                None => {
                    return Err(layout(
                        Some(&cell.name),
                        format!("{} is not declared in definition.kore", cell.kore_symbol),
                    ));
                }
            };
            let collection = (cell.multiplicity == CellMultiplicity::Star)
                .then(|| {
                    collection(
                        hooked
                            .get(&cell.position_kore_sort)
                            .map_or(&[][..], Vec::as_slice),
                        cell_sort,
                    )
                })
                .flatten();
            let here = cells.len();
            cells.push(LaidOutCell {
                name: cell.name.clone(),
                kore_symbol: cell.kore_symbol.clone(),
                multiplicity: cell.multiplicity,
                unobservable: cell.unobservable,
                parent,
                index,
                sort: cell.position_kore_sort.clone(),
                heads: heads
                    .get(&cell.position_kore_sort)
                    .into_iter()
                    .flatten()
                    .map(|&head| head.to_owned())
                    .collect(),
                collection: collection
                    .as_ref()
                    .map(|(collection, _)| collection.clone()),
                key: None,
            });
            keys.push(collection.and_then(|(_, key)| key));
            let mut children = Vec::new();
            for (child, held) in holders.iter().enumerate() {
                let here_held = held
                    .iter()
                    .filter(|(holder, _)| *holder == at)
                    .map(|(_, index)| *index)
                    .collect::<Vec<_>>();
                if here_held.is_empty() {
                    continue;
                }
                // A cycle in the tree also shows here: its first cell is held by the cell before
                // it on the cycle and by its parent, or it is the top cell.
                if held.len() != 1 {
                    return Err(layout(
                        Some(&declared[child].name),
                        format!(
                            "the cell is held at {} arguments of cells of the configuration",
                            held.len()
                        ),
                    ));
                }
                let index = u32::try_from(here_held[0]).map_err(|_| {
                    layout(
                        Some(&declared[child].name),
                        "an argument index beyond u32".to_owned(),
                    )
                })?;
                children.push((child, Some(here), index));
            }
            // Popped in argument order.
            children.sort_by_key(|&(_, _, index)| std::cmp::Reverse(index));
            pending.extend(children);
        }
        // A Map's key is the child of its `*` cell at the key sort.
        for (at, key) in keys.into_iter().enumerate() {
            if let Some(key) = key {
                cells[at].key = (0..cells.len())
                    .find(|&child| cells[child].parent == Some(at) && cells[child].sort == *key);
            }
        }
        // A declaration the projection would silently ignore is refused: an unobservable cell
        // outside the top cell's tree has no position to leave out.
        if let Some(detached) = declared
            .iter()
            .zip(&in_tree)
            .find(|&(cell, &placed)| cell.unobservable && !placed)
        {
            return Err(CellLayoutRefusal::UnobservableCellOutsideConfiguration {
                cell: detached.0.name.clone(),
            });
        }
        Ok(Self { cells })
    }

    /// The cells, in configuration preorder, the top cell first.
    #[must_use]
    pub fn cells(&self) -> &[LaidOutCell] {
        &self.cells
    }

    /// The index of the cell named `name`.
    #[must_use]
    pub fn cell(&self, name: &str) -> Option<usize> {
        self.cells.iter().position(|cell| cell.name == name)
    }

    /// The strict ancestors of `cell`, nearest first.
    pub fn ancestors(&self, cell: usize) -> impl Iterator<Item = usize> + '_ {
        std::iter::successors(self.cells[cell].parent, |&at| self.cells[at].parent)
    }

    /// The key of a Map that `cell` is or lies inside, with that Map's `*` cell: `(key, cell)`.
    #[must_use]
    pub fn map_key(&self, cell: usize) -> Option<(usize, usize)> {
        std::iter::once(cell)
            .chain(self.ancestors(cell))
            .find_map(|at| {
                let parent = self.cells[at].parent?;
                (self.cells[parent].key == Some(at)).then_some((at, parent))
            })
    }

    /// The position of `cell`: its argument path from the top cell, passing each `*` cell on the
    /// way from its collection to each instance ([`UnobservedPosition::through`]).
    ///
    /// Refused ([`CellLayoutRefusal::MapKeyLeftOut`]) when `cell` is or lies inside the key of a
    /// Map, and ([`CellLayoutRefusal::Layout`]) for the top cell, whose position is the whole end,
    /// and below a `*` cell whose collection sort declares no element, concatenation and unit.
    pub fn position(&self, cell: usize) -> Result<UnobservedPosition, CellLayoutRefusal> {
        let layout = |detail: &str| CellLayoutRefusal::Layout {
            cell: Some(self.cells[cell].name.clone()),
            detail: detail.to_owned(),
        };
        if self.cells[cell].parent.is_none() {
            return Err(layout("the top cell's position is the whole end"));
        }
        if let Some((key, collection)) = self.map_key(cell) {
            return Err(CellLayoutRefusal::MapKeyLeftOut {
                cell: self.cells[cell].name.clone(),
                key: self.cells[key].name.clone(),
                collection: self.cells[collection].name.clone(),
            });
        }
        let mut chain = std::iter::once(cell)
            .chain(self.ancestors(cell))
            .collect::<Vec<_>>();
        chain.reverse();
        // chain[0] is the top cell, and chain[i] is reached after i steps of the path.
        let mut through = Vec::new();
        for (at, &holder) in chain.iter().enumerate().take(chain.len() - 1).skip(1) {
            let held = &self.cells[holder];
            if held.multiplicity != CellMultiplicity::Star {
                continue;
            }
            let collection = held.collection.clone().ok_or_else(|| {
                layout(&format!(
                    "the collection sort {} of the * cell <{}> declares no element, \
                     concatenation and unit",
                    held.sort, held.name
                ))
            })?;
            through.push(Through {
                at: u32::try_from(at).map_err(|_| layout("a path beyond u32 steps"))?,
                cell: held.name.clone(),
                sort: held.sort.clone(),
                heads: held.heads.clone(),
                collection,
            });
        }
        Ok(UnobservedPosition {
            path: chain[1..].iter().map(|&at| self.cells[at].index).collect(),
            symbols: chain[..chain.len() - 1]
                .iter()
                .map(|&at| self.cells[at].kore_symbol.clone())
                .collect(),
            cell: self.cells[cell].name.clone(),
            sort: self.cells[cell].sort.clone(),
            heads: self.cells[cell].heads.clone(),
            through,
        })
    }

    /// The cells declared unobservable that no unobservable cell encloses (a cell under an
    /// unobservable cell is left out with it), in configuration preorder.
    #[must_use]
    pub fn maximal_unobservable(&self) -> Vec<usize> {
        (0..self.cells.len())
            .filter(|&at| {
                self.cells[at].unobservable
                    && !self
                        .ancestors(at)
                        .any(|ancestor| self.cells[ancestor].unobservable)
            })
            .collect()
    }

    /// The projection that leaves out every unobservable cell; `None` when the configuration
    /// declares none, so that a slot then compares the whole term.
    ///
    /// Refused ([`CellLayoutRefusal::MapKeyLeftOut`]) when an unobservable cell no unobservable
    /// cell encloses is or lies inside the key of a Map ([`Self::position`]).
    pub fn unobservable_projection(&self) -> Result<Option<CellProjection>, CellLayoutRefusal> {
        let maximal = self.maximal_unobservable();
        if maximal.is_empty() {
            return Ok(None);
        }
        self.projection(&maximal).map(Some)
    }

    /// The projection that leaves out the cells `left_out`, no one inside another; refused as
    /// [`Self::position`] refuses one of them.
    pub fn projection(&self, left_out: &[usize]) -> Result<CellProjection, CellLayoutRefusal> {
        let mut positions = left_out
            .iter()
            .map(|&at| self.position(at))
            .collect::<Result<Vec<_>, _>>()?;
        positions.sort();
        CellProjection::new(positions).map_err(|failure| CellLayoutRefusal::Layout {
            cell: None,
            detail: failure.to_string(),
        })
    }
}

/// The collection a `*` cell whose application has the sort `cell_sort` sits in, read from the
/// hooked symbols of its collection sort, `(hook, symbol, argument sorts)`, with the sort of a
/// Map's key; `None` when they declare no element holding the instance, concatenation and unit
/// of one kind.
fn collection<'k>(
    hooked: &[(&str, &str, &'k [Sort])],
    cell_sort: &Sort,
) -> Option<(Collection, Option<&'k Sort>)> {
    let find = |suffix: &str| {
        hooked.iter().find_map(|&(hook, symbol, arguments)| {
            let (kind, operation) = hook.split_once('.')?;
            let kind = match kind {
                "MAP" => CollectionKind::Map,
                "SET" => CollectionKind::Set,
                "LIST" => CollectionKind::List,
                _ => return None,
            };
            (operation == suffix).then_some((kind, symbol, arguments))
        })
    };
    let (kind, element, arguments) = find("element")?;
    let (concat_kind, concat, _) = find("concat")?;
    let (unit_kind, unit, _) = find("unit")?;
    if concat_kind != kind || unit_kind != kind {
        return None;
    }
    let instance = arguments.iter().rposition(|sort| sort == cell_sort)?;
    let key = match (kind, arguments) {
        (CollectionKind::Map, [key, _]) if instance == 1 => Some(key),
        (CollectionKind::Map, _) => return None,
        (_, [_]) => None,
        _ => return None,
    };
    Some((
        Collection {
            kind,
            element: element.to_owned(),
            instance: u32::try_from(instance).ok()?,
            concat: concat.to_owned(),
            unit: unit.to_owned(),
        },
        key,
    ))
}

fn sorts(sorts: &[Sort]) -> String {
    sorts
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

/// Why a cell projection cannot be built for a configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CellLayoutRefusal {
    /// The configuration's cells cannot be placed in its KORE terms (reason `cell-layout`).
    /// Never for a configuration compilation generated.
    Layout {
        cell: Option<String>,
        detail: String,
    },
    /// A `cell` production no configuration places in the top cell's tree is declared
    /// unobservable: no end has its position, so the declaration would leave nothing out (reason
    /// `unobservable-cell-outside-configuration`). `cell` is the production's cell name as k-rust
    /// reads it: its `cellName`, or its label without the angle brackets of a `<name>` label.
    UnobservableCellOutsideConfiguration { cell: String },
    /// The cell left out is or lies inside `key`, the key by which the Map's `*` cell
    /// `collection` holds its instances (reason `map-key-left-out`): each element holds the key as
    /// its first argument beside the instance, and the projection leaves out positions of the
    /// instance only, so the content left out would still be compared in the element's key.
    MapKeyLeftOut {
        cell: String,
        key: String,
        collection: String,
    },
}

impl CellLayoutRefusal {
    /// The refusal's reason, a stable name.
    #[must_use]
    pub const fn reason(&self) -> &'static str {
        match self {
            Self::Layout { .. } => "cell-layout",
            Self::UnobservableCellOutsideConfiguration { .. } => {
                "unobservable-cell-outside-configuration"
            }
            Self::MapKeyLeftOut { .. } => "map-key-left-out",
        }
    }
}

impl fmt::Display for CellLayoutRefusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Layout { cell, detail } => {
                write!(formatter, "the configuration's cells cannot be placed")?;
                if let Some(cell) = cell {
                    write!(formatter, " at <{cell}>")?;
                }
                write!(
                    formatter,
                    ": {detail}; k-rust's cell reader and its compilation disagree, so report \
                     the definition as a k-rust defect"
                )
            }
            Self::UnobservableCellOutsideConfiguration { cell } => write!(
                formatter,
                "the unobservable cell production `{cell}` is placed by no configuration, so no \
                 end has its position; declare the cell in a configuration instead of writing \
                 its production, or drop `unobservable`"
            ),
            Self::MapKeyLeftOut {
                cell,
                key,
                collection,
            } => {
                if cell == key {
                    write!(
                        formatter,
                        "the cell <{cell}> is left out, but it is the key"
                    )?;
                } else {
                    write!(
                        formatter,
                        "the cell <{cell}> is left out, but it lies inside <{key}>, the key"
                    )?;
                }
                write!(
                    formatter,
                    " by which the Map cell <{collection}> holds its instances: each element holds \
                     the key as its first argument beside the instance, so its content would still \
                     be compared there, and the projection cannot leave <{cell}> out; drop \
                     `unobservable` from <{cell}>, or compare no cell inside <{collection}>, so \
                     that it is left out whole: mark <{collection}> unobservable, or narrow the \
                     compared cells to cells outside it"
                )
            }
        }
    }
}

impl std::error::Error for CellLayoutRefusal {}
