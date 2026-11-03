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
//! Below a `?` or `*` cell a child's position varies between ends (the optional cell may be
//! absent; a collection's element count and order vary), so no index list names it, and a
//! projection there is refused ([`CellLayoutRefusal::UnobservableCellPosition`]). A `?` or `*`
//! cell's own position is fixed: the projection then leaves out the whole optional cell or
//! collection.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use k_rust::backend::counter_erased;
use k_rust::definition::ResolvedDefinition;
use k_rust::definition::configuration::{CellMultiplicity, declared_cells};
use k_rust::kore::ast::{Definition as KoreDefinition, Pattern, Sentence, Sort};
use k_rust::kore::parser::parse_definition;
use kink_native::ValidatedDefinition;

use crate::OracleFailureKind;
use crate::oracle::OracleFailure;

/// The KORE symbol of a compiled configuration's top cell, the head of every end.
const GENERATED_TOP: &str = "Lbl'-LT-'generatedTop'-GT-'";

/// One position of an end that a cell projection leaves uncompared.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct UnobservedPosition {
    /// KORE argument indices from the end's top application to the position. First, so that
    /// positions order by path.
    pub path: Vec<u32>,
    /// The KORE symbol each strict prefix of [`Self::path`] must reach: `symbols[0]` is the top
    /// cell's (`Lbl'-LT-'generatedTop'-GT-'`), `symbols[i]` the application at `path[..i]`.
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
}

impl UnobservedPosition {
    /// The subterm of `term` at this position, when the walk from `term` reaches it through
    /// applications of [`Self::symbols`] that have the argument the path names, and the subterm
    /// there has the position's sort ([`Self::heads`]).
    fn reached<'a>(&self, term: &'a Pattern) -> Option<&'a Pattern> {
        let at = self
            .path
            .iter()
            .zip(&self.symbols)
            .try_fold(term, |term, (step, symbol)| match term {
                Pattern::Application {
                    symbol: head,
                    arguments,
                } if head.name == *symbol => arguments.get(usize::try_from(*step).ok()?),
                _ => None,
            })?;
        self.has_sort(at).then_some(at)
    }

    /// [`Self::reached`], mutably.
    fn reached_mut<'a>(&self, term: &'a mut Pattern) -> Option<&'a mut Pattern> {
        let at = self
            .path
            .iter()
            .zip(&self.symbols)
            .try_fold(term, |term, (step, symbol)| match term {
                Pattern::Application {
                    symbol: head,
                    arguments,
                } if head.name == *symbol => arguments.get_mut(usize::try_from(*step).ok()?),
                _ => None,
            })?;
        self.has_sort(at).then_some(at)
    }

    /// Whether `term`, the subterm at the position, has the position's sort under the baseline's
    /// declarations ([`Self::heads`]). Any other pattern is not the position's content: the end has
    /// another shape there.
    fn has_sort(&self, term: &Pattern) -> bool {
        match term {
            Pattern::Application { symbol, .. }
            | Pattern::AssociativeApplication { symbol, .. } => match symbol.name.as_str() {
                "inj" => {
                    symbol.sort_parameters.len() == 2 && symbol.sort_parameters[1] == self.sort
                }
                name => {
                    symbol.sort_parameters.is_empty() && self.heads.iter().any(|head| head == name)
                }
            },
            Pattern::Variable(variable) => variable.sort == self.sort,
            Pattern::Top { sort } => *sort == self.sort,
            _ => false,
        }
    }
}

/// The ends' configurations without the content of their uncompared cells: the state projection
/// [`crate::StateProjection::Cells`].
///
/// Two ends have equal projections exactly when they are equal outside the `<generatedCounter>`
/// content and outside the content of the uncompared positions: where both ends have a position,
/// both placeholders are `\top` of its sort and the rest is compared; where neither has it,
/// nothing is replaced; where one has it and the other does not, they differ at or above the
/// position (a symbol on the path, an arity, or whether the subterm at the path has the
/// position's sort), and one projection holds `\top` of the sort where the other holds a
/// subterm that is not that placeholder. So a slot projecting
/// them distinguishes only by a difference some compared cell shows, never by a difference in an
/// uncompared one. The projection is defined on every pattern, which the one-sided kill needs
/// ([`crate::OneSided`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellProjection {
    positions: Vec<UnobservedPosition>,
}

impl CellProjection {
    /// Requires at least one position, each path nonempty with one symbol per step, and the paths
    /// sorted and prefix-free (as term paths are), so that no position lies inside another.
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
    /// projection erases it), then, at each position the walk reaches, the subterm replaced by
    /// `\top` of the position's sort. A position `end` does not have (another symbol on the path,
    /// a missing argument, or a subterm there that does not have the position's sort) is left as
    /// it is. Total.
    ///
    /// The walk replaces only a subterm of the position's sort, so `\top{S}()` stands where a
    /// pattern of sort `S` stood and the projection is well-sorted wherever the end is; it is
    /// ground, and it reads as "any value of `S`", which is what an uncompared position is; no sort
    /// has a canonical constant to use instead.
    #[must_use]
    pub fn project<'a>(&self, end: &'a Pattern) -> Cow<'a, Pattern> {
        let mut projected = counter_erased(end);
        for position in &self.positions {
            let placeholder = Pattern::Top {
                sort: position.sort.clone(),
            };
            if position
                .reached(&projected)
                .is_some_and(|at| *at != placeholder)
                && let Some(at) = position.reached_mut(projected.to_mut())
            {
                *at = placeholder;
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
        for module in &kore.modules {
            for sentence in &module.sentences {
                if let Sentence::SymbolDeclaration {
                    symbol,
                    argument_sorts,
                    result_sort,
                    ..
                } = sentence
                {
                    signatures.insert(symbol.name.as_str(), argument_sorts);
                    if symbol.sort_parameters.is_empty() {
                        heads
                            .entry(result_sort)
                            .or_default()
                            .insert(symbol.name.as_str());
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
        // (declared index, parent's layout index, argument index), visited in preorder.
        let mut pending = vec![(root, None, 0_u32)];
        while let Some((at, parent, index)) = pending.pop() {
            let cell = &declared[at];
            match signatures.get(cell.kore_symbol.as_str()) {
                Some(arguments) if **arguments == cell.child_kore_sorts => {}
                Some(arguments) => {
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
            }
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
            });
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

    /// The outermost strict ancestor of `cell` whose multiplicity is `?` or `*`: `None` exactly
    /// when the cell's position is fixed.
    #[must_use]
    pub fn varying_ancestor(&self, cell: usize) -> Option<usize> {
        self.ancestors(cell)
            .filter(|&at| self.cells[at].multiplicity != CellMultiplicity::One)
            .last()
    }

    /// The position of `cell`, when it has a fixed one: every strict ancestor has multiplicity
    /// `1`, and the cell is not the top cell (whose position is the whole end).
    #[must_use]
    pub fn position(&self, cell: usize) -> Option<UnobservedPosition> {
        if self.varying_ancestor(cell).is_some() || self.cells[cell].parent.is_none() {
            return None;
        }
        let mut chain = std::iter::once(cell)
            .chain(self.ancestors(cell))
            .collect::<Vec<_>>();
        chain.reverse();
        // chain[0] is the top cell.
        Some(UnobservedPosition {
            path: chain[1..].iter().map(|&at| self.cells[at].index).collect(),
            symbols: chain[..chain.len() - 1]
                .iter()
                .map(|&at| self.cells[at].kore_symbol.clone())
                .collect(),
            cell: self.cells[cell].name.clone(),
            sort: self.cells[cell].sort.clone(),
            heads: self.cells[cell].heads.clone(),
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
    /// Refused ([`CellLayoutRefusal::UnobservableCellPosition`]) when an unobservable cell no
    /// unobservable cell encloses lies inside a `?` or `*` cell, naming the outermost such cell.
    pub fn unobservable_projection(&self) -> Result<Option<CellProjection>, CellLayoutRefusal> {
        let maximal = self.maximal_unobservable();
        if maximal.is_empty() {
            return Ok(None);
        }
        let mut positions = Vec::new();
        for at in maximal {
            let cell = &self.cells[at];
            if let Some(enclosing) = self.varying_ancestor(at) {
                return Err(CellLayoutRefusal::UnobservableCellPosition {
                    cell: cell.name.clone(),
                    enclosing: self.cells[enclosing].name.clone(),
                    multiplicity: self.cells[enclosing].multiplicity,
                });
            }
            positions.push(self.position(at).ok_or_else(|| CellLayoutRefusal::Layout {
                cell: Some(cell.name.clone()),
                detail: "the top cell cannot be unobservable".to_owned(),
            })?);
        }
        positions.sort();
        CellProjection::new(positions)
            .map(Some)
            .map_err(|failure| CellLayoutRefusal::Layout {
                cell: None,
                detail: failure.to_string(),
            })
    }
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
    /// An unobservable cell lies inside the `?` or `*` cell `enclosing`, so its position varies
    /// between ends (reason `unobservable-cell-position`).
    UnobservableCellPosition {
        cell: String,
        enclosing: String,
        multiplicity: CellMultiplicity,
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
            Self::UnobservableCellPosition { .. } => "unobservable-cell-position",
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
            Self::UnobservableCellPosition {
                cell,
                enclosing,
                multiplicity,
            } => {
                let multiplicity = match multiplicity {
                    CellMultiplicity::Optional => "?",
                    CellMultiplicity::Star => "*",
                    CellMultiplicity::One => "1",
                };
                write!(
                    formatter,
                    "the unobservable cell <{cell}> lies inside the {multiplicity} cell \
                     <{enclosing}>, so its position varies between ends; mark <{enclosing}> \
                     unobservable, or move <{cell}> out of it"
                )
            }
        }
    }
}

impl std::error::Error for CellLayoutRefusal {}
