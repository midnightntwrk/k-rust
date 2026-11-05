//! Views of result states: their cells, addressed by the Rust fields that declare them.

use std::fmt;
use std::sync::Arc;

use k_rust::kore::{ast::Pattern, walk};
use krs_ir::CellMultiplicity;

use crate::inputs::InputType;
use crate::values::{CellNode, Value, ValueError, ValueIndex};

/// One state of a result, as [`crate::Semantics::views`] reads it.
#[derive(Clone, Debug)]
pub enum View<'t> {
    /// `\bottom`: no configuration, as when a partial function was applied outside its domain.
    Bottom,
    /// A configuration and the constraint on it.
    State(StateView<'t>),
}

/// A configuration, or one group cell of it, whose cells are addressed by path: the Rust field
/// names from this view's root, joined by `.` (`"regs"`, `"cpu.regs"`).
///
/// A view borrows the result's term and decodes a cell only when asked.
#[derive(Clone, Debug)]
pub struct StateView<'t> {
    index: Arc<ValueIndex>,
    /// The child positions in the cell tree from the configuration to this view's root.
    scope: Vec<usize>,
    term: &'t Pattern,
    constraints: Arc<[&'t Pattern]>,
}

/// Why a cell path has no value in a view.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CellError {
    /// No cell has this path; `known` lists the paths below this view's root.
    Unknown {
        /// The path as written.
        path: String,
        /// Every cell path below the view's root.
        known: Vec<String>,
    },
    /// The path passes through an optional cell that the state does not hold.
    Absent {
        /// The path as written.
        path: String,
    },
    /// The cell is not of the kind the accessor reads.
    Kind {
        /// The path as written.
        path: String,
        /// What the accessor reads: `a leaf cell`, `a group cell`, `an optional cell`, or `a
        /// repeated cell`, or `a single cell` for a path through a repeated cell.
        expected: &'static str,
    },
    /// The state is not a configuration of the definition, or the cell's content is not a term
    /// of it.
    Decode(ValueError),
}

impl fmt::Display for CellError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unknown { path, known } => write!(
                formatter,
                "no cell has the path `{path}`; the cells are {}",
                known.join(", ")
            ),
            Self::Absent { path } => write!(formatter, "the state holds no cell `{path}`"),
            Self::Kind { path, expected } => write!(formatter, "`{path}` is not {expected}"),
            Self::Decode(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for CellError {}

impl From<ValueError> for CellError {
    fn from(error: ValueError) -> Self {
        Self::Decode(error)
    }
}

/// Read a result state: one view for each disjunct of a `\or`.
pub(crate) fn views<'t>(
    index: &Arc<ValueIndex>,
    state: &'t Pattern,
) -> Result<Vec<View<'t>>, ValueError> {
    let mut disjuncts = Vec::new();
    flatten_or(state, &mut disjuncts);
    disjuncts
        .into_iter()
        .map(|disjunct| view(index, disjunct))
        .collect()
}

fn flatten_or<'t>(pattern: &'t Pattern, output: &mut Vec<&'t Pattern>) {
    match pattern {
        Pattern::Or { arguments, .. } => {
            for argument in arguments {
                flatten_or(argument, output);
            }
        }
        _ => output.push(pattern),
    }
}

fn flatten_and<'t>(pattern: &'t Pattern, output: &mut Vec<&'t Pattern>) {
    match pattern {
        Pattern::And { arguments, .. } => {
            for argument in arguments {
                flatten_and(argument, output);
            }
        }
        _ => output.push(pattern),
    }
}

fn head(pattern: &Pattern) -> Option<&str> {
    match pattern {
        Pattern::Application { symbol, .. } | Pattern::AssociativeApplication { symbol, .. } => {
            Some(&symbol.name)
        }
        _ => None,
    }
}

fn view<'t>(index: &Arc<ValueIndex>, state: &'t Pattern) -> Result<View<'t>, ValueError> {
    if matches!(state, Pattern::Bottom { .. }) {
        return Ok(View::Bottom);
    }
    let mut conjuncts = Vec::new();
    flatten_and(state, &mut conjuncts);
    let (configurations, constraints): (Vec<_>, Vec<_>) = conjuncts
        .into_iter()
        .partition(|conjunct| head(conjunct) == Some(index.top_symbol()));
    let [configuration] = configurations.as_slice() else {
        return Err(ValueError::Malformed(format!(
            "a state holds one configuration, not {}",
            configurations.len()
        )));
    };
    Ok(View::State(StateView {
        index: index.clone(),
        scope: Vec::new(),
        term: configuration,
        constraints: constraints.into(),
    }))
}

/// Every cell application reachable from `parent`'s arguments without passing another cell, in
/// order: the cells a cell holds directly, through the collection that holds a repeated cell's
/// instances. A cell is a cell of `symbols`, the configuration's cell symbols
/// ([`cell_symbols`]): a leaf cell's content is a term, never cells of the configuration, so a
/// cell term it holds as a value (a `k::fragment!` result in the computation cell) is no cell
/// of the state.
pub(crate) fn cells_below<'t>(parent: &'t Pattern, symbols: &[&str]) -> Vec<&'t Pattern> {
    let mut found = Vec::new();
    let mut stack: Vec<&Pattern> = match parent {
        Pattern::Application { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => arguments.iter().rev().collect(),
        _ => Vec::new(),
    };
    while let Some(pattern) = stack.pop() {
        if head(pattern).is_some_and(|symbol| symbols.contains(&symbol)) {
            found.push(pattern);
            continue;
        }
        stack.extend(walk::children(pattern).into_iter().rev());
    }
    found
}

/// The KORE symbols of the cells of `nodes` and of every cell below them.
pub(crate) fn cell_symbols<'n>(nodes: &'n [CellNode], output: &mut Vec<&'n str>) {
    for node in nodes {
        output.push(&node.symbol);
        cell_symbols(&node.children, output);
    }
}

fn paths(nodes: &[CellNode], prefix: &str, output: &mut Vec<String>) {
    for node in nodes {
        let path = format!("{prefix}{}", node.field);
        paths(&node.children, &format!("{path}."), output);
        output.push(path);
    }
}

/// The paths of the leaf cells of `nodes`, in declaration order, below no repeated cell.
fn leaf_paths(nodes: &[CellNode], prefix: &str, output: &mut Vec<String>) {
    for node in nodes {
        if node.multiplicity == Some(CellMultiplicity::Star) {
            continue;
        }
        let path = format!("{prefix}{}", node.field);
        if node.children.is_empty() {
            output.push(path);
        } else {
            leaf_paths(&node.children, &format!("{path}."), output);
        }
    }
}

/// The paths of the repeated cells of `nodes`, in declaration order, below no other repeated
/// cell.
fn repeated_paths(nodes: &[CellNode], prefix: &str, output: &mut Vec<String>) {
    for node in nodes {
        let path = format!("{prefix}{}", node.field);
        if node.multiplicity == Some(CellMultiplicity::Star) {
            output.push(path);
        } else {
            repeated_paths(&node.children, &format!("{path}."), output);
        }
    }
}

/// A located cell: its node, the positions from the configuration, and its term in the state.
struct Located<'t, 'n> {
    node: &'n CellNode,
    scope: Vec<usize>,
    term: Option<&'t Pattern>,
}

impl<'t> StateView<'t> {
    /// The cells `parent` holds directly ([`cells_below`]) whose symbol is `symbol`.
    fn cells_of(&self, parent: &'t Pattern, symbol: &str) -> Vec<&'t Pattern> {
        let mut symbols = Vec::new();
        cell_symbols(self.index.cells(), &mut symbols);
        cells_below(parent, &symbols)
            .into_iter()
            .filter(|cell| head(cell) == Some(symbol))
            .collect()
    }

    fn root_nodes(&self) -> &[CellNode] {
        let mut nodes = self.index.cells();
        for position in &self.scope {
            nodes = &nodes[*position].children;
        }
        nodes
    }

    /// Follow `path` from this view's root. `term` is `None` past an absent optional cell;
    /// a repeated cell is accepted only as the last segment, and only when `repeated` is true.
    fn locate(&self, path: &str, repeated: bool) -> Result<Located<'t, '_>, CellError> {
        let unknown = || {
            let mut known = Vec::new();
            paths(self.root_nodes(), "", &mut known);
            known.sort();
            CellError::Unknown {
                path: path.to_owned(),
                known,
            }
        };
        let mut nodes = self.root_nodes();
        let mut scope = self.scope.clone();
        let mut term = Some(self.term);
        let segments = path.split('.').collect::<Vec<_>>();
        let mut located = None;
        for (index, segment) in segments.iter().enumerate() {
            let position = nodes
                .iter()
                .position(|node| node.field == *segment)
                .ok_or_else(unknown)?;
            let node = &nodes[position];
            scope.push(position);
            let last = index + 1 == segments.len();
            if node.multiplicity == Some(CellMultiplicity::Star) && !(last && repeated) {
                return Err(CellError::Kind {
                    path: path.to_owned(),
                    expected: "a single cell; read a repeated cell with `instances`",
                });
            }
            if !(last && repeated) {
                term = match term {
                    Some(parent) => {
                        let found = self.cells_of(parent, &node.symbol);
                        match found.as_slice() {
                            [] if node.multiplicity == Some(CellMultiplicity::Optional) => None,
                            [cell] => Some(*cell),
                            _ => {
                                return Err(CellError::Decode(ValueError::Malformed(format!(
                                    "the state holds {} cells `{segment}`, not one",
                                    found.len()
                                ))));
                            }
                        }
                    }
                    None => None,
                };
            }
            nodes = &node.children;
            located = Some(node);
        }
        Ok(Located {
            node: located.ok_or_else(unknown)?,
            scope,
            term,
        })
    }

    /// The content of the leaf cell at `path`.
    ///
    /// # Errors
    ///
    /// Returns a [`CellError`] for an unknown path, a group or repeated cell, a path through
    /// an absent optional cell, or content that is no term of the definition.
    pub fn value(&self, path: &str) -> Result<Value, CellError> {
        Ok(self.index.decode(self.content(path)?)?)
    }

    /// The content of the leaf cell at `path` as the state holds it, its injections and
    /// instances included: [`Self::value`] before it is decoded.
    ///
    /// # Errors
    ///
    /// As [`Self::value`], but for content that is no term of the definition.
    pub fn content(&self, path: &str) -> Result<&'t Pattern, CellError> {
        let located = self.locate(path, false)?;
        if !located.node.children.is_empty() {
            return Err(CellError::Kind {
                path: path.to_owned(),
                expected: "a leaf cell",
            });
        }
        let term = located.term.ok_or_else(|| CellError::Absent {
            path: path.to_owned(),
        })?;
        match term {
            Pattern::Application { arguments, .. } => match arguments.as_slice() {
                [content] => Ok(content),
                _ => Err(CellError::Decode(ValueError::Malformed(format!(
                    "{term} is not a leaf cell"
                )))),
            },
            _ => unreachable!("cells are found by their head"),
        }
    }

    /// The declared type of the leaf cell at `path`: its content sort and element types, the
    /// position its value's canonical document is written at ([`crate::encode()`]). A sort no
    /// KRS declaration names is the untyped position.
    ///
    /// # Errors
    ///
    /// Returns a [`CellError`] for an unknown path, a group cell, or a path through a repeated
    /// cell.
    pub fn cell_type(&self, path: &str) -> Result<InputType, CellError> {
        let located = self.locate(path, false)?;
        let Some((sort, arguments)) = &located.node.content else {
            return Err(CellError::Kind {
                path: path.to_owned(),
                expected: "a leaf cell",
            });
        };
        Ok(crate::inputs::input_type(&self.index, sort, arguments)
            .unwrap_or_else(InputType::untyped))
    }

    /// The paths of the leaf cells below this view's root, in declaration order: every path
    /// [`Self::value`] reads, the leaves inside an optional cell included. A repeated cell's
    /// leaves are read through [`Self::instances`], and are not listed.
    #[must_use]
    pub fn leaf_paths(&self) -> Vec<String> {
        let mut paths = Vec::new();
        leaf_paths(self.root_nodes(), "", &mut paths);
        paths
    }

    /// The paths of the repeated cells below this view's root, in declaration order, below no
    /// other repeated cell; a repeated cell inside a repeated cell is listed by its instances'
    /// views. With [`Self::leaf_paths`], a walk through [`Self::instances`] reaches every leaf
    /// cell of a configuration whose repeated cells are groups, as KRS declares every one (a
    /// `multiplicity = "*"` cell is `nested`). The instance of a repeated leaf cell, which only
    /// Definition IR built by other means holds, is a view with no paths, so neither
    /// [`Self::leaf_paths`] nor [`Self::value`] reads its content;
    /// [`crate::Semantics::end_of`] reads every cell, such an instance's content included.
    #[must_use]
    pub fn repeated_paths(&self) -> Vec<String> {
        let mut paths = Vec::new();
        repeated_paths(self.root_nodes(), "", &mut paths);
        paths
    }

    /// The group cell at `path` as a view whose paths start below it.
    ///
    /// # Errors
    ///
    /// Returns a [`CellError`] for an unknown path, a leaf or repeated cell, or a path through
    /// an absent optional cell.
    pub fn at(&self, path: &str) -> Result<Self, CellError> {
        let located = self.locate(path, false)?;
        if located.node.children.is_empty() {
            return Err(CellError::Kind {
                path: path.to_owned(),
                expected: "a group cell",
            });
        }
        let term = located.term.ok_or_else(|| CellError::Absent {
            path: path.to_owned(),
        })?;
        Ok(Self {
            index: self.index.clone(),
            scope: located.scope,
            term,
            constraints: self.constraints.clone(),
        })
    }

    /// Whether the state holds the optional cell at `path`.
    ///
    /// # Errors
    ///
    /// Returns a [`CellError`] for an unknown path or a cell that is not optional.
    pub fn present(&self, path: &str) -> Result<bool, CellError> {
        let located = self.locate(path, false)?;
        if located.node.multiplicity != Some(CellMultiplicity::Optional) {
            return Err(CellError::Kind {
                path: path.to_owned(),
                expected: "an optional cell",
            });
        }
        Ok(located.term.is_some())
    }

    /// The instances of the repeated cell at `path`, each a view whose paths start below it.
    ///
    /// # Errors
    ///
    /// Returns a [`CellError`] for an unknown path or a cell that is not repeated.
    pub fn instances(&self, path: &str) -> Result<Vec<Self>, CellError> {
        let located = self.locate(path, true)?;
        if located.node.multiplicity != Some(CellMultiplicity::Star) {
            return Err(CellError::Kind {
                path: path.to_owned(),
                expected: "a repeated cell",
            });
        }
        let Some(parent) = located.term else {
            return Ok(Vec::new());
        };
        Ok(self
            .cells_of(parent, &located.node.symbol)
            .into_iter()
            .map(|term| Self {
                index: self.index.clone(),
                scope: located.scope.clone(),
                term,
                constraints: self.constraints.clone(),
            })
            .collect())
    }

    /// The constraint on the state, as the KORE predicates conjoined with its configuration.
    #[must_use]
    pub fn constraints(&self) -> &[&'t Pattern] {
        &self.constraints
    }

    /// The term of this view's root cell (the configuration, for a state's view).
    pub(crate) const fn term(&self) -> &'t Pattern {
        self.term
    }
}

#[cfg(test)]
mod tests {
    use super::{cells_below, head};
    use k_rust::kore::parser::parse_pattern;

    /// A cell's cells are those it holds directly or through the collection of a repeated
    /// cell's instances; a cell term that a leaf cell holds as its content (here a `<frame>`
    /// fragment in the computation cell, and a `<row>` one in a row's `<id>`) is a value, not a
    /// cell of the state.
    #[test]
    fn the_cells_below_a_cell_pass_no_other_cell() {
        let frame = |ret: &str| {
            format!(
                r#"Lbl'-LT-'frame'-GT-'{{}}(Lbl'-LT-'ret'-GT-'{{}}(\dv{{SortInt{{}}}}("{ret}")))"#
            )
        };
        let row = |id: &str| format!(r"Lbl'-LT-'row'-GT-'{{}}(Lbl'-LT-'id'-GT-'{{}}({id}))");
        let fragment_row = format!(
            "inj{{SortRowCell{{}}, SortKItem{{}}}}({})",
            row(r#"\dv{SortInt{}}("9")"#)
        );
        let state = parse_pattern(&format!(
            r"Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortFrameCell{{}}, SortKItem{{}}}}({}), dotk{{}}())), {}, Lbl'-LT-'table'-GT-'{{}}(Lbl'Unds'RowCellBag'Unds'{{}}({}, {})))",
            frame("1"),
            frame("5"),
            row(r#"\dv{SortInt{}}("1")"#),
            row(&format!("kseq{{}}({fragment_row}, dotk{{}}())")),
        ))
        .unwrap();
        let symbols = [
            "Lbl'-LT-'k'-GT-'",
            "Lbl'-LT-'frame'-GT-'",
            "Lbl'-LT-'ret'-GT-'",
            "Lbl'-LT-'table'-GT-'",
            "Lbl'-LT-'row'-GT-'",
            "Lbl'-LT-'id'-GT-'",
        ];
        let below = cells_below(&state, &symbols);
        let heads = below.iter().map(|cell| head(cell)).collect::<Vec<_>>();
        assert_eq!(
            heads,
            [
                Some("Lbl'-LT-'k'-GT-'"),
                Some("Lbl'-LT-'frame'-GT-'"),
                Some("Lbl'-LT-'table'-GT-'")
            ]
        );
        assert_eq!(
            below[1].to_string(),
            parse_pattern(&frame("5")).unwrap().to_string()
        );
        let rows = cells_below(below[2], &symbols);
        assert_eq!(rows.len(), 2, "{rows:?}");
        assert!(
            rows.iter()
                .all(|row| head(row) == Some("Lbl'-LT-'row'-GT-'"))
        );
    }
}
