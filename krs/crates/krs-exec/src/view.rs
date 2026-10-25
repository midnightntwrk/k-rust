//! Views of result states: their cells, addressed by the Rust fields that declare them.

use std::fmt;
use std::sync::Arc;

use k_rust::kore::{ast::Pattern, walk};
use krs_ir::CellMultiplicity;

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

/// Every pattern below `root` (itself included) whose head is `symbol`, outermost first.
fn occurrences<'t>(root: &'t Pattern, symbol: &str) -> Vec<&'t Pattern> {
    let mut found = Vec::new();
    let mut stack = vec![root];
    while let Some(pattern) = stack.pop() {
        if head(pattern) == Some(symbol) {
            found.push(pattern);
            continue;
        }
        stack.extend(walk::children(pattern).into_iter().rev());
    }
    found
}

fn paths(nodes: &[CellNode], prefix: &str, output: &mut Vec<String>) {
    for node in nodes {
        let path = format!("{prefix}{}", node.field);
        paths(&node.children, &format!("{path}."), output);
        output.push(path);
    }
}

/// A located cell: its node, the positions from the configuration, and its term in the state.
struct Located<'t, 'n> {
    node: &'n CellNode,
    scope: Vec<usize>,
    term: Option<&'t Pattern>,
}

impl<'t> StateView<'t> {
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
                        let found = occurrences(parent, &node.symbol);
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
        let content = match term {
            Pattern::Application { arguments, .. } => match arguments.as_slice() {
                [content] => content,
                _ => {
                    return Err(CellError::Decode(ValueError::Malformed(format!(
                        "{term} is not a leaf cell"
                    ))));
                }
            },
            _ => unreachable!("cells are found by their head"),
        };
        Ok(self.index.decode(content)?)
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
        Ok(occurrences(parent, &located.node.symbol)
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
}
