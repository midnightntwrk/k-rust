//! Target-neutral fixed-configuration and state-rewrite contracts.
//!
//! These types describe declaration-led fixed cell trees. Optional and
//! repeated cells deliberately remain outside this schema slice.

use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

use serde::{Deserialize, Serialize};

use crate::{NodeOrigin, SemanticId};

/// User-authored root policy for a fixed configuration.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "root_kind", content = "name", rename_all = "snake_case")]
pub enum ConfigurationRoot {
    /// Multiple top-level cells use the frontend-provided generated top.
    GeneratedTop,
    /// One explicit user-visible root cell contains the top-level cells.
    Named {
        /// Provenance for the authored root-cell name token.
        origin: NodeOrigin,
        /// Exact authored root-cell name.
        name: String,
    },
}

impl ConfigurationRoot {
    /// Creates an explicit user-visible root cell.
    ///
    /// # Errors
    ///
    /// Returns [`StateShapeError::EmptyText`] for a blank name.
    pub fn named(origin: NodeOrigin, name: impl Into<String>) -> Result<Self, StateShapeError> {
        Ok(Self::Named {
            origin,
            name: checked_text("configuration root", name.into())?,
        })
    }

    /// Returns provenance for an authored named root.
    #[must_use]
    pub const fn origin(&self) -> Option<&NodeOrigin> {
        match self {
            Self::GeneratedTop => None,
            Self::Named { origin, .. } => Some(origin),
        }
    }

    /// Returns the authored root name, or `None` for a generated top.
    #[must_use]
    pub fn name(&self) -> Option<&str> {
        match self {
            Self::GeneratedTop => None,
            Self::Named { name, .. } => Some(name),
        }
    }
}

/// Validated cell color metadata.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct CellColor(String);

impl CellColor {
    /// Creates nonempty target-neutral color metadata.
    ///
    /// # Errors
    ///
    /// Returns [`StateShapeError::EmptyText`] for a blank value.
    pub fn new(value: impl Into<String>) -> Result<Self, StateShapeError> {
        let value = value.into();
        if value.trim().is_empty() {
            Err(StateShapeError::EmptyText("cell color"))
        } else {
            Ok(Self(value))
        }
    }

    /// Returns the exact authored color spelling.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for CellColor {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Self::new(String::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

/// Classified fixed-cell metadata.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "attribute_kind", content = "value", rename_all = "snake_case")]
pub enum CellAttribute {
    /// Presentation color preserved without a raw K attribute.
    Color {
        /// Provenance for the authored attribute value.
        origin: NodeOrigin,
        /// Validated target-neutral color value.
        value: CellColor,
    },
}

impl CellAttribute {
    /// Creates classified cell-color metadata.
    ///
    /// # Errors
    ///
    /// Returns [`StateShapeError::EmptyText`] for a blank value.
    pub fn color(origin: NodeOrigin, value: impl Into<String>) -> Result<Self, StateShapeError> {
        Ok(Self::Color {
            origin,
            value: CellColor::new(value)?,
        })
    }

    /// Returns provenance for this metadata value.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        match self {
            Self::Color { origin, .. } => origin,
        }
    }
}

/// One exactly-once cell in an ordered fixed configuration tree.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedCell<S, C> {
    origin: NodeOrigin,
    id: C,
    name: String,
    attributes: Vec<CellAttribute>,
    content: FixedCellContent<S, C>,
}

impl<S, C> FixedCell<S, C> {
    /// Creates a fixed leaf cell containing one typed term.
    ///
    /// # Errors
    ///
    /// Returns [`StateShapeError::EmptyText`] for a blank cell name.
    pub fn leaf(
        origin: NodeOrigin,
        id: C,
        name: impl Into<String>,
        attributes: Vec<CellAttribute>,
        sort: S,
    ) -> Result<Self, StateShapeError> {
        let name = checked_text("cell name", name.into())?;
        Ok(Self {
            origin,
            id,
            name,
            attributes,
            content: FixedCellContent::Term { sort },
        })
    }

    /// Creates a fixed parent cell containing ordered fixed children.
    ///
    /// # Errors
    ///
    /// Returns [`StateShapeError`] for a blank name or empty child list.
    pub fn nested(
        origin: NodeOrigin,
        id: C,
        name: impl Into<String>,
        attributes: Vec<CellAttribute>,
        children: Vec<Self>,
    ) -> Result<Self, StateShapeError> {
        let name = checked_text("cell name", name.into())?;
        if children.is_empty() {
            return Err(StateShapeError::EmptyCollection("nested cell children"));
        }
        Ok(Self {
            origin,
            id,
            name,
            attributes,
            content: FixedCellContent::Children { children },
        })
    }

    /// Returns provenance for this cell declaration.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns stable cell identity.
    #[must_use]
    pub const fn id(&self) -> &C {
        &self.id
    }

    /// Returns the exact authored cell name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns classified metadata in authored order.
    #[must_use]
    pub fn attributes(&self) -> &[CellAttribute] {
        &self.attributes
    }

    /// Returns leaf or nested content.
    #[must_use]
    pub const fn content(&self) -> &FixedCellContent<S, C> {
        &self.content
    }
}

/// A fixed cell contains either one ordinary term or ordered child cells.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "content_kind", rename_all = "snake_case")]
pub enum FixedCellContent<S, C> {
    /// Leaf term content with an exact sort.
    Term {
        /// Exact leaf content sort.
        sort: S,
    },
    /// Structural content made exclusively of fixed children.
    Children {
        /// Ordered exactly-once child cells.
        children: Vec<FixedCell<S, C>>,
    },
}

/// One ordered external configuration variable.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedConfigurationVariable<S> {
    origin: NodeOrigin,
    id: SemanticId,
    external_name: String,
    sort: S,
    main: bool,
}

impl<S> FixedConfigurationVariable<S> {
    /// Creates configuration-variable metadata.
    ///
    /// # Errors
    ///
    /// Returns [`StateShapeError::EmptyText`] for a blank external name.
    pub fn new(
        origin: NodeOrigin,
        id: SemanticId,
        external_name: impl Into<String>,
        sort: S,
        main: bool,
    ) -> Result<Self, StateShapeError> {
        Ok(Self {
            origin,
            id,
            external_name: checked_text("configuration variable name", external_name.into())?,
            sort,
            main,
        })
    }

    /// Returns provenance for the authored configuration variable.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns the stable binding identity.
    #[must_use]
    pub const fn id(&self) -> &SemanticId {
        &self.id
    }

    /// Returns the external `$`-variable name without the sigil.
    #[must_use]
    pub fn external_name(&self) -> &str {
        &self.external_name
    }

    /// Returns its exact term sort.
    #[must_use]
    pub const fn sort(&self) -> &S {
        &self.sort
    }

    /// Whether this is the sole main program input.
    #[must_use]
    pub const fn is_main(&self) -> bool {
        self.main
    }
}

/// One node in a complete declarative initializer tree.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedInitializerCell<C, T> {
    origin: NodeOrigin,
    cell: C,
    content: FixedInitializerContent<C, T>,
}

impl<C, T> FixedInitializerCell<C, T> {
    /// Initializes one leaf cell with a structured term.
    #[must_use]
    pub const fn term(origin: NodeOrigin, cell: C, term: T) -> Self {
        Self {
            origin,
            cell,
            content: FixedInitializerContent::Term { term },
        }
    }

    /// Initializes one parent cell with ordered initialized children.
    ///
    /// # Errors
    ///
    /// Returns [`StateShapeError::EmptyCollection`] for no children.
    pub fn children(
        origin: NodeOrigin,
        cell: C,
        children: Vec<Self>,
    ) -> Result<Self, StateShapeError> {
        if children.is_empty() {
            return Err(StateShapeError::EmptyCollection("initializer children"));
        }
        Ok(Self {
            origin,
            cell,
            content: FixedInitializerContent::Children { children },
        })
    }

    /// Returns provenance for this initializer node.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns the declaration identity initialized here.
    #[must_use]
    pub const fn cell(&self) -> &C {
        &self.cell
    }

    /// Returns structured leaf or child initialization.
    #[must_use]
    pub const fn content(&self) -> &FixedInitializerContent<C, T> {
        &self.content
    }
}

/// Structured initializer content.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "content_kind", rename_all = "snake_case")]
pub enum FixedInitializerContent<C, T> {
    /// Complete typed leaf content.
    Term {
        /// Structured initial leaf term.
        term: T,
    },
    /// Complete ordered child initialization.
    Children {
        /// Complete ordered initialized child cells.
        children: Vec<FixedInitializerCell<C, T>>,
    },
}

/// One complete structured fixed configuration and initializer.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedConfiguration<S, C, T> {
    origin: NodeOrigin,
    id: SemanticId,
    root: ConfigurationRoot,
    cells: Vec<FixedCell<S, C>>,
    initializer_origin: NodeOrigin,
    initializer_id: SemanticId,
    variables: Vec<FixedConfigurationVariable<S>>,
    initializer: Vec<FixedInitializerCell<C, T>>,
}

impl<S, C, T> FixedConfiguration<S, C, T>
where
    C: Clone + Ord,
{
    /// Creates a locally valid ordered fixed configuration.
    ///
    /// Whole-theory validation additionally checks sorts, initializer terms,
    /// provenance uniqueness, and configuration-variable closure.
    ///
    /// # Errors
    ///
    /// Returns [`StateShapeError`] for empty/duplicate cells or variables.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        origin: NodeOrigin,
        id: SemanticId,
        root: ConfigurationRoot,
        cells: Vec<FixedCell<S, C>>,
        initializer_origin: NodeOrigin,
        initializer_id: SemanticId,
        variables: Vec<FixedConfigurationVariable<S>>,
        initializer: Vec<FixedInitializerCell<C, T>>,
    ) -> Result<Self, StateShapeError> {
        if let ConfigurationRoot::Named { name, .. } = &root {
            checked_text("configuration root", name.clone())?;
        }
        if cells.is_empty() {
            return Err(StateShapeError::EmptyCollection("top-level cells"));
        }
        let mut cell_ids = BTreeSet::new();
        let mut cell_names = BTreeSet::new();
        collect_cell_identities(&cells, &mut cell_ids, &mut cell_names)?;
        let mut variable_ids = BTreeSet::new();
        let mut external_names = BTreeSet::new();
        let mut main_count = 0_usize;
        for variable in &variables {
            if !variable_ids.insert(variable.id.clone()) {
                return Err(StateShapeError::DuplicateVariable(variable.id.clone()));
            }
            if !external_names.insert(variable.external_name.clone()) {
                return Err(StateShapeError::DuplicateExternalVariable(
                    variable.external_name.clone(),
                ));
            }
            main_count += usize::from(variable.main);
        }
        if main_count > 1 {
            return Err(StateShapeError::MultipleMainVariables);
        }
        Ok(Self {
            origin,
            id,
            root,
            cells,
            initializer_origin,
            initializer_id,
            variables,
            initializer,
        })
    }

    /// Returns configuration provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns stable configuration identity.
    #[must_use]
    pub const fn id(&self) -> &SemanticId {
        &self.id
    }

    /// Returns generated-top or explicit-root policy.
    #[must_use]
    pub const fn root(&self) -> &ConfigurationRoot {
        &self.root
    }

    /// Returns top-level cells in authored order.
    #[must_use]
    pub fn cells(&self) -> &[FixedCell<S, C>] {
        &self.cells
    }

    /// Returns initializer declaration provenance.
    #[must_use]
    pub const fn initializer_origin(&self) -> &NodeOrigin {
        &self.initializer_origin
    }

    /// Returns generated initializer identity.
    #[must_use]
    pub const fn initializer_id(&self) -> &SemanticId {
        &self.initializer_id
    }

    /// Returns ordered external variables.
    #[must_use]
    pub fn variables(&self) -> &[FixedConfigurationVariable<S>] {
        &self.variables
    }

    /// Returns the complete ordered initializer forest.
    #[must_use]
    pub fn initializer(&self) -> &[FixedInitializerCell<C, T>] {
        &self.initializer
    }
}

/// Exact associative frame attached to one cell-content pattern.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "frame_kind", rename_all = "snake_case")]
pub enum CellContentFrame {
    /// No omitted content.
    Exact,
    /// Omitted K-sequence tail, optionally bound.
    KSequenceTail {
        /// Provenance for the authored frame marker.
        origin: NodeOrigin,
        /// Optional binding for the omitted sequence tail.
        #[serde(skip_serializing_if = "Option::is_none")]
        binding: Option<SemanticId>,
    },
    /// Omitted associative map remainder, optionally bound.
    MapRemainder {
        /// Provenance for the authored frame marker.
        origin: NodeOrigin,
        /// Optional binding for the omitted associative map remainder.
        #[serde(skip_serializing_if = "Option::is_none")]
        binding: Option<SemanticId>,
    },
}

/// Post-state of one mentioned cell.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "post_kind", rename_all = "snake_case")]
pub enum CellPost<T> {
    /// Cell content is matched but unchanged.
    Preserve,
    /// Cell content is replaced simultaneously with all other replacements.
    Replace {
        /// Complete replacement content term.
        term: T,
    },
}

/// One leaf-cell clause in a simultaneous configuration rewrite.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedCellClause<C, T> {
    origin: NodeOrigin,
    cell: C,
    before: T,
    after: CellPost<T>,
    frame: CellContentFrame,
}

/// One leaf-cell pattern in a one-sided configuration sentence.
///
/// Unlike [`FixedCellClause`], this node has no post-state and therefore
/// cannot accidentally acquire rewrite meaning.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedCellPattern<C, T> {
    origin: NodeOrigin,
    cell: C,
    pattern: T,
    frame: CellContentFrame,
}

impl<C, T> FixedCellPattern<C, T> {
    /// Creates one explicitly framed leaf-cell pattern.
    #[must_use]
    pub const fn new(origin: NodeOrigin, cell: C, pattern: T, frame: CellContentFrame) -> Self {
        Self {
            origin,
            cell,
            pattern,
            frame,
        }
    }

    /// Returns pattern provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the selected leaf cell.
    #[must_use]
    pub const fn cell(&self) -> &C {
        &self.cell
    }
    /// Returns the one-sided cell-content pattern.
    #[must_use]
    pub const fn pattern(&self) -> &T {
        &self.pattern
    }
    /// Returns the explicit associative frame.
    #[must_use]
    pub const fn frame(&self) -> &CellContentFrame {
        &self.frame
    }
}

/// One complete one-sided fixed-configuration pattern.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedConfigurationPattern<C, T> {
    origin: NodeOrigin,
    configuration: SemanticId,
    cells: Vec<FixedCellPattern<C, T>>,
    omitted_siblings: Vec<C>,
}

impl<C, T> FixedConfigurationPattern<C, T>
where
    C: Clone + Ord,
{
    /// Creates a pattern with every unmentioned leaf listed explicitly.
    ///
    /// # Errors
    ///
    /// Returns [`StateShapeError`] for no cells, repeated cells, or overlap
    /// between mentioned and omitted cells.
    pub fn new(
        origin: NodeOrigin,
        configuration: SemanticId,
        cells: Vec<FixedCellPattern<C, T>>,
        omitted_siblings: Vec<C>,
    ) -> Result<Self, StateShapeError> {
        if cells.is_empty() {
            return Err(StateShapeError::EmptyCollection(
                "configuration pattern cells",
            ));
        }
        let mut mentioned = BTreeSet::new();
        for cell in &cells {
            if !mentioned.insert(cell.cell.clone()) {
                return Err(StateShapeError::DuplicateCell);
            }
        }
        let mut omitted = BTreeSet::new();
        for cell in &omitted_siblings {
            if mentioned.contains(cell) {
                return Err(StateShapeError::MentionedAndOmittedCell);
            }
            if !omitted.insert(cell.clone()) {
                return Err(StateShapeError::DuplicateOmittedCell);
            }
        }
        Ok(Self {
            origin,
            configuration,
            cells,
            omitted_siblings,
        })
    }

    /// Returns sentence provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }
    /// Returns the selected fixed configuration.
    #[must_use]
    pub const fn configuration(&self) -> &SemanticId {
        &self.configuration
    }
    /// Returns selected cells in authored order.
    #[must_use]
    pub fn cells(&self) -> &[FixedCellPattern<C, T>] {
        &self.cells
    }
    /// Returns explicitly omitted sibling cells.
    #[must_use]
    pub fn omitted_siblings(&self) -> &[C] {
        &self.omitted_siblings
    }
}

impl<C, T> FixedCellClause<C, T> {
    /// Creates an explicit framed cell clause.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        cell: C,
        before: T,
        after: CellPost<T>,
        frame: CellContentFrame,
    ) -> Self {
        Self {
            origin,
            cell,
            before,
            after,
            frame,
        }
    }

    /// Returns clause provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns stable leaf-cell identity.
    #[must_use]
    pub const fn cell(&self) -> &C {
        &self.cell
    }

    /// Returns the pre-pattern.
    #[must_use]
    pub const fn before(&self) -> &T {
        &self.before
    }

    /// Returns preserved or replaced post-state.
    #[must_use]
    pub const fn after(&self) -> &CellPost<T> {
        &self.after
    }

    /// Returns the explicit content frame.
    #[must_use]
    pub const fn frame(&self) -> &CellContentFrame {
        &self.frame
    }
}

/// One simultaneous fixed-configuration rewrite.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedConfigurationRewrite<C, T> {
    origin: NodeOrigin,
    configuration: SemanticId,
    clauses: Vec<FixedCellClause<C, T>>,
    omitted_siblings: Vec<C>,
}

impl<C, T> FixedConfigurationRewrite<C, T>
where
    C: Clone + Ord,
{
    /// Creates a rewrite with every unmentioned leaf listed explicitly.
    ///
    /// # Errors
    ///
    /// Returns [`StateShapeError`] for no clauses, repeated cells, or overlap
    /// between mentioned and omitted cells.
    pub fn new(
        origin: NodeOrigin,
        configuration: SemanticId,
        clauses: Vec<FixedCellClause<C, T>>,
        omitted_siblings: Vec<C>,
    ) -> Result<Self, StateShapeError> {
        if clauses.is_empty() {
            return Err(StateShapeError::EmptyCollection(
                "configuration rewrite clauses",
            ));
        }
        let mut mentioned = BTreeSet::new();
        for clause in &clauses {
            if !mentioned.insert(clause.cell.clone()) {
                return Err(StateShapeError::DuplicateCell);
            }
        }
        let mut omitted = BTreeSet::new();
        for cell in &omitted_siblings {
            if mentioned.contains(cell) {
                return Err(StateShapeError::MentionedAndOmittedCell);
            }
            if !omitted.insert(cell.clone()) {
                return Err(StateShapeError::DuplicateOmittedCell);
            }
        }
        Ok(Self {
            origin,
            configuration,
            clauses,
            omitted_siblings,
        })
    }

    /// Returns the exact fixed configuration rewritten by this rule.
    #[must_use]
    pub const fn configuration(&self) -> &SemanticId {
        &self.configuration
    }

    /// Returns rewrite provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns mentioned cells in authored order.
    #[must_use]
    pub fn clauses(&self) -> &[FixedCellClause<C, T>] {
        &self.clauses
    }

    /// Returns explicitly framed unmentioned leaf cells.
    #[must_use]
    pub fn omitted_siblings(&self) -> &[C] {
        &self.omitted_siblings
    }
}

/// Exact map-theory term operations needed by the IMP state slice.
///
/// Map item keys and values are intentionally not assigned fake builtin sorts;
/// their enclosing structured terms retain their authored sorts.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MapOperation {
    /// Empty map unit (`.Map`).
    Empty,
    /// One or more flattened key/value map items, also usable in associative matching.
    Item,
    /// Functional map update.
    Update,
}

impl MapOperation {
    /// Map operations which may occur as ordinary authored term applications.
    ///
    /// Empty maps and map items retain their dedicated `map!` structural
    /// syntax. Persistent update is the one function-shaped operation and is
    /// therefore resolved through the ordinary application-head registry.
    pub const TERM_APPLICATIONS: [Self; 1] = [Self::Update];
}

/// Exact builtin-list operations selected from pinned module `LIST`.
///
/// List elements deliberately retain their authored sorts. The K frontend
/// injects them into `KItem` at `ListItem`, lookup, and update boundaries.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ListOperation {
    /// Empty list unit (`.List`).
    Empty,
    /// Singleton list element (`ListItem(K)`).
    Item,
    /// Associative list concatenation (`L1 L2`).
    Concat,
    /// Indexed element lookup (`L[I]`).
    Get,
    /// Persistent indexed update (`L[I <- K]`).
    Update,
    /// List length (`size(L)`).
    Size,
}

impl ListOperation {
    /// Complete ordinary application catalog in stable semantic order.
    pub const TERM_APPLICATIONS: [Self; 6] = [
        Self::Empty,
        Self::Item,
        Self::Concat,
        Self::Get,
        Self::Update,
        Self::Size,
    ];
}

/// Locally invalid fixed-state structure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StateShapeError {
    /// Textual metadata was blank.
    EmptyText(&'static str),
    /// A mandatory ordered collection was empty.
    EmptyCollection(&'static str),
    /// A stable cell identity occurred twice.
    DuplicateCell,
    /// A globally resolved cell name occurred twice.
    DuplicateCellName(String),
    /// One configuration binding occurred twice.
    DuplicateVariable(SemanticId),
    /// Two variables share one external `$` name.
    DuplicateExternalVariable(String),
    /// More than one variable was marked main.
    MultipleMainVariables,
    /// One cell was both mentioned and structurally omitted.
    MentionedAndOmittedCell,
    /// An omitted sibling identity occurred twice.
    DuplicateOmittedCell,
}

impl fmt::Display for StateShapeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyText(field) => write!(formatter, "{field} must not be blank"),
            Self::EmptyCollection(field) => write!(formatter, "{field} must not be empty"),
            Self::DuplicateCell => formatter.write_str("fixed cell identity occurs more than once"),
            Self::DuplicateCellName(name) => {
                write!(formatter, "fixed cell name {name:?} occurs more than once")
            }
            Self::DuplicateVariable(id) => {
                write!(
                    formatter,
                    "configuration variable {:?} occurs more than once",
                    id.as_str()
                )
            }
            Self::DuplicateExternalVariable(name) => {
                write!(
                    formatter,
                    "external configuration variable {name:?} occurs more than once"
                )
            }
            Self::MultipleMainVariables => {
                formatter.write_str("configuration has more than one main variable")
            }
            Self::MentionedAndOmittedCell => {
                formatter.write_str("cell is both mentioned and omitted in one rewrite")
            }
            Self::DuplicateOmittedCell => {
                formatter.write_str("omitted sibling cell occurs more than once")
            }
        }
    }
}

impl Error for StateShapeError {}

fn checked_text(field: &'static str, value: String) -> Result<String, StateShapeError> {
    if value.trim().is_empty() {
        Err(StateShapeError::EmptyText(field))
    } else {
        Ok(value)
    }
}

fn collect_cell_identities<S, C>(
    cells: &[FixedCell<S, C>],
    ids: &mut BTreeSet<C>,
    names: &mut BTreeSet<String>,
) -> Result<(), StateShapeError>
where
    C: Clone + Ord,
{
    for cell in cells {
        if !ids.insert(cell.id.clone()) {
            return Err(StateShapeError::DuplicateCell);
        }
        if !names.insert(cell.name.clone()) {
            return Err(StateShapeError::DuplicateCellName(cell.name.clone()));
        }
        if let FixedCellContent::Children { children } = &cell.content {
            collect_cell_identities(children, ids, names)?;
        }
    }
    Ok(())
}
