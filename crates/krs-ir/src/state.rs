//! Target-neutral fixed-configuration and state-rewrite contracts.
//!
//! These types describe declaration-led cell trees, including optional (`?`)
//! cells and repeated (`*`) collection cells, and the configuration rewrites
//! over them (KF-023).

use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

use serde::{Deserialize, Serialize};

pub use crate::catalog::{ListOperation, MapOperation, SetOperation, TermMapOperation};
use crate::{NodeOrigin, SemanticId, StableItemId};

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
            name: checked_text(crate::IrField::ConfigurationRoot, name.into())?,
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
            Err(StateShapeError::EmptyText(crate::IrField::CellColor))
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
    /// Repeated-cell multiplicity.
    Multiplicity {
        /// Provenance for the authored attribute value.
        origin: NodeOrigin,
        /// Validated multiplicity value.
        value: CellMultiplicity,
    },
    /// Collection type for a repeated cell.
    CollectionType {
        /// Provenance for the authored attribute value.
        origin: NodeOrigin,
        /// Validated collection type.
        value: CellCollectionType,
    },
    /// K console stream (`stream="stdin"` or `stream="stdout"`).
    Stream {
        /// Provenance for the authored attribute value.
        origin: NodeOrigin,
        /// The connected standard stream.
        value: CellStream,
    },
    /// The exit cell (`exit=""`): its final Int value is the process exit status.
    Exit {
        /// Provenance for the authored flag.
        origin: NodeOrigin,
    },
    /// `initial=""` on an optional or collection cell: the initial
    /// configuration holds the cell (one instance of it) built from its
    /// declaration template (KF-023).
    Initial {
        /// Provenance for the authored flag.
        origin: NodeOrigin,
    },
}

/// Standard streams K connects a stream cell to (K 7.1.337 has no stderr stream cell).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CellStream {
    /// Standard input, bound to `$STDIN`.
    Stdin,
    /// Standard output.
    Stdout,
}

impl CellStream {
    /// Returns the exact K attribute value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Stdin => "stdin",
            Self::Stdout => "stdout",
        }
    }

    /// Parses the exact K attribute value.
    #[must_use]
    pub fn from_k(value: &str) -> Option<Self> {
        match value {
            "stdin" => Some(Self::Stdin),
            "stdout" => Some(Self::Stdout),
            _ => None,
        }
    }
}

/// Supported K cell multiplicities.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CellMultiplicity {
    /// Zero or more cells.
    Star,
    /// Zero or one cell (KF-023).
    Optional,
}

impl CellMultiplicity {
    /// Returns the exact K attribute spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Star => "*",
            Self::Optional => "?",
        }
    }

    /// Parses the exact K attribute spelling.
    #[must_use]
    pub fn from_k(value: &str) -> Option<Self> {
        match value {
            "*" => Some(Self::Star),
            "?" => Some(Self::Optional),
            _ => None,
        }
    }
}

/// Supported collection types for repeated cells. K's cell bags are
/// unsupported by its LLVM and Haskell backends, so KRS rejects them.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CellCollectionType {
    /// Ordered list collection.
    List,
    /// Keyed map collection.
    Map,
    /// Commutative set collection.
    Set,
}

impl CellCollectionType {
    /// Returns the exact K attribute spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::List => "List",
            Self::Map => "Map",
            Self::Set => "Set",
        }
    }
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

    /// Creates repeated-cell multiplicity metadata.
    #[must_use]
    pub const fn multiplicity(origin: NodeOrigin, value: CellMultiplicity) -> Self {
        Self::Multiplicity { origin, value }
    }

    /// Creates repeated-cell collection-type metadata.
    #[must_use]
    pub const fn collection_type(origin: NodeOrigin, value: CellCollectionType) -> Self {
        Self::CollectionType { origin, value }
    }

    /// Creates console-stream metadata.
    #[must_use]
    pub const fn stream(origin: NodeOrigin, value: CellStream) -> Self {
        Self::Stream { origin, value }
    }

    /// Creates the exit-cell flag.
    #[must_use]
    pub const fn exit(origin: NodeOrigin) -> Self {
        Self::Exit { origin }
    }

    /// Creates the `initial` flag of an optional or collection cell.
    #[must_use]
    pub const fn initial(origin: NodeOrigin) -> Self {
        Self::Initial { origin }
    }

    /// Returns provenance for this metadata value.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        match self {
            Self::Color { origin, .. }
            | Self::Multiplicity { origin, .. }
            | Self::CollectionType { origin, .. }
            | Self::Stream { origin, .. }
            | Self::Exit { origin }
            | Self::Initial { origin } => origin,
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
    /// Nominal `#[k::cell]` declaration of a nested cell, recorded in Semantic
    /// IR so that a group-cell sort (`IrSortRef::Cell`) can name its cell.
    /// Definition IR names the cell by its symbol instead and omits it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    declaration: Option<StableItemId>,
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
        let name = checked_text(crate::IrField::CellName, name.into())?;
        Ok(Self {
            origin,
            id,
            name,
            attributes,
            content: FixedCellContent::Term { sort },
            declaration: None,
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
        let name = checked_text(crate::IrField::CellName, name.into())?;
        if children.is_empty() {
            return Err(StateShapeError::EmptyCollection(
                crate::IrField::NestedCellChildren,
            ));
        }
        Ok(Self {
            origin,
            id,
            name,
            attributes,
            content: FixedCellContent::Children { children },
            declaration: None,
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

    /// Records the nominal `#[k::cell]` declaration of a nested cell.
    #[must_use]
    pub fn with_declaration(mut self, declaration: StableItemId) -> Self {
        self.declaration = Some(declaration);
        self
    }

    /// Returns the nominal declaration of a nested cell in Semantic IR.
    #[must_use]
    pub const fn declaration(&self) -> Option<&StableItemId> {
        self.declaration.as_ref()
    }

    /// Returns the cell's multiplicity, `None` for an exactly-once cell.
    #[must_use]
    pub fn multiplicity(&self) -> Option<CellMultiplicity> {
        self.attributes
            .iter()
            .find_map(|attribute| match attribute {
                CellAttribute::Multiplicity { value, .. } => Some(*value),
                _ => None,
            })
    }

    /// Returns the collection type of a repeated cell.
    #[must_use]
    pub fn collection_type(&self) -> Option<CellCollectionType> {
        self.attributes
            .iter()
            .find_map(|attribute| match attribute {
                CellAttribute::CollectionType { value, .. } => Some(*value),
                _ => None,
            })
    }

    /// Whether an optional or collection cell carries `initial`.
    #[must_use]
    pub fn is_initial(&self) -> bool {
        self.attributes
            .iter()
            .any(|attribute| matches!(attribute, CellAttribute::Initial { .. }))
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
            external_name: checked_text(
                crate::IrField::ConfigurationVariableName,
                external_name.into(),
            )?,
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
            return Err(StateShapeError::EmptyCollection(
                crate::IrField::InitializerChildren,
            ));
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
    #[expect(
        clippy::too_many_arguments,
        reason = "The constructor explicitly supplies every fixed-configuration and initializer field."
    )]
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
            checked_text(crate::IrField::ConfigurationRoot, name.clone())?;
        }
        if cells.is_empty() {
            return Err(StateShapeError::EmptyCollection(
                crate::IrField::TopLevelCells,
            ));
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
    /// Omitted, unbound List tail after the matched front items (K's `...` in a List cell).
    ///
    /// The compiler produces it for a read of a `stream = "stdin"` cell, the one shape K's
    /// stream rules unblock (KF-035).
    ListRemainder {
        /// Provenance for the authored list remainder.
        origin: NodeOrigin,
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
    /// Cell content is rewritten in place by a single-body rule (KF-011):
    /// the clause's `before` contains `Rewrite` nodes below its root, its
    /// left image is the pre-pattern and its right image the post-state.
    Local,
}

/// What a configuration-rewrite clause matches and rewrites.
#[derive(
    Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize,
)]
#[serde(rename_all = "snake_case")]
pub enum CellClauseKind {
    /// The content of one leaf cell, written inside its `<cell>` brackets.
    #[default]
    Content,
    /// One whole nested (group) cell, written as a term of its generated
    /// `<Name>Cell` sort without enclosing brackets (KF-016). The frame is
    /// always exact.
    Whole,
}

impl CellClauseKind {
    /// Returns whether this is the default leaf-content kind.
    #[must_use]
    pub const fn is_content(&self) -> bool {
        matches!(self, Self::Content)
    }
}

/// One cell clause in a simultaneous configuration rewrite.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedCellClause<C, T> {
    origin: NodeOrigin,
    cell: C,
    before: T,
    after: CellPost<T>,
    frame: CellContentFrame,
    /// Leaf content or a whole group cell; omitted when it is leaf content.
    #[serde(default, skip_serializing_if = "CellClauseKind::is_content")]
    kind: CellClauseKind,
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
                crate::IrField::ConfigurationPatternCells,
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
            kind: CellClauseKind::Content,
        }
    }

    /// Creates a clause over one whole nested (group) cell, whose terms have
    /// the group's generated cell sort and whose frame is exact (KF-016).
    #[must_use]
    pub const fn whole(origin: NodeOrigin, cell: C, before: T, after: CellPost<T>) -> Self {
        Self {
            origin,
            cell,
            before,
            after,
            frame: CellContentFrame::Exact,
            kind: CellClauseKind::Whole,
        }
    }

    /// Replaces the clause kind, preserving every other field; IR validation
    /// checks that a whole-cell clause keeps an exact frame.
    #[must_use]
    pub const fn with_kind(mut self, kind: CellClauseKind) -> Self {
        self.kind = kind;
        self
    }

    /// Returns whether the clause rewrites leaf content or a whole group cell.
    #[must_use]
    pub const fn kind(&self) -> CellClauseKind {
        self.kind
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

/// Whether an optional cell is present, and its content when it is.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "presence", rename_all = "snake_case")]
pub enum Presence<T> {
    /// The cell is present with this content.
    Present {
        /// The cell's content (a whole group term for a group cell).
        term: T,
    },
    /// The cell is absent (K's `.Bag`).
    Absent,
}

impl<T> Presence<T> {
    /// Returns the content of a present cell.
    #[must_use]
    pub const fn term(&self) -> Option<&T> {
        match self {
            Self::Present { term } => Some(term),
            Self::Absent => None,
        }
    }
}

/// One optional (`?`) cell in a simultaneous configuration rewrite (KF-023):
/// read, updated, created (absent before), or deleted (absent after).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OptionalCellClause<C, T> {
    origin: NodeOrigin,
    cell: C,
    before: Presence<T>,
    /// `None` when the rule leaves the cell as it matched it.
    after: Option<Presence<T>>,
    frame: CellContentFrame,
    /// Leaf content or a whole group cell; omitted when it is leaf content.
    #[serde(default, skip_serializing_if = "CellClauseKind::is_content")]
    kind: CellClauseKind,
}

impl<C, T> OptionalCellClause<C, T> {
    /// Creates an optional-cell clause; IR validation checks that a present
    /// state precedes a preserved post-state and that an absent pre-state is
    /// followed by a present one.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        cell: C,
        kind: CellClauseKind,
        before: Presence<T>,
        after: Option<Presence<T>>,
        frame: CellContentFrame,
    ) -> Self {
        Self {
            origin,
            cell,
            before,
            after,
            frame,
            kind,
        }
    }

    /// Returns clause provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns the optional cell.
    #[must_use]
    pub const fn cell(&self) -> &C {
        &self.cell
    }

    /// Returns leaf content or a whole group cell.
    #[must_use]
    pub const fn kind(&self) -> CellClauseKind {
        self.kind
    }

    /// Returns the matched state.
    #[must_use]
    pub const fn before(&self) -> &Presence<T> {
        &self.before
    }

    /// Returns the rewritten state, `None` when the cell is only read.
    #[must_use]
    pub const fn after(&self) -> Option<&Presence<T>> {
        self.after.as_ref()
    }

    /// Returns the content frame of a present matched cell.
    #[must_use]
    pub const fn frame(&self) -> &CellContentFrame {
        &self.frame
    }
}

/// How the instances of a collection cell are ordered (KF-023, R8).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InstanceOrdering {
    /// A Set or Map collection: the clause matches *some* instances.
    Unordered,
    /// A List collection: `front` instances sit at the front, `back` ones at the back.
    List,
}

/// One child cell of a matched-and-removed or created collection instance.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InstanceChild<C, T> {
    origin: NodeOrigin,
    cell: C,
    term: T,
    frame: CellContentFrame,
    /// Leaf content or a whole group cell; omitted when it is leaf content.
    #[serde(default, skip_serializing_if = "CellClauseKind::is_content")]
    kind: CellClauseKind,
}

impl<C, T> InstanceChild<C, T> {
    /// Creates one instance child.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        cell: C,
        kind: CellClauseKind,
        term: T,
        frame: CellContentFrame,
    ) -> Self {
        Self {
            origin,
            cell,
            term,
            frame,
            kind,
        }
    }

    /// Returns child provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns the child cell.
    #[must_use]
    pub const fn cell(&self) -> &C {
        &self.cell
    }

    /// Returns the child's matched or created content.
    #[must_use]
    pub const fn term(&self) -> &T {
        &self.term
    }

    /// Returns the child's content frame.
    #[must_use]
    pub const fn frame(&self) -> &CellContentFrame {
        &self.frame
    }

    /// Returns leaf content or a whole group cell.
    #[must_use]
    pub const fn kind(&self) -> CellClauseKind {
        self.kind
    }
}

/// One instance of a collection cell in a configuration rewrite (KF-023).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "instance_kind", rename_all = "snake_case")]
pub enum InstanceClause<C, T> {
    /// A matched instance that stays, its children read or rewritten in
    /// place (`label @ Decl { .. }` and `Decl { .., ..label }`).
    Kept {
        /// Instance provenance.
        origin: NodeOrigin,
        /// The authored instance label.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        label: Option<String>,
        /// The mentioned children, in authored order.
        children: Vec<FixedCellClause<C, T>>,
        /// Whether the other children are unconstrained (`..`).
        open: bool,
    },
    /// A matched instance the rule removes (K's `(<c> .. </c> => .Bag)`).
    Removed {
        /// Instance provenance.
        origin: NodeOrigin,
        /// The authored instance label.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        label: Option<String>,
        /// The mentioned children, in authored order.
        children: Vec<InstanceChild<C, T>>,
        /// Whether the other children are unconstrained (`..`).
        open: bool,
    },
    /// A new instance (K's `(.Bag => <c> .. </c>)`).
    Created {
        /// Instance provenance.
        origin: NodeOrigin,
        /// The given children, in authored order.
        children: Vec<InstanceChild<C, T>>,
        /// Whether the other children take their template defaults (`..`).
        defaults: bool,
    },
}

impl<C, T> InstanceClause<C, T> {
    /// Returns instance provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        match self {
            Self::Kept { origin, .. }
            | Self::Removed { origin, .. }
            | Self::Created { origin, .. } => origin,
        }
    }

    /// Returns the authored label of a matched instance.
    #[must_use]
    pub fn label(&self) -> Option<&str> {
        match self {
            Self::Kept { label, .. } | Self::Removed { label, .. } => label.as_deref(),
            Self::Created { .. } => None,
        }
    }
}

/// The instances of one collection (`*`) cell that a rewrite names (KF-023).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InstancesClause<C, T> {
    origin: NodeOrigin,
    cell: C,
    ordering: InstanceOrdering,
    front: Vec<InstanceClause<C, T>>,
    #[serde(default = "Vec::new", skip_serializing_if = "Vec::is_empty")]
    back: Vec<InstanceClause<C, T>>,
    open: bool,
}

impl<C, T> InstancesClause<C, T> {
    /// Creates a collection clause. `front` and `back` are in emission order;
    /// an unordered collection has no `back`. `open` frames every other
    /// instance; an exact clause names every instance.
    #[must_use]
    pub const fn new(
        origin: NodeOrigin,
        cell: C,
        ordering: InstanceOrdering,
        front: Vec<InstanceClause<C, T>>,
        back: Vec<InstanceClause<C, T>>,
        open: bool,
    ) -> Self {
        Self {
            origin,
            cell,
            ordering,
            front,
            back,
            open,
        }
    }

    /// Returns clause provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        &self.origin
    }

    /// Returns the collection cell.
    #[must_use]
    pub const fn cell(&self) -> &C {
        &self.cell
    }

    /// Returns how the collection is ordered.
    #[must_use]
    pub const fn ordering(&self) -> InstanceOrdering {
        self.ordering
    }

    /// Returns the front (or, unordered, every) instance in emission order.
    #[must_use]
    pub fn front(&self) -> &[InstanceClause<C, T>] {
        &self.front
    }

    /// Returns the back instances of a List collection in emission order.
    #[must_use]
    pub fn back(&self) -> &[InstanceClause<C, T>] {
        &self.back
    }

    /// Returns every instance, front then back.
    pub fn instances(&self) -> impl Iterator<Item = &InstanceClause<C, T>> {
        self.front.iter().chain(&self.back)
    }

    /// Whether the other instances are framed.
    #[must_use]
    pub const fn is_open(&self) -> bool {
        self.open
    }
}

/// One clause of a simultaneous configuration rewrite.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "clause_kind", rename_all = "snake_case")]
pub enum ConfigurationClause<C, T> {
    /// One exactly-once cell: leaf content or a whole group.
    Fixed(FixedCellClause<C, T>),
    /// One optional (`?`) cell (KF-023).
    Optional(OptionalCellClause<C, T>),
    /// Instances of one collection (`*`) cell (KF-023).
    Instances(InstancesClause<C, T>),
}

impl<C, T> ConfigurationClause<C, T> {
    /// Returns the selected cell.
    #[must_use]
    pub const fn cell(&self) -> &C {
        match self {
            Self::Fixed(clause) => clause.cell(),
            Self::Optional(clause) => clause.cell(),
            Self::Instances(clause) => clause.cell(),
        }
    }

    /// Returns clause provenance.
    #[must_use]
    pub const fn origin(&self) -> &NodeOrigin {
        match self {
            Self::Fixed(clause) => clause.origin(),
            Self::Optional(clause) => clause.origin(),
            Self::Instances(clause) => clause.origin(),
        }
    }

    /// Returns the exactly-once clause, if this is one.
    #[must_use]
    pub const fn as_fixed(&self) -> Option<&FixedCellClause<C, T>> {
        match self {
            Self::Fixed(clause) => Some(clause),
            Self::Optional(_) | Self::Instances(_) => None,
        }
    }
}

/// The post-state of one matched cell in a [`ClausePart`].
#[derive(Clone, Copy, Debug)]
pub enum PartPost<'a, T> {
    /// Matched and unchanged.
    Preserve,
    /// Replaced by this term.
    Replace(&'a T),
    /// Rewritten in place by the `k::rewrite!` below its pattern (KF-011).
    Local,
    /// Removed: an optional cell or a collection instance the rule deletes.
    Removed,
}

/// One cell-level part of a configuration clause (KF-023): a matched cell
/// (a fixed clause, a present optional cell, a child of a matched instance)
/// or a cell the rule creates (an optional cell absent before, a child of a
/// created instance).
#[derive(Clone, Copy, Debug)]
pub enum ClausePart<'a, C, T> {
    /// A matched cell with its pattern, post-state, and frame.
    Matched {
        /// The cell.
        cell: &'a C,
        /// Leaf content or a whole group.
        kind: CellClauseKind,
        /// The pattern.
        before: &'a T,
        /// What the rule does to it.
        after: PartPost<'a, T>,
        /// The pattern's content frame.
        frame: &'a CellContentFrame,
    },
    /// A cell the rule creates, with its content.
    Written {
        /// The cell.
        cell: &'a C,
        /// Leaf content or a whole group.
        kind: CellClauseKind,
        /// The created content.
        term: &'a T,
    },
}

impl<'a, C, T> ClausePart<'a, C, T> {
    /// The terms the part matches (left side).
    #[must_use]
    pub fn pre_term(&self) -> Option<&'a T> {
        match self {
            Self::Matched { before, .. } => Some(before),
            Self::Written { .. } => None,
        }
    }

    /// The term the part writes (right side), if any.
    #[must_use]
    pub fn post_term(&self) -> Option<&'a T> {
        match self {
            Self::Matched {
                after: PartPost::Replace(term),
                ..
            }
            | Self::Written { term, .. } => Some(term),
            Self::Matched { .. } => None,
        }
    }

    /// Every term of the part, pattern first.
    #[must_use]
    pub fn terms(&self) -> Vec<&'a T> {
        self.pre_term()
            .into_iter()
            .chain(self.post_term())
            .collect()
    }

    /// The pattern's frame of a matched part.
    #[must_use]
    pub fn frame(&self) -> Option<&'a CellContentFrame> {
        match self {
            Self::Matched { frame, .. } => Some(frame),
            Self::Written { .. } => None,
        }
    }
}

impl<C, T> ConfigurationClause<C, T> {
    /// The clause's cell-level parts in authored order: one for a fixed or
    /// optional clause, one per mentioned child of each instance for a
    /// collection clause (KF-023).
    #[must_use]
    pub fn parts(&self) -> Vec<ClausePart<'_, C, T>> {
        fn fixed<C, T>(clause: &FixedCellClause<C, T>) -> ClausePart<'_, C, T> {
            ClausePart::Matched {
                cell: clause.cell(),
                kind: clause.kind(),
                before: clause.before(),
                after: match clause.after() {
                    CellPost::Preserve => PartPost::Preserve,
                    CellPost::Replace { term } => PartPost::Replace(term),
                    CellPost::Local => PartPost::Local,
                },
                frame: clause.frame(),
            }
        }
        match self {
            Self::Fixed(clause) => vec![fixed(clause)],
            Self::Optional(clause) => match (clause.before(), clause.after()) {
                (Presence::Present { term }, after) => vec![ClausePart::Matched {
                    cell: clause.cell(),
                    kind: clause.kind(),
                    before: term,
                    after: match after {
                        None => PartPost::Preserve,
                        Some(Presence::Present { term }) => PartPost::Replace(term),
                        Some(Presence::Absent) => PartPost::Removed,
                    },
                    frame: clause.frame(),
                }],
                (Presence::Absent, Some(Presence::Present { term })) => {
                    vec![ClausePart::Written {
                        cell: clause.cell(),
                        kind: clause.kind(),
                        term,
                    }]
                }
                (Presence::Absent, _) => Vec::new(),
            },
            Self::Instances(clause) => clause
                .instances()
                .flat_map(|instance| match instance {
                    InstanceClause::Kept { children, .. } => {
                        children.iter().map(fixed).collect::<Vec<_>>()
                    }
                    InstanceClause::Removed { children, .. } => children
                        .iter()
                        .map(|child| ClausePart::Matched {
                            cell: child.cell(),
                            kind: child.kind(),
                            before: child.term(),
                            after: PartPost::Removed,
                            frame: child.frame(),
                        })
                        .collect(),
                    InstanceClause::Created { children, .. } => children
                        .iter()
                        .map(|child| ClausePart::Written {
                            cell: child.cell(),
                            kind: child.kind(),
                            term: child.term(),
                        })
                        .collect(),
                })
                .collect(),
        }
    }
}

impl<C, T> From<FixedCellClause<C, T>> for ConfigurationClause<C, T> {
    fn from(clause: FixedCellClause<C, T>) -> Self {
        Self::Fixed(clause)
    }
}

/// One simultaneous fixed-configuration rewrite.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedConfigurationRewrite<C, T> {
    origin: NodeOrigin,
    configuration: SemanticId,
    clauses: Vec<ConfigurationClause<C, T>>,
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
        clauses: Vec<impl Into<ConfigurationClause<C, T>>>,
        omitted_siblings: Vec<C>,
    ) -> Result<Self, StateShapeError> {
        let clauses = clauses.into_iter().map(Into::into).collect::<Vec<_>>();
        if clauses.is_empty() {
            return Err(StateShapeError::EmptyCollection(
                crate::IrField::ConfigurationRewriteClauses,
            ));
        }
        let mut mentioned = BTreeSet::new();
        for clause in &clauses {
            if !mentioned.insert(clause.cell().clone()) {
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
    pub fn clauses(&self) -> &[ConfigurationClause<C, T>] {
        &self.clauses
    }

    /// Returns the exactly-once clauses in authored order.
    pub fn fixed_clauses(&self) -> impl Iterator<Item = &FixedCellClause<C, T>> {
        self.clauses
            .iter()
            .filter_map(ConfigurationClause::as_fixed)
    }

    /// Returns every cell-level part of every clause in authored order.
    #[must_use]
    pub fn parts(&self) -> Vec<ClausePart<'_, C, T>> {
        self.clauses
            .iter()
            .flat_map(ConfigurationClause::parts)
            .collect()
    }

    /// Returns explicitly framed unmentioned leaf cells.
    #[must_use]
    pub fn omitted_siblings(&self) -> &[C] {
        &self.omitted_siblings
    }
}

/// Locally invalid fixed-state structure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StateShapeError {
    /// Textual metadata was blank.
    EmptyText(crate::IrField),
    /// A mandatory ordered collection was empty.
    EmptyCollection(crate::IrField),
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
                    "configuration variable {id} occurs more than once"
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

fn checked_text(field: crate::IrField, value: String) -> Result<String, StateShapeError> {
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
