use std::error::Error;
use std::fmt;

use krs_ir::{IrIdentityError, ItemKind, SemanticValidationError, StableItemId};

/// Typed failure at the sole descriptor-bundle to semantic-theory boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DescriptorLoweringError {
    /// Two descriptors claim one stable identity.
    DuplicateItemId(Box<StableItemId>),
    /// Lowering requires exactly one selected configuration descriptor.
    ConfigurationCount(usize),
    /// A descriptor payload and stable item kind disagree.
    WrongItemKind {
        /// Offending stable item.
        id: Box<StableItemId>,
        /// Kind required by the payload.
        expected: ItemKind,
        /// Kind present in the item identity.
        actual: ItemKind,
    },
    /// A stable reference names no selected descriptor.
    DanglingReference(Box<StableItemId>),
    /// A reference or term uses a declaration in the wrong namespace.
    ReferenceKindMismatch {
        /// Referenced stable item.
        id: Box<StableItemId>,
        /// Required namespace.
        expected: ItemKind,
        /// Actual namespace.
        actual: ItemKind,
    },
    /// A required parser-keyed origin or reference was absent or unexpected.
    ParserReferenceDisagreement {
        /// Descriptor being lowered.
        id: Box<StableItemId>,
        /// Stable diagnostic detail.
        detail: String,
    },
    /// The term could not be represented structurally.
    InvalidTerm {
        /// Descriptor containing the term.
        id: Box<StableItemId>,
        /// Stable diagnostic detail.
        detail: String,
    },
    /// The descriptor graph is outside the supported shape.
    UnsupportedShape {
        /// Semantic node family.
        node: &'static str,
        /// Stable diagnostic detail.
        detail: String,
    },
    /// Two readable head-rule patterns can match one configuration state.
    OverlappingRules {
        /// First rule in deterministic stable-identity order.
        first: Box<StableItemId>,
        /// Second rule in deterministic stable-identity order.
        second: Box<StableItemId>,
    },
    /// A compiler-generated module, semantic, or source-map identity was invalid.
    InvalidGeneratedIdentity(String),
    /// Whole-theory validation rejected the constructed graph.
    InvalidSemanticTheory(SemanticValidationError),
}

impl fmt::Display for DescriptorLoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateItemId(id) => write!(formatter, "duplicate stable descriptor {id:?}"),
            Self::ConfigurationCount(count) => write!(
                formatter,
                "descriptor bundle requires exactly one configuration, found {count}"
            ),
            Self::WrongItemKind {
                id,
                expected,
                actual,
            }
            | Self::ReferenceKindMismatch {
                id,
                expected,
                actual,
            } => write!(
                formatter,
                "descriptor reference {id:?} has kind {actual:?}, expected {expected:?}"
            ),
            Self::DanglingReference(id) => {
                write!(formatter, "dangling descriptor reference {id:?}")
            }
            Self::ParserReferenceDisagreement { id, detail } => write!(
                formatter,
                "parser/reference disagreement for {id:?}: {detail}"
            ),
            Self::InvalidTerm { id, detail } => {
                write!(formatter, "invalid descriptor term for {id:?}: {detail}")
            }
            Self::UnsupportedShape { node, detail } => {
                write!(formatter, "unsupported {node}: {detail}")
            }
            Self::OverlappingRules { first, second } => write!(
                formatter,
                "readable rules {first:?} and {second:?} have overlapping left-hand patterns at the same priority; refine a pattern, add disjoint `where` sorts, or mark the fallback `#[k::rule(owise)]`"
            ),
            Self::InvalidGeneratedIdentity(detail) => formatter.write_str(detail),
            Self::InvalidSemanticTheory(error) => error.fmt(formatter),
        }
    }
}

impl Error for DescriptorLoweringError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::InvalidSemanticTheory(error) => Some(error),
            _ => None,
        }
    }
}

impl From<IrIdentityError> for DescriptorLoweringError {
    fn from(error: IrIdentityError) -> Self {
        Self::InvalidGeneratedIdentity(error.to_string())
    }
}

impl From<SemanticValidationError> for DescriptorLoweringError {
    fn from(error: SemanticValidationError) -> Self {
        Self::InvalidSemanticTheory(error)
    }
}

impl From<krs_ir::StateShapeError> for DescriptorLoweringError {
    fn from(error: krs_ir::StateShapeError) -> Self {
        Self::UnsupportedShape {
            node: "fixed configuration",
            detail: error.to_string(),
        }
    }
}
