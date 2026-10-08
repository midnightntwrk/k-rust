use std::error::Error;
use std::fmt;

use krs_diagnostic::{Diagnostic, Location, ToDiagnostic, codes};
use krs_ir::{BuiltinSort, IrIdentityError, ItemKind, SourceRange, StableItemId};
use krs_ir_levels::SemanticValidationError;

/// Typed failure at the sole descriptor-bundle to semantic-theory boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DescriptorLoweringError {
    /// An authored sort would emit the name of a compiler builtin sort.
    BuiltinSortNameCollision {
        /// Offending authored sort.
        id: Box<StableItemId>,
        /// Compiler builtin sort to use.
        builtin: BuiltinSort,
    },
    /// Lowering requires exactly one selected configuration descriptor.
    ConfigurationCount(usize),
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
        /// Sole exact authored range of the second rule's application head.
        second_head_range: Option<Box<SourceRange>>,
    },
    /// A `nondet = group` key is not a valid nondeterminism group.
    NondetGroup {
        /// The rule the diagnostic points at.
        rule: Box<StableItemId>,
        /// Exact authored range of that rule's subject head or name.
        range: Option<Box<SourceRange>>,
        /// What is wrong with the group.
        problem: NondetGroupProblem,
    },
    /// A compiler-generated module, semantic, or source-map identity was invalid.
    InvalidGeneratedIdentity(String),
    /// Whole-theory validation rejected the constructed graph.
    InvalidSemanticTheory(SemanticValidationError),
}

/// How a `nondet = group` key fails group validation (F2 amendment, clause 3).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NondetGroupProblem {
    /// The group has one rule.
    SingleMember {
        /// Authored group identifier.
        group: String,
    },
    /// The rule overlaps no other rule of its group.
    StaleMember {
        /// Authored group identifier.
        group: String,
    },
    /// The group's rules have different priorities.
    MixedPriorities {
        /// Authored group identifier.
        group: String,
        /// The first rule's priority and the differing one.
        priorities: (u32, u32),
    },
}

impl fmt::Display for DescriptorLoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BuiltinSortNameCollision { id, builtin } => write!(
                formatter,
                "declared sort {id} has K name `{}`; use `k::builtin::{}` instead",
                builtin.k_name(),
                builtin.marker_name()
            ),
            Self::ConfigurationCount(count) => write!(
                formatter,
                "descriptor bundle requires exactly one configuration, found {count}"
            ),
            Self::ReferenceKindMismatch {
                id,
                expected,
                actual,
            } => write!(
                formatter,
                "descriptor reference {id} has kind {actual}, expected {expected}"
            ),
            Self::DanglingReference(id) => {
                write!(formatter, "dangling descriptor reference {id}")
            }
            Self::ParserReferenceDisagreement { id, detail } => write!(
                formatter,
                "parser/reference disagreement for {id}: {detail}"
            ),
            Self::InvalidTerm { id, detail } => {
                write!(formatter, "invalid descriptor term for {id}: {detail}")
            }
            Self::UnsupportedShape { node, detail } => {
                write!(formatter, "unsupported {node}: {detail}")
            }
            Self::OverlappingRules { first, second, .. } => write!(
                formatter,
                "rules `{}` and `{}` can both apply to the same configuration at the same priority; K would take either one (nondeterminism). If that is intended, put both in one group with `#[k::rule(nondet = NAME)]`; otherwise refine a pattern, add disjoint `where` sorts or complementary requires guards, or order them with `owise` or `priority = N`.",
                first.item_name(),
                second.item_name()
            ),
            Self::NondetGroup { rule, problem, .. } => match problem {
                NondetGroupProblem::SingleMember { group } => {
                    write!(formatter, "nondet group `{group}` has only one rule")
                }
                NondetGroupProblem::StaleMember { group } => write!(
                    formatter,
                    "rule `{}` is in nondet group `{group}` but overlaps no other rule of the group",
                    rule.item_name()
                ),
                NondetGroupProblem::MixedPriorities {
                    group,
                    priorities: (first, second),
                } => write!(
                    formatter,
                    "nondet group `{group}` mixes priorities {first} and {second}; rules at different priorities never compete"
                ),
            },
            Self::InvalidGeneratedIdentity(detail) => formatter.write_str(detail),
            Self::InvalidSemanticTheory(error) => error.fmt(formatter),
        }
    }
}

impl ToDiagnostic for DescriptorLoweringError {
    fn to_diagnostic(&self) -> Diagnostic {
        let code = match self {
            Self::BuiltinSortNameCollision { .. } => codes::analysis::BUILTIN_SORT_NAME_COLLISION,
            Self::ConfigurationCount(_) => codes::analysis::CONFIGURATION_COUNT,
            Self::DanglingReference(_) => codes::analysis::DANGLING_REFERENCE,
            Self::ReferenceKindMismatch { .. } => codes::analysis::REFERENCE_KIND_MISMATCH,
            Self::ParserReferenceDisagreement { .. } => {
                codes::analysis::PARSER_REFERENCE_DISAGREEMENT
            }
            Self::InvalidTerm { .. } => codes::analysis::INVALID_TERM,
            Self::UnsupportedShape { .. } => codes::analysis::UNSUPPORTED_SHAPE,
            Self::OverlappingRules { .. } => codes::analysis::OVERLAPPING_RULE_HEADS,
            Self::NondetGroup { .. } => codes::analysis::NONDET_GROUP,
            Self::InvalidGeneratedIdentity(_) => codes::analysis::INVALID_GENERATED_IDENTITY,
            Self::InvalidSemanticTheory(_) => codes::analysis::INVALID_SEMANTIC_THEORY,
        };
        let location = match self {
            Self::OverlappingRules {
                second_head_range, ..
            } => second_head_range
                .as_deref()
                .cloned()
                .map_or(Location::None, Location::Source),
            Self::NondetGroup { range, .. } => range
                .as_deref()
                .cloned()
                .map_or(Location::None, Location::Source),
            _ => Location::None,
        };
        let diagnostic = Diagnostic::error(code, self.to_string(), location);
        match self {
            Self::OverlappingRules { first, second, .. } => diagnostic
                .with_note(format!("first rule: {first}"))
                .with_note(format!("second rule: {second}")),
            Self::NondetGroup { rule, .. } => diagnostic.with_note(format!("rule: {rule}")),
            _ => diagnostic,
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

impl From<krs_ir::LookupError> for DescriptorLoweringError {
    fn from(error: krs_ir::LookupError) -> Self {
        match error {
            krs_ir::LookupError::Missing { id } => Self::DanglingReference(id),
            krs_ir::LookupError::WrongKind {
                id,
                expected,
                actual,
            } => Self::ReferenceKindMismatch {
                id,
                expected,
                actual,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn overlapping_rules_own_the_code_head_range_and_ordered_notes() {
        let first = krs_ir::testing::item("rules", "first", ItemKind::Rule);
        let second = krs_ir::testing::item("rules", "second", ItemKind::Rule);
        let range = krs_ir::testing::authored(3, 8)
            .exact_authored_range()
            .unwrap();
        let error = DescriptorLoweringError::OverlappingRules {
            first: Box::new(first.clone()),
            second: Box::new(second.clone()),
            second_head_range: Some(Box::new(range.clone())),
        };
        let diagnostic = error.to_diagnostic();
        assert_eq!(diagnostic.code, codes::analysis::OVERLAPPING_RULE_HEADS);
        assert_eq!(diagnostic.message, error.to_string());
        let Location::Source(actual) = diagnostic.primary.location else {
            panic!("missing overlap application head range");
        };
        assert_eq!(actual, range);
        assert_eq!(
            diagnostic.notes,
            [
                format!("first rule: {first}"),
                format!("second rule: {second}"),
            ]
        );
    }
}
