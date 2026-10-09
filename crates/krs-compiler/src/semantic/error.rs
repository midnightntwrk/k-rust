use std::error::Error;
use std::fmt;

use krs_diagnostic::{Diagnostic, Location, ToDiagnostic, codes};
use krs_ir::{BuiltinSort, IrIdentityError, ItemKind, SourceRange, StableItemId};
use krs_ir_levels::SemanticValidationError;

/// The lexical rule a definition breaks (KF-004).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LexicalProblem {
    /// A lexical name is declared twice.
    Duplicate,
    /// A regex refers to a `{Name}` no lexical declares.
    Undefined,
    /// Lexicals refer to each other in a cycle.
    Recursive,
}

/// The fresh-value rule a definition breaks (KF-022).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FreshProblem {
    /// A `#[k::fresh]` binder's sort has no `fresh_generator` function.
    NoGenerator,
    /// A sort has more than one `fresh_generator` function.
    DuplicateGenerator,
    /// A `fresh_generator` function is not total, does not take exactly one
    /// Int argument, or returns a sort it cannot generate.
    InvalidGenerator,
}

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
    /// An `overload` key relates productions K cannot treat as one family.
    InvalidOverload {
        /// Production that carries the key.
        production: Box<StableItemId>,
        /// Stable reason naming both productions.
        reason: String,
        /// Sole exact authored range of the target path.
        range: Option<Box<SourceRange>>,
    },
    /// An author spec module breaks a K proof-module rule (KF-041).
    InvalidSpecModule {
        /// The spec module, or the item the diagnostic is about.
        item: Box<StableItemId>,
        /// Complete reason naming the fix.
        reason: String,
        /// Sole exact authored range of the offending occurrence.
        range: Option<Box<SourceRange>>,
    },
    /// A claim names a private production, which its proof module cannot see.
    PrivateProductionInSpec {
        /// The private production.
        production: Box<StableItemId>,
        /// The claim that names it.
        claim: Box<StableItemId>,
        /// Sole exact authored range of the claim.
        range: Option<Box<SourceRange>>,
    },
    /// A readable rule without the computation cell changes no cell (KF-015).
    RuleChangesNoCell {
        /// The rule.
        rule: Box<StableItemId>,
        /// Sole exact authored range of the rule's subject record.
        range: Option<Box<SourceRange>>,
    },
    /// A rule selects a nested (group) cell together with a cell below it
    /// (KF-016).
    GroupAndDescendant {
        /// The rule.
        rule: Box<StableItemId>,
        /// Rust field of the selected group cell.
        group: String,
        /// Rust field of the selected cell below it.
        descendant: String,
        /// Sole exact authored range of the rule's subject.
        range: Option<Box<SourceRange>>,
    },
    /// One nominal `#[k::cell]` declaration is the content of two cell
    /// fields, so its generated cell sort is ambiguous (KF-016).
    AmbiguousCellSort {
        /// The nested cell declaration.
        declaration: Box<StableItemId>,
        /// Rust fields whose content it is, in declaration order.
        fields: Vec<String>,
        /// Sole exact authored range of the second field.
        range: Option<Box<SourceRange>>,
    },
    /// A readable rule without the computation cell matches every
    /// configuration, so execution never terminates (KF-015).
    AlwaysEnabledRule {
        /// The rule.
        rule: Box<StableItemId>,
        /// Sole exact authored range of the rule's subject record.
        range: Option<Box<SourceRange>>,
    },
    /// A `k::is!` or `k::project!` term is matched or projects into `K` (KF-013).
    InvalidSortTest {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the fix.
        reason: String,
        /// Sole exact authored range of the offending occurrence.
        range: Option<Box<SourceRange>>,
    },
    /// A typed binder's declared sort is not below the sort one of its
    /// occurrences needs (KF-009).
    IncompatibleBinder {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the binder and both sorts.
        reason: String,
        /// Sole exact authored range of the binder's declared type.
        range: Option<Box<SourceRange>>,
    },
    /// A token sort, token alias, or `k::lexeme!` term is not well formed (KF-003).
    InvalidTokenSort {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the sort and the fix.
        reason: String,
        /// Sole exact authored range of the offending occurrence.
        range: Option<Box<SourceRange>>,
    },
    /// A `#[k::syntax_list]` sort is used in a way K's `List{}` forbids
    /// (KF-020).
    InvalidSyntaxList {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the list and the fix.
        reason: String,
        /// Sole exact authored range of the offending occurrence.
        range: Option<Box<SourceRange>>,
    },
    /// A `k::lexical!` name or a `{Name}` regex reference is invalid (KF-004).
    InvalidLexical {
        /// Which rule the definition breaks.
        problem: LexicalProblem,
        /// Stable reason naming the lexical and the fix.
        reason: String,
        /// Sole exact authored range of the offending declaration.
        range: Option<Box<SourceRange>>,
    },
    /// A fresh binder's sort has no usable generator, or a generator is
    /// malformed or repeated (KF-022).
    InvalidFresh {
        /// Which rule the definition breaks.
        problem: FreshProblem,
        /// Stable reason naming the sort or function and the fix.
        reason: String,
        /// Sole exact authored range of the offending binder or function.
        range: Option<Box<SourceRange>>,
    },
    /// A `concrete` or `symbolic` key names no left-hand binder, restricts one
    /// binder both ways, or is inconsistent across a function's equations (KF-043).
    InvalidMatchRestriction {
        /// Stable reason naming the binder or function and the fix.
        reason: String,
        /// Sole exact authored range of the offending key or binder.
        range: Option<Box<SourceRange>>,
    },
    /// An alias or desugar clause does not expand a production of its own
    /// mode, or a desugar production has no clause (KF-028).
    InvalidStaticClause {
        /// Stable reason naming the clause or production and the fix.
        reason: String,
        /// Sole exact authored range of the clause name or production marker.
        range: Option<Box<SourceRange>>,
    },
    /// An `smt_lemma` mentions a function Z3 cannot see (KF-043).
    SmtLemmaUntranslatable {
        /// Stable reason naming the function and the fix.
        reason: String,
        /// Sole exact authored range of the `smt_lemma` flag.
        range: Option<Box<SourceRange>>,
    },
    /// Two functions declare the same `smtlib` symbol (KF-044).
    DuplicateSmtlib {
        /// Stable reason naming the symbol and both functions.
        reason: String,
        /// Sole exact authored range of the second declaration.
        range: Option<Box<SourceRange>>,
    },
    /// A `stream` or `exit` cell does not have the shape K requires (KF-035).
    InvalidConsoleCell {
        /// Stable reason naming the cell.
        reason: String,
        /// Sole exact authored range of the offending attribute.
        range: Option<Box<SourceRange>>,
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
    #[expect(
        clippy::too_many_lines,
        reason = "One arm per lowering error keeps every message beside its variant."
    )]
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
            Self::InvalidOverload { reason, .. } => {
                write!(formatter, "invalid `overload`: {reason}")
            }
            Self::PrivateProductionInSpec { production, .. } => {
                formatter.write_str(&super::visibility::private_production_message(production))
            }
            Self::RuleChangesNoCell { rule, .. } => write!(
                formatter,
                "rule `{}` changes no cell: every cell it names keeps its content and it leaves the computation cell out, so applying it changes nothing",
                rule.item_name()
            ),
            Self::GroupAndDescendant {
                rule,
                group,
                descendant,
                ..
            } => write!(
                formatter,
                "rule `{}` selects the nested cell `{group}` and the cell `{descendant}` inside it; the whole-cell entry `{group}` already names every cell below it, so select one or the other",
                rule.item_name()
            ),
            Self::AmbiguousCellSort {
                declaration,
                fields,
                ..
            } => write!(
                formatter,
                "cell declaration `{}` is the content of more than one cell field ({}), so its K cell sort is ambiguous; declare one struct per nested cell",
                declaration.item_name(),
                quoted_fields(fields)
            ),
            Self::AlwaysEnabledRule { rule, .. } => write!(
                formatter,
                "rule `{}` is always enabled, so execution never terminates: it leaves the computation cell out, every cell pattern is a variable or `_` of the cell's sort, and it has no requires guard",
                rule.item_name()
            ),
            Self::InvalidSpecModule { reason, .. }
            | Self::InvalidTokenSort { reason, .. }
            | Self::InvalidSortTest { reason, .. }
            | Self::IncompatibleBinder { reason, .. }
            | Self::InvalidLexical { reason, .. }
            | Self::InvalidFresh { reason, .. }
            | Self::DuplicateSmtlib { reason, .. }
            | Self::InvalidMatchRestriction { reason, .. }
            | Self::InvalidStaticClause { reason, .. }
            | Self::SmtLemmaUntranslatable { reason, .. }
            | Self::InvalidSyntaxList { reason, .. }
            | Self::InvalidConsoleCell { reason, .. } => formatter.write_str(reason),
            Self::InvalidGeneratedIdentity(detail) => formatter.write_str(detail),
            Self::InvalidSemanticTheory(error) => error.fmt(formatter),
        }
    }
}

/// Backquotes each Rust field name and joins them with commas.
fn quoted_fields(fields: &[String]) -> String {
    fields
        .iter()
        .map(|field| format!("`{field}`"))
        .collect::<Vec<_>>()
        .join(", ")
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
            Self::InvalidOverload { .. } => codes::analysis::INVALID_OVERLOAD,
            Self::PrivateProductionInSpec { .. } => codes::analysis::PRIVATE_PRODUCTION_IN_SPEC,
            Self::InvalidSpecModule { .. } => codes::analysis::INVALID_SPEC_MODULE,
            Self::RuleChangesNoCell { .. } => codes::analysis::RULE_CHANGES_NO_CELL,
            Self::AlwaysEnabledRule { .. } => codes::analysis::ALWAYS_ENABLED_RULE,
            Self::GroupAndDescendant { .. } => codes::analysis::GROUP_AND_DESCENDANT,
            Self::AmbiguousCellSort { .. } => codes::analysis::AMBIGUOUS_CELL_SORT,
            Self::InvalidTokenSort { .. } => codes::analysis::INVALID_TOKEN_SORT,
            Self::InvalidSortTest { .. } => codes::analysis::INVALID_SORT_TEST,
            Self::IncompatibleBinder { .. } => codes::analysis::INCOMPATIBLE_BINDER,
            Self::InvalidSyntaxList { .. } => codes::analysis::INVALID_SYNTAX_LIST,
            Self::InvalidLexical { problem, .. } => match problem {
                LexicalProblem::Duplicate => codes::analysis::DUPLICATE_LEXICAL,
                LexicalProblem::Undefined => codes::analysis::UNDEFINED_LEXICAL,
                LexicalProblem::Recursive => codes::analysis::RECURSIVE_LEXICAL,
            },
            Self::InvalidConsoleCell { .. } => codes::analysis::CONSOLE_CELL,
            Self::InvalidFresh { problem, .. } => match problem {
                FreshProblem::NoGenerator => codes::analysis::NO_FRESH_GENERATOR,
                FreshProblem::DuplicateGenerator => codes::analysis::DUPLICATE_FRESH_GENERATOR,
                FreshProblem::InvalidGenerator => codes::analysis::INVALID_FRESH_GENERATOR,
            },
            Self::DuplicateSmtlib { .. } => codes::analysis::DUPLICATE_SMTLIB,
            Self::InvalidMatchRestriction { .. } => codes::analysis::INVALID_MATCH_RESTRICTION,
            Self::SmtLemmaUntranslatable { .. } => codes::analysis::SMT_LEMMA_UNTRANSLATABLE,
            Self::InvalidStaticClause { .. } => codes::analysis::INVALID_STATIC_CLAUSE,
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
            Self::NondetGroup { range, .. }
            | Self::InvalidOverload { range, .. }
            | Self::PrivateProductionInSpec { range, .. }
            | Self::InvalidSpecModule { range, .. }
            | Self::RuleChangesNoCell { range, .. }
            | Self::AlwaysEnabledRule { range, .. }
            | Self::GroupAndDescendant { range, .. }
            | Self::AmbiguousCellSort { range, .. }
            | Self::InvalidTokenSort { range, .. }
            | Self::InvalidSortTest { range, .. }
            | Self::IncompatibleBinder { range, .. }
            | Self::InvalidSyntaxList { range, .. }
            | Self::InvalidLexical { range, .. }
            | Self::InvalidFresh { range, .. }
            | Self::DuplicateSmtlib { range, .. }
            | Self::InvalidMatchRestriction { range, .. }
            | Self::InvalidStaticClause { range, .. }
            | Self::SmtLemmaUntranslatable { range, .. }
            | Self::InvalidConsoleCell { range, .. } => range
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
            Self::PrivateProductionInSpec { claim, .. } => {
                diagnostic.with_note(format!("claim: {claim}"))
            }
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
