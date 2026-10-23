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

/// How an operator (`a + b`) fails to denote one builtin operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OperatorProblem {
    /// The operands' sorts choose no builtin domain, or two.
    Ambiguous,
    /// The chosen domain defines no such operation (`&` on `Bool`).
    Undefined,
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
        /// The innermost enclosing term with an exact authored range.
        range: Option<Box<krs_ir::SourceRange>>,
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
    /// Two equations of one function at one priority apply to one argument
    /// and give it different results.
    OverlappingEquations {
        /// The function, rendered.
        function: String,
        /// First equation in deterministic stable-identity order.
        first: Box<StableItemId>,
        /// Second equation in deterministic stable-identity order.
        second: Box<StableItemId>,
        /// The application both apply to, rendered.
        application: String,
        /// The first and the second equation's result there, rendered.
        results: Box<(String, String)>,
        /// Sole exact authored range of the second equation's head.
        second_head_range: Option<Box<SourceRange>>,
    },
    /// Two arms of one function shorthand body's `match` both apply to one
    /// argument and give it different results.
    OverlappingMatchArms {
        /// The function, rendered.
        function: String,
        /// First arm's equation in deterministic stable-identity order.
        first: Box<StableItemId>,
        /// Second arm's equation in deterministic stable-identity order.
        second: Box<StableItemId>,
        /// The application both apply to, rendered.
        application: String,
        /// The first and the second arm's result there, rendered.
        results: Box<(String, String)>,
        /// The exact authored ranges of the first and the second arm.
        arms: Box<(SourceRange, SourceRange)>,
    },
    /// Two alternatives of one `A | B` or-pattern can match the same term with
    /// different bindings (F2 amendment clause 8, KF-030).
    AmbiguousOrPattern {
        /// The sentence with the or-pattern.
        rule: Box<StableItemId>,
        /// The first alternative, rendered.
        first: String,
        /// The second alternative, rendered.
        second: String,
        /// Sole exact authored range of the or-pattern.
        range: Option<Box<SourceRange>>,
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
    /// A constructor family without a `#[k::precedence]` chain has a variant
    /// that can sit directly at the edge of another of its variants, where a
    /// chain decides how they parse.
    MissingPrecedenceChain {
        /// Complete reason naming the family and every such variant.
        reason: String,
        /// Sole exact authored range of the first such variant.
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
    /// A claim, or any sentence of a spec module, names a private production,
    /// which its proof module cannot see.
    PrivateProductionInSpec {
        /// The private production.
        production: Box<StableItemId>,
        /// The claim or spec-module sentence that names it.
        sentence: Box<StableItemId>,
        /// How the note names the sentence (`claim`, `simplification lemma`).
        kind: &'static str,
        /// The author spec module holding the sentence; `None` for a claim in
        /// the generated `<MAIN>-SPEC`.
        module: Option<Box<str>>,
        /// Sole exact authored range of the sentence.
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
    /// A `k::bits!` template, which matches an `Int`, stands at a position
    /// of a sort neither `Int` nor above it.
    BitTemplateSort {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the position's sort.
        reason: String,
        /// Sole exact authored range of the template.
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
    /// A term at a typed collection position (`Map<K, V>`, `List<T>`,
    /// `Set<T>`) does not fit its element types, a read asks for a sort the
    /// collection never holds, or a collection type has the wrong number of
    /// arguments.
    CollectionElementSort {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the position, its declared type, and the term.
        reason: String,
        /// Sole exact authored range of the offending term.
        range: Option<Box<SourceRange>>,
    },
    /// A `name @ pattern` (K's `#as`) reaches a position that is not a
    /// pattern, or its alias needs a sort its pattern does not have (KF-029).
    InvalidPatternAs {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the alias.
        reason: String,
        /// Sole exact authored range of the `name @ pattern`.
        range: Option<Box<SourceRange>>,
    },
    /// A record update `Ctor { f: e, ..t }` (F5) whose base is not the alias
    /// of one record of the same constructor or cell in the left-hand side.
    InvalidRecordUpdate {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the base.
        reason: String,
        /// Sole exact authored range of the base or the alias.
        range: Option<Box<SourceRange>>,
    },
    /// An `A | B` or-pattern (K's `#Or`) reaches a position that is not a
    /// pattern, or its alternatives bind a name at different sorts (KF-030).
    InvalidPatternOr {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason.
        reason: String,
        /// Sole exact authored range of the or-pattern.
        range: Option<Box<SourceRange>>,
    },
    /// An operator's operands choose no single builtin domain, or the domain
    /// they choose does not define the operator.
    InvalidOperator {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Which of the two failures it is.
        problem: OperatorProblem,
        /// Stable reason, naming the calls to write instead.
        reason: String,
        /// Sole exact authored range of the operator.
        range: Option<Box<SourceRange>>,
    },
    /// A `k::matches!` (K's `:=K`) pattern name shadows a rule binder or is
    /// read once, or its pattern cannot meet its subject's sort (KF-031).
    InvalidMatches {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason.
        reason: String,
        /// Sole exact authored range of the offending name or term.
        range: Option<Box<SourceRange>>,
    },
    /// A `let` statement's (K's `#let`) pattern cannot meet its value's sort,
    /// one of its names has no single sort, or a let-bound name is used at a
    /// sort it does not have (KF-032).
    InvalidLet {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason.
        reason: String,
        /// Sole exact authored range of the offending statement or name.
        range: Option<Box<SourceRange>>,
    },
    /// A matching-logic predicate (KF-039) is in the condition of a
    /// transition or equation.
    MlPlacement {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason.
        reason: String,
        /// Sole exact authored range of the offending predicate.
        range: Option<Box<SourceRange>>,
    },
    /// A matching-logic predicate (KF-039) is malformed: a connective as an
    /// object operand, a Bool where a predicate is expected, `ml::equals`
    /// operands without a common sort, a predicate simplification rooted
    /// elsewhere than `ml::equals` or `ml::ceil`, a wrong arity, or an
    /// `ml::exists` binder that shadows a rule binder.
    InvalidMlPredicate {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason.
        reason: String,
        /// Sole exact authored range of the offending node.
        range: Option<Box<SourceRange>>,
    },
    /// A single-body rule (`k::rewrite!`, KF-011) changes no cell, or a
    /// rewrite's sides have no sort in common.
    InvalidLocalRewrite {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason.
        reason: String,
        /// Sole exact authored range of the offending rewrite or rule.
        range: Option<Box<SourceRange>>,
    },
    /// An equation's function context names a cell shape it cannot read, or
    /// declares a binder at a sort its cell does not have (KF-025).
    InvalidFunctionContext {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason.
        reason: String,
        /// Sole exact authored range of the offending cell or binder.
        range: Option<Box<SourceRange>>,
    },
    /// A parametric production (K's `syntax {S}`) names a parameter like a
    /// sort, or carries strictness, an alias, a hook, a token, or a bracket
    /// (KF-027).
    InvalidParametricProduction {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the fix.
        reason: String,
        /// Sole exact authored range of the offending node.
        range: Option<Box<SourceRange>>,
    },
    /// A parametric application's instance is missing, disagrees with its
    /// declared sort or arguments, or cannot be determined (KF-027).
    ParametricInstance {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the fix.
        reason: String,
        /// Sole exact authored range of the offending head or argument.
        range: Option<Box<SourceRange>>,
    },
    /// The instance k-rust solves from a head's argument sorts differs from
    /// its turbofish (KF-027, R2).
    NativeInstance {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the fix.
        reason: String,
        /// Sole exact authored range of the head.
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
    /// A token regex collides with one of K's own tokens, which both routes
    /// or Java K's configuration parser then reject
    /// (upstream k/token-regex-collisions, reviewed, not a request).
    TokenCollision {
        /// The token production.
        item: Box<StableItemId>,
        /// Stable reason naming K's token and the fix.
        reason: String,
        /// Sole exact authored range of the token attribute.
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
    /// Bracket list notation stands where no cons list is expected, or a
    /// readable record's bracketed value names a cell no reading fits (F6).
    InvalidListNotation {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the position's sort and the fix.
        reason: String,
        /// Sole exact authored range of the brackets.
        range: Option<Box<SourceRange>>,
    },
    /// A `#[k::cons_list]` enum does not build a cons list of its own sort,
    /// or two cons-list declarations construct one sort (F6).
    InvalidConsList {
        /// Item the diagnostic is about.
        item: Box<StableItemId>,
        /// Stable reason naming the constructor and the fix.
        reason: String,
        /// Sole exact authored range of the offending declaration.
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
    /// A heat or cool rule does not bind its hole exactly once on its left
    /// side (KF-014).
    InvalidEvaluationStep {
        /// Stable reason naming the hole and the fix.
        reason: String,
        /// Sole exact authored range of the `hole = x` binder.
        range: Option<Box<SourceRange>>,
    },
    /// A context's hole is absent, bound twice, outside the computation
    /// cell, or badly rewritten, or a context alias's HERE is outside the
    /// computation cell (KF-021).
    InvalidContext {
        /// Stable reason naming the hole and the fix.
        reason: String,
        /// Exact authored range of the offending binder or cell.
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
    /// mode, or an alias or desugar production has no clause (KF-028).
    InvalidStaticClause {
        /// Stable reason naming the clause or production and the fix.
        reason: String,
        /// Sole exact authored range of the clause name or production marker.
        range: Option<Box<SourceRange>>,
    },
    /// A named constant's value is not a ground constructor term, the
    /// constants form a cycle, or a use applies a constant to arguments.
    InvalidConstant {
        /// Stable reason naming the constant and the offending term.
        reason: String,
        /// Sole exact authored range of the offending term or use.
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
    /// An optional or collection cell entry K cannot express (KF-023).
    CellCollection {
        /// The diagnostic code of the specific check.
        code: krs_diagnostic::Code,
        /// Stable reason naming the cell.
        reason: String,
        /// Sole exact authored range of the offending entry.
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

impl DescriptorLoweringError {
    /// An invalid-term error for the descriptor `id`, without a range: where
    /// it arises in a term, sort inference and lowering locate it.
    pub(crate) fn invalid_term(id: &StableItemId, detail: impl Into<String>) -> Self {
        Self::InvalidTerm {
            id: Box::new(id.clone()),
            detail: detail.into(),
            range: None,
        }
    }
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
            Self::InvalidTerm { id, detail, .. } => {
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
            Self::OverlappingEquations {
                function,
                first,
                second,
                application,
                results,
                ..
            } => write!(
                formatter,
                "equations `{}` and `{}` of `{function}` both apply to `{application}` at the same priority and give it different results, `{}` and `{}`; equations are unordered, so the definition would state that these are equal. Make the equations disjoint (a pattern, or a `requires` that excludes the argument), or give one of them another priority (`owise` or `priority = N`).",
                first.item_name(),
                second.item_name(),
                results.0,
                results.1
            ),
            Self::OverlappingMatchArms {
                function,
                first,
                second,
                application,
                results,
                ..
            } => write!(
                formatter,
                "branches `{}` and `{}` of `{function}` both apply to `{application}` and give it different results, `{}` and `{}`; Rust would take the earlier arm, but each branch is an equation and equations are unordered, so the arms of a branching body must not overlap. Make them disjoint with a pattern or a guard that excludes the argument.",
                first.item_name(),
                second.item_name(),
                results.0,
                results.1
            ),
            Self::AmbiguousOrPattern { first, second, .. } => write!(
                formatter,
                "alternatives `{first}` and `{second}` of this or-pattern can match the same term with different bindings; K's #Or then is ambiguous (LLVM takes one, Haskell explores both). Make them disjoint or split the rule."
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
            | Self::MissingPrecedenceChain { reason, .. }
            | Self::InvalidTokenSort { reason, .. }
            | Self::TokenCollision { reason, .. }
            | Self::InvalidSortTest { reason, .. }
            | Self::BitTemplateSort { reason, .. }
            | Self::IncompatibleBinder { reason, .. }
            | Self::CollectionElementSort { reason, .. }
            | Self::InvalidPatternAs { reason, .. }
            | Self::InvalidRecordUpdate { reason, .. }
            | Self::InvalidPatternOr { reason, .. }
            | Self::InvalidOperator { reason, .. }
            | Self::InvalidMatches { reason, .. }
            | Self::InvalidLet { reason, .. }
            | Self::MlPlacement { reason, .. }
            | Self::InvalidMlPredicate { reason, .. }
            | Self::InvalidLocalRewrite { reason, .. }
            | Self::InvalidFunctionContext { reason, .. }
            | Self::InvalidParametricProduction { reason, .. }
            | Self::ParametricInstance { reason, .. }
            | Self::NativeInstance { reason, .. }
            | Self::InvalidLexical { reason, .. }
            | Self::InvalidFresh { reason, .. }
            | Self::InvalidEvaluationStep { reason, .. }
            | Self::InvalidContext { reason, .. }
            | Self::DuplicateSmtlib { reason, .. }
            | Self::InvalidMatchRestriction { reason, .. }
            | Self::InvalidStaticClause { reason, .. }
            | Self::InvalidConstant { reason, .. }
            | Self::SmtLemmaUntranslatable { reason, .. }
            | Self::InvalidSyntaxList { reason, .. }
            | Self::InvalidListNotation { reason, .. }
            | Self::InvalidConsList { reason, .. }
            | Self::InvalidConsoleCell { reason, .. }
            | Self::CellCollection { reason, .. } => formatter.write_str(reason),
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
    #[expect(
        clippy::too_many_lines,
        reason = "One code and note per lowering error variant keeps the mapping exhaustive."
    )]
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
            Self::OverlappingEquations { .. } => codes::analysis::OVERLAPPING_EQUATIONS,
            Self::OverlappingMatchArms { .. } => codes::analysis::OVERLAPPING_MATCH_ARMS,
            Self::AmbiguousOrPattern { .. } => codes::analysis::AMBIGUOUS_OR_PATTERN,
            Self::NondetGroup { .. } => codes::analysis::NONDET_GROUP,
            Self::InvalidOverload { .. } => codes::analysis::INVALID_OVERLOAD,
            Self::MissingPrecedenceChain { .. } => codes::analysis::MISSING_PRECEDENCE_CHAIN,
            Self::PrivateProductionInSpec { .. } => codes::analysis::PRIVATE_PRODUCTION_IN_SPEC,
            Self::InvalidSpecModule { .. } => codes::analysis::INVALID_SPEC_MODULE,
            Self::RuleChangesNoCell { .. } => codes::analysis::RULE_CHANGES_NO_CELL,
            Self::AlwaysEnabledRule { .. } => codes::analysis::ALWAYS_ENABLED_RULE,
            Self::GroupAndDescendant { .. } => codes::analysis::GROUP_AND_DESCENDANT,
            Self::AmbiguousCellSort { .. } => codes::analysis::AMBIGUOUS_CELL_SORT,
            Self::InvalidTokenSort { .. } => codes::analysis::INVALID_TOKEN_SORT,
            Self::TokenCollision { .. } => codes::analysis::TOKEN_COLLISION,
            Self::InvalidSortTest { .. } => codes::analysis::INVALID_SORT_TEST,
            Self::BitTemplateSort { .. } => codes::analysis::BIT_TEMPLATE_SORT,
            Self::IncompatibleBinder { .. } => codes::analysis::INCOMPATIBLE_BINDER,
            Self::CollectionElementSort { .. } => codes::analysis::COLLECTION_ELEMENT_SORT,
            Self::InvalidPatternAs { .. } => codes::analysis::INVALID_PATTERN_AS,
            Self::InvalidRecordUpdate { .. } => codes::analysis::INVALID_RECORD_UPDATE,
            Self::InvalidPatternOr { .. } => codes::analysis::INVALID_PATTERN_OR,
            Self::InvalidOperator { problem, .. } => match problem {
                OperatorProblem::Ambiguous => codes::analysis::AMBIGUOUS_OPERATOR,
                OperatorProblem::Undefined => codes::syntax::INVALID_EXPRESSION_NOTATION,
            },
            Self::InvalidMatches { .. } => codes::analysis::INVALID_MATCHES,
            Self::InvalidLet { .. } => codes::analysis::INVALID_LET,
            Self::MlPlacement { .. } => codes::analysis::ML_PLACEMENT,
            Self::InvalidMlPredicate { .. } => codes::analysis::INVALID_ML_PREDICATE,
            Self::InvalidLocalRewrite { .. } => codes::analysis::INVALID_LOCAL_REWRITE,
            Self::InvalidFunctionContext { .. } => codes::analysis::INVALID_FUNCTION_CONTEXT,
            Self::InvalidParametricProduction { .. } => {
                codes::analysis::INVALID_PARAMETRIC_PRODUCTION
            }
            Self::ParametricInstance { .. } => codes::analysis::PARAMETRIC_INSTANCE,
            Self::NativeInstance { .. } => codes::analysis::NATIVE_INSTANCE,
            Self::InvalidSyntaxList { .. } => codes::analysis::INVALID_SYNTAX_LIST,
            Self::InvalidListNotation { .. } => codes::analysis::INVALID_LIST_NOTATION,
            Self::InvalidConsList { .. } => codes::analysis::INVALID_CONS_LIST,
            Self::InvalidLexical { problem, .. } => match problem {
                LexicalProblem::Duplicate => codes::analysis::DUPLICATE_LEXICAL,
                LexicalProblem::Undefined => codes::analysis::UNDEFINED_LEXICAL,
                LexicalProblem::Recursive => codes::analysis::RECURSIVE_LEXICAL,
            },
            Self::InvalidConsoleCell { .. } => codes::analysis::CONSOLE_CELL,
            Self::CellCollection { code, .. } => code.clone(),
            Self::InvalidFresh { problem, .. } => match problem {
                FreshProblem::NoGenerator => codes::analysis::NO_FRESH_GENERATOR,
                FreshProblem::DuplicateGenerator => codes::analysis::DUPLICATE_FRESH_GENERATOR,
                FreshProblem::InvalidGenerator => codes::analysis::INVALID_FRESH_GENERATOR,
            },
            Self::InvalidEvaluationStep { .. } => codes::analysis::INVALID_HEAT_COOL,
            Self::InvalidContext { .. } => codes::analysis::INVALID_CONTEXT,
            Self::DuplicateSmtlib { .. } => codes::analysis::DUPLICATE_SMTLIB,
            Self::InvalidMatchRestriction { .. } => codes::analysis::INVALID_MATCH_RESTRICTION,
            Self::SmtLemmaUntranslatable { .. } => codes::analysis::SMT_LEMMA_UNTRANSLATABLE,
            Self::InvalidStaticClause { .. } => codes::analysis::INVALID_STATIC_CLAUSE,
            Self::InvalidConstant { .. } => codes::analysis::INVALID_CONSTANT,
            Self::InvalidGeneratedIdentity(_) => codes::analysis::INVALID_GENERATED_IDENTITY,
            Self::InvalidSemanticTheory(_) => codes::analysis::INVALID_SEMANTIC_THEORY,
        };
        let location = match self {
            Self::OverlappingRules {
                second_head_range, ..
            }
            | Self::OverlappingEquations {
                second_head_range, ..
            } => second_head_range
                .as_deref()
                .cloned()
                .map_or(Location::None, Location::Source),
            // The later arm is the one Rust would not reach.
            Self::OverlappingMatchArms { arms, .. } => Location::Source(later_arm(arms).1.clone()),
            Self::NondetGroup { range, .. }
            | Self::AmbiguousOrPattern { range, .. }
            | Self::InvalidOverload { range, .. }
            | Self::MissingPrecedenceChain { range, .. }
            | Self::PrivateProductionInSpec { range, .. }
            | Self::InvalidSpecModule { range, .. }
            | Self::RuleChangesNoCell { range, .. }
            | Self::AlwaysEnabledRule { range, .. }
            | Self::GroupAndDescendant { range, .. }
            | Self::AmbiguousCellSort { range, .. }
            | Self::InvalidTokenSort { range, .. }
            | Self::TokenCollision { range, .. }
            | Self::InvalidSortTest { range, .. }
            | Self::BitTemplateSort { range, .. }
            | Self::InvalidTerm { range, .. }
            | Self::IncompatibleBinder { range, .. }
            | Self::CollectionElementSort { range, .. }
            | Self::InvalidPatternAs { range, .. }
            | Self::InvalidRecordUpdate { range, .. }
            | Self::InvalidPatternOr { range, .. }
            | Self::InvalidOperator { range, .. }
            | Self::InvalidMatches { range, .. }
            | Self::InvalidLet { range, .. }
            | Self::MlPlacement { range, .. }
            | Self::InvalidMlPredicate { range, .. }
            | Self::InvalidLocalRewrite { range, .. }
            | Self::InvalidFunctionContext { range, .. }
            | Self::InvalidParametricProduction { range, .. }
            | Self::ParametricInstance { range, .. }
            | Self::NativeInstance { range, .. }
            | Self::InvalidSyntaxList { range, .. }
            | Self::InvalidListNotation { range, .. }
            | Self::InvalidConsList { range, .. }
            | Self::InvalidLexical { range, .. }
            | Self::InvalidFresh { range, .. }
            | Self::InvalidEvaluationStep { range, .. }
            | Self::InvalidContext { range, .. }
            | Self::DuplicateSmtlib { range, .. }
            | Self::InvalidMatchRestriction { range, .. }
            | Self::InvalidStaticClause { range, .. }
            | Self::InvalidConstant { range, .. }
            | Self::SmtLemmaUntranslatable { range, .. }
            | Self::InvalidConsoleCell { range, .. }
            | Self::CellCollection { range, .. } => range
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
            Self::OverlappingEquations { first, second, .. } => diagnostic
                .with_note(format!("first equation: {first}"))
                .with_note(format!("second equation: {second}")),
            Self::OverlappingMatchArms {
                first,
                second,
                arms,
                ..
            } => diagnostic
                .with_secondary({
                    let (earlier, name) = if later_arm(arms).1 == &arms.1 {
                        (&arms.0, first.item_name())
                    } else {
                        (&arms.1, second.item_name())
                    };
                    krs_diagnostic::Label::new(Location::Source(earlier.clone()))
                        .with_message(format!("the earlier arm, `{name}`, also applies"))
                })
                .with_note(format!("first equation: {first}"))
                .with_note(format!("second equation: {second}")),
            Self::NondetGroup { rule, .. } | Self::AmbiguousOrPattern { rule, .. } => {
                diagnostic.with_note(format!("rule: {rule}"))
            }
            Self::PrivateProductionInSpec {
                sentence,
                kind,
                module,
                ..
            } => {
                let diagnostic = diagnostic.with_note(format!("{kind}: {sentence}"));
                match module {
                    Some(module) => diagnostic.with_note(format!("spec module: {module}")),
                    None => diagnostic,
                }
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

/// The earlier and the later of two arms, by their authored position.
fn later_arm(arms: &(SourceRange, SourceRange)) -> (&SourceRange, &SourceRange) {
    if arms.1.start_byte >= arms.0.start_byte {
        (&arms.0, &arms.1)
    } else {
        (&arms.1, &arms.0)
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

    #[test]
    fn overlapping_match_arms_point_at_the_later_arm_and_name_the_earlier() {
        // Stable-identity order puts `f_10` before `f_2`; the arm written
        // later is still the primary location.
        let first = krs_ir::testing::item("arms", "f_10", ItemKind::Equation);
        let second = krs_ir::testing::item("arms", "f_2", ItemKind::Equation);
        let later = krs_ir::testing::authored(40, 45)
            .exact_authored_range()
            .unwrap();
        let earlier = krs_ir::testing::authored(10, 15)
            .exact_authored_range()
            .unwrap();
        let error = DescriptorLoweringError::OverlappingMatchArms {
            function: "F".to_owned(),
            first: Box::new(first),
            second: Box::new(second),
            application: "F(0)".to_owned(),
            results: Box::new(("1".to_owned(), "2".to_owned())),
            arms: Box::new((later.clone(), earlier.clone())),
        };
        let diagnostic = error.to_diagnostic();
        assert_eq!(diagnostic.code, codes::analysis::OVERLAPPING_MATCH_ARMS);
        let Location::Source(primary) = diagnostic.primary.location else {
            panic!("missing the later arm");
        };
        assert_eq!(primary, later);
        let [label] = diagnostic.secondary.as_slice() else {
            panic!("one secondary label");
        };
        assert!(matches!(&label.location, Location::Source(range) if *range == earlier));
        assert_eq!(
            label.message.as_deref(),
            Some("the earlier arm, `f_2`, also applies")
        );
    }
}
