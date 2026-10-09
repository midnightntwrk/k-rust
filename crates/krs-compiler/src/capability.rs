//! Backend capability requirements of a definition (V8).
//!
//! The compiler derives a deterministic list of [`CapabilityRequirement`]s
//! from Definition IR. Each backend route states which features it lacks in
//! one table (`krs_k_rust::ROUTE_CAPABILITIES`); a route that lacks a required
//! feature refuses the definition with `krs::capability::unavailable` before
//! any compilation, and never weakens it. `krs emit-k` still writes the
//! faithful `.k`, marks each affected sentence with a `// krs-capability:`
//! comment, and records the requirements in `symbols.json`.
//!
//! Features are appended at the tail of [`CapabilityFeature`] and of the
//! derivation in [`sentence_features`].

use krs_diagnostic::{Diagnostic, Location, Severity, codes};
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, CellAttribute, CellPost, FixedCell,
    FixedCellContent, SentenceKind, SourceMapKey,
};
use krs_ir_levels::{
    DefinitionIr, DefinitionSentence, DefinitionSortRef, DefinitionTerm, DefinitionTermKind,
    RuleBodyRef, RuleSentence,
};
use serde::{Deserialize, Serialize};

/// One language feature that some backend route cannot run.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CapabilityFeature {
    /// A rule with K's `anywhere` attribute (`#[k::rule(anywhere)]`).
    AnywhereRule,
    /// A `FLOAT`-hooked application whose arguments are all tokens, which the
    /// native frontend folds at compile time and can fold only with MPFR.
    GroundFloatFolding,
    /// A Float token, or a `round`, `max_value`, or `from_int` format argument
    /// pair, whose precision is neither binary32 (`p24x8`) nor binary64 (`p53x11`).
    FloatPrecisionBeyondBinary64,
    /// A `stream` cell or an `io::` operation: console input and output.
    ConsoleIO,
    /// A transition whose result introduces a symbolic value (`#[k::exists]`, K's `?X`).
    RuleExistential,
}

impl CapabilityFeature {
    /// Every feature, in catalog order.
    pub const ALL: &'static [Self] = &[
        Self::AnywhereRule,
        Self::GroundFloatFolding,
        Self::FloatPrecisionBeyondBinary64,
        Self::ConsoleIO,
        Self::RuleExistential,
    ];

    /// The stable feature name used in sidecars, comments, and route tables.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::AnywhereRule => "AnywhereRule",
            Self::GroundFloatFolding => "GroundFloatFolding",
            Self::FloatPrecisionBeyondBinary64 => "FloatPrecisionBeyondBinary64",
            Self::ConsoleIO => "ConsoleIO",
            Self::RuleExistential => "RuleExistential",
        }
    }

    /// The noun phrase a refusal uses for the sentences that need the feature.
    #[must_use]
    pub const fn description(self) -> &'static str {
        match self {
            Self::AnywhereRule => "anywhere rules",
            Self::GroundFloatFolding => "Float applications to tokens only",
            Self::FloatPrecisionBeyondBinary64 => "Float formats other than f32 and f64",
            Self::ConsoleIO => "console input or output",
            Self::RuleExistential => "rules that introduce symbolic values",
        }
    }
}

/// One sentence that needs a capability.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CapabilityRequirement {
    feature: CapabilityFeature,
    /// Emitted name of the sentence (its K label).
    symbol: String,
    origin: SourceMapKey,
}

impl CapabilityRequirement {
    /// The required feature.
    #[must_use]
    pub const fn feature(&self) -> CapabilityFeature {
        self.feature
    }

    /// The emitted name of the sentence that needs it.
    #[must_use]
    pub fn symbol(&self) -> &str {
        &self.symbol
    }

    /// The source-map key of that sentence.
    #[must_use]
    pub const fn origin(&self) -> &SourceMapKey {
        &self.origin
    }
}

/// The features one rule sentence needs, in catalog order.
#[must_use]
pub fn sentence_features(sentence: &RuleSentence) -> Vec<CapabilityFeature> {
    let mut features = Vec::new();
    if sentence.anywhere().is_some() {
        features.push(CapabilityFeature::AnywhereRule);
    }
    let mut floats = TermUse::default();
    for term in sentence_terms(sentence) {
        floats.term(term);
    }
    if floats.ground {
        features.push(CapabilityFeature::GroundFloatFolding);
    }
    if floats.beyond_binary64 {
        features.push(CapabilityFeature::FloatPrecisionBeyondBinary64);
    }
    if floats.console {
        features.push(CapabilityFeature::ConsoleIO);
    }
    if sentence.kind() == SentenceKind::Transition && !sentence.existentials().is_empty() {
        features.push(CapabilityFeature::RuleExistential);
    }
    features
}

/// Every term of a rule, equation, or claim sentence.
pub(crate) fn sentence_terms(sentence: &RuleSentence) -> Vec<&DefinitionTerm> {
    let mut terms = Vec::new();
    match sentence.relational_body() {
        RuleBodyRef::Term(rewrite) => {
            terms.push(rewrite.from());
            terms.push(rewrite.to());
        }
        RuleBodyRef::Configuration { body, .. } => {
            for clause in body.clauses() {
                terms.push(clause.before());
                if let CellPost::Replace { term } = clause.after() {
                    terms.push(term);
                }
            }
        }
    }
    if let Some(condition) = sentence.requires() {
        terms.push(condition.term());
    }
    if let Some(condition) = sentence.ensures() {
        terms.push(condition.term());
    }
    terms
}

fn token(term: &DefinitionTerm) -> Option<&str> {
    match term.kind() {
        DefinitionTermKind::Token { value } => Some(value),
        _ => None,
    }
}

/// The Float and console capabilities one sentence's terms need.
#[derive(Default)]
struct TermUse {
    ground: bool,
    beyond_binary64: bool,
    console: bool,
}

impl TermUse {
    fn term(&mut self, term: &DefinitionTerm) {
        match term.kind() {
            DefinitionTermKind::Variable { .. } => {}
            DefinitionTermKind::Token { value } => {
                if matches!(term.sort(), DefinitionSortRef::Builtin(BuiltinSort::Float))
                    && krs_ir::float_token::validate(value)
                        .is_ok_and(|format| !format.is_binary32_or_binary64())
                {
                    self.beyond_binary64 = true;
                }
            }
            DefinitionTermKind::Application {
                application,
                arguments,
            } => {
                if let ApplicationRef::Builtin(operation) = application {
                    self.operation(*operation, arguments);
                }
                for argument in arguments {
                    self.term(argument);
                }
            }
            DefinitionTermKind::KSequence { items, .. } => {
                for item in items {
                    self.term(item);
                }
            }
            DefinitionTermKind::Map(operands) => {
                for operand in operands.operands() {
                    self.term(operand);
                }
            }
            DefinitionTermKind::List(operands) => {
                for operand in operands.operands() {
                    self.term(operand);
                }
            }
            DefinitionTermKind::Set(operands) => {
                for operand in operands.operands() {
                    self.term(operand);
                }
            }
            DefinitionTermKind::Rewrite { from, to } => {
                self.term(from);
                self.term(to);
            }
            DefinitionTermKind::Cell { children, .. } => {
                for child in children {
                    self.term(child);
                }
            }
            DefinitionTermKind::As { pattern, .. } => self.term(pattern),
        }
    }

    fn operation(&mut self, operation: BuiltinOperation, arguments: &[DefinitionTerm]) {
        if operation.spec().k_module == "K-IO" {
            self.console = true;
        }
        // k-rust folds every hooked application whose arguments are all tokens
        // (`constant_folding.rs`); its FLOAT hooks need the MPFR build.
        if operation
            .spec()
            .k_hook
            .is_some_and(|hook| hook.starts_with("FLOAT."))
            && arguments.iter().all(|argument| token(argument).is_some())
        {
            self.ground = true;
        }
        let format = match operation {
            BuiltinOperation::FloatRound | BuiltinOperation::FloatFromInt => arguments.get(1..3),
            BuiltinOperation::FloatMaxValue => arguments.get(0..2),
            _ => None,
        };
        if let Some([precision, exponent_bits]) = format
            && let (Some(precision), Some(exponent_bits)) = (token(precision), token(exponent_bits))
            && !matches!((precision, exponent_bits), ("24", "8") | ("53", "11"))
        {
            self.beyond_binary64 = true;
        }
    }
}

/// Every capability requirement of a definition, ordered by feature, then sentence name.
#[must_use]
pub fn capability_requirements(definition: &DefinitionIr) -> Vec<CapabilityRequirement> {
    let mut requirements = Vec::new();
    for module in definition.modules() {
        for sentence in module.sentences() {
            if let DefinitionSentence::Configuration(configuration) = sentence {
                for (name, origin) in stream_cells(configuration.cells()) {
                    requirements.push(CapabilityRequirement {
                        feature: CapabilityFeature::ConsoleIO,
                        symbol: name,
                        origin,
                    });
                }
            }
            let DefinitionSentence::Rule(rule) = sentence else {
                continue;
            };
            for feature in sentence_features(rule) {
                requirements.push(CapabilityRequirement {
                    feature,
                    symbol: rule.label().emitted_name().to_owned(),
                    origin: rule.origin().key().clone(),
                });
            }
        }
    }
    requirements.sort();
    requirements
}

/// `warning[krs::capability::ignored-ensures]` for each transition with an
/// `ensures` condition: concrete (LLVM) execution does not assume it.
#[must_use]
pub fn concrete_execution_warnings(definition: &DefinitionIr) -> Vec<Diagnostic> {
    let mut warnings = Vec::new();
    for module in definition.modules() {
        for sentence in module.sentences() {
            let DefinitionSentence::Rule(rule) = sentence else {
                continue;
            };
            let Some(ensures) = rule.ensures() else {
                continue;
            };
            if rule.kind() != SentenceKind::Transition {
                continue;
            }
            let mut diagnostic = Diagnostic::error(
                codes::capability::IGNORED_ENSURES,
                format!(
                    "rule `{}` has an ensures condition; concrete (LLVM) execution ignores it, so build with --backend haskell to assume it",
                    rule.label().emitted_name()
                ),
                ensures
                    .origin()
                    .origin()
                    .exact_authored_range()
                    .map_or(Location::None, Location::Source),
            );
            diagnostic.severity = Severity::Warning;
            warnings.push(diagnostic);
        }
    }
    warnings
}

/// The `stream` cells of a configuration, by emitted name, with their attribute origins.
#[must_use]
pub fn stream_cells<S, C>(cells: &[FixedCell<S, C>]) -> Vec<(String, SourceMapKey)> {
    let mut streams = Vec::new();
    for cell in cells {
        for attribute in cell.attributes() {
            if let CellAttribute::Stream { origin, .. } = attribute {
                streams.push((format!("<{}>", cell.name()), origin.key().clone()));
            }
        }
        if let FixedCellContent::Children { children } = cell.content() {
            streams.extend(stream_cells(children));
        }
    }
    streams
}

/// The refusal text for a route that lacks `feature`, naming the sentences that need it.
#[must_use]
pub fn unavailable_message(
    feature: CapabilityFeature,
    route_reason: &str,
    requirements: &[CapabilityRequirement],
) -> String {
    let symbols = requirements
        .iter()
        .filter(|requirement| requirement.feature == feature)
        .map(CapabilityRequirement::symbol)
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "definition contains {} [{symbols}]; {route_reason}",
        feature.description()
    )
}

#[cfg(test)]
mod tests {
    use krs_ir::{BuiltinOperation, BuiltinSort, NodeOrigin};
    use krs_ir_levels::{DefinitionApplicationRef, DefinitionSortRef, DefinitionTerm};

    use super::TermUse;

    fn node(key: &str) -> NodeOrigin {
        krs_ir::testing::origin_in(
            key,
            krs_ir::testing::package("KRS-CAPABILITY-TEST", "capability-test"),
            "src/lib.rs",
            krs_ir::testing::digest(),
            0,
            1,
        )
    }

    fn token(sort: BuiltinSort, value: &str) -> DefinitionTerm {
        DefinitionTerm::token(node(value), DefinitionSortRef::Builtin(sort), value).unwrap()
    }

    fn variable(sort: BuiltinSort) -> DefinitionTerm {
        DefinitionTerm::variable(
            node("variable"),
            DefinitionSortRef::Builtin(sort),
            krs_ir::SemanticId::new("x".to_owned()).unwrap(),
        )
    }

    fn apply(operation: BuiltinOperation, arguments: Vec<DefinitionTerm>) -> DefinitionTerm {
        let sort = operation.result_sort().builtin().unwrap();
        DefinitionTerm::application(
            node("application"),
            DefinitionSortRef::Builtin(sort),
            DefinitionApplicationRef::Builtin(operation),
            arguments,
        )
    }

    fn uses(term: &DefinitionTerm) -> (bool, bool) {
        let mut floats = TermUse::default();
        floats.term(term);
        (floats.ground, floats.beyond_binary64)
    }

    #[test]
    fn ground_float_applications_need_mpfr_folding() {
        let float = |value| token(BuiltinSort::Float, value);
        let int = |value| token(BuiltinSort::Int, value);
        let ground = apply(BuiltinOperation::FloatAdd, vec![float("0.1"), float("0.2")]);
        assert_eq!(uses(&ground), (true, false));
        let nested = apply(
            BuiltinOperation::FloatEqual,
            vec![variable(BuiltinSort::Float), ground],
        );
        assert_eq!(uses(&nested), (true, false));
        let open = apply(
            BuiltinOperation::FloatAdd,
            vec![variable(BuiltinSort::Float), float("0.2")],
        );
        assert_eq!(uses(&open), (false, false));
        assert_eq!(
            uses(&apply(
                BuiltinOperation::FloatMaxValue,
                vec![int("53"), int("11")]
            )),
            (true, false)
        );
        // `sqrtFloat` and `=/=Float` are unhooked, so k-rust does not fold them.
        assert_eq!(
            uses(&apply(BuiltinOperation::FloatSqrt, vec![float("2.0")])),
            (false, false)
        );
    }

    #[test]
    fn formats_beyond_binary64_are_java_only() {
        let float = |value| token(BuiltinSort::Float, value);
        let int = |value| token(BuiltinSort::Int, value);
        assert_eq!(uses(&float("1.0p113x15")), (false, true));
        assert_eq!(uses(&float("1.0f")), (false, false));
        assert_eq!(uses(&float("1.0p53x11")), (false, false));
        let round = |precision, exponent| {
            apply(
                BuiltinOperation::FloatRound,
                vec![variable(BuiltinSort::Float), int(precision), int(exponent)],
            )
        };
        assert_eq!(uses(&round("24", "8")), (false, false));
        assert_eq!(uses(&round("113", "15")), (false, true));
        let from_int = apply(
            BuiltinOperation::FloatFromInt,
            vec![variable(BuiltinSort::Int), int("11"), int("53")],
        );
        assert_eq!(uses(&from_int), (false, true));
    }

    #[test]
    fn io_operations_need_console_io() {
        let write = DefinitionTerm::application(
            node("application"),
            DefinitionSortRef::Builtin(BuiltinSort::KSequence),
            DefinitionApplicationRef::Builtin(BuiltinOperation::IoWrite),
            vec![
                token(BuiltinSort::Int, "2"),
                token(BuiltinSort::String, "\"warn\""),
            ],
        );
        let mut console = TermUse::default();
        console.term(&write);
        assert!(console.console);
        let mut pure = TermUse::default();
        pure.term(&variable(BuiltinSort::Int));
        assert!(!pure.console);
    }
}
