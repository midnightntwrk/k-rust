//! Frontend-only identities: labels the compiler generates or treats specially, sorts that
//! never reach KORE, the generated configuration cells, and the modules the loader looks for.
//! KORE-level names (`inj`, `SortK`, …) are `k_rust_kore::names`.
//!
//! Spellings live here once; production code compares through the predicates on `Label` and
//! `Sort` and builds labels through the constructors, so a reviewer sees which identity a
//! site tests instead of a string.

use crate::names::{BuiltinSort, WellKnownSymbol};

use super::{Label, Sort};

/// A fixed spelling `Label::is` compares against: a well-known KORE symbol or an internal
/// frontend label.
pub trait LabelName: Copy {
    fn spelling(self) -> &'static str;
}

impl LabelName for WellKnownSymbol {
    fn spelling(self) -> &'static str {
        self.as_str()
    }
}

impl LabelName for InternalLabel {
    fn spelling(self) -> &'static str {
        self.as_str()
    }
}

/// Labels with one fixed spelling that a pass or check tests for.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum InternalLabel {
    KRewrite,
    WithConfig,
    Cells,
    Dots,
    NoDots,
    Or,
    And,
    Not,
    Implies,
    Iff,
    Top,
    Bottom,
    Ceil,
    Floor,
    Equals,
    Exists,
    Forall,
    /// `#AG`, the all-path reachability marker of the matching-logic table.
    AG,
    WeakExistsFinally,
    WeakAlwaysFinally,
    Fun2,
    Fun3,
    Let,
    OuterCast,
    SyntacticCast,
    SyntacticCastBraced,
    KSequence,
    EmptyK,
    KToken,
    KApply,
    KAs,
    /// `#KList`, the rule grammar's argument list.
    KList,
    /// `#token`, the textual KAST token wrapper.
    Token,
    /// `#klabel`, the textual KAST injected-label wrapper.
    KLabel,
    RuleNoConditions,
    RuleRequires,
    RuleEnsures,
    RuleRequiresEnsures,
    ConfigCell,
    ExternalCell,
    CellProperty,
    CellPropertyList,
    CellPropertyListTerminator,
    /// `_:=K_`.
    KEqualsK,
    /// `_:/=K_`.
    KNotEqualsK,
    /// `.Bag`.
    DotBag,
}

impl InternalLabel {
    pub const ALL: [Self; 46] = [
        Self::KRewrite,
        Self::WithConfig,
        Self::Cells,
        Self::Dots,
        Self::NoDots,
        Self::Or,
        Self::And,
        Self::Not,
        Self::Implies,
        Self::Iff,
        Self::Top,
        Self::Bottom,
        Self::Ceil,
        Self::Floor,
        Self::Equals,
        Self::Exists,
        Self::Forall,
        Self::AG,
        Self::WeakExistsFinally,
        Self::WeakAlwaysFinally,
        Self::Fun2,
        Self::Fun3,
        Self::Let,
        Self::OuterCast,
        Self::SyntacticCast,
        Self::SyntacticCastBraced,
        Self::KSequence,
        Self::EmptyK,
        Self::KToken,
        Self::KApply,
        Self::KAs,
        Self::KList,
        Self::Token,
        Self::KLabel,
        Self::RuleNoConditions,
        Self::RuleRequires,
        Self::RuleEnsures,
        Self::RuleRequiresEnsures,
        Self::ConfigCell,
        Self::ExternalCell,
        Self::CellProperty,
        Self::CellPropertyList,
        Self::CellPropertyListTerminator,
        Self::KEqualsK,
        Self::KNotEqualsK,
        Self::DotBag,
    ];

    /// The matching-logic labels the emitter never declares as symbols (the former
    /// `module_to_kore.rs::BUILTIN_LABELS`).
    pub const MATCHING_LOGIC: [Self; 14] = [
        Self::Bottom,
        Self::Top,
        Self::Or,
        Self::And,
        Self::Not,
        Self::Ceil,
        Self::Floor,
        Self::Equals,
        Self::Implies,
        Self::Exists,
        Self::Forall,
        Self::AG,
        Self::WeakExistsFinally,
        Self::WeakAlwaysFinally,
    ];

    /// The fixed labels the KLabel checks treat as compiler-internal (the former
    /// `checks/labels.rs::FIXED_INTERNAL_LABELS` minus `#SemanticCastToBag` and
    /// `<generatedTop>`, which `GeneratedLabel` and `GeneratedCell` cover).
    pub const CHECKED_INTERNAL: [Self; 11] = [
        Self::Cells,
        Self::Dots,
        Self::NoDots,
        Self::Or,
        Self::Fun2,
        Self::Fun3,
        Self::Let,
        Self::WithConfig,
        Self::OuterCast,
        Self::KEqualsK,
        Self::KNotEqualsK,
    ];

    /// The label's spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::KRewrite => "#KRewrite",
            Self::WithConfig => "#withConfig",
            Self::Cells => "#cells",
            Self::Dots => "#dots",
            Self::NoDots => "#noDots",
            Self::Or => "#Or",
            Self::And => "#And",
            Self::Not => "#Not",
            Self::Implies => "#Implies",
            Self::Iff => "#Iff",
            Self::Top => "#Top",
            Self::Bottom => "#Bottom",
            Self::Ceil => "#Ceil",
            Self::Floor => "#Floor",
            Self::Equals => "#Equals",
            Self::Exists => "#Exists",
            Self::Forall => "#Forall",
            Self::AG => "#AG",
            Self::WeakExistsFinally => "weakExistsFinally",
            Self::WeakAlwaysFinally => "weakAlwaysFinally",
            Self::Fun2 => "#fun2",
            Self::Fun3 => "#fun3",
            Self::Let => "#let",
            Self::OuterCast => "#OuterCast",
            Self::SyntacticCast => "#SyntacticCast",
            Self::SyntacticCastBraced => "#SyntacticCastBraced",
            Self::KSequence => "#KSequence",
            Self::EmptyK => "#EmptyK",
            Self::KToken => "#KToken",
            Self::KApply => "#KApply",
            Self::KAs => "#KAs",
            Self::KList => "#KList",
            Self::Token => "#token",
            Self::KLabel => "#klabel",
            Self::RuleNoConditions => "#ruleNoConditions",
            Self::RuleRequires => "#ruleRequires",
            Self::RuleEnsures => "#ruleEnsures",
            Self::RuleRequiresEnsures => "#ruleRequiresEnsures",
            Self::ConfigCell => "#configCell",
            Self::ExternalCell => "#externalCell",
            Self::CellProperty => "#cellProperty",
            Self::CellPropertyList => "#cellPropertyList",
            Self::CellPropertyListTerminator => "#cellPropertyListTerminator",
            Self::KEqualsK => "_:=K_",
            Self::KNotEqualsK => "_:/=K_",
            Self::DotBag => ".Bag",
        }
    }

    /// The label with this spelling, for dispatching a `match` on a label name.
    pub fn of(name: &str) -> Option<Self> {
        match name {
            "#KRewrite" => Some(Self::KRewrite),
            "#withConfig" => Some(Self::WithConfig),
            "#cells" => Some(Self::Cells),
            "#dots" => Some(Self::Dots),
            "#noDots" => Some(Self::NoDots),
            "#Or" => Some(Self::Or),
            "#And" => Some(Self::And),
            "#Not" => Some(Self::Not),
            "#Implies" => Some(Self::Implies),
            "#Iff" => Some(Self::Iff),
            "#Top" => Some(Self::Top),
            "#Bottom" => Some(Self::Bottom),
            "#Ceil" => Some(Self::Ceil),
            "#Floor" => Some(Self::Floor),
            "#Equals" => Some(Self::Equals),
            "#Exists" => Some(Self::Exists),
            "#Forall" => Some(Self::Forall),
            "#AG" => Some(Self::AG),
            "weakExistsFinally" => Some(Self::WeakExistsFinally),
            "weakAlwaysFinally" => Some(Self::WeakAlwaysFinally),
            "#fun2" => Some(Self::Fun2),
            "#fun3" => Some(Self::Fun3),
            "#let" => Some(Self::Let),
            "#OuterCast" => Some(Self::OuterCast),
            "#SyntacticCast" => Some(Self::SyntacticCast),
            "#SyntacticCastBraced" => Some(Self::SyntacticCastBraced),
            "#KSequence" => Some(Self::KSequence),
            "#EmptyK" => Some(Self::EmptyK),
            "#KToken" => Some(Self::KToken),
            "#KApply" => Some(Self::KApply),
            "#KAs" => Some(Self::KAs),
            "#KList" => Some(Self::KList),
            "#token" => Some(Self::Token),
            "#klabel" => Some(Self::KLabel),
            "#ruleNoConditions" => Some(Self::RuleNoConditions),
            "#ruleRequires" => Some(Self::RuleRequires),
            "#ruleEnsures" => Some(Self::RuleEnsures),
            "#ruleRequiresEnsures" => Some(Self::RuleRequiresEnsures),
            "#configCell" => Some(Self::ConfigCell),
            "#externalCell" => Some(Self::ExternalCell),
            "#cellProperty" => Some(Self::CellProperty),
            "#cellPropertyList" => Some(Self::CellPropertyList),
            "#cellPropertyListTerminator" => Some(Self::CellPropertyListTerminator),
            "_:=K_" => Some(Self::KEqualsK),
            "_:/=K_" => Some(Self::KNotEqualsK),
            ".Bag" => Some(Self::DotBag),
            _ => None,
        }
    }
}

/// A label whose spelling carries a payload, recognised by prefix.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GeneratedLabel<'a> {
    /// `#SemanticCastTo{sort}`, `sort_text` non-empty (K sort syntax, possibly parametric).
    SemanticCast { sort_text: &'a str },
    /// `project:{sort}` (no second colon).
    Projection { sort_text: &'a str },
    /// `project:{label}:{field}` (the projection of a named non-terminal).
    FieldProjection { label: &'a str, field: &'a str },
    /// `#lambda{hint1}_{hint2}_{suffix}`.
    Lambda { rest: &'a str },
    /// `#freezer{hint}_{suffix}`.
    Freezer { rest: &'a str },
}

const SEMANTIC_CAST_PREFIX: &str = "#SemanticCastTo";
const PROJECTION_PREFIX: &str = "project:";
const LAMBDA_PREFIX: &str = "#lambda";
const FREEZER_PREFIX: &str = "#freezer";
/// The prefix of the sort-predicate labels `is{sort}`; a constructor only, because any user
/// label may start with `is` and the family cannot be recognised by spelling.
const SORT_PREDICATE_PREFIX: &str = "is";

impl<'a> GeneratedLabel<'a> {
    /// The first matching prefix in the declared order; `None` for every other label,
    /// including `is…`. The prefixes cannot overlap, so the order is documentation.
    pub fn of(label: &'a Label) -> Option<Self> {
        Self::of_name(&label.name)
    }

    /// As `of`, for a site that holds a label's name and not the `Label`.
    pub fn of_name(name: &'a str) -> Option<Self> {
        if let Some(sort_text) = name.strip_prefix(SEMANTIC_CAST_PREFIX) {
            return (!sort_text.is_empty()).then_some(Self::SemanticCast { sort_text });
        }
        if let Some(rest) = name.strip_prefix(PROJECTION_PREFIX) {
            // A K label never contains `:`, so the first colon after the prefix separates
            // `project:{label}:{field}` from `project:{sort}`.
            return Some(match rest.split_once(':') {
                Some((label, field)) => Self::FieldProjection { label, field },
                None => Self::Projection { sort_text: rest },
            });
        }
        if let Some(rest) = name.strip_prefix(LAMBDA_PREFIX) {
            return Some(Self::Lambda { rest });
        }
        if let Some(rest) = name.strip_prefix(FREEZER_PREFIX) {
            return Some(Self::Freezer { rest });
        }
        None
    }
}

impl Label {
    /// The prefix family the label belongs to, with its payload.
    pub fn generated(&self) -> Option<GeneratedLabel<'_>> {
        GeneratedLabel::of(self)
    }

    /// `Some` iff `self` is a semantic cast whose suffix parses as a sort
    /// (`kast::parser::parse_sort_text`); a suffix that does not parse reads as "not a cast".
    pub fn semantic_cast_sort(&self) -> Option<Sort> {
        match self.generated()? {
            GeneratedLabel::SemanticCast { sort_text } => {
                super::parser::parse_sort_text(sort_text).ok()
            }
            _ => None,
        }
    }

    /// `#SemanticCastTo{sort}`.
    pub fn semantic_cast(sort: &Sort) -> Self {
        Self::new(format!("{SEMANTIC_CAST_PREFIX}{sort}"))
    }

    /// `project:{sort}`.
    pub fn projection(sort: &Sort) -> Self {
        Self::new(format!("{PROJECTION_PREFIX}{sort}"))
    }

    /// `project:{label}:{field}`.
    pub fn field_projection(label: &str, field: &str) -> Self {
        Self::new(format!("{PROJECTION_PREFIX}{label}:{field}"))
    }

    /// `is{sort}`.
    pub fn sort_predicate(sort: &Sort) -> Self {
        Self::new(format!("{SORT_PREDICATE_PREFIX}{sort}"))
    }

    /// `#lambda{hint1}_{hint2}_{suffix}`.
    pub fn lambda(hint1: &str, hint2: &str, suffix: &str) -> Self {
        Self::new(format!("{LAMBDA_PREFIX}{hint1}_{hint2}_{suffix}"))
    }

    /// `#freezer{hint}_{suffix}`.
    pub fn freezer(hint: &str, suffix: &str) -> Self {
        Self::new(format!("{FREEZER_PREFIX}{hint}_{suffix}"))
    }

    /// The nullary label with the internal label's spelling.
    pub fn internal(label: InternalLabel) -> Self {
        Self::new(label.as_str())
    }
}

/// Sorts the frontend uses that never reach KORE, plus K-only prelude sorts.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FrontendSort {
    RuleContent,
    RuleBody,
    KVariable,
    SortParam,
    Layout,
    LineMarker,
    CellName,
    KBott,
    KList,
    KLabel,
    KString,
    KResult,
    Cell,
    Bag,
    Stream,
    MInt,
}

impl FrontendSort {
    pub const ALL: [Self; 16] = [
        Self::RuleContent,
        Self::RuleBody,
        Self::KVariable,
        Self::SortParam,
        Self::Layout,
        Self::LineMarker,
        Self::CellName,
        Self::KBott,
        Self::KList,
        Self::KLabel,
        Self::KString,
        Self::KResult,
        Self::Cell,
        Self::Bag,
        Self::Stream,
        Self::MInt,
    ];

    /// The K spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RuleContent => "#RuleContent",
            Self::RuleBody => "#RuleBody",
            Self::KVariable => "#KVariable",
            Self::SortParam => "#SortParam",
            Self::Layout => "#Layout",
            Self::LineMarker => "#LineMarker",
            Self::CellName => "#CellName",
            Self::KBott => "KBott",
            Self::KList => "KList",
            Self::KLabel => "KLabel",
            Self::KString => "KString",
            Self::KResult => "KResult",
            Self::Cell => "Cell",
            Self::Bag => "Bag",
            Self::Stream => "Stream",
            Self::MInt => "MInt",
        }
    }
}

impl Sort {
    /// True for the nullary sort with the frontend sort's spelling.
    pub fn is_frontend(&self, sort: FrontendSort) -> bool {
        self.parameters.is_empty() && self.name == sort.as_str()
    }

    /// The nullary sort with the frontend sort's spelling.
    pub fn frontend(sort: FrontendSort) -> Self {
        Self::new(sort.as_str())
    }

    /// The configuration grammar's "not a user sort" test, stated once: the `K`, `KItem`, and
    /// `KConfigVar` builtins, the `KBott`, `Cell`, and `Bag` frontend sorts, or any `#`-prefixed
    /// name. Parameters are ignored, as the original name test ignored them.
    pub fn is_reserved(&self) -> bool {
        [BuiltinSort::K, BuiltinSort::KItem, BuiltinSort::KConfigVar]
            .iter()
            .any(|sort| self.name == sort.k_name())
            || [FrontendSort::KBott, FrontendSort::Cell, FrontendSort::Bag]
                .iter()
                .any(|sort| self.name == sort.as_str())
            || self.name.starts_with('#')
    }
}

/// The two cells every compiled definition gains.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum GeneratedCell {
    Top,
    Counter,
}

impl GeneratedCell {
    /// The cell's label (`<generatedTop>`, `<generatedCounter>`).
    pub const fn label(self) -> &'static str {
        match self {
            Self::Top => "<generatedTop>",
            Self::Counter => "<generatedCounter>",
        }
    }

    /// The cell's name as a `#CellName` token (`generatedTop`, `generatedCounter`).
    pub const fn name(self) -> &'static str {
        match self {
            Self::Top => "generatedTop",
            Self::Counter => "generatedCounter",
        }
    }

    /// The cell's sort, which the backend also names.
    pub const fn sort(self) -> BuiltinSort {
        match self {
            Self::Top => BuiltinSort::GeneratedTopCell,
            Self::Counter => BuiltinSort::GeneratedCounterCell,
        }
    }

    /// The cell's initializer function label.
    pub const fn initializer(self) -> &'static str {
        match self {
            Self::Top => "initGeneratedTopCell",
            Self::Counter => "initGeneratedCounterCell",
        }
    }
}

/// Modules the loader and passes look for by name.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum WellKnownModule {
    K,
    Bool,
    Map,
    KReflection,
    DefaultConfiguration,
    StdinStream,
    StdoutStream,
    LanguageParsing,
}

impl WellKnownModule {
    /// The module name.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::K => "K",
            Self::Bool => "BOOL",
            Self::Map => "MAP",
            Self::KReflection => "K-REFLECTION",
            Self::DefaultConfiguration => "DEFAULT-CONFIGURATION",
            Self::StdinStream => "STDIN-STREAM",
            Self::StdoutStream => "STDOUT-STREAM",
            Self::LanguageParsing => "LANGUAGE-PARSING",
        }
    }
}

/// The suffix of the generated program-parsing companion of a module.
pub const PROGRAM_PARSING_POSTFIX: &str = "-PROGRAM-PARSING";

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    fn label(name: &str) -> Label {
        Label::new(name)
    }

    #[test]
    fn classifies_a_nullary_semantic_cast() {
        let cast = label("#SemanticCastToInt");
        assert_eq!(
            cast.generated(),
            Some(GeneratedLabel::SemanticCast { sort_text: "Int" })
        );
        assert_eq!(
            cast.semantic_cast_sort(),
            Some(Sort::builtin(BuiltinSort::Int))
        );
    }

    #[test]
    fn classifies_a_parametric_semantic_cast() {
        let cast = label("#SemanticCastToList{Int}");
        assert_eq!(
            cast.generated(),
            Some(GeneratedLabel::SemanticCast {
                sort_text: "List{Int}"
            })
        );
        assert_eq!(
            cast.semantic_cast_sort(),
            Some(Sort::with_parameters(
                "List",
                vec![Sort::builtin(BuiltinSort::Int)]
            ))
        );
    }

    #[test]
    fn an_empty_cast_suffix_is_not_a_cast() {
        let bare = label("#SemanticCastTo");
        assert_eq!(bare.generated(), None);
        assert_eq!(bare.semantic_cast_sort(), None);
    }

    #[test]
    fn classifies_a_sort_projection() {
        assert_eq!(
            label("project:Int").generated(),
            Some(GeneratedLabel::Projection { sort_text: "Int" })
        );
        assert_eq!(label("project:Int").semantic_cast_sort(), None);
    }

    #[test]
    fn classifies_a_field_projection() {
        assert_eq!(
            label("project:foo:bar").generated(),
            Some(GeneratedLabel::FieldProjection {
                label: "foo",
                field: "bar"
            })
        );
    }

    #[test]
    fn classifies_a_lambda() {
        assert_eq!(
            label("#lambda1_2_3").generated(),
            Some(GeneratedLabel::Lambda { rest: "1_2_3" })
        );
    }

    #[test]
    fn classifies_a_freezer() {
        assert_eq!(
            label("#freezer1_2").generated(),
            Some(GeneratedLabel::Freezer { rest: "1_2" })
        );
    }

    #[test]
    fn sort_predicates_and_user_labels_are_not_generated() {
        assert_eq!(label("isInt").generated(), None);
        assert_eq!(label("foo").generated(), None);
        assert_eq!(label("#KRewrite").generated(), None);
    }

    #[test]
    fn constructors_round_trip_through_the_classifier() {
        let int = Sort::builtin(BuiltinSort::Int);
        let list = Sort::with_parameters("List", vec![int.clone()]);
        assert_eq!(
            Label::semantic_cast(&list).generated(),
            Some(GeneratedLabel::SemanticCast {
                sort_text: "List{Int}"
            })
        );
        assert_eq!(Label::semantic_cast(&list).semantic_cast_sort(), Some(list));
        assert_eq!(
            Label::projection(&int).generated(),
            Some(GeneratedLabel::Projection { sort_text: "Int" })
        );
        assert_eq!(
            Label::field_projection("pair", "fst").generated(),
            Some(GeneratedLabel::FieldProjection {
                label: "pair",
                field: "fst"
            })
        );
        assert_eq!(
            Label::lambda("1", "2", "3").generated(),
            Some(GeneratedLabel::Lambda { rest: "1_2_3" })
        );
        assert_eq!(
            Label::freezer("1", "2").generated(),
            Some(GeneratedLabel::Freezer { rest: "1_2" })
        );
        assert_eq!(Label::sort_predicate(&int).name, "isInt");
        assert_eq!(Label::sort_predicate(&int).generated(), None);
        for internal in InternalLabel::ALL {
            let built = Label::internal(internal);
            assert!(built.is(internal), "{internal:?}");
            assert_eq!(InternalLabel::of(&built.name), Some(internal));
            assert_eq!(built.generated(), None, "{internal:?}");
        }
    }

    #[test]
    fn internal_label_spellings_are_distinct_and_matching_logic_is_the_builtin_table() {
        let spellings: Vec<_> = InternalLabel::ALL.iter().map(|l| l.as_str()).collect();
        for (index, spelling) in spellings.iter().enumerate() {
            assert!(!spellings[index + 1..].contains(spelling), "{spelling}");
        }
        assert_eq!(InternalLabel::of("#cellS"), None);
        // `module_to_kore.rs::BUILTIN_LABELS` at c5bf88f.
        let builtin_labels: BTreeSet<&str> = [
            "#Bottom",
            "#Top",
            "#Or",
            "#And",
            "#Not",
            "#Ceil",
            "#Floor",
            "#Equals",
            "#Implies",
            "#Exists",
            "#Forall",
            "#AG",
            "weakExistsFinally",
            "weakAlwaysFinally",
        ]
        .into_iter()
        .collect();
        let matching_logic: BTreeSet<&str> = InternalLabel::MATCHING_LOGIC
            .iter()
            .map(|l| l.as_str())
            .collect();
        assert_eq!(matching_logic, builtin_labels);
    }

    #[test]
    fn checked_internal_plus_the_classifier_cover_the_fixed_internal_labels() {
        // `checks/labels.rs::FIXED_INTERNAL_LABELS` at c5bf88f.
        let fixed: BTreeSet<&str> = [
            "#cells",
            "#dots",
            "#noDots",
            "#Or",
            "#fun2",
            "#fun3",
            "#let",
            "#withConfig",
            "#OuterCast",
            "<generatedTop>",
            "#SemanticCastToBag",
            "_:=K_",
            "_:/=K_",
        ]
        .into_iter()
        .collect();
        let mut covered: BTreeSet<&str> = InternalLabel::CHECKED_INTERNAL
            .iter()
            .map(|l| l.as_str())
            .collect();
        covered.insert(GeneratedCell::Top.label());
        assert_eq!(
            label("#SemanticCastToBag").generated(),
            Some(GeneratedLabel::SemanticCast { sort_text: "Bag" })
        );
        covered.insert("#SemanticCastToBag");
        assert_eq!(covered, fixed);
    }

    #[test]
    fn is_reserved_agrees_with_the_configuration_grammar_predicate() {
        // `inner/config.rs` at c5bf88f: the sorts that get no cast, subsort, or bracket.
        let reference = |sort: &Sort| {
            matches!(
                sort.name.as_str(),
                "K" | "KItem"
                    | "KBott"
                    | "KConfigVar"
                    | "Cell"
                    | "Bag"
                    | "#RuleBody"
                    | "#RuleContent"
            ) || sort.name.starts_with('#')
        };
        for sort in FrontendSort::ALL {
            let sort = Sort::frontend(sort);
            assert_eq!(sort.is_reserved(), reference(&sort), "{sort}");
        }
        for sort in BuiltinSort::ALL {
            let sort = Sort::builtin(sort);
            assert_eq!(sort.is_reserved(), reference(&sort), "{sort}");
        }
        let hashed = Sort::new("#X");
        assert!(hashed.is_reserved() && reference(&hashed));
        let user = Sort::new("Exp");
        assert!(!user.is_reserved() && !reference(&user));
        assert!(Sort::frontend(FrontendSort::Layout).is_frontend(FrontendSort::Layout));
        assert!(!Sort::with_parameters("KLabel", vec![user]).is_frontend(FrontendSort::KLabel));
        assert_eq!(
            GeneratedCell::Counter.sort(),
            BuiltinSort::GeneratedCounterCell
        );
        assert_eq!(
            WellKnownModule::DefaultConfiguration.as_str(),
            "DEFAULT-CONFIGURATION"
        );
    }
}
