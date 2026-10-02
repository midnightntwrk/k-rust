//! The role of a sort head, decided once from its spelling.
//!
//! A sort name in the frontend denotes a kernel sort (whose meaning K fixes whatever the
//! definition declares), a sort the definition declares, a numeral sort argument, parser
//! scaffolding, or a rigid sort variable of a sentence. [`SortRole::of_name`] reads the role from
//! the spelling, and every property that separates those roles is one exhaustive
//! `match` on [`SortRole`], so adding a role forces a decision in every property.

#![deny(clippy::wildcard_enum_match_arm)]

use crate::names::BuiltinSort;

use super::{FrontendSort, Sort};

/// A numeral sort is spelled with one or more ASCII decimal digits, of any length.
/// A width is a natural number that the frontend never computes with.
pub(crate) const fn is_numeral_spelling(name: &str) -> bool {
    let bytes = name.as_bytes();
    if bytes.is_empty() {
        return false;
    }
    let mut i = 0;
    while i < bytes.len() {
        if !bytes[i].is_ascii_digit() {
            return false;
        }
        i += 1;
    }
    true
}

/// A sort whose meaning K fixes, whatever the definition declares.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) enum KernelSort {
    K,
    KItem,
    KConfigVar,
    KBott,
    KLabel,
    KList,
    KString,
    Bag,
    Cell,
    Bool,
}

impl KernelSort {
    pub(crate) const ALL: [Self; 10] = [
        Self::K,
        Self::KItem,
        Self::KConfigVar,
        Self::KBott,
        Self::KLabel,
        Self::KList,
        Self::KString,
        Self::Bag,
        Self::Cell,
        Self::Bool,
    ];

    /// The K spelling, taken from the sort-name enums that already own it.
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::K => BuiltinSort::K.k_name(),
            Self::KItem => BuiltinSort::KItem.k_name(),
            Self::KConfigVar => BuiltinSort::KConfigVar.k_name(),
            Self::Bool => BuiltinSort::Bool.k_name(),
            Self::KBott => FrontendSort::KBott.as_str(),
            Self::KLabel => FrontendSort::KLabel.as_str(),
            Self::KList => FrontendSort::KList.as_str(),
            Self::KString => FrontendSort::KString.as_str(),
            Self::Bag => FrontendSort::Bag.as_str(),
            Self::Cell => FrontendSort::Cell.as_str(),
        }
    }

    /// The kernel sort spelled `name`, if any.
    pub(crate) fn of_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|sort| sort.name() == name)
    }

    /// The nullary sort with the kernel spelling.
    pub(crate) fn sort(self) -> Sort {
        Sort::new(self.name())
    }
}

/// The role of a sort head, decided from its name alone.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum SortRole {
    Kernel(KernelSort),
    /// `#SortParam`: a sort variable of a sentence, universally quantified.
    RigidVariable,
    /// Any other `#`-prefixed head: parser scaffolding, which denotes no set of terms.
    Scaffolding,
    /// A decimal numeral: a width, the argument of a parametric sort such as `MInt{8}`.
    /// It has no terms ([`SortRole::has_terms`]).
    Nat,
    /// Any other head: its meaning comes from the definition.
    Defined,
}

impl Sort {
    /// The role of this sort's head: a kernel spelling, then `#SortParam`, then any other leading
    /// `#`, then a decimal numeral of any length, else a defined sort.
    ///
    /// Parameters are ignored: the role of `MInt{8}` is the role of `MInt`.
    pub(crate) fn role(&self) -> SortRole {
        SortRole::of_name(&self.name)
    }

    /// Whether this sort is a rigid sort variable of a sentence (`#SortParam{Q}`), which stands
    /// for every sort at once and is never solved.
    pub(crate) fn is_rigid_variable(&self) -> bool {
        self.role() == SortRole::RigidVariable
    }

    /// Whether a position of a grammar at this sort is a real sort rather than parser
    /// scaffolding: a shape-level classifier of positions, which admits every parametric sort
    /// and a nullary sort by its role.
    ///
    /// It does not decide which values an inference unknown can take. Those are the grammar's
    /// sorts: the Z3 `DomainSolver` admits a parametric value only when it is one of
    /// `Grammar::parametric_values`, the parametric sorts of the module.
    pub(crate) fn in_inference_domain(&self) -> bool {
        !self.parameters.is_empty() || self.role().in_inference_domain()
    }
}

impl SortRole {
    /// The role of a sort head, from its spelling.
    pub(crate) fn of_name(name: &str) -> SortRole {
        if let Some(kernel) = KernelSort::of_name(name) {
            Self::Kernel(kernel)
        } else if name == FrontendSort::SortParam.as_str() {
            Self::RigidVariable
        } else if name.starts_with('#') {
            Self::Scaffolding
        } else if is_numeral_spelling(name) {
            Self::Nat
        } else {
            Self::Defined
        }
    }

    /// A term can have the sort, at parse time or in the compiled definition, so a sentence may
    /// give it terms (a production of it, a token or hooked declaration of it) and positions (an
    /// operand of it).
    /// This holds for every role except a numeral, which is a width: the argument of a parametric
    /// sort such as `MInt{8}`, naming a natural number, not a set of terms.
    /// `check_sorts` rejects every sentence that would give a numeral terms or positions.
    pub(crate) const fn has_terms(self) -> bool {
        match self {
            Self::Nat => false,
            Self::Kernel(..) | Self::RigidVariable | Self::Scaffolding | Self::Defined => true,
        }
    }

    /// Every term of the sort is a K item and the sort is neither `K` nor `KItem`, so compilation
    /// declares `S < KItem` for it. The inner grammars may generate a per-member `KItem ::= S`
    /// production only for this role, enforced by the const assertion in `sort_universe`.
    /// `KLabel`, `KList` and `KString` are sorts of the term syntax itself (a label, an argument
    /// sequence, the spelling inside `#token`), so they are not sorts of K items.
    /// `KBott` and `KConfigVar` lie below `KItem` through the fixed kernel syntax; a rigid
    /// variable stands for every sort at once and a scaffolding sort is parser structure.
    pub(crate) const fn has_implicit_kitem_subsort(self) -> bool {
        use KernelSort as S;
        match self {
            Self::Kernel(S::Bag | S::Cell | S::Bool) | Self::Defined => true,
            Self::Kernel(
                S::K | S::KItem | S::KConfigVar | S::KBott | S::KLabel | S::KList | S::KString,
            )
            | Self::RigidVariable
            | Self::Scaffolding
            | Self::Nat => false,
        }
    }

    /// A variable or a configuration variable may stand at a position of the sort, so `KBott`,
    /// `#KVariable` and `KConfigVar` lie below it: a per-member subsort from `KBott`, `KConfigVar`
    /// or `#KVariable` may be generated only for a sort with this role.
    ///
    /// `KBott` and `KConfigVar` are themselves those bottom sorts, below which nothing but the
    /// variable tokens lies; a rigid variable stands for every sort at once and a scaffolding sort
    /// is parser structure, so no variable stands at either. A numeral has no terms, so no
    /// variable stands at it.
    pub(crate) const fn admits_variables(self) -> bool {
        use KernelSort as S;
        match self {
            Self::Kernel(
                S::K | S::KItem | S::KLabel | S::KList | S::KString | S::Bag | S::Cell | S::Bool,
            )
            | Self::Defined => true,
            Self::Kernel(S::KBott | S::KConfigVar)
            | Self::RigidVariable
            | Self::Scaffolding
            | Self::Nat => false,
        }
    }

    /// A sort of the K term algebra: `K`, `KItem`, or a sort below `KItem`.
    pub(crate) const fn is_k_term_sort(self) -> bool {
        use KernelSort as S;
        match self {
            Self::Kernel(S::K | S::KItem | S::Bag | S::Cell | S::Bool) | Self::Defined => true,
            Self::Kernel(S::KConfigVar | S::KBott | S::KLabel | S::KList | S::KString)
            | Self::RigidVariable
            | Self::Scaffolding
            | Self::Nat => false,
        }
    }

    /// Compilation declares the sort predicate `isS(K)` for the sort, and a rule may mention it.
    ///
    /// `isS(T)` holds when the K term `T` is a term of `S`, so it exists exactly for the sorts
    /// whose terms are K terms of the compiled definition: `K`, `KItem`, `Bool`, a defined sort,
    /// and `KConfigVar`, whose tokens (`$PGM`) are K items (`KItem ::= KConfigVar`) that key the
    /// initial configuration. `KLabel`, `KList` and `KString` are sorts of the term syntax itself
    /// (a label, an argument sequence, the spelling inside `#token`), not sorts of K terms.
    /// `KBott` is the parse-time bottom of the K sorts, whose terms are variables and `#token`
    /// spellings that compilation gives the sort of their position. `Bag` and `Cell` are the
    /// sorts of the configuration's cell structure, which compilation replaces by one generated
    /// sort per cell, so no compiled term has them. A numeral is a sort argument (the width of
    /// `MInt{8}`), a scaffolding sort is parser structure and a rigid variable stands for every
    /// sort at once: none of them is a set of K terms to test membership in.
    ///
    /// The rule grammar offers `isS(_)`, and compilation generates it, from this one predicate.
    pub(crate) const fn has_sort_predicate(self) -> bool {
        use KernelSort as S;
        match self {
            Self::Kernel(S::K | S::KItem | S::KConfigVar | S::Bool) | Self::Defined => true,
            Self::Kernel(S::KBott | S::KLabel | S::KList | S::KString | S::Bag | S::Cell)
            | Self::RigidVariable
            | Self::Scaffolding
            | Self::Nat => false,
        }
    }

    /// Compilation declares the sort projection `project:S(K)` for the sort, and a rule may
    /// mention it.
    ///
    /// `project:S(T)` is `T` as a term of sort `S`, so it exists for the sorts of K terms that a
    /// computed term may have to be coerced to: `K`, `KItem`, `Bool` and a defined sort. The
    /// sorts without a predicate ([`SortRole::has_sort_predicate`]) have no K terms to coerce
    /// to. A `KConfigVar` token is only ever written as a literal (`$PGM`) and never computed, so
    /// no rule coerces a computed term to it: it has a predicate and no projection.
    ///
    /// The rule grammar offers `project:S(_)`, and compilation generates it, from this one
    /// predicate.
    pub(crate) const fn has_sort_projection(self) -> bool {
        use KernelSort as S;
        match self {
            Self::Kernel(S::K | S::KItem | S::Bool) | Self::Defined => true,
            Self::Kernel(
                S::KConfigVar | S::KBott | S::KLabel | S::KList | S::KString | S::Bag | S::Cell,
            )
            | Self::RigidVariable
            | Self::Scaffolding
            | Self::Nat => false,
        }
    }

    /// A value an inference unknown can take: a K term sort, `KLabel` (the sort of label
    /// variables), or a numeral (the width parameters of sorts such as `MInt{N}`).
    ///
    /// A numeral is a value only of a width parameter. No term unknown can take one, because
    /// no grammar relation mentions a sort without terms.
    /// This is the row for a head; [`Sort::in_inference_domain`] adds every parametric sort.
    pub(crate) const fn in_inference_domain(self) -> bool {
        use KernelSort as S;
        match self {
            Self::Kernel(S::K | S::KItem | S::KLabel | S::Bag | S::Cell | S::Bool)
            | Self::Nat
            | Self::Defined => true,
            Self::Kernel(S::KConfigVar | S::KBott | S::KList | S::KString)
            | Self::RigidVariable
            | Self::Scaffolding => false,
        }
    }

    /// A value a production's sort parameter can take: the inference domain without `KLabel`,
    /// since a sort parameter ranges over sorts of terms and widths, not over labels. A numeral
    /// is a value only of a width parameter; no term unknown can take one, because no grammar
    /// relation mentions a sort without terms.
    #[cfg_attr(
        not(any(test, feature = "z3-inference")),
        expect(
            dead_code,
            reason = "read only by the Z3 encoder's DomainSolver, which the portable build omits"
        )
    )]
    pub(crate) const fn in_parameter_domain(self) -> bool {
        use KernelSort as S;
        match self {
            Self::Kernel(S::K | S::KItem | S::Bag | S::Cell | S::Bool)
            | Self::Nat
            | Self::Defined => true,
            Self::Kernel(S::KConfigVar | S::KBott | S::KLabel | S::KList | S::KString)
            | Self::RigidVariable
            | Self::Scaffolding => false,
        }
    }

    /// The configuration grammar's "not a user sort" set: `K`, `KItem`, `KConfigVar`, `KBott`,
    /// `Bag`, `Cell`, and every `#`-prefixed head. It is kept only as the body of the deprecated
    /// [`Sort::is_reserved`].
    pub(crate) const fn is_reserved(self) -> bool {
        use KernelSort as S;
        match self {
            Self::Kernel(S::K | S::KItem | S::KConfigVar | S::KBott | S::Bag | S::Cell)
            | Self::RigidVariable
            | Self::Scaffolding => true,
            Self::Kernel(S::KLabel | S::KList | S::KString | S::Bool)
            | Self::Nat
            | Self::Defined => false,
        }
    }
}

// A term-presupposing predicate cannot grant positions to a role without terms.
const _: () = {
    let mut i = 0;
    while i < KernelSort::ALL.len() {
        let role = SortRole::Kernel(KernelSort::ALL[i]);
        assert!(
            !(role.has_implicit_kitem_subsort()
                || role.is_k_term_sort()
                || role.has_sort_predicate()
                || role.has_sort_projection()
                || role.admits_variables())
                || role.has_terms(),
            "a role predicate that presupposes terms holds for a role without terms"
        );
        i += 1;
    }
    let roles = [
        SortRole::RigidVariable,
        SortRole::Scaffolding,
        SortRole::Nat,
        SortRole::Defined,
    ];
    i = 0;
    while i < roles.len() {
        let role = roles[i];
        assert!(
            !(role.has_implicit_kitem_subsort()
                || role.is_k_term_sort()
                || role.has_sort_predicate()
                || role.has_sort_projection()
                || role.admits_variables())
                || role.has_terms(),
            "a role predicate that presupposes terms holds for a role without terms"
        );
        i += 1;
    }
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numeral_spellings_are_every_digit_string() {
        for name in [
            "99999999999999999999999",
            "8",
            "08",
            "4294967296",
            "18446744073709551616",
        ] {
            assert_eq!(Sort::new(name).role(), SortRole::Nat, "{name}");
        }
        for name in ["+8", "-8", "8a", ""] {
            assert_ne!(Sort::new(name).role(), SortRole::Nat, "{name}");
        }
    }

    #[test]
    fn term_presupposing_predicates_require_terms() {
        for role in KernelSort::ALL.into_iter().map(SortRole::Kernel).chain([
            SortRole::RigidVariable,
            SortRole::Scaffolding,
            SortRole::Nat,
            SortRole::Defined,
        ]) {
            assert!(
                !(role.has_implicit_kitem_subsort()
                    || role.is_k_term_sort()
                    || role.has_sort_predicate()
                    || role.has_sort_projection()
                    || role.admits_variables())
                    || role.has_terms(),
                "a role predicate that presupposes terms holds for a role without terms: {role:?}"
            );
        }
    }

    #[test]
    fn has_terms_rows_are_pinned() {
        for role in KernelSort::ALL.into_iter().map(SortRole::Kernel).chain([
            SortRole::RigidVariable,
            SortRole::Scaffolding,
            SortRole::Nat,
            SortRole::Defined,
        ]) {
            assert_eq!(role.has_terms(), role != SortRole::Nat, "{role:?}");
        }
    }

    // Verbatim copies of the classifier bodies the predicates replace. They are frozen here so
    // that the table below keeps comparing against the rules the consumers used when the
    // classification was introduced, after those consumers switch to `SortRole`.

    /// `is_parser_sort` (four byte-identical copies: inner/parser/parametric.rs,
    /// inner/parser/z3_inference.rs, kompile/passes/subsort_kitem.rs,
    /// kompile/passes/generate_sort_helpers.rs).
    fn legacy_is_parser_sort(sort: &Sort) -> bool {
        [BuiltinSort::K, BuiltinSort::KItem, BuiltinSort::KConfigVar]
            .iter()
            .any(|builtin| sort.name == builtin.k_name())
            || [
                FrontendSort::KBott,
                FrontendSort::KLabel,
                FrontendSort::KList,
                FrontendSort::KString,
            ]
            .iter()
            .any(|frontend| sort.name == frontend.as_str())
            || sort.name.starts_with('#')
            || sort.name.parse::<u64>().is_ok()
    }

    /// `is_real_ground_sort` (two identical copies: inner/parser/inference.rs,
    /// inner/parser/z3_inference.rs).
    fn legacy_is_real_ground_sort(sort: &Sort) -> bool {
        !sort.parameters.is_empty()
            || !legacy_is_parser_sort(sort)
            || sort.name == BuiltinSort::K.k_name()
            || sort.name == BuiltinSort::KItem.k_name()
            || sort.is_frontend(FrontendSort::KLabel)
            || sort.name.parse::<u64>().is_ok()
    }

    /// The domain filter of `concretize_parametric_productions` (inner/parser/parametric.rs).
    fn legacy_parametric_domain_filter(sort: &Sort) -> bool {
        !legacy_is_parser_sort(sort)
            || sort.name == BuiltinSort::K.k_name()
            || sort.name == BuiltinSort::KItem.k_name()
    }

    /// The skip condition of the projection loop (kompile/passes/generate_sort_helpers.rs): a
    /// sort that it skips gets no projection.
    fn legacy_projection_skip(sort: &Sort) -> bool {
        legacy_is_parser_sort(sort)
            && sort.name != BuiltinSort::K.k_name()
            && sort.name != BuiltinSort::KItem.k_name()
    }

    /// The values a Z3 parameter unknown could take at a nullary head before
    /// `in_parameter_domain`: the encoder admitted the heads that pass `is_real_ground_sort`
    /// for every unknown and removed `KLabel` from the parameter unknowns.
    fn legacy_parameter_domain(head: &Sort) -> bool {
        legacy_is_real_ground_sort(head) && !head.is_frontend(FrontendSort::KLabel)
    }

    /// `Sort::is_reserved` (kast/names.rs) as it read before it delegated to `SortRole`.
    fn legacy_is_reserved(sort: &Sort) -> bool {
        [BuiltinSort::K, BuiltinSort::KItem, BuiltinSort::KConfigVar]
            .iter()
            .any(|builtin| sort.name == builtin.k_name())
            || [FrontendSort::KBott, FrontendSort::Cell, FrontendSort::Bag]
                .iter()
                .any(|frontend| sort.name == frontend.as_str())
            || sort.name.starts_with('#')
    }

    fn parametric(name: &str, parameters: &[&str]) -> Sort {
        Sort::with_parameters(name, parameters.iter().copied().map(Sort::new).collect())
    }

    /// One pinned row: the sort, its role, and in order `has_implicit_kitem_subsort`,
    /// `is_k_term_sort`, `Sort::in_inference_domain`, `in_parameter_domain`, `is_reserved`.
    type Row = (Sort, SortRole, [bool; 5]);

    fn pinned_rows() -> Vec<Row> {
        use KernelSort as S;
        const T: bool = true;
        const F: bool = false;
        vec![
            (Sort::new("K"), SortRole::Kernel(S::K), [F, T, T, T, T]),
            (
                Sort::new("KItem"),
                SortRole::Kernel(S::KItem),
                [F, T, T, T, T],
            ),
            (
                Sort::new("KConfigVar"),
                SortRole::Kernel(S::KConfigVar),
                [F, F, F, F, T],
            ),
            (
                Sort::new("KBott"),
                SortRole::Kernel(S::KBott),
                [F, F, F, F, T],
            ),
            (
                Sort::new("KLabel"),
                SortRole::Kernel(S::KLabel),
                [F, F, T, F, F],
            ),
            (
                Sort::new("KList"),
                SortRole::Kernel(S::KList),
                [F, F, F, F, F],
            ),
            (
                Sort::new("KString"),
                SortRole::Kernel(S::KString),
                [F, F, F, F, F],
            ),
            (Sort::new("Bag"), SortRole::Kernel(S::Bag), [T, T, T, T, T]),
            (
                Sort::new("Cell"),
                SortRole::Kernel(S::Cell),
                [T, T, T, T, T],
            ),
            (
                Sort::new("Bool"),
                SortRole::Kernel(S::Bool),
                [T, T, T, T, F],
            ),
            (
                Sort::new("#RuleBody"),
                SortRole::Scaffolding,
                [F, F, F, F, T],
            ),
            (
                Sort::new("#KVariable"),
                SortRole::Scaffolding,
                [F, F, F, F, T],
            ),
            (
                Sort::new("#SortParam"),
                SortRole::RigidVariable,
                [F, F, F, F, T],
            ),
            // Every parametric sort is in the inference domain, whatever its head.
            (
                parametric("#SortParam", &["Q0"]),
                SortRole::RigidVariable,
                [F, F, T, F, T],
            ),
            (
                parametric("MInt", &["K"]),
                SortRole::Defined,
                [T, T, T, T, F],
            ),
            (Sort::new("8"), SortRole::Nat, [F, F, T, T, F]),
            (Sort::new("Exp"), SortRole::Defined, [T, T, T, T, F]),
            (Sort::new("KResult"), SortRole::Defined, [T, T, T, T, F]),
            (
                parametric("MInt", &["8"]),
                SortRole::Defined,
                [T, T, T, T, F],
            ),
            // A user-list helper sort does not start with `#`, so its spelling says `Defined`.
            (Sort::new("Ne#Exps"), SortRole::Defined, [T, T, T, T, F]),
        ]
    }

    #[test]
    fn pinned_roles_and_predicates_equal_the_legacy_classifiers() {
        let rows = pinned_rows();
        for kernel in KernelSort::ALL {
            assert!(
                rows.iter().any(|(sort, _, _)| *sort == kernel.sort()),
                "{} has a pinned row",
                kernel.name()
            );
        }
        for (sort, role, expected) in &rows {
            let head = Sort::new(sort.name.as_str());
            assert_eq!(sort.role(), *role, "role of {sort}");
            let actual = [
                role.has_implicit_kitem_subsort(),
                role.is_k_term_sort(),
                sort.in_inference_domain(),
                role.in_parameter_domain(),
                role.is_reserved(),
            ];
            assert_eq!(actual, *expected, "pinned predicates of {sort}");
            let legacy = [
                !legacy_is_parser_sort(sort),
                legacy_parametric_domain_filter(sort),
                legacy_is_real_ground_sort(sort),
                legacy_parameter_domain(&head),
                legacy_is_reserved(sort),
            ];
            assert_eq!(actual, legacy, "legacy predicates of {sort}");
            // The two legacy K-term filters are one property.
            assert_eq!(
                role.is_k_term_sort(),
                !legacy_projection_skip(sort),
                "projection filter of {sort}"
            );
            // The head row of the inference domain is the legacy rule on the nullary head.
            assert_eq!(
                role.in_inference_domain(),
                legacy_is_real_ground_sort(&head),
                "head inference domain of {sort}"
            );
            #[expect(
                deprecated,
                reason = "the deprecated wrapper must still answer as the legacy body did"
            )]
            let reserved = sort.is_reserved();
            assert_eq!(
                reserved,
                legacy_is_reserved(sort),
                "Sort::is_reserved of {sort}"
            );
            assert_eq!(
                sort.is_rigid_variable(),
                *role == SortRole::RigidVariable,
                "rigid variable {sort}"
            );
        }
    }

    /// The sort helpers of every role: `[has_sort_predicate, has_sort_projection]`. The kernel
    /// rows are the kernel helpers that compiled definitions declared before both the rule
    /// grammar and compilation read these predicates (`isK`, `isKItem`, `isKConfigVar`, `isBool`,
    /// `project:K`, `project:KItem`, `project:Bool`), and a projection always has a predicate.
    #[test]
    fn sort_helper_rows_are_pinned() {
        use KernelSort as S;
        let rows = [
            (SortRole::Kernel(S::K), [true, true]),
            (SortRole::Kernel(S::KItem), [true, true]),
            (SortRole::Kernel(S::KConfigVar), [true, false]),
            (SortRole::Kernel(S::KBott), [false, false]),
            (SortRole::Kernel(S::KLabel), [false, false]),
            (SortRole::Kernel(S::KList), [false, false]),
            (SortRole::Kernel(S::KString), [false, false]),
            (SortRole::Kernel(S::Bag), [false, false]),
            (SortRole::Kernel(S::Cell), [false, false]),
            (SortRole::Kernel(S::Bool), [true, true]),
            (SortRole::RigidVariable, [false, false]),
            (SortRole::Scaffolding, [false, false]),
            (SortRole::Nat, [false, false]),
            (SortRole::Defined, [true, true]),
        ];
        for kernel in KernelSort::ALL {
            assert!(
                rows.iter()
                    .any(|(role, _)| *role == SortRole::Kernel(kernel)),
                "{} has a row",
                kernel.name()
            );
        }
        for (role, expected) in rows {
            assert_eq!(
                [role.has_sort_predicate(), role.has_sort_projection()],
                expected,
                "{role:?}"
            );
            assert!(
                !role.has_sort_projection() || role.has_sort_predicate(),
                "{role:?} has a projection without a predicate"
            );
        }
    }

    /// The kernel positions of every role: `[has_implicit_kitem_subsort, admits_variables]`. A sort strictly
    /// below `KItem` is a sort of K items, so it is also a sort a variable stands at; `K` and
    /// `KItem` are above every such sort, and the bottom sorts `KBott` and `KConfigVar` are below
    /// every sort a variable stands at.
    #[test]
    fn kernel_position_rows_are_pinned() {
        use KernelSort as S;
        let rows = [
            (SortRole::Kernel(S::K), [false, true]),
            (SortRole::Kernel(S::KItem), [false, true]),
            (SortRole::Kernel(S::KConfigVar), [false, false]),
            (SortRole::Kernel(S::KBott), [false, false]),
            (SortRole::Kernel(S::KLabel), [false, true]),
            (SortRole::Kernel(S::KList), [false, true]),
            (SortRole::Kernel(S::KString), [false, true]),
            (SortRole::Kernel(S::Bag), [true, true]),
            (SortRole::Kernel(S::Cell), [true, true]),
            (SortRole::Kernel(S::Bool), [true, true]),
            (SortRole::RigidVariable, [false, false]),
            (SortRole::Scaffolding, [false, false]),
            (SortRole::Nat, [false, false]),
            (SortRole::Defined, [true, true]),
        ];
        for kernel in KernelSort::ALL {
            assert!(
                rows.iter()
                    .any(|(role, _)| *role == SortRole::Kernel(kernel)),
                "{} has a row",
                kernel.name()
            );
        }
        for (role, expected) in rows {
            assert_eq!(
                [role.has_implicit_kitem_subsort(), role.admits_variables()],
                expected,
                "{role:?}"
            );
            assert!(
                !role.has_implicit_kitem_subsort() || role.admits_variables(),
                "{role:?} lies below KItem but admits no variable"
            );
        }
    }

    #[test]
    fn kernel_sorts_round_trip_through_their_names() {
        for kernel in KernelSort::ALL {
            assert_eq!(KernelSort::of_name(kernel.name()), Some(kernel));
            assert_eq!(kernel.sort().role(), SortRole::Kernel(kernel));
        }
        assert_eq!(KernelSort::of_name("KResult"), None);
        assert_eq!(KernelSort::of_name("#KVariable"), None);
    }
}
