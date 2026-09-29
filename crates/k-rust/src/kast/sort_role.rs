//! The role of a sort head, decided once from its spelling.
//!
//! A sort name in the frontend denotes a kernel sort (whose meaning K fixes whatever the
//! definition declares), a sort the definition declares, a numeral sort argument, parser
//! scaffolding, or a rigid sort variable of a sentence. [`Sort::role`] is the one place that reads
//! the role from the spelling, and every property that separates those roles is one exhaustive
//! `match` on [`SortRole`], so adding a role forces a decision in every property.

#![deny(clippy::wildcard_enum_match_arm)]

use crate::names::BuiltinSort;

use super::{FrontendSort, Sort};

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
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "first read by the per-sort grammar generators (CBC-05-T3)"
        )
    )]
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
    /// A decimal numeral: a sort argument such as the width of `MInt{8}`.
    Nat,
    /// Any other head: its meaning comes from the definition.
    Defined,
}

impl Sort {
    /// The role of this sort's head: a kernel spelling, then `#SortParam`, then any other leading
    /// `#`, then a decimal numeral that fits in a `u64`, else a defined sort.
    ///
    /// Parameters are ignored: the role of `MInt{8}` is the role of `MInt`.
    pub(crate) fn role(&self) -> SortRole {
        if let Some(kernel) = KernelSort::of_name(&self.name) {
            SortRole::Kernel(kernel)
        } else if self.name == FrontendSort::SortParam.as_str() {
            SortRole::RigidVariable
        } else if self.name.starts_with('#') {
            SortRole::Scaffolding
        } else if self.name.parse::<u64>().is_ok() {
            SortRole::Nat
        } else {
            SortRole::Defined
        }
    }

    /// Whether this sort is a rigid sort variable of a sentence (`#SortParam{Q}`), which stands
    /// for every sort at once and is never solved.
    pub(crate) fn is_rigid_variable(&self) -> bool {
        self.role() == SortRole::RigidVariable
    }

    /// Whether this sort is a value an inference unknown can take.
    ///
    /// A parametric sort reaches the inner parser only as a declared instance or as a registered
    /// placeholder, and inference treats both as values, so every parametric sort is admitted;
    /// a nullary sort is admitted by its role.
    pub(crate) fn in_inference_domain(&self) -> bool {
        !self.parameters.is_empty() || self.role().in_inference_domain()
    }
}

impl SortRole {
    /// Every term of the sort is a `KItem`: compilation declares `S < KItem` for it.
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

    /// A value an inference unknown can take: a K term sort, `KLabel` (the sort of label
    /// variables), or a numeral (the width parameters of sorts such as `MInt{N}`).
    ///
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
    /// since a sort parameter ranges over sorts of terms and widths, not over labels.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "first read by the Z3 parameter encoding (CBC-05-T2)"
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

#[cfg(test)]
mod tests {
    use super::*;

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

    /// The values a Z3 parameter unknown can take at a nullary head: `restrict_to_real_sorts`
    /// admits the heads that pass `is_real_ground_sort`, and `exclude_klabel_parameters` removes
    /// `KLabel` from the parameter unknowns (inner/parser/z3_inference.rs).
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
