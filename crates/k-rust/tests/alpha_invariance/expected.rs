//! The results that fail today, each with the ticket whose fix makes it pass.
//!
//! The tickets, and the reason each of their results fails:
//! - `BIND/A3` (FU-26, FU-32/D1): the converter reads a quantifier over an anonymous variable as
//!   binding every anonymous variable of its body, and drops the binder's own variable and sort;
//!   the alpha-variant that names each `_` apart binds exactly the binder's own variable. This
//!   includes a function competitor's own axiom, where an anonymous binder's sort annotation
//!   (`#Exists _:Bool . ...`) is lost as well.
//! - `BIND/A4` (FU-33/D2): existential lifting reads the `?` variables of the right side and the
//!   `ensures` through their binders; on an anonymous `?_` binder the outer binder is vacuous and
//!   the kompile invariant K3 panics, so the base itself fails.
//! - `BIND/A5` (FU-34/D3): the definition check treats a binder as binding its name in the whole
//!   sentence, so a right-side variable spelled like an `ensures` binder passes the check, and the
//!   variant with the binder renamed apart is refused.
//! - `BIND/A6` (FU-35/D4, FU-36/D5): passes apply one name map to a whole sentence, so a binder
//!   that shadows another variable of its sentence is captured: macro substitution replaces a
//!   parameter under a macro binder of the same name, and `minimize term construction` replaces
//!   a subterm of the left side under a binder that rebinds one of its variables.
//! - `BIND/A7` (FU-37/D6): the strictness and context sentences place the minted `K<i>` and
//!   `HERE` beside a context alias's variables without renaming them apart, so an alias variable
//!   spelled `K<i>` merges with a strictness variable.
//! - `FU-B` (outside BIND): the parser's sort inference refuses one name bound at two sorts in
//!   separate scopes, so the base does not load and nothing is compared.
//! - `unassigned`: no BIND ticket covers these. The `UNIQUE_ID` digest numbers variables by
//!   spelling (`number_sentences.rs`), so a shadowing binder renamed apart, a variable named in
//!   an attribute (`concrete(X)`), or a `#let`/`#fun` whose minted label carries a variable's
//!   spelling changes the identifier of an alpha-equivalent sentence; and fresh constants take
//!   their counter offsets in the order of their spellings (`fresh-variables`), so a renaming
//!   that reorders the spellings changes which fresh value each variable gets.

pub use super::harness::Kind;

/// One expected failure: the case, the strategy (`*` for a failure of the base itself), the
/// ticket, the kind of failure and a text the failure's report holds.
pub struct Expected {
    pub case: &'static str,
    pub strategy: &'static str,
    pub ticket: &'static str,
    pub kind: Kind,
    pub needle: &'static str,
}

impl Expected {
    pub fn key(&self) -> String {
        format!("{} {}", self.case, self.strategy)
    }
}

const fn expected(
    case: &'static str,
    strategy: &'static str,
    ticket: &'static str,
    kind: Kind,
    needle: &'static str,
) -> Expected {
    Expected {
        case,
        strategy,
        ticket,
        kind,
        needle,
    }
}

#[rustfmt::skip]
pub const EXPECTED: &[Expected] = &[
    // BIND/A3 (29)
    expected("anon/E-anon-binder-requires", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("anon/E-anon-binder-sorted-requires", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("anon/F-anon-binder-requires", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("anon/F-anon-binder-sorted-requires", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("compile/exists-anon", "anon-named", "BIND/A3", Kind::Kore, "Var'Unds'B1:SortK{}"),
    expected("condition-exists-anonymous", "anon-named", "BIND/A3", Kind::Kore, "Var'Unds'B1:SortK{}"),
    expected("d1-macro-binder-anonymous-use", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("fixture/fixtures/search-pattern/pattern.k", "anon-named", "BIND/A3", Kind::Kore, "MACROS"),
    expected("fu26-exists-anonymous", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("fu26-forall-anonymous", "anon-named", "BIND/A3", Kind::Kore, "Var'Unds'B1:SortK{}"),
    expected("macro/E-fresh-anon-first", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("macro/E-fresh-anon-second", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("macro/F-fresh-anon-first", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("macro/F-fresh-anon-second", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise-partial-anonymous", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise-partial-anonymous-and-named", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise-rule-anonymous-binder-sort", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-Y-P-ensures", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-Y-P-plain", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-Y-P-requires", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-Y-Y-plain", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-Y0-P-ensures", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-Y0-P-plain", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-Y0-P-requires", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-Y0-Y-plain", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-none-P-ensures", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-none-P-plain", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-none-P-requires", "anon-named", "BIND/A3", Kind::Kore, ""),
    expected("owise/anon-none-Y-plain", "anon-named", "BIND/A3", Kind::Kore, ""),
    // BIND/A4 (2)
    expected("anon/E-anon-binder-ensures", "*", "BIND/A4", Kind::BasePanic, "K3"),
    expected("d2-ensures-exists-anonymous", "*", "BIND/A4", Kind::BasePanic, "Var'QuesUnds'Gen1"),
    // BIND/A5 (1)
    expected("d3-rhs-variable-under-ensures-binder", "binder-apart", "BIND/A5", Kind::VariantRefused, "UnboundVariable"),
    // BIND/A6 (103)
    expected("d4-macro-binder-shadows-parameter", "binder-apart", "BIND/A6", Kind::Kore, "run go(3)"),
    expected("d4-macro-binder-shadows-parameter-literal", "binder-apart", "BIND/A6", Kind::BaseRefused, "the first argument must be a variable"),
    expected("d5-binder-apart-from-lhs-variable", "binder-capture", "BIND/A6", Kind::Kore, "run go(s(3))"),
    expected("d5-binder-shadows-lhs-variable", "binder-apart", "BIND/A6", Kind::Kore, "run go(s(3))"),
    expected("function/E-lhs-owise", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("function/F-fresh-owise", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("function/F-lhs-owise", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("lambda/fun-fresh", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("lambda/fun-lhs", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("lambda/let-fresh", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("lambda/let-lhs", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("macro/E-param1-anon-second", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("macro/E-param1-literal", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("macro/E-param1-twice", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("macro/E-param2-anon-first", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("macro/E-param2-literal", "binder-apart", "BIND/A6", Kind::BaseRefused, ""),
    expected("macro/E-param2-twice", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("macro/F-param1-anon-second", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("macro/F-param1-literal", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("macro/F-param1-twice", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("macro/F-param2-anon-first", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("macro/F-param2-literal", "binder-apart", "BIND/A6", Kind::BaseRefused, ""),
    expected("macro/F-param2-twice", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("one/E-fresh-same-argument", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/E-fresh-same-ensures", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/E-fresh-same-requires", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/E-fresh-same-rhs", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/E-lhs-same-argument", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("one/E-lhs-same-ensures", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("one/E-lhs-same-requires", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("one/E-lhs-same-rhs", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("one/E-minted-same-argument", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/E-minted-same-ensures", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/E-minted-same-requires", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/E-minted-same-rhs", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/F-fresh-same-argument", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/F-fresh-same-ensures", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/F-fresh-same-requires", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/F-fresh-same-rhs", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/F-lhs-same-argument", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("one/F-lhs-same-ensures", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("one/F-lhs-same-requires", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("one/F-lhs-same-rhs", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("one/F-minted-same-argument", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/F-minted-same-ensures", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/F-minted-same-requires", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("one/F-minted-same-rhs", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-distinct-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-distinct-nested", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-distinct-nested-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-lhs-conj", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-lhs-nested", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-lhs-nested-split", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-mixed-conj", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-mixed-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-mixed-nested", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-mixed-nested-split", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-mixed-nested-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-same-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-same-nested", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EEE-same-nested-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-distinct-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-distinct-nested", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-distinct-nested-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-lhs-conj", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-lhs-nested", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-lhs-nested-split", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-mixed-conj", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-mixed-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-mixed-nested", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-mixed-nested-split", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-mixed-nested-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-same-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-same-nested", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("three/EFE-same-nested-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EE-distinct-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EE-distinct-conj-other-sort", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EE-distinct-nested", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EE-distinct-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EE-lhs-conj", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("two/EE-lhs-nested", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("two/EE-lhs-split", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("two/EE-same-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EE-same-nested", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EE-same-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EF-distinct-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EF-distinct-nested", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EF-distinct-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EF-lhs-conj", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("two/EF-lhs-nested", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("two/EF-lhs-split", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("two/EF-same-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EF-same-nested", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/EF-same-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/FE-distinct-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/FE-distinct-nested", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/FE-distinct-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/FE-lhs-conj", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("two/FE-lhs-nested", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("two/FE-lhs-split", "binder-apart", "BIND/A6", Kind::Kore, ""),
    expected("two/FE-same-conj", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/FE-same-nested", "binder-capture", "BIND/A6", Kind::Kore, ""),
    expected("two/FE-same-split", "binder-capture", "BIND/A6", Kind::Kore, ""),
    // BIND/A7 (12)
    expected("context/seqstrict-I1", "k-index", "BIND/A7", Kind::Kore, "-heat"),
    expected("context/seqstrict-K0", "fresh", "BIND/A7", Kind::Kore, "-heat"),
    expected("context/seqstrict-K1", "fresh", "BIND/A7", Kind::Kore, "-heat"),
    expected("context/seqstrict-K1", "k-index", "BIND/A7", Kind::Kore, "-heat"),
    expected("context/seqstrict-S", "k-index", "BIND/A7", Kind::Kore, "-heat"),
    expected("context/strict-I1", "k-index", "BIND/A7", Kind::Kore, "-heat"),
    expected("context/strict-K0", "fresh", "BIND/A7", Kind::Kore, "-heat"),
    expected("context/strict-K1", "fresh", "BIND/A7", Kind::Kore, "-heat"),
    expected("context/strict-K1", "k-index", "BIND/A7", Kind::Kore, "-heat"),
    expected("context/strict-S", "k-index", "BIND/A7", Kind::Kore, "-heat"),
    expected("d6-context-alias-variable-k0", "fresh", "BIND/A7", Kind::Kore, "run 1 + (2 + 3)"),
    expected("d6-context-alias-variable-s", "k-index", "BIND/A7", Kind::Kore, "run 1 + (2 + 3)"),
    // FU-B (27)
    expected("one/E-lhs-other-argument", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("one/E-lhs-other-ensures", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("one/E-lhs-other-requires", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("one/E-lhs-other-rhs", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("one/F-lhs-other-argument", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("one/F-lhs-other-ensures", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("one/F-lhs-other-requires", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("one/F-lhs-other-rhs", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y-Y-Y-ensures", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y-Y-Y-requires", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y-Y0-Y-ensures", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y-Y0-Y-requires", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y-none-Y-ensures", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y-none-Y-requires", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y0-Y-Y-ensures", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y0-Y-Y-requires", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y0-Y0-Y-ensures", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y0-Y0-Y-requires", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y0-none-Y-ensures", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/Y0-none-Y-requires", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/anon-Y-Y-ensures", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/anon-Y-Y-requires", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/anon-Y0-Y-ensures", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/anon-Y0-Y-requires", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/anon-none-Y-ensures", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("owise/anon-none-Y-requires", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    expected("two/EE-same-conj-other-sort", "*", "FU-B", Kind::BaseRefused, "could not parse rule"),
    // unassigned (46)
    expected("binder-shadows-lhs-variable-same-sort", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("compile/concrete-rw2", "fresh", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("compile/concrete-rw2", "k-index", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("compile/fresh-variables", "rotate", "unassigned", Kind::Kore, "freshFoo"),
    expected("compile/let-list-binder", "fresh", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("compile/let-list-binder", "k-index", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("compile/let-list-binder", "rotate", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/collection-cell-content.k", "fresh", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/collection-cell-content.k", "k-index", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/collection-cell-content.k", "rotate", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/generated-rule-syntax.k", "fresh", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/generated-rule-syntax.k", "k-index", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/generated-rule-syntax.k", "rotate", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/regression/equals-pattern.k", "fresh", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/regression/equals-pattern.k", "k-index", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/regression/equals-pattern.k", "rotate", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/regression/let-test.k", "fresh", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/regression/let-test.k", "k-index", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("fixture/fixtures/sentence-typing/regression/let-test.k", "rotate", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("lambda/fun-fresh", "fresh", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("lambda/fun-fresh", "k-index", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("lambda/fun-fresh", "rotate", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("lambda/fun-lhs", "fresh", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("lambda/fun-lhs", "k-index", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("macro/E-param1-anon-first", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("macro/E-param2-anon-second", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("macro/F-param1-anon-first", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("macro/F-param2-anon-second", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("prelude", "fresh", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("prelude", "k-index", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("prelude", "rotate", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("three/EEE-same-conj", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("three/EEE-same-nested", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("three/EEE-same-nested-split", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("three/EFE-same-conj", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("three/EFE-same-nested", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("three/EFE-same-nested-split", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("two/EE-same-conj", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("two/EE-same-nested", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("two/EE-same-split", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("two/EF-same-conj", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("two/EF-same-nested", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("two/EF-same-split", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("two/FE-same-conj", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("two/FE-same-nested", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
    expected("two/FE-same-split", "binder-apart", "unassigned", Kind::Id, "UNIQUE_ID differs"),
];
