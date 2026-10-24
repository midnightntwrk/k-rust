//! fz26 KINK-BASELINE-FINDINGS: kink-native's data facts (`data`), each definition's full
//! critical-pair check as kink reads it, on the route kink runs it on.
//!
//! - r3-plainq (`testdata/flow/findings/r3-plainq`, `q(_) => a` beside `q(_) => bb`) has one
//!   genuine finding, so no end is data; naming it makes every end the terminal-value walk admits
//!   data again, the finding marked assumed.
//! - A name that names no finding, or a decided one, is refused; a decided finding is never
//!   assumed.
//! - The mutant comparison reads only the findings outside the checked heads, and every finding
//!   when the gate read no head (an `IndexedAt` row is read for every set of heads).
//! - The names of a precondition row and of an equation finding are pinned (k-rust-fuzz pins the
//!   same literals).

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::BTreeSet;
use std::path::Path;

use k_rust::kompile::CompileOptions;
use k_rust::kore::parser::parse_definition;
use k_rust_backend::definition::BackendDefinition;
use kink_native::NativeValidator;
use kink_native::consistency::loaded_definition;
use kink_native::data::{DataEnds, DataFacts, FindingVerdict, data_ends};

const PLAINQ_PAIR: &str = "spec.k:7:3,spec.k:8:3@root";

/// The name of `kbf/listrow.k`'s precondition row.
const LISTROW_ROW: &str = "precondition:listrow.k:11:3";

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// A compiled flow fixture's `spec.k`, loaded as kink runs it.
fn flow_definition(flow: &str, main_module: &str) -> std::sync::Arc<BackendDefinition> {
    let path = Path::new(support::DIR).join(format!("../flow/findings/{flow}/spec.k"));
    let compiled = NativeValidator::bind(
        support::load_path(&path, main_module),
        CompileOptions::default(),
    )
    .compile_baseline()
    .unwrap();
    loaded_definition(&compiled).unwrap()
}

/// The facts of a compiled flow fixture's `spec.k`, loaded as kink runs it.
fn flow_facts(flow: &str, main_module: &str, names: &[String]) -> DataFacts {
    DataFacts::of(&flow_definition(flow, main_module), names)
}

fn counter_facts() -> DataFacts {
    let compiled = NativeValidator::bind(support::load("counter.k"), CompileOptions::default())
        .compile_baseline()
        .unwrap();
    DataFacts::of(&loaded_definition(&compiled).unwrap(), &[])
}

#[test]
fn a_finding_leaves_no_end_data_until_it_is_named() {
    on_a_big_stack(|| {
        let strict = flow_facts("r3-plainq", "PQ", &[]);
        assert_eq!(data_ends(&strict), DataEnds::None);
        let [finding] = strict.unnamed().try_into().unwrap();
        assert_eq!(finding.name.as_deref(), Some(PLAINQ_PAIR));
        assert_eq!(finding.verdict, FindingVerdict::Genuine);
        assert!(!finding.assumed);
        assert!(strict.refused_names().is_empty());

        let named = flow_facts("r3-plainq", "PQ", &[PLAINQ_PAIR.to_owned()]);
        assert_eq!(data_ends(&named), DataEnds::Admitted);
        assert!(named.unnamed().is_empty());
        let [assumed] = named.findings().try_into().unwrap();
        assert!(assumed.assumed);
        assert_eq!(assumed.identity, finding.identity);
        assert!(named.refused_names().is_empty());
        assert_eq!(
            named.value()["assume_joined"],
            serde_json::json!([PLAINQ_PAIR])
        );

        assert_eq!(data_ends(&counter_facts()), DataEnds::Admitted);
    });
}

#[test]
fn a_name_that_names_no_finding_is_refused() {
    on_a_big_stack(|| {
        let facts = flow_facts(
            "r3-plainq",
            "PQ",
            &["spec.k:1:1,spec.k:2:1@root".to_owned()],
        );
        let [refusal] = facts.refused_names().try_into().unwrap();
        assert!(refusal.reason.contains("names no finding"), "{refusal:?}");
        assert_eq!(data_ends(&facts), DataEnds::None);
    });
}

/// INT8 follow-ups (review N4)'s hand-written KORE: an equation whose right-hand side leaves `Y`
/// unbound is a decided finding, which no name assumes and whose name is refused.
#[test]
fn a_decided_finding_is_never_assumed_and_its_name_is_refused() {
    const FIXTURE: &str =
        include_str!("../../../../crates/k-rust-backend/tests/fixtures/overloaded-list-owise.kore");
    let (head, tail) = FIXTURE.rsplit_once("endmodule").expect("one module");
    let source = format!(
        r#"{head}
    symbol any{{}}(SortExps{{}}) : SortVal{{}} [function{{}}()]
    axiom{{R}} \implies{{R}}(
        \and{{R}}(\top{{R}}(),
            \and{{R}}(\in{{SortExps{{}}, R}}(X0:SortExps{{}}, Es:SortExps{{}}), \top{{R}}())),
        \equals{{SortVal{{}}, R}}(any{{}}(X0:SortExps{{}}), \and{{SortVal{{}}}}(Y:SortVal{{}}, \top{{SortVal{{}}}}())))
        [label{{}}("any-unbound")]
endmodule{tail}"#
    );
    let definition = BackendDefinition::internalize(
        &parse_definition(&source).unwrap(),
        "OVERLOADED-LIST-OWISE",
    )
    .unwrap();
    let strict = DataFacts::of(&definition, &[]);
    let decided = strict
        .unnamed()
        .into_iter()
        .find(|finding| finding.verdict == FindingVerdict::Decided)
        .expect("a decided finding");
    let name = decided.name.clone().expect("named");
    // k-rust-fuzz `findings.rs` pins the same name.
    assert_eq!(name, "equation:any-unbound");
    let named = DataFacts::of(&definition, std::slice::from_ref(&name));
    assert!(
        named.unnamed().contains(&decided),
        "a decided finding is never assumed"
    );
    let refusals = named.refused_names();
    assert!(
        refusals
            .iter()
            .any(|refusal| refusal.name == name && refusal.reason.contains("decided finding")),
        "{refusals:?}"
    );
}

/// The mutant comparison: findings inside the checked heads are the consistency gate's; only
/// those outside are compared, by identity and name.
#[test]
fn only_the_findings_outside_the_checked_heads_are_compared() {
    on_a_big_stack(|| {
        let plainq = flow_facts("r3-plainq", "PQ", &[]);
        let clean = counter_facts();
        let none = BTreeSet::new();
        assert!(!plainq.differs_outside(&plainq, Some(&none)));
        assert!(plainq.differs_outside(&clean, Some(&none)));
        assert!(clean.differs_outside(&plainq, Some(&none)));
        // Every head checked: every finding is the gate's.
        assert!(!plainq.differs_outside(&clean, None));
        // `q` checked: its pair is inside.
        let q = flow_definition("r3-plainq", "PQ")
            .symbols()
            .keys()
            .filter(|name| name.starts_with("Lblq"))
            .map(ToString::to_string)
            .collect::<BTreeSet<_>>();
        assert_eq!(q.len(), 1, "{q:?}");
        assert!(!plainq.differs_outside(&clean, Some(&q)));
        // Assuming a finding does not hide it from the comparison.
        let named = flow_facts("r3-plainq", "PQ", &[PLAINQ_PAIR.to_owned()]);
        assert!(!named.differs_outside(&plainq, Some(&none)));
        assert!(named.differs_outside(&clean, Some(&none)));
    });
}

fn listrow_facts(names: &[String]) -> DataFacts {
    let compiled = NativeValidator::bind(
        support::load_path(&Path::new(support::DIR).join("kbf/listrow.k"), "LISTROW"),
        CompileOptions::default(),
    )
    .compile_baseline()
    .unwrap();
    DataFacts::of(&loaded_definition(&compiled).unwrap(), names)
}

/// Review S1: an `IndexedAt` row is read by the consistency gate for every set of heads, the
/// empty one included, so a comparison of the findings outside no head misses it; when the gate
/// read no head, every finding is compared. Review N4: the row's name is pinned (k-rust-fuzz's
/// `tests/kink_names.rs` pins it too) and, being decided, refused.
#[test]
fn every_finding_is_compared_when_the_gate_read_no_head() {
    on_a_big_stack(|| {
        let listrow = listrow_facts(&[]);
        let clean = counter_facts();
        let [row] = listrow.unnamed().try_into().unwrap();
        assert_eq!(row.name.as_deref(), Some(LISTROW_ROW));
        assert_eq!(row.verdict, FindingVerdict::Decided);
        assert_eq!(data_ends(&listrow), DataEnds::None);
        let none = BTreeSet::new();
        assert!(!listrow.differs_outside(&clean, Some(&none)));
        assert!(listrow.differs(&clean));
        assert!(clean.differs(&listrow));
        assert!(!listrow.differs(&listrow_facts(&[])));
        let named = listrow_facts(&[LISTROW_ROW.to_owned()]);
        let [refusal] = named.refused_names().try_into().unwrap();
        assert!(refusal.reason.contains("decided finding"), "{refusal:?}");
        assert!(listrow.incomplete().is_none() && clean.incomplete().is_none());
    });
}

/// Review N4: a side prefix is k-rust-fuzz's; kink says so when it refuses one.
#[test]
fn a_side_prefixed_name_is_refused_as_such() {
    on_a_big_stack(|| {
        let facts = flow_facts("r3-plainq", "PQ", &[format!("baseline:{PLAINQ_PAIR}")]);
        let [refusal] = facts.refused_names().try_into().unwrap();
        assert!(
            refusal.reason.contains("without a side prefix"),
            "{refusal:?}"
        );
    });
}
