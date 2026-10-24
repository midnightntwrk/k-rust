//! fz26 KINK-BASELINE-FINDINGS: kink-native's data facts (`data`), each definition's full
//! critical-pair check as kink reads it, on the route kink runs it on.
//!
//! - r3-plainq (`testdata/flow/findings/r3-plainq`, `q(_) => a` beside `q(_) => bb`) has one
//!   genuine finding, so no end is data; naming it makes every end the terminal-value walk admits
//!   data again, the finding marked assumed.
//! - A name that names no finding, or a decided one, is refused; a decided finding is never
//!   assumed.
//! - The mutant comparison reads only the findings outside the checked heads.

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
        assert!(matches!(data_ends(&named), DataEnds::Admitted(_)));
        assert!(named.unnamed().is_empty());
        let [assumed] = named.findings().try_into().unwrap();
        assert!(assumed.assumed);
        assert_eq!(assumed.identity, finding.identity);
        assert!(named.refused_names().is_empty());
        assert_eq!(
            named.value()["assume_joined"],
            serde_json::json!([PLAINQ_PAIR])
        );

        assert!(matches!(data_ends(&counter_facts()), DataEnds::Admitted(_)));
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
    assert!(name.starts_with("equation:"), "{name}");
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

/// fz26 KINK-OVERLOAD-VALUE: the walk admits an application of an overload data head only with
/// the definition's own facts (`data_ends`, `ObservationDecider::judging_data`), only where
/// k-rust's `is_data` holds on it (instance-normal: no overload equation of the definition
/// applies), and, for leaves of another definition, only where it is data there too. FZ-OVERLIST's
/// `ov` (`testdata/k/overload/ov.k`): `1, .Ids` at sort `Exps` holds an `Int`, which no overload
/// equation lowers to `Ids`, so it is a normal form; `a, .Ids` at sort `Exps` is lowered to an
/// `Ids` list by an overload equation, so it is not.
#[test]
fn an_overload_application_is_data_only_where_it_is_instance_normal() {
    use k_rust::kore::ast::{Pattern, Sort, Symbol};
    use k_rust_backend::term::Sort as InternalSort;
    use kink_native::feasibility::TestInitialState;
    use kink_native::step_events::ObservationDecider;
    on_a_big_stack(|| {
        let compiled = NativeValidator::bind(
            support::load_path(&Path::new(support::DIR).join("overload/ov.k"), "OV"),
            CompileOptions::default(),
        )
        .compile_baseline()
        .unwrap();
        let definition = loaded_definition(&compiled).unwrap();
        let facts = DataFacts::of(&definition, &[]);
        let ends = data_ends(&facts);
        assert!(matches!(ends, DataEnds::Admitted(_)), "{facts:?}");
        let sort = |name: &str| Sort::Application {
            name: name.to_owned(),
            arguments: Vec::new(),
        };
        let symbol = |result: &str, arity: usize, data_head: bool| {
            definition
                .symbols()
                .values()
                .find(|symbol| {
                    symbol.result_sort == InternalSort::simple(result)
                        && symbol.argument_sorts.len() == arity
                        && symbol.name.starts_with("Lbl")
                        && ends.overload_head(&symbol.name) == data_head
                        && (arity == 2 || symbol.name.contains("List"))
                })
                .unwrap_or_else(|| panic!("a symbol of {result}/{arity}"))
                .name
                .to_string()
        };
        let cons = symbol("SortExps", 2, true);
        let unit = symbol("SortIds", 0, false);
        let app = |name: &str, arguments| Pattern::Application {
            symbol: Symbol {
                name: name.to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments,
        };
        let inj = |from: &str, to: &str, argument| Pattern::Application {
            symbol: Symbol {
                name: "inj".to_owned(),
                sort_parameters: vec![sort(from), sort(to)],
            },
            arguments: vec![argument],
        };
        let dv = |of: &str, value: &str| Pattern::DomainValue {
            sort: sort(of),
            value: value.into(),
        };
        let list = |element: Pattern| {
            app(
                &cons,
                vec![element, inj("SortIds", "SortExps", app(&unit, Vec::new()))],
            )
        };
        let int = list(inj("SortInt", "SortExp", dv("SortInt", "1")));
        let id = list(inj("SortId", "SortExp", dv("SortId", "a")));
        let solver = k_rust_backend::smt::NoSolver;
        let decider = |judging: bool| {
            let decider =
                ObservationDecider::new(&definition, &solver, TestInitialState::of_test(&int));
            if judging {
                decider.judging_data(ends, ends)
            } else {
                decider
            }
        };
        assert!(ends.overload_application_is_data(&definition, &int));
        assert!(decider(true).definition_independent(&int));
        assert_eq!(decider(true).terminal_value(&int), Some(int.clone()));
        // Without the definition's facts, or with a finding left, no overload application.
        assert!(!decider(false).definition_independent(&int));
        assert!(!DataEnds::None.overload_head(&cons));
        // Not instance-normal: an overload equation lowers it.
        assert!(!ends.overload_application_is_data(&definition, &id));
        assert!(!decider(true).definition_independent(&id));
        // Nested in a free constructor, judged once at the outermost overload application.
        assert!(decider(true).definition_independent(&inj("SortExps", "SortKItem", int.clone())));
        // A leaf of another definition (counter.k lacks the symbols): not data there.
        let counter = loaded_definition(
            &NativeValidator::bind(support::load("counter.k"), CompileOptions::default())
                .compile_baseline()
                .unwrap(),
        )
        .unwrap();
        let counter_facts = DataFacts::of(&counter, &[]);
        let leaves = ObservationDecider::for_leaves_of(
            &definition,
            &counter,
            &solver,
            TestInitialState::of_test(&int),
        );
        assert!(
            !leaves
                .judging_data(ends, data_ends(&counter_facts))
                .definition_independent(&int)
        );
    });
}

/// fz26 KINK-OVERLOAD-VALUE consumes k-rust's data judgement rather than re-implementing it, so
/// the passages its soundness rests on are pinned by digest: `data_term`'s module documentation
/// from "The class" through "Two definitions" (what a data term is, why two differ in each
/// definition's initial model under A1 and A2, and that ends compared across two definitions
/// must be data in both, each judged by its own), the selection of the overload data heads
/// (`overload_data_heads`, `canonical_overload_equation`) and the walk `is_data` makes
/// (`built_from_data`). A k-rust change that moves any of them fails here, and kink's reading
/// (kink-native `data::data_ends`, the TV-01 walk) is checked against it again before re-pinning.
#[test]
fn the_data_judgement_kink_reads_is_pinned() {
    const SOURCE: &str = include_str!("../../../../crates/k-rust-backend/src/data_term.rs");
    let between = |from: &str, to: &str| {
        let start = SOURCE.find(from).unwrap_or_else(|| panic!("no {from:?}"));
        let end = SOURCE[start..]
            .find(to)
            .unwrap_or_else(|| panic!("no {to:?}"))
            + start;
        &SOURCE[start..end]
    };
    let function = |name: &str| between(&format!("fn {name}("), "\n}\n");
    let method = |name: &str| between(&format!("    fn {name}("), "\n    }\n");
    let pinned = [
        (
            between("//! # The class", "//! # Findings: genuine or undecided"),
            "doc",
        ),
        (method("overload_data_heads"), "overload_data_heads"),
        (
            function("canonical_overload_equation"),
            "canonical_overload_equation",
        ),
        (method("built_from_data"), "built_from_data"),
    ]
    .map(|(text, name)| (name, kink_patch::sha256(text.as_bytes()).to_string()));
    assert_eq!(
        pinned,
        [
            (
                "doc",
                "5ebdb4fa12e513bb1c2da9be194120fe9b2b322ab49800a4c5b073cd5c18fdff",
            ),
            (
                "overload_data_heads",
                "655cb79c76f4bb457e81e60681043fc35de8661cc9a475efe378faa9001fbb34",
            ),
            (
                "canonical_overload_equation",
                "ce72331ace58ecd71b41ed67068c952b3d972d2e84cab18a36cef89f9a42c26b",
            ),
            (
                "built_from_data",
                "7b76f08166b68d2a94290b090933f570af2e701f64df7114399ec57964b311e5",
            ),
        ]
        .map(|(name, digest)| (name, digest.to_owned()))
    );
}
