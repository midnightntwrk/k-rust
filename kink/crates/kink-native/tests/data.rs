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

/// fz26 KRUST-ANYWHERE-HEAD (review M7, the reverse r2-anyw shape): in `anyw-anywhere.k` the
/// production `c(Int)` heads the plain rule `c(1) => d [anywhere]`, so the compiler declares it
/// `anywhere, function, value-production`. It is a data head now (no overload equation is
/// needed), and the walk admits an application of it exactly where k-rust's `is_data` holds:
/// `c(2)`, which the rule does not match, is a normal form in every context and a value; `c(1)`,
/// which the rule rewrites to `d`, is not data, so the two definitions of the r2-anyw pair never
/// compare `c(1)` with `d`.
#[test]
fn a_plain_anywhere_head_is_a_data_head_and_admits_only_irreducible_applications() {
    use k_rust::kore::ast::{Pattern, Sort, Symbol};
    use kink_native::feasibility::TestInitialState;
    use kink_native::step_events::ObservationDecider;
    on_a_big_stack(|| {
        let compiled = NativeValidator::bind(
            support::load_path(
                &Path::new(support::DIR).join("overload/anyw-anywhere.k"),
                "AW",
            ),
            CompileOptions::default(),
        )
        .compile_baseline()
        .unwrap();
        let definition = loaded_definition(&compiled).unwrap();
        let facts = DataFacts::of(&definition, &[]);
        let ends = data_ends(&facts);
        let DataEnds::Admitted(heads) = ends else {
            panic!("{facts:?}");
        };
        let c = "Lblc'LParUndsRParUnds'AW-SYNTAX'Unds'Foo'Unds'Int";
        assert_eq!(
            heads.names().map(ToString::to_string).collect::<Vec<_>>(),
            [c]
        );
        let application = |value: &str| Pattern::Application {
            symbol: Symbol {
                name: c.to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments: vec![Pattern::DomainValue {
                sort: Sort::Application {
                    name: "SortInt".to_owned(),
                    arguments: Vec::new(),
                },
                value: value.into(),
            }],
        };
        let solver = k_rust_backend::smt::NoSolver;
        let decider = |term: &Pattern| {
            ObservationDecider::new(&definition, &solver, TestInitialState::of_test(term))
                .judging_data(ends, ends)
        };
        let irreducible = application("2");
        assert!(ends.overload_application_is_data(&definition, &irreducible));
        assert!(decider(&irreducible).definition_independent(&irreducible));
        let reducible = application("1");
        assert!(!ends.overload_application_is_data(&definition, &reducible));
        assert!(!decider(&reducible).definition_independent(&reducible));
    });
}

/// fz26 KINK-OVERLOAD-VALUE consumes k-rust's data judgement rather than re-implementing it, so
/// the passages its soundness rests on are pinned by digest (kink-flow's query reads the existence
/// predicate, `definedness`'s `ground_defined`, which is pinned here too):
/// - `data_term`'s module documentation from "The class" through "Two definitions" (what a data
///   term is, why two differ in each definition's initial model under A1+ and A2, and that ends
///   compared across two definitions must be data in both, each judged by its own);
/// - `data_heads` (a finding leaves no head), the selection of the data heads
///   (`data_head_names`, `canonical_overload_equation`), `is_data_walk` (no data without a
///   confluent check) and the walk `is_data` makes (`built_from_data`);
/// - the instance-normal scan `built_from_data` calls on an overload application
///   (`instance_normal.rs`: its module documentation, `instance_normal` and `excluded`), whose
///   equations are rooted at the application's head and read only its own subterm, which is why
///   judging once at the outermost overload application is `is_data` on the whole end (review N1).
///
/// A k-rust change that moves any of them fails here, and kink's reading (kink-native
/// `data::data_ends`, the TV-01 walk) is checked against it again before re-pinning.
///
/// fz26 int9: the module documentation was re-pinned after FZ-EMPTYJOIN-WITNESS, which reads
/// the definition in `M+` under A1+ (witness equations, fresh constants) where it read `M_NF`
/// under A1. Data terms are still free of the constants and normal forms, and two different data
/// terms still differ in the initial model, so `data_ends` and the walk are unchanged; kink's
/// own docs quote `M+` and A1+ since KINK-WITNESS. `data_heads` was re-pinned after KINK-WITNESS,
/// which also copies the check's adopted witnesses into `DataHeads`; the heads and findings it
/// returns are unchanged.
///
/// fz26 INT9-FIX-DOCS (review CHKB-1): "Two definitions" now says that two different data terms
/// differ in each definition's initial model by the argument above under A1+ and A2, where it
/// said A1 and A2; the argument it points to already read `M+` under A1+, so the sentence names
/// the premise that argument needs. Only the module documentation is re-pinned (`doc`).
///
/// fz26 KRUST-ANYWHERE-HEAD: the head selection is `data_head_names` (H1-H3 of the module
/// documentation): an `anywhere` production that is not a declared function, declared total or
/// `value-production`, with no hook, lemma or ceil equation at its index, rooting executable
/// equations whose overload ones are canonical. "The class" states why an instance-normal
/// application of such a head over data is a normal form in every context (an `anywhere`
/// equation reads only the term it matches) and an element (H2), and that data implies
/// existence in `M+`; A2 names the predicate lemmas outside the scan; "Two definitions" names
/// the `X:Id[N]` and `Id < Val` mutants; "Assumed pairs" says "data heads". `data_heads` changes
/// only by the selection's name. `canonical_overload_equation`, `is_data_walk`,
/// `built_from_data` and the instance-normal scan are byte-identical. kink's walk is unchanged:
/// it reads the heads through `DataEnds::overload_head` and judges each outermost application
/// with `is_data`, which now admits SIMPLE's `a[4]`, hence `TERMINAL_VALUE_VERSION` v2.
/// `ground_defined` is new: the existence predicate kink-flow's query reads on a matched state.
///
/// fz26 KRUST-ANYWHERE-HEAD fix round (review D1, SD1, M-f, M-h): `ground_defined` runs its walk
/// in `Proof` mode (a function of the term and the definition), and the pin now also covers what
/// it delegates to, the walk and its node (`ceil_term`, `ceil_term_walk`, `ceil_term_node`), the
/// ceil-equation step (`apply_ceil_equation`, `ceil_theory_condition`, the new
/// `value_production_ceil_equations`: a conditional, undecided or unusable ceil equation offered
/// at a `value-production` application keeps its `\ceil` owed, one whose `requires` is decided
/// true gives its condition), the discharge (`irreducible_application_is_defined`,
/// `is_value_production`), `only_top` and the witness `application_owes_nothing`. The module
/// documentation (`doc`) says that k-rust's apartness test does not separate two applications of
/// an equation head even of one shape, so data implies existence only in `M+`.
/// Literal-row recovery adds `LiteralCandidate` beside `Undecided` in the two ceil
/// consumers. Both retain the same unknown branch; neither applies a recovered literal
/// candidate. Removing those two alternatives recovers the previous pinned bytes exactly.
/// POST-01 renames that branch from `RecoveredLiteral` to `LiteralCandidate`: eligibility is
/// checked lazily only by term-equation application. The ceil consumers still take the same
/// unknown branch, and their only changed bytes are the variant name.
#[test]
fn the_data_judgement_kink_reads_is_pinned() {
    const DATA_TERM: &str = include_str!("../../../../crates/k-rust-backend/src/data_term.rs");
    const INSTANCE_NORMAL: &str =
        include_str!("../../../../crates/k-rust-backend/src/instance_normal.rs");
    const DEFINEDNESS: &str = include_str!("../../../../crates/k-rust-backend/src/definedness.rs");
    const DEFINITION: &str = include_str!("../../../../crates/k-rust-backend/src/definition.rs");
    let between = |source: &'static str, from: &str, to: &str| {
        let start = source.find(from).unwrap_or_else(|| panic!("no {from:?}"));
        let end = source[start..]
            .find(to)
            .unwrap_or_else(|| panic!("no {to:?}"))
            + start;
        &source[start..end]
    };
    let function = |name: &str| between(DATA_TERM, &format!("\nfn {name}("), "\n}\n");
    let method = |source, prefix: &str, name: &str| {
        between(source, &format!("\n    {prefix}fn {name}("), "\n    }\n")
    };
    let pinned = [
        (
            between(
                DATA_TERM,
                "//! # The class",
                "//! # Findings: genuine or undecided",
            ),
            "doc",
        ),
        (method(DATA_TERM, "pub ", "data_heads"), "data_heads"),
        (method(DATA_TERM, "", "data_head_names"), "data_head_names"),
        (
            function("canonical_overload_equation"),
            "canonical_overload_equation",
        ),
        (method(DATA_TERM, "", "is_data_walk"), "is_data_walk"),
        (method(DATA_TERM, "", "built_from_data"), "built_from_data"),
        (
            between(INSTANCE_NORMAL, "//! Instance normality", "\nmod token;"),
            "instance_normal_doc",
        ),
        (
            method(INSTANCE_NORMAL, "pub(crate) ", "instance_normal"),
            "instance_normal",
        ),
        (method(INSTANCE_NORMAL, "", "excluded"), "excluded"),
        (
            between(
                DEFINEDNESS,
                "impl BackendDefinition {\n    /// Whether the term `term` is shown to exist",
                "\n/// Whether the definedness walk ([`ceil_term`]) owes nothing",
            ),
            "ground_defined",
        ),
        (between(DEFINEDNESS, "\nfn only_top(", "\n}\n"), "only_top"),
        (
            between(DEFINEDNESS, "\npub fn application_owes_nothing(", "\n}\n"),
            "application_owes_nothing",
        ),
        (
            between(DEFINEDNESS, "\npub fn ceil_term(", "\n}\n"),
            "ceil_term",
        ),
        (
            between(DEFINEDNESS, "\nfn ceil_term_walk(", "\n}\n"),
            "ceil_term_walk",
        ),
        (
            between(DEFINEDNESS, "\nfn ceil_term_node<'a>(", "\n}\n"),
            "ceil_term_node",
        ),
        (
            between(DEFINEDNESS, "\nfn apply_ceil_equation(", "\n}\n"),
            "apply_ceil_equation",
        ),
        (
            between(
                DEFINEDNESS,
                "\nfn value_production_ceil_equations(",
                "\n}\n",
            ),
            "value_production_ceil_equations",
        ),
        (
            between(DEFINEDNESS, "\nfn ceil_theory_condition(", "\n}\n"),
            "ceil_theory_condition",
        ),
        (
            method(
                DEFINITION,
                "pub(crate) ",
                "irreducible_application_is_defined",
            ),
            "irreducible_application_is_defined",
        ),
        (
            method(DEFINITION, "pub(crate) ", "is_value_production"),
            "is_value_production",
        ),
    ]
    .map(|(text, name)| (name, kink_patch::sha256(text.as_bytes()).to_string()));
    assert_eq!(
        pinned,
        [
            (
                "doc",
                "38e7dbfd60ebd5260406923879366f8936df3799a7ef8ab387e8d51c6e15e3d0"
            ),
            (
                "data_heads",
                "cc0a88dda42619c58ee60959289c89bafdf8cca1fd9f91cd5dde8f19932c095f"
            ),
            (
                "data_head_names",
                "e27f9610e700f28a3d70453f63f3b11eb489b4e722535525790dcfb24b0d4bb0"
            ),
            (
                "canonical_overload_equation",
                "faf42a39040681e158cf3f4f5d623040faa00fee5dc3ebd245ae4a31f4fe35eb"
            ),
            (
                "is_data_walk",
                "2c32c7ce5a5c35763062ea2bd2a0cc6a154af224430ea26c34983945ffd85862"
            ),
            (
                "built_from_data",
                "0c171d308ef0252e0f9e27fa63119c381c8944843dbfc0b93ea576a42ff53e02"
            ),
            (
                "instance_normal_doc",
                "7fba49e94666ca7c1dd2dc113566a8c43d87e54daf2205a9f65f6ba186cc56f5"
            ),
            (
                "instance_normal",
                "b1a96645c05d2e8ba7f9b464e149867b37cfe18ae4c331cc721f1875a69cd2ce"
            ),
            (
                "excluded",
                "641b47e1929c88a6e3f66d0234fca49119e0f6a7d86ab1b1321b772182e58136"
            ),
            (
                "ground_defined",
                "04e691b1989b4711ad5b48c970629af8149bc37499577f655ac15a1f26bc0dbb"
            ),
            (
                "only_top",
                "7acf84fe451a1e62b92093f730ec0e2a64cfd8d37019be51e85e0f7e34612a11"
            ),
            (
                "application_owes_nothing",
                "0abb2008b60b7312b0fed32a7307813431de08642cd0d901e103abfc2ace8db6"
            ),
            (
                "ceil_term",
                "09a4f2bf5ddbc14b2bd0e4a7c1e34870913d6ddee30bbf637d4d392b740ab1f9"
            ),
            (
                "ceil_term_walk",
                "70e84d8f96acf3b89be87fa1ea0bbee5484f2466c7506620ab5c74c4d25d32d8"
            ),
            (
                "ceil_term_node",
                "2c6ce8744cefd65a910d195e48d7eb0e566c25e7caf066e06633634a115455e6"
            ),
            (
                "apply_ceil_equation",
                "6199c329297d5f2f2954005da6eee99501989ae454cd039a7a7f4151ef365e03"
            ),
            (
                "value_production_ceil_equations",
                "635cdc006a7ca7922b73f2b0419f9c49756077a152b8c2799ac7575967c3683f"
            ),
            (
                "ceil_theory_condition",
                "16d223f688828cbd210e28fc37d035a1fbeae34cfb1d189c77758ae1b2b221c4"
            ),
            (
                "irreducible_application_is_defined",
                "75ecf13cf21924fb2c7b69637807a5d7cfdb4664429a792d34801f5bc401e9a0"
            ),
            (
                "is_value_production",
                "b35a7fdec3a4e3f90cf62576ee1d6bfb8c88caa34e4959a933a123cb9cc3eb0d"
            ),
        ]
        .map(|(name, digest)| (name, digest.to_owned()))
    );
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
