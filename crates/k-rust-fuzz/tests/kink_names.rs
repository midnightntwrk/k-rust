//! fz26 KINK-BASELINE-FINDINGS: the names the fuzz prints for a definition's findings
//! (`definition-findings`) are the names kink reads in `[spec] assume_joined`, byte for byte. Both
//! come from k-rust-backend's one renderer (`data_term::names`) called with the K label decoder.
//!
//! The definitions are kink's seven repro flows (`kink/testdata/flow/findings/*/spec.k`, compiled
//! under the source name `spec.k` as kink loads them), each against its mutation (the flow's one
//! edit of rule `go`). `FLOWS` is pinned here and in kink-flow's `tests/findings.rs`: the fuzz
//! refuses each campaign as not comparable with exactly these baseline findings, and with these
//! names assumed it finds a witness where every finding is undecided, as kink kills each such
//! mutation once the flow names them; it refuses the names of a flow with a genuine finding,
//! which a premise cannot assume (KINK-FINDING-NAMES). The names hold no position: each is the
//! finding's kind, its sentences (`id:` and the `UNIQUE_ID` of these unlabelled K rules, or a
//! generated overload axiom's pair) and the digest of its compiled sentences.

use std::collections::BTreeMap;
use std::sync::Arc;

use k_rust::{
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};
use k_rust_fuzz::{
    Budget, CallerIdentity, Campaign, CampaignSpec, CaseOptions, CompiledDefinition, Definitions,
    HoleDecl, HoleLocation, ProgramInput, ProgramSource, ProposerConfig, SpanAddress, Target,
    TargetKind,
    report::{CampaignOutcome, DefinitionRole, FindingVerdict},
    spec::{DEFAULT_REJECTION_CAP, ProgramText},
    target::DifferentialTarget,
    values::{Constraints, GenerationBounds},
};

/// One flow: its directory, main module, the edited text and its replacement, and the names and
/// verdicts of its baseline's findings.
type Flow = (
    &'static str,
    &'static str,
    (&'static str, &'static str),
    &'static [(&'static str, FindingVerdict)],
);

/// The seven flows (the names and verdicts are kink-flow `tests/findings.rs`'s).
const FLOWS: [Flow; 7] = [
    (
        "diamond",
        "DIA",
        ("_ => .Ids </s>", "_ => .Vals </s>"),
        &[
            (
                r##"root:overload:".List{\"_,__DIA-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__DIA-SYNTAX_Ids_Id2_Ids\"}_Ids",overload:".List{\"_,__DIA-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__DIA-SYNTAX_Vals_Val_Vals\"}_Vals"#f0713f365978b8f0325111d6529de2c1"##,
                FindingVerdict::Genuine,
            ),
            (
                r##"root:overload:"_,__DIA-SYNTAX_Exps_Exp_Exps":"_,__DIA-SYNTAX_Ids_Id2_Ids",overload:"_,__DIA-SYNTAX_Exps_Exp_Exps":"_,__DIA-SYNTAX_Vals_Val_Vals"#18682f3fecc6ab0fe766e46c12bb9d76"##,
                FindingVerdict::Genuine,
            ),
        ],
    ),
    (
        "r3-modov",
        "MO",
        ("_ => a </s>", "_ => bb </s>"),
        &[
            (
                r"root:id:23200bd5eccd9cd22c483cd03cf594becd61d0f12c7f0578afe3cd9e504ca3c6,id:28f258802bbbd847568a200c6e03b9d18edb5f3a79ffccbc02cc1043ca09a985#8eecc49eef3961245814e8360ef3d61d",
                FindingVerdict::Undecided,
            ),
            (
                r#"inner:id:28f258802bbbd847568a200c6e03b9d18edb5f3a79ffccbc02cc1043ca09a985,overload:"_,__MO-SYNTAX_Exps_Exp_Exps":"_,__MO-SYNTAX_Ids_Id_Ids"@0#3212f1b41e9f9bc0e70e85a5b654cf2d"#,
                FindingVerdict::Undecided,
            ),
        ],
    ),
    (
        "r3-plainq",
        "PQ",
        ("_ => a </s>", "_ => bb </s>"),
        &[(
            r"root:id:6285b82dbb479e5dc14dcefd8e60504a09e6e2a190026465403c16d2b6bc23e2,id:7c934d95ccea860a412974582dd2e4a4228f3cb2b3efeede5193d257222a2ca0#e7d18f5c1aeb100be51c4fa6e7a3aa9f",
            FindingVerdict::Genuine,
        )],
    ),
    (
        "r3-propagate",
        "PR",
        ("_ => a </s>", "_ => bb </s>"),
        &[
            (
                r##"root:overload:".List{\"_,__PR-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__PR-SYNTAX_Ids_Id2_Ids\"}_Ids",overload:".List{\"_,__PR-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__PR-SYNTAX_Vals_Val_Vals\"}_Vals"#1eda8dccb16025c8b39cf7d96557cc5d"##,
                FindingVerdict::Genuine,
            ),
            (
                r##"root:overload:"_,__PR-SYNTAX_Exps_Exp_Exps":"_,__PR-SYNTAX_Ids_Id2_Ids",overload:"_,__PR-SYNTAX_Exps_Exp_Exps":"_,__PR-SYNTAX_Vals_Val_Vals"#18b7a02cc24283e5b61b59b4139edd6a"##,
                FindingVerdict::Genuine,
            ),
        ],
    ),
    (
        "r4-empty",
        "R4",
        ("_ => a </s>", "_ => bb </s>"),
        &[(
            r"root:id:29a09fc3eebc245937e7033fb61caacaddac13a5a6737e02b53341eec6034699,id:3e0249e570bb8f33a168bdf568d46fc3509c6c938da8acea24130992d34423f3#de0660e5005a1f0bce70b9be3852089f",
            FindingVerdict::Undecided,
        )],
    ),
    (
        "r4-hookite",
        "R4",
        ("_ => a </s>", "_ => bb </s>"),
        &[(
            r"hook:id:9a2851fd5b11489fb8c0788cdfc6810987bc0dd0f05c1a432492c859bbb9dcf5#bf49450df8f22ea4186bf244add30498",
            FindingVerdict::Undecided,
        )],
    ),
    (
        "r4-partnorule",
        "R4",
        ("_ => a </s>", "_ => bb </s>"),
        &[(
            r"root:id:29a09fc3eebc245937e7033fb61caacaddac13a5a6737e02b53341eec6034699,id:3e0249e570bb8f33a168bdf568d46fc3509c6c938da8acea24130992d34423f3#de0660e5005a1f0bce70b9be3852089f",
            FindingVerdict::Undecided,
        )],
    ),
];

/// The name of `kink/testdata/k/kbf/listrow.k`'s precondition row (kink-native `tests/data.rs`
/// pins it too): an unlabelled rule, so `id:` and its `UNIQUE_ID`.
const LISTROW_ROW: &str = "precondition:id:bc25e9f808a4bf8adb532e95bbf5555a7d75a50fc54d950b294ff9975cfeb9dd#65ce51470d5cc619971b3c995cffa2ca";

fn source(flow: &str) -> String {
    read(&format!("flow/findings/{flow}/spec.k"))
}

/// The text of `kink/testdata/<path>`.
fn read(path: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../kink/testdata")
        .join(path);
    std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

/// `text` compiled under the source name `file` (`spec.k` for a flow's entry, as kink-corpus
/// loads it), on the campaign's default route.
fn compiled_as(file: &str, text: &str, main_module: &str) -> CompiledDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let options = LoadOptions {
        implicit_sources: vec![embedded("prelude.md").expect("the prelude is embedded")],
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, syntax_module) = load_for_compilation(
        ResolvedSource::new(file, text),
        main_module,
        None,
        &mut resolver,
        &options,
    )
    .unwrap_or_else(|error| panic!("{main_module} does not load: {error:?}"));
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("{main_module} does not compile: {error}"));
    let source_table = loaded.source_table().clone();
    CompiledDefinition::from_artifacts(
        main_module,
        syntax_module,
        loaded.into_definition(),
        source_table,
        artifacts,
    )
    .unwrap_or_else(|error| panic!("{main_module}: {error:?}"))
}

/// The differential campaign of the flow's mutation over a hole on `go`'s argument.
fn spec(flow: &str, main_module: &str, edit: (&str, &str)) -> CampaignSpec {
    spec_of("spec.k", &source(flow), main_module, edit)
}

/// The differential campaign of `baseline` (source name `file`) against its edit, over a hole
/// on `go`'s argument.
fn spec_of(
    file: &str,
    baseline: &str,
    main_module: &str,
    (find, replace): (&str, &str),
) -> CampaignSpec {
    assert_eq!(baseline.matches(find).count(), 1, "{file}");
    let mutant = baseline.replacen(find, replace, 1);
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(compiled_as(file, baseline, main_module)),
            mutant: Some(Arc::new(compiled_as(file, &mutant, main_module))),
        },
        program: ProgramInput::Source(ProgramSource {
            program: Some(ProgramText {
                name: "one.pgm".into(),
                text: "go(1)\n".into(),
                start_sort: "Pgm".into(),
            }),
            config_vars: Vec::new(),
        }),
        holes: vec![HoleDecl {
            name: "N".into(),
            sort: "Int".into(),
            location: HoleLocation::Span(SpanAddress {
                program: "one.pgm".into(),
                line: None,
                column: None,
                find: "1".into(),
                literal: "1".into(),
            }),
            constraints: Constraints::default(),
            allow_refused_sort: false,
        }],
        target: Target {
            kind: TargetKind::Differential(DifferentialTarget::default()),
            run_to_completion: false,
            negated_property: false,
            data_end: true,
            comparable: false,
            query_confirmable: false,
        },
        options: CaseOptions::default(),
        proposers: ProposerConfig {
            anchors_first: true,
            explicit: Vec::<BTreeMap<_, _>>::new(),
            weights: ProposerConfig::default().weights,
        },
        bounds: GenerationBounds::default(),
        rejection_cap: DEFAULT_REJECTION_CAP,
        seed: 7,
        identity: CallerIdentity {
            k_rust_revision: "fz26-test".into(),
            thread_stack_size: None,
        },
    }
}

#[test]
fn the_fuzz_names_each_repro_finding_as_kink_does_and_assuming_them_kills() {
    for (flow, main_module, edit, names) in FLOWS {
        let report = Campaign::new(spec(flow, main_module, edit))
            .expect("valid")
            .run(Budget::Cases(8), None);
        assert!(
            matches!(report.outcome, CampaignOutcome::NotComparable { .. }),
            "{flow}: {:?}",
            report.outcome
        );
        let baseline = report
            .definition_findings
            .iter()
            .filter(|finding| finding.side == DefinitionRole::Baseline)
            .map(|finding| (finding.name.clone().expect("named"), finding.verdict))
            .collect::<Vec<_>>();
        let expected = names
            .iter()
            .map(|(name, verdict)| ((*name).to_owned(), *verdict))
            .collect::<Vec<_>>();
        assert_eq!(baseline, expected, "{flow}");

        let mut assumed = spec(flow, main_module, edit);
        assumed.options.assume_joined = names.iter().map(|(name, _)| (*name).to_owned()).collect();
        if names
            .iter()
            .any(|(_, verdict)| *verdict == FindingVerdict::Genuine)
        {
            // A genuine finding's premise would be known to be false: refused (`decided`).
            let Err(refused) = Campaign::new(assumed) else {
                panic!("{flow}: a genuine name is refused");
            };
            assert!(
                format!("{refused}").contains("(decided)"),
                "{flow}: {refused}"
            );
            continue;
        }
        let report = Campaign::new(assumed)
            .expect("valid")
            .run(Budget::Cases(8), None);
        assert!(report.witness().is_some(), "{flow}: {:?}", report.outcome);
    }
}

/// Review N4: a precondition row's name. kink-native `tests/data.rs` pins the same name for
/// `kink/testdata/k/kbf/listrow.k` (`IndexedAt(List)`, decided): the fuzz names it alike and
/// refuses to assume it.
#[test]
fn the_fuzz_names_a_precondition_row_as_kink_does() {
    let text = read("k/kbf/listrow.k");
    let spec = || {
        spec_of(
            "listrow.k",
            &text,
            "LISTROW",
            ("_ => ListItem(1)", "_ => ListItem(3)"),
        )
    };
    let report = Campaign::new(spec())
        .expect("valid")
        .run(Budget::Cases(4), None);
    let baseline = report
        .definition_findings
        .iter()
        .filter(|finding| finding.side == DefinitionRole::Baseline)
        .map(|finding| (finding.name.clone().expect("named"), finding.verdict))
        .collect::<Vec<_>>();
    assert_eq!(
        baseline,
        [(LISTROW_ROW.to_owned(), FindingVerdict::Decided)]
    );
    let mut assumed = spec();
    assumed.options.assume_joined = vec![LISTROW_ROW.to_owned()];
    assert!(Campaign::new(assumed).is_err(), "a decided name is refused");
}
