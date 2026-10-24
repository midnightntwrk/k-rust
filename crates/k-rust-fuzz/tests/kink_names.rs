//! fz26 KINK-BASELINE-FINDINGS: the names the fuzz prints for a definition's findings
//! (`definition-findings`) are the names kink reads in `[spec] assume_joined`, byte for byte. Both
//! come from k-rust-backend's one renderer (`data_term::names`) called with the K label decoder.
//!
//! The definitions are kink's seven repro flows (`kink/testdata/flow/findings/*/spec.k`, compiled
//! under the source name `spec.k` as kink loads them), each against its mutation (the flow's one
//! edit of rule `go`). `NAMES` is pinned here and in kink-flow's `tests/findings.rs`: the fuzz
//! refuses each campaign as not comparable with exactly these baseline findings, and with these
//! names assumed it finds a witness, as kink kills each mutation once the flow names them.

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
                r#"overload:".List{\"_,__DIA-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__DIA-SYNTAX_Ids_Id2_Ids\"}_Ids",overload:".List{\"_,__DIA-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__DIA-SYNTAX_Vals_Val_Vals\"}_Vals"@root"#,
                FindingVerdict::Genuine,
            ),
            (
                r#"overload:"_,__DIA-SYNTAX_Exps_Exp_Exps":"_,__DIA-SYNTAX_Ids_Id2_Ids",overload:"_,__DIA-SYNTAX_Exps_Exp_Exps":"_,__DIA-SYNTAX_Vals_Val_Vals"@root"#,
                FindingVerdict::Genuine,
            ),
        ],
    ),
    (
        "r3-modov",
        "MO",
        ("_ => a </s>", "_ => bb </s>"),
        &[
            ("spec.k:16:3,spec.k:17:3@root", FindingVerdict::Undecided),
            (
                r#"spec.k:17:3,overload:"_,__MO-SYNTAX_Exps_Exp_Exps":"_,__MO-SYNTAX_Ids_Id_Ids"@0"#,
                FindingVerdict::Undecided,
            ),
        ],
    ),
    (
        "r3-plainq",
        "PQ",
        ("_ => a </s>", "_ => bb </s>"),
        &[("spec.k:7:3,spec.k:8:3@root", FindingVerdict::Genuine)],
    ),
    (
        "r3-propagate",
        "PR",
        ("_ => a </s>", "_ => bb </s>"),
        &[
            (
                r#"overload:".List{\"_,__PR-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__PR-SYNTAX_Ids_Id2_Ids\"}_Ids",overload:".List{\"_,__PR-SYNTAX_Exps_Exp_Exps\"}_Exps":".List{\"_,__PR-SYNTAX_Vals_Val_Vals\"}_Vals"@root"#,
                FindingVerdict::Genuine,
            ),
            (
                r#"overload:"_,__PR-SYNTAX_Exps_Exp_Exps":"_,__PR-SYNTAX_Ids_Id2_Ids",overload:"_,__PR-SYNTAX_Exps_Exp_Exps":"_,__PR-SYNTAX_Vals_Val_Vals"@root"#,
                FindingVerdict::Genuine,
            ),
        ],
    ),
    (
        "r4-empty",
        "R4",
        ("_ => a </s>", "_ => bb </s>"),
        &[("spec.k:9:3,spec.k:10:3@root", FindingVerdict::Undecided)],
    ),
    (
        "r4-hookite",
        "R4",
        ("_ => a </s>", "_ => bb </s>"),
        &[("hook:spec.k:8:3", FindingVerdict::Undecided)],
    ),
    (
        "r4-partnorule",
        "R4",
        ("_ => a </s>", "_ => bb </s>"),
        &[("spec.k:9:3,spec.k:10:3@root", FindingVerdict::Undecided)],
    ),
];

fn source(flow: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../kink/testdata/flow/findings")
        .join(flow)
        .join("spec.k");
    std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

/// `text` compiled under the source name `spec.k`, as kink-corpus loads a flow's entry, on the
/// campaign's default route.
fn compiled(text: &str, main_module: &str) -> CompiledDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let options = LoadOptions {
        implicit_sources: vec![embedded("prelude.md").expect("the prelude is embedded")],
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, syntax_module) = load_for_compilation(
        ResolvedSource::new("spec.k", text),
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
fn spec(flow: &str, main_module: &str, (find, replace): (&str, &str)) -> CampaignSpec {
    let baseline = source(flow);
    assert_eq!(baseline.matches(find).count(), 1, "{flow}");
    let mutant = baseline.replacen(find, replace, 1);
    CampaignSpec {
        definitions: Definitions {
            baseline: Arc::new(compiled(&baseline, main_module)),
            mutant: Some(Arc::new(compiled(&mutant, main_module))),
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
        let report = Campaign::new(assumed)
            .expect("valid")
            .run(Budget::Cases(8), None);
        assert!(report.witness().is_some(), "{flow}: {:?}", report.outcome);
    }
}
