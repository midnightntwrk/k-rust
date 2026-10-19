//! The reading of run coverage that the offered level exists for (docs/compatibility.md, "Run
//! coverage"), tested directly: an axiom in none of `applied`, `matched` and `offered` of a run
//! cannot change that run when its priority is raised, its `owise` attribute is removed, or its
//! `concrete` or `symbolic` attribute is removed.
//!
//! For every input of the coverage fixtures (`COVER`, `OFFER`) and of the probes below, the oracle
//! runs the definition with `collect_offered` under both strategies, and then, for each axiom of
//! the definition's rule catalog in none of the three lists of such a run, runs the same input
//! over each mutant of the definition that edits that axiom alone:
//! - raised: the axiom at the highest priority (`priority(0)`, or `simplification(0)` for a
//!   simplification), its `owise` attribute removed;
//! - `owise` removed, where it has one, so that it takes the default priority;
//! - `concrete` and `symbolic` removed, where it has one.
//!
//! The mutant's leaves (state, depth, halt reason, trace, candidates and remainder) must equal
//! the original run's. Diagnostics are not compared: they explain work, and the mutant may do
//! other work to reach the same leaves.
//!
//! The mutants edit the compiled KORE, the definition the backend runs, by the axiom's
//! `UNIQUE_ID`. Every run is bounded (`MAX_WORK`, `MAX_DEPTH`, `MAX_BREADTH`). A selection site
//! that stops before trying some candidates and does not offer them makes this oracle fail as
//! soon as a fixture or probe raises such a candidate over the one that decided.
//!
//! Load-time uses of an axiom are outside every coverage list; a mutant that the backend refuses
//! to load is counted and reported, not compared.

use std::collections::BTreeSet;

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest, ExecutionStrategy, ResultModalityOutput},
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar,
        compile_loaded_definition,
    },
    kore::{
        ast::{Attributes, Definition, KoreString, Pattern, Sentence, Symbol},
        parser::{parse_definition, parse_pattern},
        printer::Printer,
    },
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use serde_json::Value;

const COVER: &str = include_str!("fixtures/coverage/cover.k");
const OFFER: &str = include_str!("fixtures/coverage/offer.k");

const STRATEGIES: [ExecutionStrategy; 2] = [ExecutionStrategy::All, ExecutionStrategy::Any];

const MAX_WORK: u64 = 200;
const MAX_DEPTH: u64 = 200;
const MAX_BREADTH: usize = 16;
const MAX_SIMPLIFICATION_ITERATIONS: usize = 100;

/// The KORE of `source` and its configuration for `program` at sort `sort`.
fn compile_in(source: &str, main: &str, sort: &str, program: &str) -> (String, Pattern) {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("mutation.k", source),
        main,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let mut assembler =
        ConfigurationAssembler::new(&grammar, main, main, &artifacts.configuration_variables);
    assembler.program(&Sort::new(sort), program).unwrap();
    (artifacts.definition_kore, assembler.finish().unwrap())
}

/// One input of a definition.
#[derive(Clone, Copy)]
enum Input {
    /// A program.
    Ground(&'static str),
    /// A program whose `777`s become the variable `X` (and `778`s the variable `?_Y`).
    Symbolic(&'static str),
    /// [`Input::Symbolic`] under the constraint `X >=Int 0`.
    Constrained(&'static str),
    /// A KORE term of sort `Pgm`, for a state no program of the definition's syntax writes.
    Kore(&'static str),
}

impl Input {
    fn pattern(self, source: &str, main: &str, sort: &str) -> (String, Pattern) {
        let program = match self {
            Input::Ground(program) | Input::Symbolic(program) | Input::Constrained(program) => {
                program
            }
            Input::Kore(term) => {
                let (kore, _) = compile_in(source, main, sort, "go(0)");
                let top = format!(
                    "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{Sort{sort}{{}}, SortKItem{{}}}}({term}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
                );
                return (kore, parse_pattern(&top).unwrap());
            }
        };
        let (kore, ground) = compile_in(source, main, sort, program);
        if let Input::Ground(_) = self {
            return (kore, ground);
        }
        let printed = Printer::compact().print_pattern(&ground);
        let symbolic = printed
            .replace("\\dv{SortInt{}}(\"777\")", "VarX:SortInt{}")
            .replace("\\dv{SortInt{}}(\"778\")", "Var'QuesUnds'Y:SortInt{}");
        assert_ne!(symbolic, printed, "{program}");
        let text = match self {
            Input::Constrained(_) => format!(
                "\\and{{SortGeneratedTopCell{{}}}}({symbolic}, \\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(Lbl'Unds-GT-Eqls'Int'Unds'{{}}(VarX:SortInt{{}}, \\dv{{SortInt{{}}}}(\"0\")), \\dv{{SortBool{{}}}}(\"true\")))"
            ),
            _ => symbolic,
        };
        (kore, parse_pattern(&text).unwrap())
    }

    fn name(self) -> String {
        match self {
            Input::Ground(program) => program.to_owned(),
            Input::Symbolic(program) => format!("{program} with X for 777"),
            Input::Constrained(program) => format!("{program} with X >=Int 0 for 777"),
            Input::Kore(term) => term.to_owned(),
        }
    }
}

use Input::{Constrained, Ground, Kore, Symbolic};

fn request(initial: &Pattern, strategy: ExecutionStrategy, offered: bool) -> ExecuteRequest {
    ExecuteRequest {
        result_modality: ResultModalityOutput::PathSet,
        strategy,
        collect_coverage: offered,
        collect_offered: offered,
        max_work: Some(MAX_WORK),
        max_depth: Some(MAX_DEPTH),
        max_breadth: Some(MAX_BREADTH),
        max_simplification_iterations: MAX_SIMPLIFICATION_ITERATIONS,
        ..ExecuteRequest::new(initial.clone())
    }
}

/// The leaves of a response, without their diagnostics; an error as its message.
fn leaves(
    response: Result<k_rust::backend::ExecutionResult, k_rust::backend::BackendError>,
) -> Value {
    let response = match response {
        Ok(response) => serde_json::to_value(&response).unwrap(),
        Err(error) => return Value::String(format!("error: {}", error.message())),
    };
    let mut leaves = response["leaves"].clone();
    strip_diagnostics(&mut leaves);
    leaves
}

fn strip_diagnostics(value: &mut Value) {
    match value {
        Value::Object(object) => {
            object.remove("diagnostics");
            for value in object.values_mut() {
                strip_diagnostics(value);
            }
        }
        Value::Array(values) => values.iter_mut().for_each(strip_diagnostics),
        _ => {}
    }
}

/// One run of the original definition: its leaves and the ids in any of its three lists.
struct Original {
    input: String,
    initial: Pattern,
    strategy: ExecutionStrategy,
    leaves: Value,
    listed: BTreeSet<String>,
}

/// The name of an attribute application, such as `priority` for `priority{}("40")`.
fn attribute_name(attribute: &Pattern) -> Option<&str> {
    match attribute {
        Pattern::Application { symbol, .. } => Some(symbol.name.as_str()),
        _ => None,
    }
}

fn attribute(name: &str, value: Option<&str>) -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: name.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments: value
            .map(|value| Pattern::String(KoreString::from(value)))
            .into_iter()
            .collect(),
    }
}

fn unique_id(attributes: &Attributes) -> Option<String> {
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == "UNIQUE'Unds'ID" => {
            match arguments.as_slice() {
                [Pattern::String(id)] => id.as_utf8().ok().map(str::to_owned),
                _ => None,
            }
        }
        _ => None,
    })
}

/// The kinds of mutant of one axiom.
#[derive(Clone, Copy, Debug)]
enum Mutation {
    Raised,
    OwiseRemoved,
    SetAsideRemoved,
}

impl Mutation {
    /// Apply the mutation to `attributes`; whether it applies to this axiom.
    fn apply(self, attributes: &mut Attributes) -> bool {
        let has = |name: &str| {
            attributes
                .0
                .iter()
                .any(|attribute| attribute_name(attribute) == Some(name))
        };
        match self {
            Mutation::Raised => {
                let simplification = has("simplification");
                attributes.0.retain(|attribute| {
                    !matches!(
                        attribute_name(attribute),
                        Some("priority" | "owise" | "simplification")
                    )
                });
                attributes.0.push(if simplification {
                    attribute("simplification", Some("0"))
                } else {
                    attribute("priority", Some("0"))
                });
                true
            }
            Mutation::OwiseRemoved => {
                if !has("owise") {
                    return false;
                }
                attributes
                    .0
                    .retain(|attribute| attribute_name(attribute) != Some("owise"));
                true
            }
            Mutation::SetAsideRemoved => {
                if !has("concrete") && !has("symbolic") {
                    return false;
                }
                attributes.0.retain(|attribute| {
                    !matches!(attribute_name(attribute), Some("concrete" | "symbolic"))
                });
                true
            }
        }
    }
}

/// The KORE of `definition` with `mutation` applied to every axiom whose id is `id`; `None` when
/// the mutation does not apply to it.
fn mutant(definition: &Definition, id: &str, mutation: Mutation) -> Option<String> {
    let mut mutant = definition.clone();
    let mut applied = false;
    for module in &mut mutant.modules {
        for sentence in &mut module.sentences {
            if let Sentence::Axiom { attributes, .. } = sentence
                && unique_id(attributes).as_deref() == Some(id)
            {
                applied |= mutation.apply(attributes);
            }
        }
    }
    applied.then(|| Printer::compact().print_definition(&mutant))
}

/// What one case's mutants gave.
#[derive(Debug, Default)]
struct Tally {
    mutants: usize,
    refused: usize,
    runs: usize,
}

/// Run the mutation oracle over `inputs` of `source`; panics with every changed run.
fn assert_unlisted_axioms_are_inert(
    case: &str,
    source: &str,
    main: &str,
    sort: &str,
    inputs: &[Input],
) -> Tally {
    let mut kore = None;
    let mut originals = Vec::new();
    for &input in inputs {
        let (compiled, initial) = input.pattern(source, main, sort);
        let mut backend = Backend::new(&compiled, main, BackendOptions::default()).unwrap();
        for strategy in STRATEGIES {
            let response = backend.execute(request(&initial, strategy, true)).unwrap();
            let coverage = response.coverage.as_ref().unwrap();
            let listed = coverage
                .applied
                .iter()
                .chain(&coverage.matched)
                .chain(coverage.offered.as_deref().unwrap())
                .cloned()
                .collect();
            originals.push(Original {
                input: input.name(),
                initial: initial.clone(),
                strategy,
                leaves: leaves(Ok(response)),
                listed,
            });
        }
        kore.get_or_insert(compiled);
    }
    let kore = kore.expect("a case has an input");
    let backend = Backend::new(&kore, main, BackendOptions::default()).unwrap();
    let catalog = backend.rule_catalog(None).unwrap();
    let definition = parse_definition(&kore).unwrap();
    let ids = catalog
        .iter()
        .map(|rule| (rule.id.clone(), rule.label.clone()))
        .collect::<std::collections::BTreeMap<_, _>>();

    let mut tally = Tally::default();
    let mut changed = Vec::new();
    for (id, label) in &ids {
        let affected = originals
            .iter()
            .filter(|original| !original.listed.contains(id))
            .collect::<Vec<_>>();
        if affected.is_empty() {
            continue;
        }
        for mutation in [
            Mutation::Raised,
            Mutation::OwiseRemoved,
            Mutation::SetAsideRemoved,
        ] {
            let Some(text) = mutant(&definition, id, mutation) else {
                continue;
            };
            tally.mutants += 1;
            let Ok(mut backend) = Backend::new(&text, main, BackendOptions::default()) else {
                tally.refused += 1;
                continue;
            };
            for original in &affected {
                tally.runs += 1;
                let mutated =
                    leaves(backend.execute(request(&original.initial, original.strategy, false)));
                if mutated != original.leaves {
                    changed.push(format!(
                        "{case}: {} under {:?}: {mutation:?} {} ({id}) changes the leaves\n  original {}\n  mutant   {}",
                        original.input,
                        original.strategy,
                        label.as_deref().unwrap_or("unlabelled"),
                        original.leaves,
                        mutated,
                    ));
                }
            }
        }
    }
    eprintln!(
        "{case}: {} axioms, {} original runs, {tally:?}",
        ids.len(),
        originals.len()
    );
    assert!(
        changed.is_empty(),
        "{} runs changed by an axiom in no list:\n{}",
        changed.len(),
        changed.join("\n")
    );
    tally
}

#[test]
fn the_cover_fixtures() {
    assert_unlisted_axioms_are_inert(
        "COVER",
        COVER,
        "COVER",
        "Prog",
        &[
            Ground("seq(load(addr(1), 0), halt)"),
            Ground("seq(ens(1), halt)"),
            Ground("seq(rhsp(1), halt)"),
            Ground("seq(eqreq(1), halt)"),
            Ground("seq(rej(5), halt)"),
            Ground("seq(ow(5), halt)"),
            Ground("seq(ru(1), halt)"),
            Ground("seq(ru(-1), halt)"),
            Ground("seq(rv(-1), halt)"),
            Ground("seq(pr(1), halt)"),
            Ground("seq(hk(1), halt)"),
            Ground("seq(d1(5), halt)"),
            Ground("seq(d1(-5), halt)"),
            Ground("nd"),
            Symbolic("seq(rej(777), halt)"),
            Symbolic("seq(ow(777), halt)"),
            Symbolic("seq(d1(777), halt)"),
            Symbolic("seq(eqreq(777), halt)"),
            Constrained("seq(ru(777), halt)"),
            Constrained("seq(rhsp(777), halt)"),
        ],
    );
}

#[test]
fn the_offer_fixtures() {
    assert_unlisted_axioms_are_inert(
        "OFFER",
        OFFER,
        "OFFER",
        "Prog",
        &[
            Ground("seq(pa(1), halt)"),
            Ground("seq(pb(1), halt)"),
            Ground("seq(pc(5), halt)"),
            Ground("seq(pd(0), halt)"),
            Ground("seq(pd(5), halt)"),
            Ground("seq(pe(3), halt)"),
            Ground("seq(pn(1), halt)"),
            Ground("seq(py(1), halt)"),
            Ground("seq(ph(1), halt)"),
            Ground("seq(pk(5), halt)"),
            Ground("seq(pk(-5), halt)"),
            Symbolic("seq(pe(777), halt)"),
            Symbolic("seq(pc(777), halt)"),
            Symbolic("seq(pd(777), halt)"),
            Symbolic("seq(pk(777), halt)"),
            Constrained("seq(pc(777), halt)"),
            Constrained("seq(pk(777), halt)"),
            Symbolic("seq(pz(777), val(778))"),
            Constrained("seq(pz(777), val(778))"),
        ],
    );
}

/// The probe definitions: one per equation selection site outside the term scans, each with
/// a lower-priority competitor that a raise lets decide in place of the higher one.
const PROBES: &str = include_str!("fixtures/coverage/probes.k");

/// Ceil equations selected by the predicate simplifier (`#Ceil` in a `requires`), on a ground
/// argument, where the higher one decides.
#[test]
fn the_ceil_probe() {
    assert_unlisted_axioms_are_inert(
        "CEIL",
        PROBES,
        "CEIL",
        "Pgm",
        &[
            Ground("go(5)"),
            Ground("rhs(5)"),
            Symbolic("go(777)"),
            Symbolic("rhs(777)"),
            Symbolic("req(777)"),
        ],
    );
}

/// Predicate equations of `#Equals`, selected by the predicate simplifier.
#[test]
fn the_predicate_probe() {
    assert_unlisted_axioms_are_inert(
        "PRED",
        PROBES,
        "PRED",
        "Pgm",
        &[Ground("go(5)"), Symbolic("go(777)"), Symbolic("eq(777)")],
    );
}

/// `#Top` lemmas on an operand of a term-level conjunction (in a KORE state: the compiler reads a
/// rule's `X #And t` as a predicate), and the definedness analysis's ceil equations.
#[test]
fn the_top_and_definedness_probe() {
    assert_unlisted_axioms_are_inert(
        "TOPDEF",
        PROBES,
        "TOPDEF",
        "Pgm",
        &[
            Kore(
                r#"Lbldone{}(\and{SortInt{}}(\dv{SortInt{}}("5"), Lbltp{}(\dv{SortInt{}}("5"))))"#,
            ),
            Kore(r#"Lbldone{}(\and{SortInt{}}(VarX:SortInt{}, Lbltp{}(VarX:SortInt{})))"#),
            Ground("def(5)"),
            Symbolic("def(777)"),
        ],
    );
}
