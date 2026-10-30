//! The definition-level checks over the testdata definitions, each definition compiled once:
//! the declaration census rows (corpus-scale CS-01), the rule-author map (CS-03), the
//! definition exclusions (re-pin R0b/R0c) and the representation gate (TB-03).
//!
//! Each check used to walk the directory itself and compile every definition again. Here every
//! (file, main module) pair is compiled once, on worker threads that each have a 256 MiB stack
//! (as the exclusion sweep had), and each check runs on that compile: the census, coverage and
//! exclusion checks on every top-level `testdata/k/*.k` under its last declared module, the
//! exclusion check also on the definitions under `testdata/k`'s subdirectories (apart from the
//! fixtures their own tests pin), `testdata/flow` and `examples/imp`, and the representation
//! check on the fixture/module pairs of TB-03's snapshot. The light tier runs the checks on a
//! named subset that holds every protected fixture and a fixture for each finding a check can
//! report; the heavy tier runs them over every definition.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::{BTreeMap, BTreeSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use k_rust::definition::Sentence;
use k_rust::kompile::CompileOptions;
use kink_native::census::{CensusClass, CensusVerdict, DeclarationCensus, declaration_census};
use kink_native::coverage::{Authorship, RuleAuthors};
use kink_native::exclusion::{DefinitionExclusions, Exclusion};
use kink_native::representation::validate_representation;
use kink_native::{NativeFailure, NativeValidator, ValidatedDefinition};
use serde_json::json;

/// The fixtures the protected kills run on: census-natural, with no exclusion.
const PROTECTED: &[&str] = &[
    "counter.k",
    "symmem.k",
    "symmem_release.k",
    "guardedmem.k",
    "guardedeq.k",
    "guardeddiv.k",
    "effectmem.k",
    "memory.k",
];

/// The light tier's definitions: every protected fixture; every fixture with a pinned census
/// row (the VI-T13 fixtures, including the flagged H and U rows and the inert hook, and the two
/// TB-02 token-hook fixtures); `t13role.k`, whose compile refusal the census and coverage
/// checks pin; `tb02float.k`, whose Float literals the representation gate admits
/// (R3-ADMIT-FLOAT; it refused them as FloatLiteral until then); and `t13implemented.k` is also
/// the one implementation-chosen-hook exclusion among them.
const LIGHT: &[&str] = &[
    "counter.k",
    "symmem.k",
    "symmem_release.k",
    "guardedmem.k",
    "guardedeq.k",
    "guardeddiv.k",
    "effectmem.k",
    "memory.k",
    "t13ite.k",
    "t13owk.k",
    "t13tok.k",
    "t13role.k",
    "t13typedlist.k",
    "t13natural.k",
    "t13inert.k",
    "t13implemented.k",
    "tb02bytestoken.k",
    "tb02stringtoken.k",
    "tb02float.k",
];

/// The definitions the exclusion check flags (implementation-chosen hooks), as paths from the
/// workspace root.
///
/// Every testdata and example definition that compiles, by its definition-level exclusions
/// (decision 1's census, the load's stack stops, C-10's role-rooted axioms). The census flags
/// exactly the definitions whose own rules use a hook it reads: `String2Bytes` (`t12probe`), the
/// undocumented `KRYPTO.keccak256` (`t13implemented`) and the `String2Bytes`/`Bytes2String` pair
/// (`runlist/iop`, `runlist/lhs`). Every comparison on them is unknown. No load counts a stack
/// stop on a 256 MiB thread, and no definition has an axiom rooted at a collection role symbol.
///
/// Re-pin kink27 R3-CENSUS-RUNLEVEL: k-rust's classes left the census (a run that reads one is
/// excluded by its `implementationChosenValues` list), so `rulecondfail`, `t12hook` and `t12unev`,
/// whose own rules apply only Float arithmetic and other hooks k-rust's classes or IEEE 754
/// determine, are no longer flagged; `t12probe` stays, for its `String2Bytes`.
///
/// Re-pin R0c: deliverable 8 rewrote the Bytes keys of `bytes-map` and both copies of
/// `collstore` with `encodeBytes("UTF-8", ..)`, so R0b's three `String2Bytes` flags are gone;
/// deliverable 2's domains.md additions flag no testdata or example definition. Re-pin
/// R0c-fix-1's builtin-file additions, prelude rewrite rules and short-circuit reading flag none
/// either.
const IMPLEMENTATION_CHOSEN: &[&str] = &[
    "testdata/k/t12probe.k",
    // Re-pin R0c-fix-2: `keccak` is hooked `KRYPTO.keccak256`, which k-rust evaluates and no
    // builtin file documents.
    "testdata/k/t13implemented.k",
    // fz26 KINK-CENSUS-RUNLIST: the String2Bytes/Bytes2String pair, which k-rust evaluates with
    // no run-level record, stays in the definition-level census by design, so these fixtures are
    // excluded (iop.k applies the pair in a rule, lhs.k in a left-hand-side map key).
    "testdata/k/runlist/iop.k",
    "testdata/k/runlist/lhs.k",
];

/// Snapshot of tracked fixture/module pairs at TB-03's start; new t12 fixtures deliberately
/// exercise refusal and are tested separately. Support and alternate main modules included.
const REPRESENTATION: &[(&str, &str)] = &[
    ("annotated.k", "ANNOTATED"),
    ("claims.k", "CLAIMS"),
    ("conflate.k", "CONFLATE"),
    ("conflate2.k", "CONFLATE2"),
    ("conflate3.k", "CONFLATE3"),
    ("conflatem.k", "CONFLATEM"),
    ("counter.k", "COUNTER"),
    ("counter_bytwo.k", "COUNTER_BYTWO"),
    ("duplicate_unlabelled.k", "DUPLICATE_UNLABELLED"),
    ("effectmem.k", "EFFECTMEM"),
    ("equation-ensures-support.k", "EQSUPPORT"),
    ("freshgen.k", "FRESHGEN"),
    ("guardeddiv.k", "GUARDEDDIV"),
    ("guardedeq.k", "GUARDEDEQ"),
    ("guardedmem.k", "GUARDEDMEM"),
    ("memory.k", "MEMORY"),
    ("nd.k", "ND"),
    ("nextgap.k", "NEXTGAP"),
    ("opaquemem.k", "OPAQUEMEM"),
    ("partialreq.k", "PARTIALREQ"),
    ("partialreq.k", "TV01UNSAT"),
    ("partialstep.k", "PARTIALSTEP"),
    ("residue.k", "RESIDUE"),
    ("rulecondfail.k", "RULECONDFAIL"),
    ("scopeforge.k", "SCOPEFORGE"),
    ("subsort_steps.k", "SUBSORT_STEPS"),
    ("symbolic-claim-mutation.k", "SYMPARTIAL"),
    ("symbolic-claim-survivor.k", "SYMPARTIAL"),
    ("symbolic-equation-ensures.k", "SYMPARTIAL"),
    ("symbottom.k", "SYMBOTTOM"),
    ("symensures.k", "SYMENSURES"),
    ("symmem.k", "SYMMEM"),
    ("symmem_existential.k", "SYMMEM_EXISTENTIAL"),
    ("symmem_release.k", "SYMMEM_RELEASE"),
    ("symnarrow.k", "SYMNARROW"),
    ("symowise.k", "SYMOWISE"),
    ("sympartial.k", "SYMPARTIAL"),
    ("symwrap.k", "SYMWRAP"),
    ("symwraptotal.k", "SYMWRAPTOTAL"),
    ("tb02bytes.k", "TB02BYTES"),
    ("tb02bytestoken.k", "TB02BYTESTOKEN"),
    ("tb02float.k", "TB02FLOAT"),
    ("tb02input.k", "TB02INPUT"),
    ("tb02input.k", "TB02PRED"),
    ("tb02string.k", "TB02STRING"),
    ("tb02stringtoken.k", "TB02STRINGTOKEN"),
    ("tb02token.k", "TB02TOKEN"),
    ("unbound.k", "UNBOUND"),
    ("unbound.k", "TV01TERMINAL"),
    ("undecided.k", "UNDECIDED"),
    ("unlabelled.k", "UNLABELLED"),
];

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The census rows pinned for a fixture: its findings as (class, symbol), empty for Natural;
/// `None` for a fixture whose row is not pinned.
fn expected(name: &str) -> Option<Vec<(CensusClass, &'static str)>> {
    use CensusClass::{H, U};
    Some(match name {
        "t13ite.k" => vec![(H, "Lbli2b")],
        "t13owk.k" => vec![(H, "LbladdB")],
        "t13tok.k" => vec![(H, "Lblb2t"), (H, "Lbltok2s")],
        // t13role.k (rule C at 927b9ce6: .LI, _LI_, mkFoo) no longer compiles at 501f18b9, which
        // refuses the misfit role itself (E-06; support::EXPECTED_COMPILE_FAILURES).
        "t13typedlist.k" => vec![(H, "LblgetLE")],
        "t13implemented.k" => vec![(U, "Lblkeccak")],
        "tb02bytestoken.k" => vec![(H, "Lblb2s")],
        "tb02stringtoken.k" => vec![(H, "Lbls2b")],
        "t13natural.k" | "t13inert.k" => vec![],
        _ if PROTECTED.contains(&name) => vec![],
        _ => return None,
    })
}

fn assert_row(name: &str, census: &DeclarationCensus) {
    if let Some(expected) = expected(name) {
        assert_eq!(
            census.verdict(),
            if expected.is_empty() {
                CensusVerdict::Natural
            } else {
                CensusVerdict::Flagged
            },
            "{name}: {}",
            census.text()
        );
        let actual: Vec<_> = census
            .findings()
            .iter()
            .map(|f| (f.class, f.symbol.as_str()))
            .collect();
        assert_eq!(actual, expected, "{name}: {}", census.text());
    }
    if name == "t13inert.k" {
        assert_eq!(census.inert().len(), 1);
        assert_eq!(census.inert()[0].symbol, "Lblinert");
        assert_eq!(census.inert()[0].hook, "INT.kinktestUnimplemented");
    }
}

/// `name`'s compile result checked against support::EXPECTED_COMPILE_FAILURES: the side when it
/// is not listed, `None` (after asserting the listed stage and detail) when it is.
///
/// Re-pin R0a (finding E-06; k-rust f07565265, 55a57846b, bc90d4226): b1coll.k and t13role.k
/// are refused by compilation at 501f18b9; the refusal is pinned, not skipped.
fn side_or_expected_refusal(
    name: &str,
    compiled: &Result<ValidatedDefinition, NativeFailure>,
) -> Option<ValidatedDefinition> {
    match (support::expected_compile_failure(name), compiled) {
        (None, Ok(side)) => Some(side.clone()),
        (None, Err(error)) => panic!("{name}: {error}"),
        (
            Some((stage, detail)),
            Err(NativeFailure::Compilation {
                stage: actual,
                detail: text,
            }),
        ) => {
            assert_eq!(*actual, stage, "{name}: {text}");
            assert!(
                detail.iter().all(|fragment| text.contains(fragment)),
                "{name}: {text}"
            );
            None
        }
        (Some(_), Ok(_)) => panic!("{name}: expected a compile refusal, compiled"),
    }
}

/// One definition to compile and the checks that run on it.
#[derive(Debug)]
struct Unit {
    path: PathBuf,
    module: String,
    /// A top-level `testdata/k` definition under its last module: census and coverage.
    census_and_coverage: bool,
    /// Under its last module, outside the fixture directories pinned by their own tests.
    exclusion: bool,
    /// One of TB-03's fixture/module pairs.
    representation: bool,
}

impl Unit {
    fn file(&self) -> &str {
        self.path.file_name().unwrap().to_str().unwrap()
    }

    /// The path from the workspace root, as the exclusion check names definitions.
    fn relative(&self) -> String {
        self.path
            .strip_prefix(root())
            .unwrap()
            .display()
            .to_string()
    }
}

/// The last `module NAME` of a definition file: its main module.
fn last_module(path: &Path) -> String {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .filter_map(|l| l.trim().strip_prefix("module "))
        .next_back()
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_owned()
}

/// Every definition the checks read, each (file, module) pair once, in path order: the whole
/// testdata when `only` is `None`, else the top-level `testdata/k` definitions it names.
fn units(only: Option<&[&str]>) -> Vec<Unit> {
    let testdata = root().join("testdata/k");
    let mut files = Vec::new();
    let mut pending = vec![
        testdata.clone(),
        root().join("testdata/flow"),
        root().join("examples/imp"),
    ];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                // The Z3 fixtures and R0b's, R0c's, re-pin adoption A-1's and fz26
                // KINK-BASELINE-FINDINGS' own fixtures are pinned by their own tests (A-1's
                // `marks.k` is flagged by design; KBF's `listrow.k` rewrites a term headed by a
                // collection, a role-rooted axiom, by design: kink-native `tests/data.rs`).
                if !path.ends_with("testdata/k/z3")
                    && !path.ends_with("testdata/k/r0b")
                    && !path.ends_with("testdata/k/r0c")
                    && !path.ends_with("testdata/k/a1")
                    && !path.ends_with("testdata/k/kbf")
                {
                    pending.push(path);
                }
            } else if path.extension().is_some_and(|e| e == "k") {
                files.push(path);
            }
        }
    }
    let selected = |path: &Path| {
        only.is_none_or(|names| {
            path.parent() == Some(testdata.as_path())
                && names.contains(&path.file_name().unwrap().to_str().unwrap())
        })
    };
    let mut units = BTreeMap::<(PathBuf, String), Unit>::new();
    for path in files.into_iter().filter(|path| selected(path)) {
        let module = last_module(&path);
        units.insert(
            (path.clone(), module.clone()),
            Unit {
                census_and_coverage: path.parent() == Some(testdata.as_path()),
                exclusion: true,
                representation: false,
                path,
                module,
            },
        );
    }
    for (file, module) in REPRESENTATION {
        let path = testdata.join(file);
        if !selected(&path) {
            continue;
        }
        units
            .entry((path.clone(), (*module).to_owned()))
            .or_insert_with(|| Unit {
                path,
                module: (*module).to_owned(),
                census_and_coverage: false,
                exclusion: false,
                representation: false,
            })
            .representation = true;
    }
    if let Some(names) = only {
        for name in names {
            assert!(
                units.values().any(|unit| unit.file() == *name),
                "{name} is not a top-level testdata/k definition"
            );
        }
    }
    units.into_values().collect()
}

/// What the checks found across the definitions.
#[derive(Default)]
struct Findings {
    /// Definitions the exclusion check compiled.
    compiled: usize,
    /// Definitions the exclusion check refused for lack of compilation (skipped).
    not_compiled: usize,
    implementation_chosen: BTreeSet<String>,
    short_circuit: BTreeSet<String>,
    coverage_totals: BTreeMap<String, u64>,
    failures: Vec<String>,
}

/// The census row of a compiled top-level testdata definition (CS-01 5(c)): computed without
/// CensusError, and equal to its pinned row if it has one.
fn census_check(name: &str, side: &ValidatedDefinition) {
    let census = declaration_census(side).unwrap_or_else(|e| panic!("{name}: {e}"));
    assert_row(name, &census);
    eprintln!(
        "CENSUS_TABLE {}",
        json!({"file":name,"verdict":format!("{:?}",census.verdict()),"classes":census.findings().iter().map(|f|format!("{:?}",f.class)).collect::<BTreeSet<_>>(),"inert":census.inert().iter().map(|i|i.hook.clone()).collect::<BTreeSet<_>>() })
    );
}

/// Every Compile address of the definition names a sentence of the definition it compiled (the
/// CS-03 STOP condition), and every executable rewrite id has provenance (M-C2). Returns the
/// per-authorship counts that go to the handoff table.
fn coverage_check(name: &str, side: &ValidatedDefinition) -> BTreeMap<String, u64> {
    let authors = RuleAuthors::of(side);
    assert!(
        authors.unresolved().is_empty(),
        "{name}: {:?}",
        authors.unresolved()
    );
    for id in &side.artifacts().execution_rewrite_order {
        assert!(authors.get(id).is_some(), "{name}: {id} has no provenance");
    }
    let mut counts = BTreeMap::<String, u64>::new();
    for (_, authorship) in authors.iter() {
        let key = match authorship {
            Authorship::Sentences(sentences) => {
                let kinds = sentences
                    .iter()
                    .map(|at| {
                        let sentence = side
                            .definition()
                            .modules
                            .iter()
                            .find(|candidate| candidate.name == at.module)
                            .and_then(|module| module.local_sentences.get(at.index as usize))
                            .expect("a resolved address names a sentence");
                        match &**sentence {
                            Sentence::Rule { .. } => "rule",
                            Sentence::Production { .. } => "production",
                            Sentence::Claim { .. } => "claim",
                            _ => "other",
                        }
                    })
                    .collect::<BTreeSet<_>>();
                format!(
                    "{}:{}",
                    if sentences.len() == 1 { "one" } else { "many" },
                    kinds.into_iter().collect::<Vec<_>>().join("+")
                )
            }
            Authorship::Unmapped(reason) => format!("unmapped:{reason}"),
        };
        *counts.entry(key).or_default() += 1;
    }
    eprintln!("COVERAGE_MAP {}", json!({"file": name, "ids": counts}));
    counts
}

/// The definition-level exclusions of a compiled definition: no load stack stop, trusted
/// collections, no short-circuit condition and (re-pin R0c-fix-3) no condition that equates two
/// terms; an implementation-chosen hook makes the definition's exclusion
/// ImplementationChosenHook. Returns (implementation-chosen, short-circuit rules).
fn exclusion_check(name: &str, unit: &Unit, side: &ValidatedDefinition) -> (bool, bool) {
    let exclusions =
        DefinitionExclusions::of_validated(side, &k_rust::kast::identifier::encode(&unit.module))
            .unwrap();
    assert_eq!(exclusions.load_stack_stops, 0, "{name}");
    assert!(exclusions.collections_trusted(), "{name}: {exclusions:?}");
    assert!(
        exclusions.short_circuit_conditions.is_empty(),
        "{name}: {:?}",
        exclusions.short_circuit_conditions
    );
    assert!(
        exclusions.equals_conditions.is_empty(),
        "{name}: {:?}",
        exclusions.equals_conditions
    );
    let short_circuit = !exclusions.short_circuit_rules.is_empty();
    if short_circuit {
        eprintln!(
            "SHORT_CIRCUIT_RULES {name} {:?}",
            exclusions.short_circuit_rules
        );
    }
    let flagged = !exclusions.implementation_chosen.is_empty();
    if flagged {
        assert_eq!(
            exclusions.definition_exclusion(),
            Some(Exclusion::ImplementationChosenHook)
        );
        eprintln!(
            "IMPLEMENTATION_CHOSEN {name} {:?}",
            exclusions
                .implementation_chosen
                .iter()
                .map(|reference| (&reference.sentence, &reference.hook))
                .collect::<Vec<_>>()
        );
    }
    (flagged, short_circuit)
}

/// TB-03's representation gate admits every pre-existing fixture: no pre-existing fixture is
/// refused. The two with a Float literal (`tb02float.k`, `rulecondfail.k`) were refused with
/// FloatLiteral until R3-ADMIT-FLOAT retired G-F: k-rust stores a Float literal as the canonical
/// text of its value.
fn representation_check(unit: &Unit, compiled: &Result<ValidatedDefinition, NativeFailure>) {
    let (file, module) = (unit.file(), unit.module.as_str());
    let side = compiled
        .as_ref()
        .unwrap_or_else(|error| panic!("{file}/{module} compilation: {error}"));
    let result = validate_representation(side);
    assert!(
        result.is_ok(),
        "STOP: existing fixture {file}/{module}: {result:?}"
    );
}

/// Compiles `unit` once and runs its checks, recording what they found in `findings`.
fn check(unit: &Unit, findings: &Mutex<Findings>) {
    let name = unit.file();
    let compiled = NativeValidator::bind(
        support::load_path(&unit.path, &unit.module),
        CompileOptions::default(),
    )
    .compile_baseline();
    let record = |update: &dyn Fn(&mut Findings)| update(&mut findings.lock().unwrap());
    if unit.census_and_coverage {
        match side_or_expected_refusal(name, &compiled) {
            None => eprintln!("CENSUS_COMPILE_REFUSED {}", json!({"file": name})),
            Some(side) => {
                census_check(name, &side);
                let counts = coverage_check(name, &side);
                record(&|findings| {
                    for (key, count) in &counts {
                        *findings.coverage_totals.entry(key.clone()).or_default() += count;
                    }
                });
            }
        }
    }
    if unit.exclusion {
        match &compiled {
            Ok(side) => {
                let relative = unit.relative();
                let (flagged, short_circuit) = exclusion_check(&relative, unit, side);
                record(&|findings| {
                    findings.compiled += 1;
                    if flagged {
                        findings.implementation_chosen.insert(relative.clone());
                    }
                    if short_circuit {
                        findings.short_circuit.insert(relative.clone());
                    }
                });
            }
            // The exclusion check reads compiled definitions only; a top-level testdata/k
            // refusal is pinned above.
            Err(_) => record(&|findings| findings.not_compiled += 1),
        }
    }
    if unit.representation {
        representation_check(unit, &compiled);
    }
}

/// Compiles every unit once on worker threads with 256 MiB stacks and runs its checks; a
/// failing unit is recorded with its message and the others still run.
fn sweep(units: &[Unit]) -> Findings {
    let workers = std::thread::available_parallelism()
        .map_or(1, std::num::NonZeroUsize::get)
        .min(8)
        .min(units.len());
    let next = AtomicUsize::new(0);
    let findings = Mutex::new(Findings::default());
    std::thread::scope(|scope| {
        for _ in 0..workers {
            std::thread::Builder::new()
                .stack_size(256 << 20)
                .spawn_scoped(scope, || {
                    loop {
                        let index = next.fetch_add(1, Ordering::Relaxed);
                        let Some(unit) = units.get(index) else {
                            break;
                        };
                        if let Err(panic) =
                            catch_unwind(AssertUnwindSafe(|| check(unit, &findings)))
                        {
                            let message = panic
                                .downcast_ref::<String>()
                                .cloned()
                                .or_else(|| panic.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                                .unwrap_or_default();
                            findings.lock().unwrap().failures.push(format!(
                                "{}/{}: {message}",
                                unit.relative(),
                                unit.module
                            ));
                        }
                    }
                })
                .expect("sweep worker");
        }
    });
    let findings = findings.into_inner().unwrap();
    eprintln!("COVERAGE_MAP_TOTALS {}", json!(findings.coverage_totals));
    assert!(findings.failures.is_empty(), "{:#?}", findings.failures);
    // Re-pin R0c-fix-1: counting every rewrite rule whatever its source (deliverable 3) and the
    // short-circuit reading (deliverable 4) flag no testdata or example definition.
    assert!(
        findings.short_circuit.is_empty(),
        "{:?}",
        findings.short_circuit
    );
    findings
}

fn names(units: &[Unit], keep: impl Fn(&Unit) -> bool) -> BTreeSet<String> {
    units
        .iter()
        .filter(|unit| keep(unit))
        .map(Unit::relative)
        .collect()
}

/// The checks on the light subset: every protected fixture is census-natural, maps every rule
/// author, has no exclusion and passes the representation gate; every pinned census row holds;
/// t13role.k's compile refusal is pinned; tb02float.k passes the representation gate; and of these
/// definitions exactly t13implemented.k has an implementation-chosen hook.
#[test]
fn named_definitions_pass_every_definition_check() {
    let units = units(Some(LIGHT));
    let findings = sweep(&units);
    let selected = names(&units, |unit| unit.exclusion);
    assert_eq!(
        findings.implementation_chosen,
        IMPLEMENTATION_CHOSEN
            .iter()
            .map(|name| (*name).to_owned())
            .filter(|name| selected.contains(name))
            .collect::<BTreeSet<_>>()
    );
    assert_eq!(
        findings.implementation_chosen,
        BTreeSet::from(["testdata/k/t13implemented.k".to_owned()])
    );
    // Only t13role.k fails to compile, and the census check pinned its refusal.
    assert_eq!(
        (findings.compiled, findings.not_compiled),
        (LIGHT.len() - 1, 1)
    );
    assert!(
        PROTECTED.iter().all(|name| LIGHT.contains(name)),
        "every protected fixture is in the light subset"
    );
}

mod heavy {
    use super::*;

    /// Every check over every definition: each top-level testdata/k definition gets a census
    /// (CS-01 5(c): the pinned rows hold and none fails) and a resolved rule-author map (CS-03),
    /// with the compile refusals of support::EXPECTED_COMPILE_FAILURES pinned; the exclusion
    /// check runs over testdata/k (apart from its z3, r0b, r0c and a1 fixtures), testdata/flow
    /// and examples/imp, of which more than 70 compile and exactly IMPLEMENTATION_CHOSEN are
    /// flagged; and every TB-03 fixture/module pair passes the representation gate.
    #[test]
    #[ignore = "heavy"]
    fn every_testdata_definition_passes_every_definition_check() {
        let units = units(None);
        assert!(
            REPRESENTATION.iter().all(|(file, module)| units
                .iter()
                .any(|unit| unit.representation && unit.file() == *file && unit.module == *module)),
            "every TB-03 pair is swept"
        );
        let findings = sweep(&units);
        assert!(findings.compiled > 70, "{}", findings.compiled);
        assert_eq!(
            findings.implementation_chosen,
            IMPLEMENTATION_CHOSEN
                .iter()
                .map(|name| (*name).to_owned())
                .collect::<BTreeSet<_>>()
        );
    }
}
