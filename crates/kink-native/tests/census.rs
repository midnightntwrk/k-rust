//! Pinned declaration-census rows and reference-prelude audits.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::{collections::BTreeSet, path::Path, time::Instant};

use k_rust::{
    builtin,
    kompile::{CompilationBackend, CompileOptions},
    outer::{ResolvedSource, SyntaxBody},
};
use k_rust_backend::{
    builtin::{BuiltinError, BuiltinResult, UnsupportedHookReason, evaluate_hook},
    definition::BackendDefinition,
};
use kink_native::census::{
    CensusClass, CensusVerdict, DeclarationCensus, EXCLUDED_REFERENCE_MODULES, FOLDED_HOOKS,
    REFERENCE_FILES, declaration_census, internalize, reference_prelude,
};
use kink_native::{NativeFailure, NativeValidator, ValidatedDefinition};
use kink_patch::Baseline;
use serde_json::json;

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

fn compile(name: &str) -> ValidatedDefinition {
    NativeValidator::bind(support::load(name), CompileOptions::default())
        .compile_baseline()
        .unwrap_or_else(|e| panic!("{name}: {e}"))
}

/// `name`'s compile result checked against support::EXPECTED_COMPILE_FAILURES: the side when it
/// is not listed, `None` (after asserting the listed stage and detail) when it is.
fn compile_or_expected_refusal(
    name: &str,
    validator: NativeValidator,
) -> Option<ValidatedDefinition> {
    let result = validator.compile_baseline();
    match (support::expected_compile_failure(name), result) {
        (None, Ok(side)) => Some(side),
        (None, Err(error)) => panic!("{name}: {error}"),
        (
            Some((stage, detail)),
            Err(NativeFailure::Compilation {
                stage: actual,
                detail: text,
            }),
        ) => {
            assert_eq!(actual, stage, "{name}: {text}");
            assert!(
                detail.iter().all(|fragment| text.contains(fragment)),
                "{name}: {text}"
            );
            None
        }
        (Some(_), Ok(_)) => panic!("{name}: expected a compile refusal, compiled"),
    }
}

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

#[test]
fn census_fixture_verdicts() {
    for name in [
        "t13ite.k",
        "t13owk.k",
        "t13tok.k",
        "t13typedlist.k",
        "t13natural.k",
        "t13inert.k",
        "t13implemented.k",
        "tb02bytestoken.k",
        "tb02stringtoken.k",
    ] {
        let census = declaration_census(&compile(name)).unwrap();
        assert_row(name, &census);
        eprintln!(
            "CENSUS_FIXTURE {}",
            json!({"file":name,"census":census.value()})
        );
    }
    // Re-pin R0a (finding E-06; k-rust f07565265, 55a57846b, bc90d4226): t13role.k's rule C
    // fixture is refused by k-rust's compilation at 501f18b9, before any census runs.
    let refused = compile_or_expected_refusal(
        "t13role.k",
        NativeValidator::bind(support::load("t13role.k"), CompileOptions::default()),
    );
    assert!(refused.is_none());
}

#[test]
fn census_protected_fixtures_are_natural() {
    reference_prelude().unwrap();
    for name in PROTECTED {
        let side = compile(name);
        let start = Instant::now();
        let census = declaration_census(&side).unwrap();
        assert_row(name, &census);
        if *name == "counter.k" {
            eprintln!("COUNTER_CENSUS_MICROS {}", start.elapsed().as_micros());
        }
    }
}

#[test]
fn census_testdata_table() {
    let mut paths: Vec<_> = std::fs::read_dir(support::DIR)
        .unwrap()
        .map(|p| p.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "k"))
        .collect();
    paths.sort();
    for path in paths {
        let name = path.file_name().unwrap().to_str().unwrap();
        let text = std::fs::read_to_string(&path).unwrap();
        let module = text
            .lines()
            .filter_map(|l| l.trim().strip_prefix("module "))
            .next_back()
            .unwrap()
            .split_whitespace()
            .next()
            .unwrap();
        let mut resolver = |_: &str, required: &str| {
            builtin::embedded(required).ok_or_else(|| format!("{required} is not embedded"))
        };
        let loaded = match Baseline::load(
            ResolvedSource::new(name, text.clone()),
            module,
            None,
            &mut resolver,
            &support::options(),
        ) {
            Ok(loaded) => loaded,
            Err(error) => {
                eprintln!(
                    "CENSUS_LOAD_REFUSED {}",
                    json!({"file": name, "error": error.to_string()})
                );
                continue;
            }
        };
        let Some(side) = compile_or_expected_refusal(
            name,
            NativeValidator::bind(loaded, CompileOptions::default()),
        ) else {
            eprintln!("CENSUS_COMPILE_REFUSED {}", json!({"file": name}));
            continue;
        };
        let census = declaration_census(&side).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_row(name, &census);
        eprintln!(
            "CENSUS_TABLE {}",
            json!({"file":name,"verdict":format!("{:?}",census.verdict()),"classes":census.findings().iter().map(|f|format!("{:?}",f.class)).collect::<BTreeSet<_>>(),"inert":census.inert().iter().map(|i|i.hook.clone()).collect::<BTreeSet<_>>() })
        );
    }
}

/// Re-pin R0a (finding E-06): the flagged fixture is t13tok.k (two H findings), since t13role.k
/// no longer compiles at 501f18b9.
#[test]
fn census_is_deterministic() {
    for name in ["counter.k", "t13tok.k"] {
        let first = declaration_census(&compile(name)).unwrap();
        let second = declaration_census(&compile(name)).unwrap();
        assert_eq!(first.text(), second.text());
        assert_eq!(first.digest(), second.digest());
        assert!(!first.text().contains(env!("CARGO_MANIFEST_DIR")));
        assert!(!first.text().contains("/home"));
        if name == "t13tok.k" {
            assert_eq!(first.findings().len(), 2);
        }
        for finding in first.findings() {
            assert_eq!(finding.source.as_deref(), Some("Source(t13tok.k)"));
            assert!(finding.location.is_some());
        }
    }
}

fn reference_backend() -> BackendDefinition {
    let side = reference_prelude().unwrap();
    internalize(side).unwrap()
}

#[test]
fn census_reference_prelude_is_natural() {
    let side = reference_prelude().unwrap();
    let census = declaration_census(side).unwrap();
    assert_eq!(
        census.verdict(),
        CensusVerdict::Natural,
        "{}",
        census.text()
    );
    assert!(census.findings().is_empty());
    let backend = reference_backend();
    let hooked = backend
        .symbols()
        .values()
        .filter(|s| s.attributes.hook.is_some())
        .count();
    let hooks: BTreeSet<_> = backend
        .symbols()
        .values()
        .filter_map(|s| s.attributes.hook.clone())
        .collect();
    assert_eq!(hooked, 287);
    assert_eq!(hooks.len(), 285);
    eprintln!(
        "CENSUS_REFERENCE {}",
        json!({"files":REFERENCE_FILES,"hooked_symbols":hooked,"hooks":hooks.len()})
    );
}

#[test]
fn census_fold_table_has_reference_declarations() {
    let backend = reference_backend();
    for hook in FOLDED_HOOKS {
        assert!(
            backend
                .symbols()
                .values()
                .any(|s| s.attributes.hook.as_deref() == Some(hook)),
            "folded hook {hook} has no reference declaration"
        );
    }
    assert_eq!(FOLDED_HOOKS.len(), 62);
}

#[test]
fn census_excluded_modules_fail_and_declare_no_hooked_symbol() {
    let mut found = BTreeSet::new();
    for file in REFERENCE_FILES {
        let source = builtin::embedded(file).unwrap();
        let code = if file.ends_with(".md") {
            k_rust::outer::extract_fenced_k_code(&source.text, "k").unwrap()
        } else {
            source.text.clone()
        };
        let parsed = k_rust::outer::parse(source.source, &code).unwrap();
        for module in parsed.modules {
            if !EXCLUDED_REFERENCE_MODULES.contains(&module.name.as_str()) {
                continue;
            }
            found.insert(module.name.clone());
            assert!(
                !module
                    .attributes
                    .iter()
                    .any(|a| a.key == CompilationBackend::Rust.excluded_module_attribute())
            );
            for sentence in &module.sentences {
                if let k_rust::outer::Sentence::Syntax(syntax) = sentence
                    && let SyntaxBody::Productions(blocks) = &syntax.body
                {
                    assert!(
                        blocks
                            .iter()
                            .flat_map(|b| &b.productions)
                            .all(|p| p.attributes.iter().all(|a| a.key != "hook")),
                        "{} declares a hooked symbol",
                        module.name
                    );
                }
            }
            let mut resolver = |_: &str, required: &str| {
                builtin::embedded(required).ok_or_else(|| format!("{required} is not embedded"))
            };
            let text = format!(
                "requires \"{file}\"\nmodule CENSUS-REFERENCE\n imports {}\nendmodule\n",
                module.name
            );
            let result = Baseline::load(
                ResolvedSource::new("census-reference.k", text),
                "CENSUS-REFERENCE",
                None,
                &mut resolver,
                &support::options(),
            )
            .map_err(|e| e.to_string())
            .and_then(|b| {
                NativeValidator::bind(b, CompileOptions::default())
                    .compile_baseline()
                    .map_err(|e| e.to_string())
            })
            .and_then(|side| internalize(&side).map_err(|e| e.to_string()));
            let error = result.expect_err("excluded module must fail alone");
            eprintln!(
                "CENSUS_EXCLUDED {}",
                json!({"file":file,"module":module.name,"error":error})
            );
        }
    }
    assert_eq!(
        found,
        EXCLUDED_REFERENCE_MODULES
            .iter()
            .map(|s| (*s).to_owned())
            .collect()
    );
}

#[test]
fn census_unknown_hook_probes() {
    let inert = evaluate_hook("INT.kinktestUnimplemented", &[]);
    assert_eq!(
        inert,
        Ok(Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented
        )))
    );
    let implemented = evaluate_hook("KRYPTO.keccak256", &[]);
    assert_eq!(
        implemented,
        Ok(Err(BuiltinError::WrongArity {
            hook: "KRYPTO.keccak256".to_owned(),
            expected: 1,
            actual: 0
        }))
    );
    for file in REFERENCE_FILES {
        assert!(
            !builtin::embedded(file)
                .unwrap()
                .text
                .contains("KRYPTO.keccak256")
        );
    }
    eprintln!("CENSUS_HOOK_PROBES inert={inert:?} implemented={implemented:?}");
    assert!(Path::new(support::DIR).join("t13implemented.k").exists());
}

/// Review 1 of CS-01 (VI-T13 class V6): a LIST/MAP/SET unit, element or concat hook over a
/// non-standard collection sort C. Only C's own metadata symbol is canonicalized into a C
/// collection by the backend; any other symbol carrying the hook is evaluated by the builtin,
/// which builds K's standard SortList/SortMap/SortSet value at declared sort C.
fn typed_collection_fixture(module: &str, collection: &str, extra: &str, start: &str) -> String {
    format!(
        "module {module}-SYNTAX\n  imports INT-SYNTAX\n  imports BASIC-K\n  \
         syntax Prog ::= start(Int) [symbol(start)] | chk(KItem) [symbol(chk)] | done(Int) [symbol(done)]\n\
         endmodule\nmodule {module}\n  imports {module}-SYNTAX\n  imports BASIC-K\n  imports INT\n  \
         imports BOOL\n  imports K-EQUAL\n  configuration <k> .K </k>\n{collection}{extra}  \
         rule [start]: start(I) => chk({start})\n  rule [hit]: chk(_:Coll) => done(1)\n  \
         rule [range]: chk(X:KItem) => done(7) requires X ==K X [priority(60)]\n  \
         rule [rangeow]: chk(_) => done(0) [owise]\nendmodule\n"
    )
}

const TYPED_LIST: &str = "  syntax Coll [hook(LIST.List)]\n  \
    syntax Coll ::= Coll Coll [function, total, left, assoc, hook(LIST.concat), symbol(_Coll_), element(CollItem), unit(.Coll)]\n  \
    syntax Coll ::= \".Coll\" [function, total, hook(LIST.unit), symbol(.Coll)]\n  \
    syntax Coll ::= CollItem(Int) [function, total, hook(LIST.element), symbol(CollItem)]\n";
const TYPED_MAP: &str = "  syntax Coll [hook(MAP.Map)]\n  \
    syntax Coll ::= Coll Coll [function, total, left, assoc, comm, hook(MAP.concat), symbol(_Coll_), element(CollItem), unit(.Coll)]\n  \
    syntax Coll ::= \".Coll\" [function, total, hook(MAP.unit), symbol(.Coll)]\n  \
    syntax Coll ::= CollItem(Int, Int) [function, total, hook(MAP.element), symbol(CollItem)]\n";
const TYPED_SET: &str = "  syntax Coll [hook(SET.Set)]\n  \
    syntax Coll ::= Coll Coll [function, total, left, assoc, comm, idem, hook(SET.concat), symbol(_Coll_), element(CollItem), unit(.Coll)]\n  \
    syntax Coll ::= \".Coll\" [function, total, hook(SET.unit), symbol(.Coll)]\n  \
    syntax Coll ::= CollItem(Int) [function, total, hook(SET.element), symbol(CollItem)]\n";

fn compile_text(name: &str, module: &str, text: String) -> ValidatedDefinition {
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("{required} is not embedded"))
    };
    let loaded = Baseline::load(
        ResolvedSource::new(name, text),
        module,
        None,
        &mut resolver,
        &support::options(),
    )
    .unwrap_or_else(|e| panic!("{name}: {e}"));
    NativeValidator::bind(loaded, CompileOptions::default())
        .compile_baseline()
        .unwrap_or_else(|e| panic!("{name}: {e}"))
}

#[test]
fn census_role_hook_only_on_the_metadata_symbol() {
    use CensusClass::H;
    let rows = [
        // Review 1 reproducers: Killed on an equivalent mutant while census-natural.
        (
            "RVLISTELEM",
            TYPED_LIST,
            "  syntax Coll ::= mk2(Int) [function, total, hook(LIST.element), symbol(mk2)]\n",
            "mk2(I)",
            vec![(H, "Lblmk2")],
        ),
        (
            "RVLISTUNIT",
            TYPED_LIST,
            "  syntax Coll ::= mt() [function, total, hook(LIST.unit), symbol(mt)]\n",
            "mt()",
            vec![(H, "Lblmt")],
        ),
        (
            "RVMAPELEM",
            TYPED_MAP,
            "  syntax Coll ::= mk2(Int, Int) [function, total, hook(MAP.element), symbol(mk2)]\n",
            "mk2(I, I)",
            vec![(H, "Lblmk2")],
        ),
        (
            "RVSETELEM",
            TYPED_SET,
            "  syntax Coll ::= mk2(Int) [function, total, hook(SET.element), symbol(mk2)]\n",
            "mk2(I)",
            vec![(H, "Lblmk2")],
        ),
        // Fail closed beyond the reproducers: a second unit over a typed map or set, and a
        // concat that is not C's metadata concat, are findings too.
        (
            "RVMAPUNIT",
            TYPED_MAP,
            "  syntax Coll ::= mt() [function, total, hook(MAP.unit), symbol(mt)]\n",
            "mt()",
            vec![(H, "Lblmt")],
        ),
        (
            "RVLISTCAT",
            TYPED_LIST,
            "  syntax Coll ::= cat(Coll, Coll) [function, total, hook(LIST.concat), symbol(cat)]\n",
            "cat(CollItem(I), .Coll)",
            vec![(H, "Lblcat")],
        ),
        // Controls: the metadata element itself, and MAP.in_keys (result Bool) over a typed map.
        ("RVLISTCTL", TYPED_LIST, "", "CollItem(I)", vec![]),
        (
            "RVMAPINKEYS",
            TYPED_MAP,
            "  syntax Bool ::= Int \"inK\" Coll [function, total, hook(MAP.in_keys), symbol(inK)]\n",
            "CollItem(I, I)",
            vec![],
        ),
    ];
    for (module, collection, extra, start, expected) in rows {
        let name = format!("{}.k", module.to_ascii_lowercase());
        let side = compile_text(
            &name,
            module,
            typed_collection_fixture(module, collection, extra, start),
        );
        let census = declaration_census(&side).unwrap();
        let actual: Vec<_> = census
            .findings()
            .iter()
            .map(|f| (f.class, f.symbol.as_str()))
            .collect();
        assert_eq!(actual, expected, "{name}: {}", census.text());
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
        assert!(census.inert().is_empty(), "{name}: {}", census.text());
        eprintln!(
            "CENSUS_ROLE_HOOK {}",
            json!({"file": name, "census": census.value()})
        );
    }
}
