//! Pinned declaration-census rows and reference-prelude audits.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::{collections::BTreeSet, path::Path};

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
    CensusClass, CensusVerdict, DeclarationCensus, EXCLUDED_REFERENCE_MODULES, REFERENCE_FILES,
    declaration_census, internalize, reference_prelude,
};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::Baseline;
use serde_json::json;

fn compile(name: &str) -> ValidatedDefinition {
    NativeValidator::bind(support::load(name), CompileOptions::default())
        .compile_baseline()
        .unwrap_or_else(|e| panic!("{name}: {e}"))
}

fn reference_backend() -> BackendDefinition {
    let side = reference_prelude().unwrap();
    internalize(side).unwrap()
}

/// The reference prelude's own census is Natural (every declaration equals itself), with the
/// pinned counts of hooked symbols and hooks; and every former fold hook
/// ([`FORMER_FOLDED_HOOKS`]) has a reference declaration. One test, so that the reference
/// prelude is compiled once.
#[test]
fn census_reference_prelude_is_natural_and_declares_the_former_fold_hooks() {
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
    for hook in FORMER_FOLDED_HOOKS {
        assert!(
            backend
                .symbols()
                .values()
                .any(|s| s.attributes.hook.as_deref() == Some(hook)),
            "former fold hook {hook} has no reference declaration"
        );
    }
    assert_eq!(FORMER_FOLDED_HOOKS.len(), 62);
}

/// The hook-name arms of k-rust 927b9ce6's constant folding (kompile/passes/constant_folding.rs
/// :286-395), which kink-native's census kept out of `inert_hook` until re-pin L2-1 (finding C-07).
/// That exclusion was dead: a hook with a reference declaration goes to rule H before `inert_hook`
/// is asked. It stays dead only while every one of these hooks has a reference declaration, which
/// this list guards; rule H itself is unchanged.
#[rustfmt::skip]
const FORMER_FOLDED_HOOKS: &[&str] = &[
    "BOOL.not",
    "BOOL.and",
    "BOOL.andThen",
    "BOOL.xor",
    "BOOL.or",
    "BOOL.orElse",
    "BOOL.implies",
    "BOOL.eq",
    "BOOL.ne",
    "INT.not",
    "INT.pow",
    "INT.powmod",
    "INT.mul",
    "INT.tdiv",
    "INT.tmod",
    "INT.ediv",
    "INT.emod",
    "INT.add",
    "INT.sub",
    "INT.shr",
    "INT.shl",
    "INT.and",
    "INT.xor",
    "INT.or",
    "INT.min",
    "INT.max",
    "INT.abs",
    "INT.log2",
    "INT.bitRange",
    "INT.signExtendBitRange",
    "INT.lt",
    "INT.gt",
    "INT.le",
    "INT.ge",
    "INT.eq",
    "INT.ne",
    "STRING.concat",
    "STRING.length",
    "STRING.chr",
    "STRING.ord",
    "STRING.substr",
    "STRING.find",
    "STRING.rfind",
    "STRING.findChar",
    "STRING.rfindChar",
    "STRING.string2int",
    "STRING.int2string",
    "STRING.string2base",
    "STRING.base2string",
    "STRING.replaceAll",
    "STRING.replace",
    "STRING.replaceFirst",
    "STRING.countAllOccurrences",
    "STRING.eq",
    "STRING.ne",
    "STRING.lt",
    "STRING.gt",
    "STRING.le",
    "STRING.ge",
    "STRING.token2string",
    "STRING.string2token",
    "STRING.string2float",
];

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

mod kink_tier {
    use super::*;

    /// Re-pin R0a (finding E-06): the flagged fixture is t13tok.k (two H findings), since t13role.k
    /// no longer compiles at 501f18b9.
    #[test]
    #[ignore = "kink"]
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

    /// Re-pin L1-4: a census read back from its value ([`DeclarationCensus::from_value`], kink-flow's
    /// census memo) is the census, for a natural, a flagged (findings with hooks, sources and
    /// locations) and an inert-hook fixture; any value it would not write is refused.
    #[test]
    #[ignore = "kink"]
    fn a_census_reads_back_from_its_value_and_nothing_else_does() {
        for name in ["counter.k", "t13tok.k", "t13inert.k", "t13implemented.k"] {
            let census = declaration_census(&compile(name)).unwrap();
            let value = census.value();
            assert_eq!(
                DeclarationCensus::from_value(&value).as_ref(),
                Some(&census),
                "{name}"
            );
            let mut other = Vec::new();
            for (key, changed) in [
                ("census", json!("kink/declaration-census/v0")),
                ("k_rust", json!("0000000")),
                (
                    "verdict",
                    json!(if census.findings().is_empty() {
                        "flagged"
                    } else {
                        "natural"
                    }),
                ),
                ("findings", json!(null)),
                ("extra", json!(1)),
            ] {
                let mut forged = value.clone();
                forged[key] = changed;
                other.push(forged);
            }
            if let Some(first) = census.findings().first() {
                assert!(first.location.is_some());
                let mut forged = value.clone();
                forged["findings"][0]["class"] = json!("X");
                other.push(forged);
                let mut forged = value.clone();
                forged["findings"][0]["location"] = json!([1, 2, 3]);
                other.push(forged);
            }
            for forged in other {
                assert_eq!(
                    DeclarationCensus::from_value(&forged),
                    None,
                    "{name}: {forged}"
                );
            }
        }
    }

    #[test]
    #[ignore = "kink"]
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
}
