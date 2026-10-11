//! The two feature sets of k-rust compile one language: `z3-inference` selects the engine that
//! settles sort inference and rule placement (Z3, or the portable decision and rule grammar of the
//! `not(feature = "z3-inference")` code), not what a definition means. So a definition both
//! builds compile gives the same KORE in both, and a definition the portable build cannot settle
//! is refused with `Z3InferenceRequired` (README, "portable library subset"), never compiled
//! differently.
//!
//! The README states and `the_standard_prelude_loads_to_the_same_definition_in_both_builds` checks
//! this for the prelude only. This test compiles every manifest compile case whose source is in a
//! local checkout through the library, as the portable hosts do, in whichever build runs it:
//!
//! ```sh
//! BUILD_AGREEMENT_RECORD=/tmp/native.tsv cargo test -p k-rust --no-default-features \
//!   --features z3-inference --test build_agreement -- --ignored
//! BUILD_AGREEMENT_COMPARE=/tmp/native.tsv cargo test -p k-rust --no-default-features \
//!   --test build_agreement -- --ignored
//! ```
//!
//! Each run fails on every case it did not compile that the manifest expects to compile (an
//! `expect` other than `"reject"`), unless the error is the portable build's `Z3InferenceRequired`:
//! an error there means no build compiled the definition, so the comparison did not happen, even
//! when both builds fail alike. The native build has the engine the refusal names, so the refusal
//! is a failure to compile there like any other error. The first run records each case's outcome;
//! the second computes its own and fails on every case both builds compiled to different KORE, on
//! every case one build rejects for a reason other than the portable build's documented
//! `Z3InferenceRequired`, and on every case only one of the runs compiled. It prints the cases
//! refused with `Z3InferenceRequired`: they are not a disagreement, but each is a definition the
//! portable hosts cannot compile. When `BUILD_AGREEMENT_REFUSED` lists the cases the portable
//! build is expected to refuse (comma-separated, possibly empty), the portable run also fails on
//! every other refusal and on every listed case it compiled, so a new refusal shows and the record
//! stays exact. The real-semantics cases (`wasm`, `mir`, `evm-equivalence`) run only when
//! `BUILD_AGREEMENT_CASES` names them (for example `wasm,mir,evm-equivalence`), or with every
//! local case when it is unset and `BUILD_AGREEMENT_REAL_SEMANTICS=1`; their checkouts
//! resolve as `scripts/reference-manifest.py` resolves them, and a named case whose source cannot
//! be read fails the run. `scripts/build-agreement.sh` runs both builds, the gate registry's
//! `build-agreement` entry (`scripts/gates.toml`) with the recorded refusal set.

use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
};

use k_rust::{
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadError, LoadOptions, ResolvedSource, load_for_compilation},
};
use sha2::{Digest, Sha256};
use toml::Value;

const MANIFEST: &str = include_str!("../../../scripts/reference-differential.toml");

/// The SHA-256 of `parts`, each length-prefixed, in hexadecimal: equal exactly when the parts are.
fn digest(parts: &[&str]) -> String {
    let mut hash = Sha256::new();
    for part in parts {
        hash.update(part.len().to_le_bytes());
        hash.update(part.as_bytes());
    }
    hash.finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// The real-semantics cases, whose sources are the large checkouts beside the workspace: compiled
/// only when `BUILD_AGREEMENT_CASES` names them or `BUILD_AGREEMENT_REAL_SEMANTICS=1` adds them.
const HEAVY: [&str; 3] = ["wasm", "mir", "evm-equivalence"];

/// A manifest path with its checkout placeholder replaced, as `scripts/reference-manifest.py`
/// resolves it (the same environment variables, the same defaults beside the workspace).
fn manifest_path(workspace: &Path, path: &str) -> Option<PathBuf> {
    let (placeholder, rest) = path.strip_prefix("${")?.split_once("}/")?;
    let (variable, default) = match placeholder {
        "workspace" => ("WORKSPACE", ""),
        "k" => ("K_CHECKOUT", "k"),
        "imp" => ("IMP_SEMANTICS_CHECKOUT", "imp-semantics"),
        "wasm" => ("WASM_SEMANTICS_CHECKOUT", "wasm-semantics"),
        "evm" => ("EVM_SEMANTICS_CHECKOUT", "evm-semantics"),
        "mir" => ("MIR_SEMANTICS_CHECKOUT", "mir-semantics"),
        _ => return None,
    };
    let root = env::var_os(variable).map_or_else(|| workspace.join(default), PathBuf::from);
    Some(root.join(rest))
}

/// The identity of a source file: its canonical path. The loader recognises a file it has
/// already read by the name its resolver gives it, so two names of one file (`a/b/../c.md` and
/// `a/c.md`) must be one name; otherwise two files that require each other through `..` are read
/// as an unbounded chain of new files.
fn read_source(path: &Path) -> Result<ResolvedSource, String> {
    let canonical =
        fs::canonicalize(path).map_err(|error| format!("{}: {error}", path.display()))?;
    fs::read_to_string(&canonical)
        .map(|text| ResolvedSource::new(canonical.display().to_string(), text))
        .map_err(|error| format!("{}: {error}", canonical.display()))
}

/// What a build made of one case: the digest of its three KORE artifacts, or the kind of error.
/// An error when the case's own source cannot be read: then no build compiled it.
fn outcome(workspace: &Path, case: &toml::Table) -> Result<(String, String), String> {
    let name = case["name"]
        .as_str()
        .ok_or("a compile case without a name")?
        .to_owned();
    let source = case["source"]
        .as_str()
        .and_then(|source| manifest_path(workspace, source))
        .ok_or_else(|| format!("{name}: no resolvable source"))?;
    let include = case
        .get("include")
        .and_then(Value::as_str)
        .and_then(|include| manifest_path(workspace, include));
    let entry = read_source(&source).map_err(|error| format!("{name}: {error}"))?;
    let main = case["main-module"]
        .as_str()
        .ok_or_else(|| format!("{name}: no main module"))?;
    let syntax = case.get("syntax-module").and_then(Value::as_str);
    let backend = CompilationBackend::Rust;
    let prelude = k_rust::builtin::embedded("prelude.md").expect("the embedded prelude");
    let mut resolver = |requiring: &str, required: &str| {
        if let Some(builtin) = k_rust::builtin::embedded(required) {
            return Ok(builtin);
        }
        let beside = Path::new(requiring)
            .parent()
            .unwrap_or(Path::new("."))
            .join(required);
        let candidates = [
            Some(beside),
            include.as_ref().map(|include| include.join(required)),
        ];
        let path = candidates
            .into_iter()
            .flatten()
            .find(|path| path.is_file())
            .ok_or_else(|| format!("cannot resolve {required} from {requiring}"))?;
        read_source(&path)
    };
    let options = LoadOptions {
        markdown_selector: case
            .get("markdown-selector")
            .and_then(Value::as_str)
            .unwrap_or("k")
            .to_owned(),
        implicit_sources: vec![prelude],
        excluded_module_attributes: vec![backend.excluded_module_attribute().into()],
        ..LoadOptions::default()
    };
    let loaded = load_for_compilation(entry, main, syntax, &mut resolver, &options);
    let result = match loaded {
        Err(LoadError::SourceDiagnostics(diagnostics)) => {
            let text = format!("{diagnostics:?}");
            if text.contains("Z3InferenceRequired") {
                "error Z3InferenceRequired".to_owned()
            } else {
                format!("error load {}", digest(&[&text]))
            }
        }
        Err(error) => {
            let text = format!("{error:?}");
            if text.contains("Z3InferenceRequired") {
                "error Z3InferenceRequired".to_owned()
            } else {
                format!("error load {}", digest(&[&text]))
            }
        }
        Ok((loaded, _)) => {
            let compile_options = CompileOptions {
                backend,
                hook_namespaces: case.get("hook-namespaces").and_then(Value::as_array).map(
                    |namespaces| {
                        namespaces
                            .iter()
                            .filter_map(Value::as_str)
                            .map(str::to_owned)
                            .collect()
                    },
                ),
                ..CompileOptions::default()
            };
            match compile_loaded_definition(&loaded, compile_options) {
                Ok(artifacts) => format!(
                    "kore {}",
                    digest(&[
                        &artifacts.definition_kore,
                        &artifacts.syntax_definition_kore,
                        &artifacts.macros_kore,
                    ])
                ),
                Err(error) => {
                    let text = format!("{error:?}");
                    if text.contains("Z3InferenceRequired") {
                        "error Z3InferenceRequired".to_owned()
                    } else {
                        format!("error compile {}", digest(&[&text]))
                    }
                }
            }
        }
    };
    Ok((name, result))
}

#[test]
#[ignore = "a comparison of two builds: run once per build, as the module documentation shows"]
fn both_builds_compile_every_local_manifest_case_alike() {
    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let cases = manifest["compile"]
        .as_array()
        .expect("compile cases")
        .iter()
        .filter_map(Value::as_table)
        .collect::<Vec<_>>();
    let selected = env::var("BUILD_AGREEMENT_CASES").ok();
    let real_semantics = env::var("BUILD_AGREEMENT_REAL_SEMANTICS").is_ok_and(|value| value == "1");
    if let Some(selected) = &selected {
        let unknown = selected
            .split(',')
            .filter(|name| !cases.iter().any(|case| case["name"].as_str() == Some(name)))
            .collect::<Vec<_>>();
        assert!(
            unknown.is_empty(),
            "BUILD_AGREEMENT_CASES names no compile case: {unknown:?}"
        );
    }
    let rejected = cases
        .iter()
        .filter(|case| case.get("expect").and_then(Value::as_str) == Some("reject"))
        .filter_map(|case| case["name"].as_str())
        .collect::<BTreeSet<_>>();
    let (outcomes, unread): (Vec<_>, Vec<_>) = cases
        .into_iter()
        .filter(|case| {
            let name = case["name"].as_str().unwrap_or_default();
            match selected.as_deref() {
                Some(selected) => selected.split(',').any(|selected| selected == name),
                None => real_semantics || !HEAVY.contains(&name),
            }
        })
        .map(|case| outcome(&workspace, case))
        .partition(Result::is_ok);
    let unread = unread
        .into_iter()
        .filter_map(Result::err)
        .collect::<Vec<_>>();
    assert!(
        unread.is_empty(),
        "selected cases this build cannot read, so neither build compiles them here:\n{}",
        unread.join("\n")
    );
    let outcomes = outcomes
        .into_iter()
        .filter_map(Result::ok)
        .collect::<BTreeMap<_, _>>();
    assert!(!outcomes.is_empty(), "no local compile case");
    let native = cfg!(feature = "z3-inference");
    // A case the manifest does not expect to be rejected is a definition that compiles, so any
    // other error than the portable build's documented refusal means this build did not compile
    // it and nothing was compared; an error both builds share would otherwise read as agreement.
    // The native build settles with Z3 what the portable build refuses, so a refusal there is an
    // error like any other.
    let not_compiled = outcomes
        .iter()
        .filter(|(name, outcome)| {
            outcome.starts_with("error ")
                && (native || outcome.as_str() != "error Z3InferenceRequired")
                && !rejected.contains(name.as_str())
        })
        .map(|(name, outcome)| format!("{name}: {outcome}"))
        .collect::<Vec<_>>();
    assert!(
        not_compiled.is_empty(),
        "cases expected to compile that this build did not compile:\n{}",
        not_compiled.join("\n")
    );
    let build = if native { "z3-inference" } else { "portable" };
    let rendered = outcomes
        .iter()
        .map(|(name, outcome)| format!("{name}\t{outcome}\n"))
        .collect::<String>();
    eprintln!("{build} build:\n{rendered}");
    if let Some(path) = env::var_os("BUILD_AGREEMENT_RECORD") {
        fs::write(&path, &rendered).expect("record the outcomes");
    }
    if let (false, Ok(expected)) = (native, env::var("BUILD_AGREEMENT_REFUSED")) {
        let expected = expected
            .split(',')
            .filter(|name| !name.is_empty())
            .collect::<BTreeSet<_>>();
        let unselected = expected
            .iter()
            .filter(|name| !outcomes.contains_key(**name))
            .collect::<Vec<_>>();
        assert!(
            unselected.is_empty(),
            "BUILD_AGREEMENT_REFUSED names cases this run did not select: {unselected:?}"
        );
        let mut changes = Vec::new();
        for (name, outcome) in &outcomes {
            let refused = outcome == "error Z3InferenceRequired";
            match (refused, expected.contains(name.as_str())) {
                (true, false) => changes.push(format!("{name}: refused, and not in the record")),
                (false, true) => changes.push(format!(
                    "{name}: in the record, and {outcome} in the portable build; remove it from \
                     the record"
                )),
                _ => {}
            }
        }
        assert!(
            changes.is_empty(),
            "the portable build's refusals differ from BUILD_AGREEMENT_REFUSED:\n{}",
            changes.join("\n")
        );
    }
    let Some(path) = env::var_os("BUILD_AGREEMENT_COMPARE") else {
        return;
    };
    let other = fs::read_to_string(&path).expect("read the other build's outcomes");
    let theirs = other
        .lines()
        .filter_map(|line| line.split_once('\t'))
        .collect::<BTreeMap<_, _>>();
    let mut failures = Vec::new();
    // A case one build compiled and the other never read (a checkout missing in one run) is not
    // agreement: it is a comparison that did not happen.
    for name in outcomes
        .keys()
        .map(String::as_str)
        .chain(theirs.keys().copied())
    {
        if !outcomes.contains_key(name) || !theirs.contains_key(name) {
            failures.push(format!("{name}: compiled in one build only"));
        }
    }
    let refused_for_inference = |outcome: &str| outcome == "error Z3InferenceRequired";
    let mut refused = Vec::new();
    for (name, theirs) in &theirs {
        let Some(ours) = outcomes.get(*name) else {
            continue;
        };
        if refused_for_inference(ours) || refused_for_inference(theirs) {
            // The documented refusal is not a disagreement, but a case the portable build
            // refuses is a definition its hosts cannot compile: it is reported, never silent.
            refused.push(*name);
        } else if ours != theirs {
            failures.push(format!("{name}: {build} {ours}, other build {theirs}"));
        }
    }
    eprintln!(
        "refused with Z3InferenceRequired in one build ({}): {refused:?}",
        refused.len()
    );
    failures.sort();
    failures.dedup();
    assert!(
        failures.is_empty(),
        "the builds disagree:\n{}",
        failures.join("\n")
    );
}
