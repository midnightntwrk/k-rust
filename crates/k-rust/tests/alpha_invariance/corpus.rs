//! The corpus of the corpus mode: the definitions of the reference-differential manifest
//! (`scripts/reference-differential.toml`) and the prelude.

use std::{
    env,
    path::{Path, PathBuf},
};

use toml::Value;

use super::harness::{Case, Program, Scope, Text};

const MANIFEST: &str = include_str!("../../../../scripts/reference-differential.toml");

/// The cases whose sources live in a large checkout beside the workspace; never in the corpus.
const REAL_SEMANTICS: [&str; 3] = ["wasm", "mir", "evm-equivalence"];

pub fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// A manifest path with its checkout placeholder replaced, as `scripts/reference-manifest.py`
/// resolves it; `None` for a placeholder this corpus does not read.
fn manifest_path(path: &str) -> Option<PathBuf> {
    let (placeholder, rest) = path.strip_prefix("${")?.split_once("}/")?;
    let (variable, default) = match placeholder {
        "workspace" => ("WORKSPACE", ""),
        "k" => ("K_CHECKOUT", "k"),
        "imp" => ("IMP_SEMANTICS_CHECKOUT", "imp-semantics"),
        _ => return None,
    };
    let root = env::var_os(variable).map_or_else(|| workspace().join(default), PathBuf::from);
    Some(root.join(rest))
}

/// Whether a manifest source lies in the workspace, so the case runs without any checkout.
fn in_workspace(source: &str) -> bool {
    source.starts_with("${workspace}/")
}

fn case(table: &toml::Table, runnable: bool) -> Option<Case> {
    let name = table.get("name")?.as_str()?;
    let source = table.get("source")?.as_str()?;
    let path = manifest_path(source)?;
    let include = table
        .get("include")
        .and_then(Value::as_str)
        .and_then(manifest_path);
    let strings = |key: &str| -> Vec<String> {
        table
            .get(key)
            .and_then(Value::as_array)
            .map(|values| {
                values
                    .iter()
                    .filter_map(Value::as_str)
                    .map(str::to_owned)
                    .collect()
            })
            .unwrap_or_default()
    };
    let programs = if runnable {
        let sort = table.get("sort").and_then(Value::as_str).unwrap_or("K");
        strings("programs")
            .iter()
            .filter_map(|program| manifest_path(program))
            .filter_map(|program| std::fs::read_to_string(program).ok())
            .map(|text| Program {
                sort: sort.to_owned(),
                text,
            })
            .collect()
    } else {
        Vec::new()
    };
    let bindings = strings("configuration")
        .iter()
        .filter_map(|binding| binding.split_once('='))
        .map(|(name, text)| (name.to_owned(), text.to_owned()))
        .collect();
    Some(Case {
        name: format!("{}/{name}", if runnable { "execution" } else { "compile" }),
        text: Text::File { path, include },
        main: table.get("main-module")?.as_str()?.to_owned(),
        syntax: table
            .get("syntax-module")
            .and_then(Value::as_str)
            .map(str::to_owned),
        scope: Scope::OwnFile,
        programs,
        bindings,
        depth: table
            .get("depth")
            .and_then(Value::as_integer)
            .map_or(20, |depth| depth as u64),
        hook_namespaces: table
            .get("hook-namespaces")
            .map(|_| strings("hook-namespaces")),
        skip_unloadable: false,
        mains: Vec::new(),
        for_proving: false,
        twins: Vec::new(),
        searches: Vec::new(),
        patterns: Vec::new(),
    })
}

/// The manifest's compile and execution cases. `local` keeps the cases whose sources lie in
/// the workspace; otherwise every case whose checkout is present beside it (`k`,
/// `imp-semantics`), the real semantics excepted.
pub fn manifest_cases(local: bool) -> Vec<Case> {
    manifest_entries(local)
        .into_iter()
        .filter(|case| matches!(&case.text, Text::File { path, .. } if path.is_file()))
        .collect()
}

/// The names of every case the manifest can give, whether or not its checkout is present.
pub fn manifest_case_names() -> Vec<String> {
    manifest_entries(false)
        .into_iter()
        .map(|case| case.name)
        .collect()
}

fn manifest_entries(local: bool) -> Vec<Case> {
    let manifest: toml::Table = MANIFEST.parse().expect("the manifest parses");
    let mut cases = Vec::new();
    for (key, runnable) in [("execution", true), ("compile", false)] {
        for table in manifest
            .get(key)
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_table)
        {
            let Some(source) = table.get("source").and_then(Value::as_str) else {
                continue;
            };
            let name = table.get("name").and_then(Value::as_str).unwrap_or("");
            if REAL_SEMANTICS.contains(&name) || (local && !in_workspace(source)) {
                continue;
            }
            if table.get("expect").and_then(Value::as_str) == Some("reject") {
                continue;
            }
            if let Some(case) = case(table, runnable) {
                cases.push(case);
            }
        }
    }
    cases
}

/// The prelude's own rules: every sentence of the modules a definition importing the main
/// prelude modules compiles, the prelude's included.
pub fn prelude_case() -> Case {
    let mut case = Case::inline(
        "prelude",
        "MAIN",
        "module MAIN\n  imports DOMAINS\n  imports BYTES\n  imports ARRAY\n  imports FLOAT\n  imports RANGEMAP\nendmodule\n",
    );
    case.scope = Scope::All;
    case
}

/// Every tracked K file under `crates/k-rust/tests` that the manifest does not already name,
/// compiled with its last module as the main module, or, when it does not load that way, with
/// the first of its other modules, from the last to the first, that loads. A file that loads
/// with none of them (one written to test a load error) is left out by the harness, which
/// lists it.
pub fn fixture_cases(named: &[Case]) -> Vec<Case> {
    let named: Vec<PathBuf> = named
        .iter()
        .filter_map(|case| match &case.text {
            Text::File { path, .. } => std::fs::canonicalize(path).ok(),
            Text::Inline(_) => None,
        })
        .collect();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut files = Vec::new();
    let mut directories = vec![root.clone()];
    while let Some(directory) = directories.pop() {
        let Ok(entries) = std::fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                directories.push(path);
            } else if path.extension().is_some_and(|extension| extension == "k") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
        .into_iter()
        .filter(|path| std::fs::canonicalize(path).is_ok_and(|path| !named.contains(&path)))
        .filter_map(|path| {
            let text = std::fs::read_to_string(&path).ok()?;
            let mut modules: Vec<String> = text
                .lines()
                .filter_map(|line| line.trim_start().strip_prefix("module "))
                .filter_map(|rest| rest.split_whitespace().next())
                .map(str::to_owned)
                .collect();
            let main = modules.pop()?;
            modules.reverse();
            let name = path.strip_prefix(&root).ok()?.display().to_string();
            Some(Case {
                name: format!("fixture/{name}"),
                text: Text::File {
                    path,
                    include: None,
                },
                main,
                syntax: None,
                scope: Scope::OwnFile,
                programs: Vec::new(),
                bindings: Vec::new(),
                depth: 20,
                hook_namespaces: None,
                skip_unloadable: true,
                mains: modules,
                for_proving: false,
                twins: Vec::new(),
                searches: Vec::new(),
                patterns: Vec::new(),
            })
        })
        .collect()
}
