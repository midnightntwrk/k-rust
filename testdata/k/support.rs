//! Loading and comparison helpers for the K definitions in this directory.
//!
//! Integration tests include this file with
//! `#[path = "../../../testdata/k/support.rs"] mod support;`; each crate uses
//! a subset of it.
#![allow(dead_code)]

use k_rust::builtin;
use k_rust::definition::{AttributeKey, Definition, Sentence};
use k_rust::kast::Term;
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kompile::{
    CompilationBackend, CompileError, CompileOptions, CompiledKoreArtifacts,
    compile_loaded_definition,
};
use k_rust::kore::ast::{Pattern, Variable, VariableKind};
use k_rust::outer::{LoadOptions, LoadedDefinition, ResolvedSource};
use kink_patch::{Baseline, SentenceRef};
use serde_json::Value;
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

pub const DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../testdata/k/");

/// Keys that record where a sentence was written, not what it says.
const POSITION_KEYS: [AttributeKey; 9] = [
    AttributeKey::Location,
    AttributeKey::Source,
    AttributeKey::SourceId,
    AttributeKey::SentenceStartOffset,
    AttributeKey::SentenceEndOffset,
    AttributeKey::ContentStartLine,
    AttributeKey::ContentStartColumn,
    AttributeKey::ContentStartOffset,
    AttributeKey::Origin,
];

/// `kast.md` plus `prelude.md`, with the Rust backend's module exclusion.
pub fn options() -> LoadOptions {
    LoadOptions {
        implicit_sources: vec![
            builtin::embedded("kast.md").expect("kast.md is embedded"),
            builtin::embedded("prelude.md").expect("prelude.md is embedded"),
        ],
        excluded_module_attributes: vec![
            CompilationBackend::Rust
                .excluded_module_attribute()
                .to_owned(),
        ],
        ..LoadOptions::default()
    }
}

/// Loads `name` from this directory; its main module is the upper-cased stem.
pub fn load(name: &str) -> Baseline {
    let main_module = name
        .strip_suffix(".k")
        .expect("a .k file")
        .to_ascii_uppercase();
    load_path(&Path::new(DIR).join(name), &main_module)
}

pub fn load_path(path: &Path, main_module: &str) -> Baseline {
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .expect("file name");
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("{required} is not embedded"))
    };
    Baseline::load(
        ResolvedSource::new(name, read(path)),
        main_module,
        None,
        &mut resolver,
        &options(),
    )
    .unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

/// The one sentence labelled `label` (module-qualified, as loading writes it).
pub fn rule(baseline: &Baseline, label: &str) -> SentenceRef {
    let mut found = baseline
        .authored_sentences()
        .filter(|(_, sentence)| sentence.attributes().string(AttributeKey::Label) == Some(label))
        .map(|(at, _)| at);
    let at = found
        .next()
        .unwrap_or_else(|| panic!("no sentence labelled {label}"));
    assert!(found.next().is_none(), "two sentences labelled {label}");
    at
}

pub fn compile(loaded: &LoadedDefinition) -> Result<CompiledKoreArtifacts, CompileError> {
    compile_loaded_definition(loaded, CompileOptions::default())
}

pub fn var(name: &str, sort: &str) -> Pattern {
    Pattern::Variable(Variable {
        kind: VariableKind::Element,
        name: name.to_owned(),
        sort: kore_sort(sort),
    })
}

pub fn app(symbol: &str, args: Vec<Pattern>) -> Pattern {
    kore_application(symbol, Vec::new(), args)
}

pub fn int(value: i64) -> Pattern {
    Pattern::DomainValue {
        sort: kore_sort("SortInt"),
        value: value.to_string().into(),
    }
}

/// The path through the layout built by `initial_state`: generatedTop -> <k> ->
/// kseq -> inj -> the program term, followed by `rest`.
pub fn k_head(rest: &[u32]) -> Vec<u32> {
    let mut path = vec![0, 0, 0, 0];
    path.extend_from_slice(rest);
    path
}

/// The initial configuration `<generatedTop>(<k>(program ~> .K), <generatedCounter>(0))`
/// of a definition whose only declared cell is `<k>`, for a `program` of KORE sort `sort`.
/// Built by hand for these tests' fixed configuration shape.
pub fn initial_state(program: Pattern, sort: &str) -> Pattern {
    let item = kore_application(
        "inj",
        vec![kore_sort(sort), kore_sort("SortKItem")],
        vec![program],
    );
    let k = kore_application(
        "kseq",
        Vec::new(),
        vec![item, kore_application("dotk", Vec::new(), Vec::new())],
    );
    kore_application(
        "Lbl'-LT-'generatedTop'-GT-'",
        Vec::new(),
        vec![
            kore_application("Lbl'-LT-'k'-GT-'", Vec::new(), vec![k]),
            kore_application(
                "Lbl'-LT-'generatedCounter'-GT-'",
                Vec::new(),
                vec![Pattern::DomainValue {
                    sort: kore_sort("SortInt"),
                    value: "0".into(),
                }],
            ),
        ],
    )
}

/// `initial_state(program, sort)` of `undecided.k` under the path condition
/// `X = z /\ isZero(X) = false`, which is contradictory only once its substitution is
/// applied: k-rust defers that vacuity past the first rewrite and then halts the successor
/// as `vacuous`, keeping the rewrite's events.
pub fn deferred_vacuous_state(program: Pattern, sort: &str) -> Pattern {
    let condition = k_rust::kore::parser::parse_pattern(
        r#"\and{SortGeneratedTopCell{}}(\equals{SortNat{}, SortGeneratedTopCell{}}(VarX:SortNat{}, Lblz{}()), \equals{SortBool{}, SortGeneratedTopCell{}}(\dv{SortBool{}}("false"), LblisZero{}(VarX:SortNat{})))"#,
    )
    .expect("the deferred condition parses");
    Pattern::And {
        sort: kore_sort("SortGeneratedTopCell"),
        arguments: vec![initial_state(program, sort), condition],
    }
}

/// One written rule, claim or context, without its position attributes.
#[derive(Debug, PartialEq)]
pub struct AuthoredRule {
    pub kind: &'static str,
    pub fields: Vec<Term>,
    pub attributes: BTreeMap<String, Value>,
}

/// The written rules, claims and contexts of `module`, in order.
///
/// Productions and configuration output are left out: configuration
/// expansion places its sentences after the module's rules, so a module-end
/// insertion and source order disagree about them. Terms compare with
/// `Term ==`, which ignores compiler metadata but not variable sorts.
pub fn authored_rules(definition: &Definition, module: &str) -> Vec<AuthoredRule> {
    let module = definition
        .modules
        .iter()
        .find(|candidate| candidate.name == module)
        .unwrap_or_else(|| panic!("no module {module}"));
    module
        .local_sentences
        .iter()
        .filter(|sentence| sentence.attributes().location().is_some())
        .filter_map(|sentence| {
            let (kind, fields) = match &**sentence {
                Sentence::Rule {
                    body,
                    requires,
                    ensures,
                    ..
                } => ("rule", vec![body, requires, ensures]),
                Sentence::Claim {
                    body,
                    requires,
                    ensures,
                    ..
                } => ("claim", vec![body, requires, ensures]),
                Sentence::Context { body, requires, .. } => ("context", vec![body, requires]),
                _ => return None,
            };
            let attributes = sentence
                .attributes()
                .wire_map()
                .into_iter()
                .filter(|(key, _)| {
                    POSITION_KEYS
                        .iter()
                        .all(|position| position.as_str() != key)
                })
                .collect();
            Some(AuthoredRule {
                kind,
                fields: fields.into_iter().cloned().collect(),
                attributes,
            })
        })
        .collect()
}

pub fn assert_same_authored_rules(module: &str, actual: &Definition, expected: &Definition) {
    assert_eq!(
        authored_rules(actual, module),
        authored_rules(expected, module),
        "authored rules of {module}"
    );
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}
