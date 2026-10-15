//! The compile property the execution digest relies on: text positions and resolver
//! identities reach `definition.kore` only through `Source` and `Location`, so comments, blank
//! lines, trailing whitespace, Markdown prose outside K code blocks and another resolver identity
//! leave `CompiledKoreArtifacts::execution_digest` unchanged; and the mutation operators a host
//! applies to a definition change it.
//!
//! The corpus is every in-repository `[[compile]]` case of `scripts/reference-differential.toml`
//! (source under `${workspace}`, not expected to be rejected), so the test needs no reference
//! checkout. Each case is compiled once as written, once under another resolver identity, and
//! once per layout edit it is given. The edits move lines, columns and positions inside
//! sentences. To keep the run short the test checks a rotating sample: case `i` gets the
//! [`EDITS_PER_CASE`] edits from `i * EDITS_PER_CASE` on (modulo their number) of
//! [`LAYOUT_EDITS`], so every edit is applied to several cases, and the cases are compiled in
//! parallel.

use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

use k_rust::{
    backend::ExecutionDigest,
    builtin::embedded,
    kompile::{
        CompilationBackend, CompileOptions, CompiledKoreArtifacts, compile_loaded_definition,
    },
    kore::{ast::Sentence, parser::parse_definition, printer::Printer},
    names::KoreAttribute,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

struct Case {
    name: String,
    source: PathBuf,
    main: String,
    hook_namespaces: Option<Vec<String>>,
}

/// The in-repository compile cases the manifest expects to compile.
fn cases() -> Vec<Case> {
    let manifest =
        std::fs::read_to_string(workspace().join("scripts/reference-differential.toml")).unwrap();
    let manifest: toml::Table = toml::from_str(&manifest).unwrap();
    manifest["compile"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|case| {
            let source = case["source"].as_str().unwrap();
            let relative = source.strip_prefix("${workspace}/")?;
            if case.get("expect").and_then(toml::Value::as_str) == Some("reject") {
                return None;
            }
            Some(Case {
                name: case["name"].as_str().unwrap().to_owned(),
                source: workspace().join(relative),
                main: case["main-module"].as_str().unwrap().to_owned(),
                hook_namespaces: case.get("hook-namespaces").map(|namespaces| {
                    namespaces
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|namespace| namespace.as_str().unwrap().to_owned())
                        .collect()
                }),
            })
        })
        .collect()
}

/// Compile `text`, read as the file `declared`, resolving `requires` in `directory`.
fn compile(
    declared: &str,
    directory: &Path,
    text: &str,
    main: &str,
    hook_namespaces: Option<Vec<String>>,
) -> CompiledKoreArtifacts {
    let directory = directory.to_path_buf();
    let mut resolver = move |_: &str, required: &str| {
        if let Some(found) = embedded(required) {
            return Ok(found);
        }
        let path = directory.join(required);
        let text = std::fs::read_to_string(&path)
            .map_err(|error| format!("{}: {error}", path.display()))?;
        Ok(ResolvedSource::new(path.display().to_string(), text))
    };
    let loaded = load_with_options(
        ResolvedSource::new(declared, text),
        main,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap_or_else(|error| panic!("{declared}: {error}"));
    compile_loaded_definition(
        &loaded,
        CompileOptions {
            hook_namespaces,
            ..CompileOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{declared}: {error}"))
}

fn digest(artifacts: &CompiledKoreArtifacts) -> ExecutionDigest {
    artifacts.execution_digest().unwrap()
}

/// The sentences (first few) whose compact print differs between two definitions with their
/// origins removed, to say why two digests differ.
fn residue(left: &CompiledKoreArtifacts, right: &CompiledKoreArtifacts) -> String {
    let printed = |artifacts: &CompiledKoreArtifacts| {
        let definition = parse_definition(&artifacts.definition_kore).unwrap();
        definition
            .modules
            .iter()
            .flat_map(|module| {
                module.sentences.iter().map(move |sentence| {
                    let mut sentence = sentence.clone();
                    let attributes = match &mut sentence {
                        Sentence::Import { attributes, .. }
                        | Sentence::SortDeclaration { attributes, .. }
                        | Sentence::SymbolDeclaration { attributes, .. }
                        | Sentence::AliasDeclaration { attributes, .. }
                        | Sentence::Axiom { attributes, .. }
                        | Sentence::Claim { attributes, .. } => attributes,
                    };
                    attributes.0.retain(|attribute| {
                        !matches!(attribute, k_rust::kore::ast::Pattern::Application { symbol, .. }
                            if symbol.name == KoreAttribute::Source.as_str()
                                || symbol.name == KoreAttribute::Location.as_str())
                    });
                    format!(
                        "{}: {}",
                        module.name,
                        Printer::compact().print_sentence(&sentence)
                    )
                })
            })
            .collect::<BTreeSet<_>>()
    };
    let (left, right) = (printed(left), printed(right));
    left.symmetric_difference(&right)
        .take(4)
        .map(|line| line.chars().take(300).collect::<String>())
        .collect::<Vec<_>>()
        .join("\n")
}

/// `text` with `insert` before the first line that starts (after indentation) with `prefix`.
fn before_first(text: &str, prefix: &str, insert: &str) -> Option<String> {
    let mut offset = 0;
    for line in text.split_inclusive('\n') {
        if line.trim_start().starts_with(prefix) {
            return Some(format!("{}{insert}{}", &text[..offset], &text[offset..]));
        }
        offset += line.len();
    }
    None
}

/// `text` with `insert` before the last line that starts with `prefix`.
fn before_last(text: &str, prefix: &str, insert: &str) -> Option<String> {
    let mut found = None;
    let mut offset = 0;
    for line in text.split_inclusive('\n') {
        if line.trim_start().starts_with(prefix) {
            found = Some(offset);
        }
        offset += line.len();
    }
    found.map(|at| format!("{}{insert}{}", &text[..at], &text[at..]))
}

type LayoutEdit = fn(&str) -> Option<String>;

/// `edited` when it differs from `text`: an edit with nowhere to apply is not applied.
fn changed(text: &str, edited: String) -> Option<String> {
    (edited != text).then_some(edited)
}

/// Edits that change only layout and comments; `None` when a case has no place for one.
const LAYOUT_EDITS: [(&str, LayoutEdit); 14] = [
    ("blank lines at the start", |text| {
        Some(format!("\n\n\n{text}"))
    }),
    ("comments before the first module", |text| {
        before_first(
            text,
            "module ",
            "// a line comment\n/* a block\n   comment */\n\n",
        )
    }),
    (
        "a comment and blank lines before the last endmodule",
        |text| before_last(text, "endmodule", "\n  // a comment inside the module\n\n"),
    ),
    ("blank lines before the first rule", |text| {
        before_first(text, "rule ", "\n\n")
    }),
    ("trailing spaces on every line", |text| {
        Some(text.lines().map(|line| format!("{line}   \n")).collect())
    }),
    ("blank lines before the last rule", |text| {
        before_last(text, "rule ", "\n\n\n")
    }),
    // Edits that move columns and positions inside a sentence.
    ("indent every line by two spaces", |text| {
        Some(text.lines().map(|line| format!("  {line}\n")).collect())
    }),
    ("doubled spaces around =>", |text| {
        changed(text, text.replace(" => ", "  =>  "))
    }),
    ("a line break before =>", |text| {
        changed(text, text.replace(" => ", "\n          => "))
    }),
    ("a block comment before =>", |text| {
        changed(text, text.replace(" => ", " /* c */ => "))
    }),
    ("productions on new lines", |text| {
        changed(text, text.replace(" | ", "\n      | "))
    }),
    ("attributes on a new line", |text| {
        changed(text, text.replace(" [", "\n        ["))
    }),
    ("a line break after rule", |text| {
        changed(text, text.replace("rule ", "rule\n    "))
    }),
    ("CRLF line endings", |text| {
        changed(text, text.replace('\n', "\r\n"))
    }),
];

/// How many of [`LAYOUT_EDITS`] each case gets.
const EDITS_PER_CASE: usize = 4;

/// The layout edits applied to case `index` and the cases whose digest moved, as
/// `(edit indexes applied, failure descriptions)`.
fn check_case(index: usize, case: &Case) -> (Vec<usize>, Vec<String>) {
    let text = std::fs::read_to_string(&case.source).unwrap();
    let directory = case.source.parent().unwrap();
    let declared = case.source.display().to_string();
    let compile_as = |declared: &str, text: &str| {
        compile(
            declared,
            directory,
            text,
            &case.main,
            case.hook_namespaces.clone(),
        )
    };
    let base = compile_as(&declared, &text);
    let base_digest = digest(&base);
    let mut edits = vec![(
        "another resolver identity",
        format!(
            "/elsewhere/checkout/{}",
            case.source.file_name().unwrap().to_string_lossy()
        ),
        text.clone(),
    )];
    let mut applied = Vec::new();
    for offset in 0..EDITS_PER_CASE {
        let which = (index * EDITS_PER_CASE + offset) % LAYOUT_EDITS.len();
        let (name, edit) = LAYOUT_EDITS[which];
        if let Some(edited) = edit(&text) {
            applied.push(which);
            edits.push((name, declared.clone(), edited));
        }
    }
    let mut failures = Vec::new();
    for (name, declared, edited) in edits {
        let artifacts = compile_as(&declared, &edited);
        if digest(&artifacts) != base_digest {
            failures.push(format!(
                "{} ({name}):\n{}",
                case.name,
                residue(&base, &artifacts)
            ));
        }
    }
    (applied, failures)
}

/// Layout edits and another resolver identity leave the digest of every in-repository case
/// unchanged. The cases are compiled on eight worker threads.
#[test]
fn layout_and_resolver_identity_do_not_change_the_digest() {
    use std::sync::{
        Mutex,
        atomic::{AtomicUsize, Ordering},
    };

    let cases = cases();
    assert!(cases.len() >= 20, "{} cases", cases.len());
    let next = AtomicUsize::new(0);
    let results = Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..8 {
            std::thread::Builder::new()
                .stack_size(64 << 20)
                .spawn_scoped(scope, || {
                    loop {
                        let index = next.fetch_add(1, Ordering::Relaxed);
                        let Some(case) = cases.get(index) else {
                            break;
                        };
                        let result = check_case(index, case);
                        results.lock().unwrap().push(result);
                    }
                })
                .unwrap();
        }
    });
    let mut applied = vec![0; LAYOUT_EDITS.len()];
    let mut failures = Vec::new();
    for (edits, case_failures) in results.into_inner().unwrap() {
        for which in edits {
            applied[which] += 1;
        }
        failures.extend(case_failures);
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    assert!(
        applied.iter().all(|count| *count >= 2),
        "every layout edit is applied to some cases: {applied:?}"
    );
}

/// The K text of `case` inside a Markdown document, with `prose` around its `k` code block.
fn markdown(text: &str, prose: &str) -> String {
    format!("# A definition\n\n{prose}\n\n```k\n{text}\n```\n\nMore {prose}\n")
}

/// Markdown prose and non-`k` code blocks outside the K code block leave the digest unchanged,
/// and a definition read from Markdown has the digest of the same text read as K.
#[test]
fn markdown_prose_does_not_change_the_digest() {
    for name in ["owise-functions", "star-cell-config"] {
        let case = cases().into_iter().find(|case| case.name == name).unwrap();
        let text = std::fs::read_to_string(&case.source).unwrap();
        let directory = case.source.parent().unwrap();
        let compile_as = |declared: &str, text: &str| {
            digest(&compile(
                declared,
                directory,
                text,
                &case.main,
                case.hook_namespaces.clone(),
            ))
        };
        let plain = compile_as("case.k", &text);
        let first = compile_as("case.md", &markdown(&text, "Some prose."));
        let second = compile_as(
            "case.md",
            &markdown(
                &text,
                "Other prose,\nover two lines.\n\n```python\nprint(\"not K\")\n```",
            ),
        );
        assert_eq!(first, second, "{name}");
        assert_eq!(first, plain, "{name}");
    }
}

/// A definition with a target for each class of mutation operator.
const MUTABLE: &str = r#"
module MUT
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax KItem ::= step(Int, Int) | out(Int) | pick(Int)
  configuration <k> $PGM:KItem </k>
  rule <k> step(A, B) => out(A +Int B) </k> requires A <=Int B andBool notBool (A ==K B)
  rule <k> step(_, _) => out(0) </k> [owise]
  rule <k> pick(I) => out(I +Int 1) </k> [priority(40)]
  rule <k> pick(I) => out(I) </k> [priority(50)]
endmodule
"#;

/// One mutation per operator class changes the digest; an attribute that compiled KORE does not
/// carry (`group` on a rule) does not.
#[test]
fn mutation_operators_change_the_digest() {
    let digest_of = |text: &str| {
        digest(&compile(
            "mut.k",
            Path::new("/nonexistent"),
            text,
            "MUT",
            None,
        ))
    };
    let base = digest_of(MUTABLE);
    let condition = "requires A <=Int B andBool notBool (A ==K B)";
    let mutations = [
        ("aor", "A +Int B", "A -Int B"),
        ("ror", "A <=Int B", "A <Int B"),
        ("lcr", "andBool", "orBool"),
        ("eqk", "A ==K B", "A =/=K B"),
        ("cond-true", condition, "requires true"),
        ("cond-false", condition, "requires false"),
        (
            "cond-negate",
            condition,
            "requires notBool (A <=Int B andBool notBool (A ==K B))",
        ),
        ("not-unwrap", "notBool (A ==K B)", "(A ==K B)"),
        ("int-literal +1", "out(0)", "out(1)"),
        ("int-literal -1", "out(0)", "out(-1)"),
        ("drop-owise", " [owise]", ""),
        ("drop-priority", " [priority(40)]", ""),
        (
            "delete-rule",
            "  rule <k> pick(I) => out(I +Int 1) </k> [priority(40)]\n",
            "",
        ),
        (
            "add-label",
            "rule <k> pick(I) => out(I) </k>",
            "rule [same]: <k> pick(I) => out(I) </k>",
        ),
    ];
    for (operator, from, to) in mutations {
        assert_eq!(MUTABLE.matches(from).count(), 1, "{operator}");
        assert_ne!(
            digest_of(&MUTABLE.replacen(from, to, 1)),
            base,
            "{operator} keeps the digest"
        );
    }
    // `group` on a rule is a K attribute that compiled KORE does not carry: no digest change.
    // (On a production, `group` can change parsing through syntax priorities, which the digest
    // of `definition.kore` does not see.)
    assert_eq!(
        digest_of(&MUTABLE.replacen(" [priority(50)]", " [priority(50), group(g)]", 1)),
        base
    );
}
