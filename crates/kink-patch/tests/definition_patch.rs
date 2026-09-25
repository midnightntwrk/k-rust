#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::definition::{AttributeKey, Definition, ResolvedDefinition, Sentence, sentence_mut};
use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::outer::LoadedDefinition;
use kink_patch::{
    Baseline, Edit, InsertPosition, Patch, PatchFailureKind, PatchModelError, SentenceOrigin,
    SentenceRef, TermRef, apply, term_at,
};
use serde_json::Value;
use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Arc;

const EXPECTED: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/expected/");

/// The baseline of a row and, for rows with an expected file, that file
/// loaded the same way. Attribute values come from the loaded files, so no
/// row guesses the loader's spelling of an attribute.
struct Fixture<'a> {
    baseline: &'a Baseline,
    expected: Option<&'a Baseline>,
}

fn assert_same_rules_with_insertions(
    module: &str,
    mutant: &kink_patch::Mutant,
    expected: &Definition,
) {
    let mut projected = mutant.definition().clone();
    for output in projected.modules.iter_mut() {
        for (index, sentence) in output.local_sentences.iter_mut().enumerate() {
            let at = SentenceRef::new(output.name.clone(), u32::try_from(index).expect("index"));
            if matches!(mutant.origin(&at), Some(SentenceOrigin::Inserted { .. })) {
                sentence_mut(sentence)
                    .attributes_mut()
                    .set(AttributeKey::Location, serde_json::json!([1, 1, 1, 1]));
            }
        }
    }
    support::assert_same_authored_rules(module, &projected, expected);
}

impl Fixture<'_> {
    fn rule(&self, label: &str) -> SentenceRef {
        support::rule(self.baseline, label)
    }

    fn at(&self, label: &str, path: &[u32]) -> TermRef {
        TermRef::new(self.rule(label), path)
    }

    fn term(&self, label: &str, path: &[u32]) -> Term {
        self.baseline
            .term(&self.at(label, path))
            .unwrap_or_else(|| panic!("{label} {path:?}"))
            .clone()
    }

    fn replace(&self, label: &str, path: &[u32], replacement: Term) -> Edit {
        Edit::ReplaceTerm {
            at: self.at(label, path),
            expected: self.term(label, path),
            replacement,
        }
    }

    fn attribute(&self, label: &str, key: &str) -> Value {
        attribute(self.baseline, label, key)
    }

    fn expected_attribute(&self, label: &str, key: &str) -> Value {
        attribute(self.expected.expect("expected file"), label, key)
    }

    fn sentence(&self, label: &str) -> Sentence {
        self.baseline
            .sentence(&self.rule(label))
            .expect("sentence")
            .clone()
    }

    /// An insertion has none of the identity or position attributes of its source.
    fn anonymous_clone(&self, label: &str) -> Sentence {
        let mut sentence = self.sentence(label);
        for key in [
            AttributeKey::Label,
            AttributeKey::UniqueId,
            AttributeKey::Origin,
            AttributeKey::Location,
            AttributeKey::Source,
            AttributeKey::SourceId,
            AttributeKey::SentenceStartOffset,
            AttributeKey::SentenceEndOffset,
            AttributeKey::ContentStartLine,
            AttributeKey::ContentStartColumn,
            AttributeKey::ContentStartOffset,
        ] {
            sentence.attributes_mut().unset(key);
        }
        sentence
    }

    fn insert(&self, position: InsertPosition, ordinal: u32, label: &str) -> Edit {
        Edit::InsertSentence {
            position,
            ordinal,
            sentence: self.anonymous_clone(label),
        }
    }
}

fn attribute(baseline: &Baseline, label: &str, key: &str) -> Value {
    baseline
        .sentence(&support::rule(baseline, label))
        .and_then(|sentence| sentence.attributes().get(key))
        .unwrap_or_else(|| panic!("{label} has no {key}"))
        .clone()
}

fn z() -> Term {
    Term::apply("z", vec![])
}

fn s(term: Term) -> Term {
    Term::apply("s", vec![term])
}

fn addr(term: Term) -> Term {
    Term::apply("addr", vec![term])
}

fn boolean(value: &str) -> Term {
    Term::Token {
        token: value.to_owned(),
        sort: Sort::new("Bool"),
    }
}

enum Expect {
    /// `tests/data/expected/<id>.k`.
    File,
    Failure(PatchFailureKind),
}

type Row = (
    &'static str,
    &'static str,
    fn(&Fixture) -> Vec<Edit>,
    Expect,
);

/// The rows of the former `patch-application-vectors.json`, with their IDs
/// kept, over `memory.k` (M) and `counter.k` (C). A repeated ID is one former
/// row checked with several patches.
const ROWS: &[Row] = &[
    (
        "atomic-distinct-sentence-replacements",
        "memory.k",
        |f| {
            vec![
                f.replace("MEMORY.write", &[0, 1, 0], addr(z())),
                f.replace("MEMORY.load", &[0, 1, 1], z()),
            ]
        },
        Expect::File,
    ),
    (
        "same-sentence-disjoint-siblings",
        "memory.k",
        |f| {
            vec![
                f.replace("MEMORY.write", &[0, 1, 0], addr(z())),
                f.replace("MEMORY.write", &[0, 1, 1], z()),
            ]
        },
        Expect::File,
    ),
    (
        "original-reference-replacement",
        "memory.k",
        |f| vec![f.replace("MEMORY.load", &[0, 1], f.term("MEMORY.write", &[0, 1]))],
        Expect::File,
    ),
    (
        "stale-precondition-is-atomic",
        "memory.k",
        |f| {
            vec![
                Edit::ReplaceTerm {
                    at: f.at("MEMORY.write", &[0, 1, 0]),
                    expected: addr(s(z())),
                    replacement: addr(z()),
                },
                f.replace("MEMORY.load", &[0, 1, 1], z()),
            ]
        },
        Expect::Failure(PatchFailureKind::StalePrecondition),
    ),
    (
        "duplicate-target-rejected",
        "memory.k",
        |f| {
            vec![
                f.replace("MEMORY.write", &[0, 1, 0], addr(z())),
                f.replace("MEMORY.write", &[0, 1, 0], addr(s(z()))),
            ]
        },
        Expect::Failure(PatchFailureKind::DuplicateTarget),
    ),
    // The former row expected locally-ill-formed because its replacement
    // was also ill-sorted; both replacements here are well-sorted, which
    // isolates the overlap.
    (
        "ancestor-descendant-overlap",
        "memory.k",
        |f| {
            vec![
                f.replace(
                    "MEMORY.write",
                    &[0, 1],
                    Term::apply("stored", vec![addr(z()), z()]),
                ),
                f.replace("MEMORY.write", &[0, 1, 0], addr(z())),
            ]
        },
        Expect::Failure(PatchFailureKind::OverlappingEdit),
    ),
    (
        "delete-anchor-conflicts-with-insert",
        "memory.k",
        |f| {
            vec![
                Edit::DeleteSentence {
                    at: f.rule("MEMORY.load"),
                },
                f.insert(
                    InsertPosition::After(f.rule("MEMORY.load")),
                    0,
                    "MEMORY.free",
                ),
            ]
        },
        Expect::Failure(PatchFailureKind::OverlappingEdit),
    ),
    (
        "before-and-module-end-insertion",
        "memory.k",
        |f| {
            vec![
                f.insert(
                    InsertPosition::Before(f.rule("MEMORY.load")),
                    0,
                    "MEMORY.free",
                ),
                f.insert(
                    InsertPosition::ModuleEnd("MEMORY".to_owned()),
                    0,
                    "MEMORY.free",
                ),
            ]
        },
        Expect::File,
    ),
    (
        "after-lineage-and-module-start-insertion",
        "memory.k",
        |f| {
            vec![
                f.insert(
                    InsertPosition::After(f.rule("MEMORY.write")),
                    0,
                    "MEMORY.free",
                ),
                f.insert(
                    InsertPosition::ModuleStart("MEMORY".to_owned()),
                    0,
                    "MEMORY.free",
                ),
            ]
        },
        Expect::File,
    ),
    (
        "duplicate-insertion-ordinal",
        "memory.k",
        |f| {
            vec![
                f.insert(
                    InsertPosition::ModuleStart("MEMORY".to_owned()),
                    0,
                    "MEMORY.free",
                ),
                f.insert(
                    InsertPosition::ModuleStart("MEMORY".to_owned()),
                    0,
                    "MEMORY.load",
                ),
            ]
        },
        Expect::Failure(PatchFailureKind::DuplicateTarget),
    ),
    (
        "stale-module-insertion",
        "memory.k",
        |f| {
            vec![f.insert(
                InsertPosition::ModuleStart("NO-SUCH-MODULE".to_owned()),
                0,
                "MEMORY.free",
            )]
        },
        Expect::Failure(PatchFailureKind::StalePrecondition),
    ),
    (
        "add-attribute",
        "counter.k",
        |f| {
            vec![Edit::AddAttribute {
                at: f.rule("COUNTER.branch"),
                key: "owise".to_owned(),
                value: f.expected_attribute("COUNTER.branch", "owise"),
            }]
        },
        Expect::File,
    ),
    // Former row `add-existing-attribute`, as the M6 rows valued and bare.
    // M6, valued: the same value is still never overwritten.
    (
        "add-existing-valued-attribute",
        "counter.k",
        |f| {
            vec![Edit::AddAttribute {
                at: f.rule("COUNTER.fallback"),
                key: "priority".to_owned(),
                value: f.attribute("COUNTER.fallback", "priority"),
            }]
        },
        Expect::Failure(PatchFailureKind::StalePrecondition),
    ),
    // M6, bare.
    (
        "add-existing-bare-attribute",
        "counter.k",
        |f| {
            vec![Edit::AddAttribute {
                at: f.rule("COUNTER.fallback"),
                key: "priority".to_owned(),
                value: Value::String(String::new()),
            }]
        },
        Expect::Failure(PatchFailureKind::StalePrecondition),
    ),
    (
        "remove-attribute",
        "counter.k",
        |f| {
            vec![Edit::RemoveAttribute {
                at: f.rule("COUNTER.fallback"),
                key: "priority".to_owned(),
                expected: f.attribute("COUNTER.fallback", "priority"),
            }]
        },
        Expect::File,
    ),
    (
        "remove-missing-attribute",
        "counter.k",
        |f| {
            vec![Edit::RemoveAttribute {
                at: f.rule("COUNTER.branch"),
                key: "owise".to_owned(),
                expected: Value::String(String::new()),
            }]
        },
        Expect::Failure(PatchFailureKind::StalePrecondition),
    ),
    (
        "remove-stale-attribute",
        "counter.k",
        |f| {
            vec![Edit::RemoveAttribute {
                at: f.rule("COUNTER.fallback"),
                key: "priority".to_owned(),
                expected: Value::String("100".to_owned()),
            }]
        },
        Expect::Failure(PatchFailureKind::StalePrecondition),
    ),
    (
        "replace-attribute",
        "counter.k",
        |f| {
            vec![Edit::ReplaceAttribute {
                at: f.rule("COUNTER.fallback"),
                key: "priority".to_owned(),
                expected: f.attribute("COUNTER.fallback", "priority"),
                replacement: f.expected_attribute("COUNTER.fallback", "priority"),
            }]
        },
        Expect::File,
    ),
    (
        "replace-condition-second-family",
        "counter.k",
        |f| vec![f.replace("COUNTER.branch", &[1], boolean("false"))],
        Expect::File,
    ),
    (
        "explicit-no-change-rejection",
        "counter.k",
        |f| vec![f.replace("COUNTER.increment", &[1], boolean("true"))],
        Expect::Failure(PatchFailureKind::NoChange),
    ),
    (
        "malformed-typed-path-rejected",
        "counter.k",
        |f| {
            vec![Edit::ReplaceTerm {
                at: f.at("COUNTER.increment", &[0, 5]),
                expected: z(),
                replacement: s(z()),
            }]
        },
        Expect::Failure(PatchFailureKind::MalformedPath),
    ),
    (
        "malformed-typed-path-rejected",
        "counter.k",
        |f| {
            vec![Edit::ReplaceTerm {
                at: f.at("COUNTER.increment", &[3]),
                expected: boolean("true"),
                replacement: boolean("false"),
            }]
        },
        Expect::Failure(PatchFailureKind::MalformedPath),
    ),
    (
        "replace-sentence-second-family",
        "counter.k",
        |f| {
            let Sentence::Rule {
                body,
                ensures,
                attributes,
                ..
            } = f.sentence("COUNTER.branch")
            else {
                panic!("branch is a rule");
            };
            vec![Edit::ReplaceSentence {
                at: f.rule("COUNTER.branch"),
                replacement: Sentence::Rule {
                    body,
                    requires: boolean("false"),
                    ensures,
                    attributes,
                },
            }]
        },
        Expect::File,
    ),
    (
        "delete-sentence",
        "memory.k",
        |f| {
            vec![Edit::DeleteSentence {
                at: f.rule("MEMORY.load"),
            }]
        },
        Expect::File,
    ),
];

fn main_module(fixture: &str) -> &'static str {
    match fixture {
        "memory.k" => "MEMORY",
        "counter.k" => "COUNTER",
        other => panic!("unknown fixture {other}"),
    }
}

fn modules(fixture: &str) -> [&'static str; 2] {
    match fixture {
        "memory.k" => ["MEMORY-SYNTAX", "MEMORY"],
        "counter.k" => ["COUNTER-SYNTAX", "COUNTER"],
        other => panic!("unknown fixture {other}"),
    }
}

fn load_expected(name: &str, main_module: &str) -> Baseline {
    support::load_path(&Path::new(EXPECTED).join(format!("{name}.k")), main_module)
}

#[test]
fn testdata_definitions_load_and_compile_without_z3() {
    for (fixture, labels) in [
        (
            "counter.k",
            &["COUNTER.increment", "COUNTER.branch", "COUNTER.fallback"][..],
        ),
        (
            "memory.k",
            &["MEMORY.write", "MEMORY.load", "MEMORY.free"][..],
        ),
    ] {
        let baseline = support::load(fixture);
        for label in labels {
            support::rule(&baseline, label);
        }
        support::compile(baseline.loaded()).unwrap_or_else(|error| panic!("{fixture}: {error:?}"));
    }
}

#[test]
fn authored_sentences_exclude_builtin_catalog() {
    for fixture in ["counter.k"] {
        let baseline = support::load(fixture);
        let prefixes = CompileOptions::default().builtin_source_prefixes;
        for (at, sentence) in baseline.authored_sentences() {
            let source = sentence.attributes().source().expect("authored source");
            assert!(
                prefixes.iter().all(|prefix| !source.starts_with(prefix)),
                "{fixture}: {at:?} has builtin source {source}"
            );
        }
    }
}

#[test]
fn patch_rows_apply_or_fail_atomically() {
    let memory = support::load("memory.k");
    let counter = support::load("counter.k");
    let ids = ROWS.iter().map(|(id, ..)| *id).collect::<BTreeSet<_>>();
    // 22 former vector rows, with `add-existing-attribute` split into its
    // bare and valued M6 rows.
    assert_eq!(ids.len(), 23, "every former vector row is ported");
    for (id, fixture, edits, expect) in ROWS {
        let baseline = if *fixture == "memory.k" {
            &memory
        } else {
            &counter
        };
        let expected =
            matches!(expect, Expect::File).then(|| load_expected(id, main_module(fixture)));
        let edits = edits(&Fixture {
            baseline,
            expected: expected.as_ref(),
        });
        let patch = Patch::new(edits).expect("non-empty patch");
        match expect {
            Expect::File => {
                let mutant =
                    apply(baseline, &patch).unwrap_or_else(|failure| panic!("{id}: {failure}"));
                let expected = expected.as_ref().expect("loaded above");
                for module in modules(fixture) {
                    assert_same_rules_with_insertions(module, &mutant, expected.definition());
                }
                let repeated = apply(baseline, &patch).expect("repeat applies");
                assert_eq!(
                    mutant.definition(),
                    repeated.definition(),
                    "{id}: deterministic"
                );
            }
            Expect::Failure(kind) => {
                let failure = apply(baseline, &patch).expect_err(id);
                assert_eq!(failure.kind(), *kind, "{id}: {failure}");
            }
        }
    }
}

#[test]
fn permuted_edits_build_equal_patches_and_equal_mutants() {
    assert_eq!(Patch::new(Vec::new()), Err(PatchModelError::Empty));
    let memory = support::load("memory.k");
    let counter = support::load("counter.k");
    let mut permuted_rows = 0;
    for (id, fixture, edits, expect) in ROWS {
        let baseline = if *fixture == "memory.k" {
            &memory
        } else {
            &counter
        };
        let expected =
            matches!(expect, Expect::File).then(|| load_expected(id, main_module(fixture)));
        let edits = edits(&Fixture {
            baseline,
            expected: expected.as_ref(),
        });
        if edits.len() < 2 {
            continue;
        }
        permuted_rows += 1;
        let patch = Patch::new(edits.clone()).expect("patch");
        let permuted = Patch::new(edits.into_iter().rev().collect()).expect("patch");
        assert_eq!(patch, permuted, "{id}: canonical edit order");
        match (apply(baseline, &patch), apply(baseline, &permuted)) {
            (Ok(left), Ok(right)) => {
                assert_eq!(left.definition(), right.definition(), "{id}");
                assert_eq!(left.origins(), right.origins(), "{id}");
            }
            (Err(left), Err(right)) => assert_eq!(left, right, "{id}"),
            (left, right) => panic!("{id}: {:?} against {:?}", left.err(), right.err()),
        }
    }
    assert!(permuted_rows >= 8, "multi-edit rows exercise the ordering");
}

/// Relinks a raw definition edit, bypassing kink-patch, for compilation.
fn relink(baseline: &Baseline, definition: Definition) -> LoadedDefinition {
    LoadedDefinition {
        files: baseline.loaded().files.clone(),
        source_table: baseline.loaded().source_table.clone(),
        resolved: ResolvedDefinition::resolve(&definition).expect("resolves"),
        definition,
        diagnostics: baseline.loaded().diagnostics.clone(),
    }
}

fn raw_term_mut<'a>(sentence: &'a mut Sentence, path: &[u32]) -> &'a mut Term {
    let Sentence::Rule { body, requires, .. } = sentence else {
        panic!("a rule");
    };
    let mut term = match path[0] {
        0 => body,
        1 => requires,
        other => panic!("field {other}"),
    };
    for step in &path[1..] {
        while let Term::Annotated { term: inner, .. } = term {
            term = inner;
        }
        term = match term {
            Term::Rewrite { left, right } => {
                if *step == 0 {
                    left
                } else {
                    right
                }
            }
            Term::Apply { arguments, .. } => &mut arguments[*step as usize],
            other => panic!("{other} has no child {step}"),
        };
    }
    term
}

#[test]
fn local_sort_check_rejects_what_k_rust_compiles() {
    let counter = support::load("counter.k");
    let f = Fixture {
        baseline: &counter,
        expected: None,
    };
    // Signatures come from the baseline's productions (`ProductionCatalog`).
    // `ReplaceSentence` accepts only rule-like sentences, which declare no
    // productions, so an edit cannot change a signature. A relabelled
    // application is checked against its declared signature in the
    // `arity-drift` and `unknown-label` rows.
    // (row, path, replacement, whether k-rust itself compiles the raw edit)
    let rows: &[(&str, &[u32], Term, bool)] = &[
        (
            "bool-token-in-nat-position",
            &[0, 1, 0],
            boolean("true"),
            true,
        ),
        ("non-bool-requires", &[1], z(), true),
        (
            "arity-drift",
            &[0, 1],
            Term::apply("counter", vec![z()]),
            false,
        ),
        (
            "unknown-label",
            &[0, 1, 0],
            Term::apply("noSuch", vec![]),
            false,
        ),
        (
            "original-reference-sort-drift",
            &[0, 1, 0],
            f.term("COUNTER.increment", &[0, 0]),
            false,
        ),
        (
            "bare-variable",
            &[0, 1, 0, 0],
            Term::Variable {
                name: "N".to_owned(),
                sort: None,
            },
            false,
        ),
    ];
    for (row, path, replacement, pin_upstream_gap) in rows {
        let patch = Patch::new(vec![f.replace(
            "COUNTER.increment",
            path,
            replacement.clone(),
        )])
        .expect("patch");
        let failure = apply(&counter, &patch).expect_err(row);
        assert_eq!(
            failure.kind(),
            PatchFailureKind::LocallyIllFormed,
            "{row}: {failure}"
        );
        if *pin_upstream_gap {
            // Ledger request structured-term-sort-check: k-rust accepts the
            // same edit made without kink-patch. When this starts failing,
            // upstream checks sorts and this row can say so.
            let increment = f.rule("COUNTER.increment");
            let mut definition = counter.definition().clone();
            let module = definition
                .modules
                .iter_mut()
                .find(|module| module.name == increment.module)
                .expect("module");
            let sentence = sentence_mut(&mut module.local_sentences[increment.index as usize]);
            *raw_term_mut(sentence, path) = replacement.clone();
            support::compile(&relink(&counter, definition))
                .unwrap_or_else(|error| panic!("{row}: k-rust now rejects it: {error:?}"));
        }
    }
}

#[test]
fn path_through_semantic_cast_is_typed_at_the_cast_sort() {
    let counter = support::load("counter.k");
    let f = Fixture {
        baseline: &counter,
        expected: None,
    };
    // [0, 1, 0, 0, 0] is N in counter(s(#SemanticCastToNat(N)), L) on the right.
    let path = [0, 1, 0, 0, 0];
    assert_eq!(
        f.term("COUNTER.increment", &path),
        Term::Variable {
            name: "N".to_owned(),
            sort: None,
        }
    );
    let applied = apply(
        &counter,
        &Patch::new(vec![f.replace("COUNTER.increment", &path, z())]).expect("patch"),
    )
    .expect("a Nat below a Nat cast");
    let expected = load_expected("path-through-semantic-cast", "COUNTER");
    support::assert_same_authored_rules("COUNTER", applied.definition(), expected.definition());

    let failure = apply(
        &counter,
        &Patch::new(vec![f.replace("COUNTER.increment", &path, boolean("true"))]).expect("patch"),
    )
    .expect_err("a Bool below a Nat cast");
    assert_eq!(
        failure.kind(),
        PatchFailureKind::LocallyIllFormed,
        "{failure}"
    );
}

#[test]
fn replacement_sentence_keeps_variant_label_and_position_attributes() {
    let counter = support::load("counter.k");
    let f = Fixture {
        baseline: &counter,
        expected: None,
    };
    let Sentence::Rule {
        body,
        ensures,
        attributes,
        ..
    } = f.sentence("COUNTER.branch")
    else {
        panic!("branch is a rule");
    };
    let rule = |attributes| Sentence::Rule {
        body: body.clone(),
        requires: boolean("false"),
        ensures: ensures.clone(),
        attributes,
    };
    let with = |key: AttributeKey, value: Value| {
        let mut changed = attributes.clone();
        changed.set(key, value);
        rule(changed)
    };
    let rows = [
        (
            "kind-drift",
            Sentence::Claim {
                body: body.clone(),
                requires: boolean("false"),
                ensures: ensures.clone(),
                attributes: attributes.clone(),
            },
        ),
        (
            "location-drift",
            with(AttributeKey::Location, serde_json::json!([1, 1, 1, 2])),
        ),
        (
            "source-drift",
            with(
                AttributeKey::Source,
                Value::String("elsewhere.k".to_owned()),
            ),
        ),
        (
            "label-drift",
            with(
                AttributeKey::Label,
                Value::String("COUNTER.other".to_owned()),
            ),
        ),
    ];
    for (row, replacement) in rows {
        let patch = Patch::new(vec![Edit::ReplaceSentence {
            at: f.rule("COUNTER.branch"),
            replacement,
        }])
        .expect("patch");
        let failure = apply(&counter, &patch).expect_err(row);
        assert_eq!(
            failure.kind(),
            PatchFailureKind::LocallyIllFormed,
            "{row}: {failure}"
        );
    }
    apply(
        &counter,
        &Patch::new(vec![Edit::ReplaceSentence {
            at: f.rule("COUNTER.branch"),
            replacement: rule(attributes.clone()),
        }])
        .expect("patch"),
    )
    .expect("the unchanged attributes apply");
}

/// Observation resolves a written baseline position on each compiled side.
/// Edits cannot change its source position or the label checked against backend events.
#[test]
fn identity_and_position_attributes_are_never_edited() {
    let counter = support::load("counter.k");
    let f = Fixture {
        baseline: &counter,
        expected: None,
    };
    let branch = f.rule("COUNTER.branch");
    let label = AttributeKey::Label.as_str().to_owned();
    let mut labelled_clone = f.anonymous_clone("COUNTER.fallback");
    labelled_clone.attributes_mut().set(
        AttributeKey::Label,
        Value::String("COUNTER.clone".to_owned()),
    );
    let rows = [
        (
            "remove-label",
            Edit::RemoveAttribute {
                at: branch.clone(),
                key: label.clone(),
                expected: f.attribute("COUNTER.branch", &label),
            },
        ),
        (
            "replace-label",
            Edit::ReplaceAttribute {
                at: branch.clone(),
                key: label.clone(),
                expected: f.attribute("COUNTER.branch", &label),
                replacement: Value::String("COUNTER.other".to_owned()),
            },
        ),
        (
            "add-unique-id",
            Edit::AddAttribute {
                at: branch.clone(),
                key: AttributeKey::UniqueId.as_str().to_owned(),
                value: Value::String("0".to_owned()),
            },
        ),
        (
            "remove-location",
            Edit::RemoveAttribute {
                at: branch.clone(),
                key: AttributeKey::Location.as_str().to_owned(),
                expected: f.attribute("COUNTER.branch", AttributeKey::Location.as_str()),
            },
        ),
        (
            "insert-labelled-sentence",
            Edit::InsertSentence {
                position: InsertPosition::ModuleEnd("COUNTER".to_owned()),
                ordinal: 0,
                sentence: labelled_clone,
            },
        ),
    ];
    for (row, edit) in rows {
        let failure = apply(&counter, &Patch::new(vec![edit]).expect("patch")).expect_err(row);
        assert_eq!(
            failure.kind(),
            PatchFailureKind::LocallyIllFormed,
            "{row}: {failure}"
        );
    }
}

#[test]
fn inserted_sentence_carrying_a_location_is_ill_formed() {
    let baseline = support::load("counter.k");
    let f = Fixture {
        baseline: &baseline,
        expected: None,
    };
    let mut sentence = f.anonymous_clone("COUNTER.fallback");
    sentence.attributes_mut().set(
        AttributeKey::Location,
        f.attribute("COUNTER.fallback", AttributeKey::Location.as_str()),
    );
    assert!(sentence.attributes().has(AttributeKey::Location));
    let patch = Patch::new(vec![Edit::InsertSentence {
        position: InsertPosition::After(f.rule("COUNTER.fallback")),
        ordinal: 0,
        sentence,
    }])
    .expect("patch");
    let failure = apply(&baseline, &patch).expect_err("location cannot be copied to an insertion");
    assert_eq!(failure.kind(), PatchFailureKind::LocallyIllFormed);
}

#[test]
fn inserted_sentences_are_anchored_at_their_destination() {
    let counter = support::load("counter.k");
    let f = Fixture {
        baseline: &counter,
        expected: None,
    };
    let patch = Patch::new(vec![
        f.insert(
            InsertPosition::ModuleStart("COUNTER-SYNTAX".to_owned()),
            0,
            "COUNTER.increment",
        ),
        f.insert(
            InsertPosition::ModuleStart("COUNTER".to_owned()),
            0,
            "COUNTER.branch",
        ),
    ])
    .expect("patch");
    let mutant = apply(&counter, &patch).expect("equal slots in two modules");
    let syntax_insert = mutant
        .origin(&SentenceRef::new("COUNTER-SYNTAX", 0))
        .expect("origin");
    let semantics_insert = mutant
        .origin(&SentenceRef::new("COUNTER", 0))
        .expect("origin");
    let (
        SentenceOrigin::Inserted { edit: syntax_edit },
        SentenceOrigin::Inserted {
            edit: semantics_edit,
        },
    ) = (syntax_insert, semantics_insert)
    else {
        panic!("{syntax_insert:?} and {semantics_insert:?} are insertions");
    };
    assert_ne!(syntax_edit, semantics_edit);
    let mut output_count = 0;
    for module in &mutant.definition().modules {
        let shifted = u32::from(module.name == "COUNTER-SYNTAX" || module.name == "COUNTER");
        for index in 0..module.local_sentences.len() {
            let index = u32::try_from(index).expect("index");
            let output = SentenceRef::new(module.name.clone(), index);
            output_count += 1;
            if shifted == 1 && index == 0 {
                continue;
            }
            assert_eq!(
                mutant.origin(&output),
                Some(&SentenceOrigin::Baseline(SentenceRef::new(
                    module.name.clone(),
                    index - shifted
                ))),
                "{output:?}"
            );
        }
    }
    assert_eq!(mutant.origins().len(), output_count);
    let expected = load_expected("cross-module-insertion", "COUNTER");
    for module in ["COUNTER-SYNTAX", "COUNTER"] {
        assert_same_rules_with_insertions(module, &mutant, expected.definition());
    }
}

/// Cross-checks the term-path semantics against k-rust's own destination
/// anchors instead of against a restatement of them.
#[test]
fn term_paths_agree_with_k_rust_destination_anchors() {
    let counter = support::load("counter.k");
    let compiled = support::compile(counter.loaded()).expect("counter.k compiles");
    let definition = &compiled.execution_definition;
    let mut anchored = Vec::new();
    for module in &definition.modules {
        for sentence in &module.local_sentences {
            for field in 0..3 {
                if let Some(root) = field_root(sentence, field) {
                    collect_anchored(root, &mut anchored);
                }
            }
        }
    }
    let mut resolved = 0;
    for term in anchored {
        let record = term
            .metadata()
            .and_then(|metadata| metadata.origin.as_ref())
            .expect("collected with an origin");
        let Some(anchor) = &record.destination else {
            continue;
        };
        // Later passes shift sentence indices; only anchors whose sentence
        // still carries the anchored name are in this definition's
        // coordinates.
        let Some(target) = definition
            .modules
            .iter()
            .find(|module| module.name == anchor.module)
            .and_then(|module| module.local_sentences.get(anchor.sentence_index as usize))
        else {
            continue;
        };
        let name = target
            .attributes()
            .string(AttributeKey::UniqueId)
            .or_else(|| target.attributes().string(AttributeKey::Label));
        if name != Some(anchor.sentence.as_str()) {
            continue;
        }
        let at = term_at(
            definition,
            &anchor.module,
            anchor.sentence_index,
            &anchor.path,
        )
        .unwrap_or_else(|| panic!("{anchor:?} does not resolve"));
        let found = at
            .metadata()
            .and_then(|metadata| metadata.origin.as_ref())
            .unwrap_or_else(|| panic!("{anchor:?} resolves to {at} without an origin"));
        assert!(
            Arc::ptr_eq(found, record) || found == record,
            "{anchor:?} resolves to {at}, which carries another origin"
        );
        resolved += 1;
    }
    assert!(
        resolved > 0,
        "at least one anchor is in execution coordinates"
    );
}

fn field_root(sentence: &Sentence, field: u32) -> Option<&Term> {
    match (sentence, field) {
        (
            Sentence::Rule { body, .. }
            | Sentence::Claim { body, .. }
            | Sentence::Context { body, .. }
            | Sentence::ContextAlias { body, .. }
            | Sentence::Configuration { body, .. },
            0,
        ) => Some(body),
        (
            Sentence::Rule { requires, .. }
            | Sentence::Claim { requires, .. }
            | Sentence::Context { requires, .. }
            | Sentence::ContextAlias { requires, .. },
            1,
        ) => Some(requires),
        (Sentence::Configuration { ensures, .. }, 1)
        | (Sentence::Rule { ensures, .. } | Sentence::Claim { ensures, .. }, 2) => Some(ensures),
        _ => None,
    }
}

fn collect_anchored<'a>(term: &'a Term, out: &mut Vec<&'a Term>) {
    if term
        .metadata()
        .is_some_and(|metadata| metadata.origin.is_some())
    {
        out.push(term);
    }
    match term.unannotated() {
        Term::Rewrite { left, right } => {
            collect_anchored(left, out);
            collect_anchored(right, out);
        }
        Term::As { pattern, alias } => {
            collect_anchored(pattern, out);
            collect_anchored(alias, out);
        }
        Term::Apply { arguments, .. } | Term::Sequence(arguments) => {
            for argument in arguments {
                collect_anchored(argument, out);
            }
        }
        _ => {}
    }
}
