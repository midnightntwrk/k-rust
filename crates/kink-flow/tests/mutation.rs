//! The mutation list and its resolution into one pinned patch (flow F-04 deliverables 1-4).

use k_rust::definition::{AttributeKey, Sentence};
use kink_corpus::{LoadedSource, load_source, resolver::load_source_with_overlay};
use kink_flow::{
    FlowManifest,
    admit::corpus_source,
    mutation::{
        EditAction, EditSpec, InvalidMutation, InvalidReason, MUTATION_OPERATOR, Mutation,
        MutationList, ResolvedMutation, location_span, resolve, sentence_span,
    },
};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{
    COMPILED_KORE_DOMAIN, Edit, POSITION_KEYS, SentenceFingerprint, SentenceOrigin, SentenceRef,
    apply, canonical_json, payload_digest,
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

fn flow(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
}

/// A fresh directory for one test, under the target's temporary directory.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-mutation-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

/// A specification loaded as kink-flow loads it (no compile).
struct Spec {
    manifest: FlowManifest,
    loaded: LoadedSource,
}

impl Spec {
    fn at(manifest: &Path) -> Self {
        let manifest = FlowManifest::read(manifest).unwrap();
        let loaded = load_source(&corpus_source(&manifest)).unwrap();
        Self { manifest, loaded }
    }

    fn fixture(name: &str) -> Self {
        Self::at(&flow(name).join("FLOW.toml"))
    }

    fn resolve(&self, mutation: &Mutation) -> Result<ResolvedMutation, InvalidMutation> {
        resolve(&self.manifest, &self.loaded, mutation)
    }

    /// Resolve the one mutation of `edits` (the `[[mutation.edit]]` tables of a mutation
    /// with id `m`).
    fn resolve_edits(&self, edits: &str) -> Result<ResolvedMutation, InvalidMutation> {
        let list = MutationList::decode(&format!("[[mutation]]\nid = \"m\"\n{edits}")).unwrap();
        self.resolve(&list.mutations[0])
    }

    fn sentence(&self, at: &SentenceRef) -> &Sentence {
        self.loaded.baseline.sentence(at).unwrap()
    }
}

fn fixture_list(name: &str) -> MutationList {
    MutationList::read(&flow(name).join("MUTATIONS.toml")).unwrap()
}

fn at(module: &str, index: u32) -> SentenceRef {
    SentenceRef::new(module, index)
}

/// The kind and address of every edit of a patch.
fn shape(resolved: &ResolvedMutation) -> Vec<(&'static str, SentenceRef)> {
    resolved
        .patch
        .edits()
        .iter()
        .map(|edit| match edit {
            Edit::ReplaceSentence { at, .. } => ("replace", at.clone()),
            Edit::DeleteSentence { at } => ("delete", at.clone()),
            other => panic!("unexpected edit {other:?}"),
        })
        .collect()
}

#[track_caller]
fn expect_invalid(
    result: Result<ResolvedMutation, InvalidMutation>,
    edit: Option<usize>,
    reason: InvalidReason,
) -> InvalidMutation {
    match result {
        Ok(resolved) => panic!("expected {reason:?}, got a patch {:?}", shape(&resolved)),
        Err(invalid) => {
            assert_eq!((invalid.edit, invalid.reason), (edit, reason), "{invalid}");
            invalid
        }
    }
}

// ---------------------------------------------------------------------------------------
// Deliverable 1: decoding.

#[test]
fn decoding_rejects_unknown_keys_and_malformed_edits() {
    let edit = "[[mutation.edit]]\nrule = \"add\"\nfind = \"a\"\nreplace = \"b\"\n";
    let cases: Vec<(String, &str, &str)> = vec![
        ("colour = 1\n".into(), "colour", "unknown key"),
        (
            format!("[[mutation]]\nid = \"m\"\nwhy = \"x\"\n{edit}"),
            "mutation \"m\".why",
            "unknown key",
        ),
        (
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nrule = \"add\"\nfind = \"a\"\nreplace = \"b\"\nlabel = \"x\"\n"
                .into(),
            "mutation \"m\".edit[0].label",
            "unknown key",
        ),
        (
            format!("[[mutation]]\nid = \"m\"\n{edit}[[mutation]]\nid = \"m\"\n{edit}"),
            "mutation \"m\"",
            "duplicate mutation id",
        ),
        (
            format!("[[mutation]]\nid = \"\"\n{edit}"),
            "mutation[0].id",
            "must not be empty",
        ),
        (
            format!("[[mutation]]\nnote = \"x\"\n{edit}"),
            "mutation[0].id",
            "missing required key",
        ),
        (
            "[[mutation]]\nid = \"m\"\n".into(),
            "mutation \"m\"",
            "needs at least one [[mutation.edit]]",
        ),
        (
            "[[mutation]]\nid = \"m\"\nedit = []\n".into(),
            "mutation \"m\"",
            "needs at least one [[mutation.edit]]",
        ),
        (
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nrule = \"add\"\nfind = \"\"\nreplace = \"b\"\n"
                .into(),
            "mutation \"m\".edit[0].find",
            "must not be empty",
        ),
        (
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nrule = \"add\"\nfind = \"a\"\n".into(),
            "mutation \"m\".edit[0].replace",
            "find needs replace",
        ),
        (
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nrule = \"add\"\nreplace = \"a\"\n"
                .into(),
            "mutation \"m\".edit[0].find",
            "replace needs find",
        ),
        (
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nrule = \"add\"\n".into(),
            "mutation \"m\".edit[0]",
            "give find and replace, or delete = true",
        ),
        (
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nrule = \"add\"\ndelete = false\n".into(),
            "mutation \"m\".edit[0].delete",
            "must be true",
        ),
        (
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nrule = \"add\"\ndelete = true\nfind = \"a\"\nreplace = \"b\"\n"
                .into(),
            "mutation \"m\".edit[0]",
            "not both",
        ),
        (
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nfile = \"calc.k\"\ndelete = true\n"
                .into(),
            "mutation \"m\".edit[0]",
            "needs rule or line",
        ),
        (
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nline = 0\nfind = \"a\"\nreplace = \"b\"\n"
                .into(),
            "mutation \"m\".edit[0].line",
            "must be positive",
        ),
        (
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nline = \"3\"\nfind = \"a\"\nreplace = \"b\"\n"
                .into(),
            "mutation \"m\".edit[0].line",
            "expected an integer",
        ),
        (
            "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nrule = \"\"\nfind = \"a\"\nreplace = \"b\"\n"
                .into(),
            "mutation \"m\".edit[0].rule",
            "must not be empty",
        ),
        ("mutation = 3\n".into(), "mutation", "expected [[mutation]] tables"),
        ("[[mutation]\n".into(), "", "invalid TOML"),
    ];
    for (text, key, message) in cases {
        let error = MutationList::decode(&text).expect_err(&text);
        assert_eq!(error.key, key, "{text}");
        assert!(
            error.message.contains(message),
            "{text}: {} does not say {message:?}",
            error.message
        );
    }
}

#[test]
fn decoding_reads_every_field() {
    let list = fixture_list("calc");
    assert_eq!(
        list.mutations
            .iter()
            .map(|m| m.id.as_str())
            .collect::<Vec<_>>(),
        [
            "add-becomes-sub",
            "sub-off-by-one",
            "mul-becomes-add",
            "no-mul",
            "add-swaps-operands"
        ]
    );
    let swaps = &list.mutations[4];
    assert_eq!(
        swaps.note.as_deref(),
        Some("two edits in one rule: I1 +Int I2 becomes I2 +Int I1")
    );
    assert_eq!(
        swaps.edits,
        [
            EditSpec {
                file: None,
                rule: Some("add".into()),
                line: None,
                action: EditAction::Replace {
                    find: "=> I1".into(),
                    replace: "=> I2".into()
                },
            },
            EditSpec {
                file: Some("calc.k".into()),
                rule: None,
                line: Some(21),
                action: EditAction::Replace {
                    find: "+Int I2".into(),
                    replace: "+Int I1".into()
                },
            },
        ]
    );
    assert_eq!(list.mutations[3].edits[0].action, EditAction::Delete);
    assert_eq!(MutationList::decode("").unwrap(), MutationList::default());
    // An empty replacement is a valid edit (it removes the found text).
    let list = MutationList::decode(
        "[[mutation]]\nid = \"m\"\n[[mutation.edit]]\nline = 3\nfind = \"a\"\nreplace = \"\"\n",
    )
    .unwrap();
    assert_eq!(
        list.mutations[0].edits[0].action,
        EditAction::Replace {
            find: "a".into(),
            replace: String::new()
        }
    );
}

// ---------------------------------------------------------------------------------------
// Deliverable 2: resolution of valid mutations.

fn fixture_mutation(spec: &Spec, list: &MutationList, id: &str) -> ResolvedMutation {
    let mutation = list.mutations.iter().find(|m| m.id == id).unwrap();
    spec.resolve(mutation)
        .unwrap_or_else(|e| panic!("{id}: {e}"))
}

#[test]
fn a_labelled_rule_edit_replaces_exactly_that_rule() {
    let spec = Spec::fixture("calc");
    let resolved = fixture_mutation(&spec, &fixture_list("calc"), "add-becomes-sub");
    assert_eq!(resolved.id, "add-becomes-sub");
    assert_eq!(shape(&resolved), [("replace", at("CALC", 1))]);
    let rule = &resolved.rules[0];
    assert_eq!(
        (
            rule.at.clone(),
            rule.edits.clone(),
            rule.file.as_str(),
            rule.label.as_deref(),
            rule.start_line,
            rule.end_line
        ),
        (at("CALC", 1), vec![0], "calc.k", Some("CALC.add"), 21, 21)
    );
    assert_eq!(rule.before, "rule [add]: I1:Int + I2:Int => I1 +Int I2");
    assert_eq!(
        rule.after.as_deref(),
        Some("rule [add]: I1:Int + I2:Int => I1 -Int I2")
    );
    assert_eq!(resolved.digest, resolved.patch.digest().unwrap());
    assert!(resolved.patch.is_pinned());
    assert_eq!(
        resolved.patch.pins().keys().cloned().collect::<Vec<_>>(),
        [at("CALC", 1)]
    );
    assert_eq!(
        resolved.patch.pins()[&at("CALC", 1)],
        SentenceFingerprint::of(spec.sentence(&at("CALC", 1))).unwrap()
    );
    assert_eq!(
        resolved.edited_sources.keys().collect::<Vec<_>>(),
        ["calc.k"]
    );
}

#[test]
fn an_unlabelled_rule_is_addressed_by_line() {
    let spec = Spec::fixture("calc");
    let resolved = fixture_mutation(&spec, &fixture_list("calc"), "sub-off-by-one");
    assert_eq!(shape(&resolved), [("replace", at("CALC", 3))]);
    let rule = &resolved.rules[0];
    assert_eq!(rule.label, None);
    assert_eq!(rule.before, "rule I1:Int - I2:Int => I1 -Int I2");
    assert_eq!(
        rule.after.as_deref(),
        Some("rule I1:Int - I2:Int => I1 -Int I2 -Int 1")
    );
}

#[test]
fn a_unique_find_addresses_its_rule_without_rule_or_line() {
    let spec = Spec::fixture("calc");
    let resolved = fixture_mutation(&spec, &fixture_list("calc"), "mul-becomes-add");
    assert_eq!(shape(&resolved), [("replace", at("CALC", 2))]);
    assert_eq!(resolved.rules[0].label.as_deref(), Some("CALC.mul"));
}

#[test]
fn a_delete_removes_the_rule() {
    let spec = Spec::fixture("calc");
    let resolved = fixture_mutation(&spec, &fixture_list("calc"), "no-mul");
    assert_eq!(shape(&resolved), [("delete", at("CALC", 2))]);
    assert_eq!(resolved.rules[0].after, None);
    assert_eq!(
        resolved.rules[0].before,
        "rule [mul]: I1:Int * I2:Int => I1 *Int I2"
    );
    // The rule's text is removed and its line stays, so no other sentence moves.
    let text = fs::read_to_string(flow("calc").join("calc.k")).unwrap();
    assert_eq!(
        resolved.edited_sources["calc.k"],
        text.replace("rule [mul]: I1:Int * I2:Int => I1 *Int I2", "")
    );
    let register = Spec::fixture("register");
    let resolved = fixture_mutation(&register, &fixture_list("register"), "no-seq");
    assert_eq!(shape(&resolved), [("delete", at("REGISTER", 1))]);
}

#[test]
fn two_edits_in_one_rule_are_one_replace_sentence() {
    let spec = Spec::fixture("calc");
    let resolved = fixture_mutation(&spec, &fixture_list("calc"), "add-swaps-operands");
    assert_eq!(shape(&resolved), [("replace", at("CALC", 1))]);
    assert_eq!(resolved.rules[0].edits, [0, 1]);
    assert_eq!(
        resolved.rules[0].after.as_deref(),
        Some("rule [add]: I1:Int + I2:Int => I2 +Int I1")
    );
}

#[test]
fn a_correlated_mutation_is_one_patch_applied_all_or_none() {
    let spec = Spec::fixture("register");
    let list = fixture_list("register");
    let both = fixture_mutation(&spec, &list, "put-and-get-offset");
    assert_eq!(
        shape(&both),
        [
            ("replace", at("REGISTER", 2)),
            ("replace", at("REGISTER", 3))
        ]
    );
    assert_eq!(
        both.rules
            .iter()
            .map(|r| (r.label.as_deref(), r.after.as_deref()))
            .collect::<Vec<_>>(),
        [
            (
                Some("REGISTER.put"),
                Some("rule [put]: <k> put(I:Int) => .K ... </k> <reg> _ => I +Int 1 </reg>")
            ),
            (
                Some("REGISTER.get"),
                Some("rule [get]: <k> get => I -Int 1 ... </k> <reg> I </reg>")
            ),
        ]
    );
    // The two edits are one candidate of one generation: its patch is the whole mutation.
    let generation = both.generation(&spec.loaded.baseline).unwrap();
    assert_eq!(generation.candidates().len(), 1);
    assert_eq!(generation.candidates()[0].operator, MUTATION_OPERATOR);
    assert_eq!(generation.candidates()[0].patch, both.patch);
    assert!(generation.derived_from(&spec.loaded.baseline));
    assert!(!generation.scored());
    // Each single edit is its own, different patch.
    let put = fixture_mutation(&spec, &list, "put-offset");
    let get = fixture_mutation(&spec, &list, "get-offset");
    assert_eq!(shape(&put), [("replace", at("REGISTER", 2))]);
    assert_eq!(shape(&get), [("replace", at("REGISTER", 3))]);
    assert_eq!(
        BTreeSet::from([both.digest, put.digest, get.digest]).len(),
        3
    );

    // A second edit that fails makes the whole mutation invalid: no patch at all.
    let put_edit = "[[mutation.edit]]\nrule = \"put\"\nfind = \"_ => I </reg>\"\nreplace = \"_ => I +Int 1 </reg>\"\n";
    expect_invalid(
        spec.resolve_edits(&format!(
            "{put_edit}[[mutation.edit]]\nrule = \"get\"\nfind = \"get => J\"\nreplace = \"get => J\"\n"
        )),
        Some(1),
        InvalidReason::FindNotFound,
    );
    expect_invalid(
        spec.resolve_edits(&format!(
            "{put_edit}[[mutation.edit]]\nrule = \"get\"\nfind = \"get => I ...\"\nreplace = \"get => I +Int ...\"\n"
        )),
        None,
        InvalidReason::EditedLoadFailed,
    );
    expect_invalid(
        spec.resolve_edits(&format!(
            "{put_edit}[[mutation.edit]]\nrule = \"get\"\nfind = \"get => I ...\"\nreplace = \"get  =>  I ...\"\n"
        )),
        Some(1),
        InvalidReason::NoChange,
    );
    expect_invalid(
        spec.resolve_edits(&format!(
            "{put_edit}[[mutation.edit]]\nrule = \"get\"\nfind = \"[get]\"\nreplace = \"[read]\"\n"
        )),
        Some(1),
        InvalidReason::LabelChanged,
    );
}

#[test]
fn differently_formatted_finds_of_the_same_rule_give_one_patch_digest() {
    let spec = Spec::fixture("calc");
    let reference = fixture_mutation(&spec, &fixture_list("calc"), "add-becomes-sub");
    for edits in [
        "[[mutation.edit]]\nrule = \"add\"\nfind = \"+Int I2\"\nreplace = \"-Int I2\"\n",
        "[[mutation.edit]]\nline = 21\nfind = \"I1 +Int I2\"\nreplace = \"I1  -Int\\n    I2\"\n",
        "[[mutation.edit]]\nrule = \"CALC.add\"\nfind = \"=> I1 +Int I2\"\nreplace = \"=>   I1 -Int I2   \"\n",
        "[[mutation.edit]]\nfind = \"I1 +Int I2\"\nreplace = \"(I1 -Int I2)\"\n",
    ] {
        let resolved = spec
            .resolve_edits(edits)
            .unwrap_or_else(|e| panic!("{edits}: {e}"));
        assert_eq!(resolved.patch, reference.patch, "{edits}");
        assert_eq!(resolved.digest, reference.digest, "{edits}");
    }
    let other = fixture_mutation(&spec, &fixture_list("calc"), "mul-becomes-add");
    assert_ne!(other.digest, reference.digest);
}

/// Every mutation of the calc and register fixture lists, resolved, with its spec.
fn fixture_mutations() -> Vec<(Spec, Vec<ResolvedMutation>)> {
    ["calc", "register"]
        .into_iter()
        .map(|name| {
            let spec = Spec::fixture(name);
            let resolved = fixture_list(name)
                .mutations
                .iter()
                .map(|m| spec.resolve(m).unwrap_or_else(|e| panic!("{}: {e}", m.id)))
                .collect();
            (spec, resolved)
        })
        .collect()
}

#[test]
fn every_valid_fixture_mutation_changes_exactly_its_addressed_rules() {
    for (spec, mutations) in fixture_mutations() {
        let baseline = &spec.loaded.baseline;
        for resolved in mutations {
            let id = &resolved.id;
            let edited =
                load_source_with_overlay(&corpus_source(&spec.manifest), &resolved.edited_sources)
                    .unwrap();
            let replaced = shape(&resolved)
                .into_iter()
                .filter(|(kind, _)| *kind == "replace")
                .map(|(_, at)| at)
                .collect::<BTreeSet<_>>();
            let deleted = shape(&resolved)
                .into_iter()
                .filter(|(kind, _)| *kind == "delete")
                .map(|(_, at)| at)
                .collect::<BTreeSet<_>>();
            let mutant = apply(baseline, &resolved.patch).unwrap();
            let definition = mutant.definition();
            let mut seen = BTreeSet::new();
            let mut outputs = 0;
            for module in &definition.modules {
                for (index, sentence) in module.local_sentences.iter().enumerate() {
                    outputs += 1;
                    let output = SentenceRef::new(module.name.clone(), index as u32);
                    let Some(SentenceOrigin::Baseline(origin)) = mutant.origin(&output) else {
                        panic!("{id}: {output:?} has no baseline origin");
                    };
                    seen.insert(origin.clone());
                    let original = baseline.sentence(origin).unwrap();
                    if !replaced.contains(origin) {
                        // Untouched: the very baseline sentence, positions included.
                        assert!(**sentence == *original, "{id}: {origin:?} changed");
                        assert_eq!(
                            SentenceFingerprint::of(sentence).ok(),
                            SentenceFingerprint::of(original).ok(),
                            "{id}: {origin:?}"
                        );
                        continue;
                    }
                    // Replaced: the edited load's rule at that place, with the baseline's
                    // position and provenance attributes and nothing else of the baseline.
                    let edited_index = origin.index
                        - deleted
                            .iter()
                            .filter(|d| d.module == origin.module && d.index < origin.index)
                            .count() as u32;
                    let edited_sentence = edited
                        .baseline
                        .sentence(&SentenceRef::new(origin.module.clone(), edited_index))
                        .unwrap();
                    assert_eq!(
                        SentenceFingerprint::of(sentence).unwrap(),
                        SentenceFingerprint::of(edited_sentence).unwrap(),
                        "{id}: {origin:?} is not the edited rule"
                    );
                    assert_ne!(
                        SentenceFingerprint::of(sentence).unwrap(),
                        SentenceFingerprint::of(original).unwrap(),
                        "{id}: {origin:?} is unchanged"
                    );
                    let entries = sentence.attributes().entries();
                    let original_entries = original.attributes().entries();
                    let edited_entries = edited_sentence.attributes().entries();
                    for (key, value) in entries.iter().chain(&original_entries) {
                        let position = POSITION_KEYS.iter().any(|k| k.as_str() == key);
                        let expected = if position {
                            original_entries.get(key)
                        } else {
                            edited_entries.get(key)
                        };
                        assert_eq!(entries.get(key), expected, "{id}: {origin:?} {key} {value}");
                    }
                    for key in edited_entries.keys() {
                        let position = POSITION_KEYS.iter().any(|k| k.as_str() == key);
                        assert!(position || entries.contains_key(key), "{id}: {key}");
                    }
                    assert_eq!(
                        sentence.attributes().value(AttributeKey::Label),
                        original.attributes().value(AttributeKey::Label)
                    );
                }
            }
            let baseline_count = baseline
                .definition()
                .modules
                .iter()
                .map(|m| m.local_sentences.len())
                .sum::<usize>();
            assert_eq!(outputs, baseline_count - deleted.len(), "{id}");
            for d in &deleted {
                assert!(!seen.contains(d), "{id}: {d:?} still present");
            }
            assert_eq!(
                resolved.patch.written_sentences(),
                replaced.union(&deleted).cloned().collect::<Vec<_>>(),
                "{id}"
            );
        }
    }
}

/// Every `"Location(a,b,c,d)"` attribute value of a KORE text, as `"Location()"`.
fn without_locations(text: &str) -> String {
    let mut normalised = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("\"Location(") {
        normalised.push_str(&rest[..start]);
        normalised.push_str("\"Location()\"");
        let value = &rest[start + "\"Location(".len()..];
        rest = &value[value.find(")\"").expect("a Location value ends") + 2..];
    }
    normalised.push_str(rest);
    normalised
}

/// The `"Location(...)"` attribute values of a KORE text, in order.
fn locations(text: &str) -> Vec<&str> {
    text.match_indices("\"Location(")
        .map(|(start, _)| {
            let value = &text[start..];
            &value[..value.find(")\"").expect("a Location value ends") + 2]
        })
        .collect()
}

/// The compiled KORE identity of `ValidatedDefinition::kore_sha256`, computed after applying
/// `normalise` to the three KORE texts (the rewrite order is taken as it is).
fn kore_digest(compiled: &ValidatedDefinition, normalise: fn(&str) -> String) -> String {
    let artifacts = compiled.artifacts();
    let value = json!({
        "definition": normalise(&artifacts.definition_kore),
        "macros": normalise(&artifacts.macros_kore),
        "rewrite_order": artifacts.execution_rewrite_order,
        "syntax": normalise(&artifacts.syntax_definition_kore),
    });
    payload_digest(COMPILED_KORE_DOMAIN, canonical_json(&value).as_bytes()).to_string()
}

/// README 5.5 as restated after F-04 review 1 (M2): compiling the patched baseline gives the
/// compiled KORE of the edited sources after normalising every Location attribute, with an
/// equal rewrite order. The patch keeps each replaced rule's baseline position attributes
/// (kink-patch requires it of a ReplaceSentence), so a replacement that changes a rule's
/// extent changes its Location in the edited sources only, and one that changes the line
/// count also moves the Location of every later sentence of the file (the review's probe,
/// pinned below). Location is provenance only in the k-rust backend (RuleOrigin) and enters
/// no UNIQUE_ID. Checked over the calc and register fixture lists, the probe, and the valid
/// mutations of the Markdown fixture, whose edited sources are loaded through the Markdown
/// envelope (`ResolvedMutation::overlay`).
#[test]
fn the_patched_baseline_compiles_to_the_kore_of_the_edited_sources() {
    let mut cases = fixture_mutations();
    let calc = Spec::fixture("calc");
    let line_break = calc
        .resolve_edits(
            "[[mutation.edit]]\nrule = \"add\"\nfind = \"I1 +Int I2\"\nreplace = \"I1 -Int\\n    I2\"\n",
        )
        .unwrap();
    cases.push((calc, vec![line_break]));
    let markdown = Spec::fixture("markdown");
    let valid = fixture_list("markdown")
        .mutations
        .iter()
        .filter_map(|m| markdown.resolve(m).ok())
        .collect::<Vec<_>>();
    assert_eq!(valid.len(), 6);
    cases.push((markdown, valid));
    let identity: fn(&str) -> String = str::to_owned;
    let mut checked = Vec::new();
    for (spec, mutations) in cases {
        let validator = NativeValidator::bind(spec.loaded.baseline.clone(), Default::default());
        for resolved in mutations {
            let id = resolved.id.as_str();
            let patched = validator
                .validate(&resolved.patch)
                .unwrap_or_else(|e| panic!("{id}: the patched baseline does not compile: {e}"));
            let edited =
                load_source_with_overlay(&corpus_source(&spec.manifest), resolved.overlay())
                    .unwrap_or_else(|e| panic!("{id}: the edited sources do not load: {e}"));
            let direct = NativeValidator::bind(edited.baseline.clone(), Default::default())
                .compile_baseline()
                .unwrap_or_else(|e| panic!("{id}: the edited sources do not compile: {e}"));
            // The digest formula is kink-patch's compiled KORE identity.
            assert_eq!(
                kore_digest(&patched, identity),
                patched.kore_sha256().to_string()
            );
            assert_eq!(
                patched.artifacts().execution_rewrite_order,
                direct.artifacts().execution_rewrite_order,
                "{id}: the rewrite orders differ"
            );
            assert_eq!(
                kore_digest(&patched, without_locations),
                kore_digest(&direct, without_locations),
                "{id}: the compiles differ beyond Location attributes"
            );
            let (from, to) = (
                locations(&patched.artifacts().definition_kore),
                locations(&direct.artifacts().definition_kore),
            );
            assert_eq!(from.len(), to.len(), "{id}");
            let moved = from.iter().zip(&to).filter(|(a, b)| a != b).count();
            checked.push((
                format!("{}/{id}", spec.manifest.spec.entry),
                patched.kore_sha256() == direct.kore_sha256(),
                moved,
            ));
        }
    }
    let row = |key: &str| {
        checked
            .iter()
            .find(|(k, _, _)| k == key)
            .unwrap_or_else(|| panic!("{key} not checked: {checked:?}"))
    };
    // The probe: the replaced rule and the two rules below it moved one line down.
    assert!(!row("calc.k/m").1);
    assert!(row("calc.k/m").2 > 1, "{:?}", row("calc.k/m"));
    // A delete keeps the rule's line, and an extent-preserving edit changes no Location.
    assert!(row("calc.k/no-mul").1);
    assert!(row("calc.k/add-becomes-sub").1);
    assert!(row("spec.md/inc-adds-two").1);
    assert_eq!(checked.len(), 9 + 1 + 6);
}

// ---------------------------------------------------------------------------------------
// Deliverable 2: invalid mutations.

/// Every reason of [`InvalidReason`] a test below produces; `PatchRejected` and
/// `NoUsableSpan` are defensive (the earlier checks and the k-rust loader make them
/// unreachable on authored rules) and are listed separately.
const DEFENSIVE: [InvalidReason; 2] = [InvalidReason::PatchRejected, InvalidReason::NoUsableSpan];

#[test]
fn every_invalid_mutation_reason_on_calc() {
    use InvalidReason::*;
    let spec = Spec::fixture("calc");
    let add = "rule = \"add\"\n";
    let cases: Vec<(String, Option<usize>, InvalidReason)> = vec![
        (
            "[[mutation.edit]]\nrule = \"div\"\nfind = \"a\"\nreplace = \"b\"\n".into(),
            Some(0),
            UnknownLabel,
        ),
        (
            "[[mutation.edit]]\nline = 14\nfind = \"a\"\nreplace = \"b\"\n".into(),
            Some(0),
            LineOutsideRules,
        ),
        (
            "[[mutation.edit]]\nline = 2000\ndelete = true\n".into(),
            Some(0),
            LineOutsideRules,
        ),
        (
            "[[mutation.edit]]\nline = 9\nfind = \"*\"\nreplace = \"x\"\n".into(),
            Some(0),
            NonRuleSentence,
        ),
        (
            "[[mutation.edit]]\nline = 18\ndelete = true\n".into(),
            Some(0),
            NonRuleSentence,
        ),
        (
            "[[mutation.edit]]\nfind = \"[bracket]\"\nreplace = \"[strict]\"\n".into(),
            Some(0),
            NonRuleSentence,
        ),
        (
            format!("[[mutation.edit]]\n{add}line = 22\nfind = \"I1\"\nreplace = \"I2\"\n"),
            Some(0),
            AddressMismatch,
        ),
        (
            format!("[[mutation.edit]]\n{add}find = \"/Int\"\nreplace = \"*Int\"\n"),
            Some(0),
            FindNotFound,
        ),
        (
            "[[mutation.edit]]\nfind = \"I1 /Int I2\"\nreplace = \"I1\"\n".into(),
            Some(0),
            FindNotFound,
        ),
        (
            format!("[[mutation.edit]]\n{add}find = \"I1\"\nreplace = \"I2\"\n"),
            Some(0),
            FindAmbiguous,
        ),
        (
            "[[mutation.edit]]\nfind = \"Int\"\nreplace = \"Bool\"\n".into(),
            Some(0),
            FindAmbiguous,
        ),
        (
            format!("[[mutation.edit]]\n{add}find = \"I1 *Int I2\"\nreplace = \"I1\"\n"),
            Some(0),
            EditOutsideRule,
        ),
        (
            "[[mutation.edit]]\nfind = \"tiny expression language\"\nreplace = \"x\"\n".into(),
            Some(0),
            EditOutsideRule,
        ),
        (
            format!(
                "[[mutation.edit]]\n{add}find = \"I1 +Int\"\nreplace = \"I2 +Int\"\n\
                 [[mutation.edit]]\n{add}find = \"+Int I2\"\nreplace = \"-Int I2\"\n"
            ),
            Some(1),
            OverlappingEdits,
        ),
        (
            "[[mutation.edit]]\nrule = \"mul\"\nfind = \"*Int\"\nreplace = \"+Int\"\n\
             [[mutation.edit]]\nrule = \"mul\"\ndelete = true\n"
                .into(),
            Some(1),
            OverlappingEdits,
        ),
        (
            format!("[[mutation.edit]]\n{add}find = \"I1 +Int I2\"\nreplace = \"I1 +Int\"\n"),
            Some(0),
            EditedLoadFailed,
        ),
        (
            // Ill-sorted: the edited rule does not parse (k-rust parses rules with sorts).
            format!("[[mutation.edit]]\n{add}find = \"I1 +Int I2\"\nreplace = \"I1 +Int true\"\n"),
            Some(0),
            EditedLoadFailed,
        ),
        (
            // The replacement parses as two sentences.
            format!(
                "[[mutation.edit]]\n{add}find = \"I1 +Int I2\"\n\
                 replace = \"I1 +Int I2\\n  rule [add2]: 0 + 0 => 0\"\n"
            ),
            Some(0),
            StructureChanged,
        ),
        (
            // The replacement removes the rule (a delete must say delete = true).
            format!(
                "[[mutation.edit]]\n{add}find = \"rule [add]: I1:Int + I2:Int => I1 +Int I2\"\n\
                 replace = \"\"\n"
            ),
            Some(0),
            StructureChanged,
        ),
        (
            // The rule becomes a production in its place: same count, another kind.
            format!(
                "[[mutation.edit]]\n{add}find = \"rule [add]: I1:Int + I2:Int => I1 +Int I2\"\n\
                 replace = \"syntax Exp ::= \\\"zz\\\"\"\n"
            ),
            Some(0),
            StructureChanged,
        ),
        (
            format!("[[mutation.edit]]\n{add}find = \"[add]\"\nreplace = \"[plus]\"\n"),
            Some(0),
            LabelChanged,
        ),
        (
            format!("[[mutation.edit]]\n{add}find = \"[add]: \"\nreplace = \"\"\n"),
            Some(0),
            LabelChanged,
        ),
        (
            format!("[[mutation.edit]]\n{add}find = \"I1 +Int I2\"\nreplace = \"I1  +Int  I2\"\n"),
            Some(0),
            NoChange,
        ),
        (
            format!("[[mutation.edit]]\n{add}find = \"I1 +Int I2\"\nreplace = \"I1 +Int I2\"\n"),
            Some(0),
            NoChange,
        ),
        (
            "[[mutation.edit]]\nfile = \"nope.k\"\nline = 21\ndelete = true\n".into(),
            Some(0),
            UnknownFile,
        ),
        (
            "[[mutation.edit]]\nfile = \"../calc/calc.k\"\nline = 21\ndelete = true\n".into(),
            Some(0),
            UnknownFile,
        ),
    ];
    for (edits, edit, reason) in cases {
        let invalid = expect_invalid(spec.resolve_edits(&edits), edit, reason);
        assert!(!invalid.detail.is_empty(), "{edits}");
    }
    // The display names the edit and the reason.
    let invalid = spec
        .resolve_edits("[[mutation.edit]]\nrule = \"div\"\nfind = \"a\"\nreplace = \"b\"\n")
        .unwrap_err();
    assert_eq!(
        invalid.to_string(),
        "edit[0]: unknown-label: no rule is labelled \"div\""
    );
    // A file named another way that normalises to the source is the source.
    let ok = spec
        .resolve_edits(
            "[[mutation.edit]]\nfile = \"./sub/../calc.k\"\nline = 21\nfind = \"+Int\"\nreplace = \"-Int\"\n",
        )
        .unwrap();
    assert_eq!(shape(&ok), [("replace", at("CALC", 1))]);
}

const LIB_K: &str = r#"module LIB-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int | "a" | "b" | "c" | "d"
endmodule

module LIB
  imports LIB-SYNTAX
  rule [r]: a => 1
endmodule
"#;

const MAIN_K: &str = r#"requires "lib.k"

module MAIN
  imports LIB
  imports INT
  configuration <k> $PGM:Exp </k>

  rule [r]: b => 2
  rule [c]: c => 3  rule [d]: d => 4
endmodule
"#;

const MULTI_FLOW: &str = r#"[spec]
entry = "main.k"
main_module = "MAIN"
syntax_module = "LIB-SYNTAX"
"#;

/// A two-file specification: a label used in two modules and two rules on one line.
fn multi(test: &str) -> Spec {
    let dir = scratch(test);
    write(&dir.join("lib.k"), LIB_K);
    write(&dir.join("main.k"), MAIN_K);
    write(&dir.join("FLOW.toml"), MULTI_FLOW);
    Spec::at(&dir.join("FLOW.toml"))
}

#[test]
fn invalid_mutation_reasons_on_a_two_file_spec() {
    use InvalidReason::*;
    let spec = multi("two-files");
    assert_eq!(
        spec.loaded
            .files
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>(),
        ["lib.k", "main.k"]
    );
    let cases: Vec<(&str, Option<usize>, InvalidReason)> = vec![
        (
            "[[mutation.edit]]\nrule = \"r\"\nfind = \"=>\"\nreplace = \"=>\"\n",
            Some(0),
            AmbiguousLabel,
        ),
        (
            "[[mutation.edit]]\nline = 8\nfind = \"2\"\nreplace = \"3\"\n",
            Some(0),
            FileRequired,
        ),
        (
            "[[mutation.edit]]\nfind = \"=> 2\"\nreplace = \"=> 3\"\n",
            Some(0),
            FileRequired,
        ),
        (
            "[[mutation.edit]]\nfile = \"main.k\"\nline = 9\nfind = \"3\"\nreplace = \"5\"\n",
            Some(0),
            LineAmbiguous,
        ),
        (
            "[[mutation.edit]]\nfile = \"lib.k\"\nrule = \"MAIN.r\"\nfind = \"2\"\nreplace = \"3\"\n",
            Some(0),
            AddressMismatch,
        ),
        (
            // A rule on a shared line is addressed by its label; its find stays inside it.
            "[[mutation.edit]]\nrule = \"c\"\nfind = \"=> 4\"\nreplace = \"=> 5\"\n",
            Some(0),
            EditOutsideRule,
        ),
        (
            // The edit text stays inside rule c, but it comments out rule d: one sentence
            // fewer.
            "[[mutation.edit]]\nrule = \"c\"\nfind = \"=> 3\"\nreplace = \"=> 3 //\"\n",
            Some(0),
            StructureChanged,
        ),
        (
            // The same, writing a new rule d in place of the commented one: the sentence
            // count holds, but a sentence no edit addresses changed.
            "[[mutation.edit]]\nrule = \"c\"\nfind = \"=> 3\"\nreplace = \"=> 3 rule [d]: d => 5 //\"\n",
            Some(0),
            StructureChanged,
        ),
        (
            // The same with another label in place of rule d.
            "[[mutation.edit]]\nrule = \"c\"\nfind = \"=> 3\"\nreplace = \"=> 3 rule [e]: d => 4 //\"\n",
            Some(0),
            StructureChanged,
        ),
    ];
    for (edits, edit, reason) in cases {
        expect_invalid(spec.resolve_edits(edits), edit, reason);
    }
    // A correlated mutation across the two files is one patch.
    let resolved = spec
        .resolve_edits(
            "[[mutation.edit]]\nrule = \"LIB.r\"\nfind = \"=> 1\"\nreplace = \"=> 7\"\n\
             [[mutation.edit]]\nfile = \"main.k\"\nfind = \"=> 3\"\nreplace = \"=> 8\"\n\
             [[mutation.edit]]\nrule = \"MAIN.r\"\ndelete = true\n",
        )
        .unwrap();
    assert_eq!(
        shape(&resolved),
        [
            ("replace", at("LIB", 0)),
            ("delete", at("MAIN", 0)),
            ("replace", at("MAIN", 1)),
        ]
    );
    assert_eq!(
        resolved.edited_sources.keys().collect::<Vec<_>>(),
        ["lib.k", "main.k"]
    );
    let index = |label: &str| {
        spec.loaded
            .baseline
            .authored_sentences()
            .find(|(_, s)| s.attributes().string(AttributeKey::Label) == Some(label))
            .unwrap()
            .0
    };
    assert_eq!(
        (
            index("LIB.r"),
            index("MAIN.r"),
            index("MAIN.c"),
            index("MAIN.d")
        ),
        (at("LIB", 0), at("MAIN", 0), at("MAIN", 1), at("MAIN", 2))
    );
    assert_eq!(resolved.rules[2].after.as_deref(), Some("rule [c]: c => 8"));
}

#[test]
fn a_source_changed_since_the_load_is_never_edited() {
    let dir = scratch("source-changed");
    for name in ["calc.k", "FLOW.toml"] {
        fs::copy(flow("calc").join(name), dir.join(name)).unwrap();
    }
    let spec = Spec::at(&dir.join("FLOW.toml"));
    let edits = "[[mutation.edit]]\nrule = \"add\"\nfind = \"+Int\"\nreplace = \"-Int\"\n";
    spec.resolve_edits(edits).unwrap();
    let text = fs::read_to_string(dir.join("calc.k")).unwrap();
    fs::write(dir.join("calc.k"), text.replace("*Int", "+Int")).unwrap();
    expect_invalid(
        spec.resolve_edits(edits),
        Some(0),
        InvalidReason::SourceChanged,
    );
}

#[test]
fn every_reason_is_produced_or_listed_as_defensive() {
    use InvalidReason::*;
    // Keep this list equal to the reasons the tests above produce.
    let produced = [
        UnknownFile,
        FileRequired,
        UnknownLabel,
        AmbiguousLabel,
        LineOutsideRules,
        LineAmbiguous,
        AddressMismatch,
        NonRuleSentence,
        FindNotFound,
        FindAmbiguous,
        EditOutsideRule,
        OverlappingEdits,
        SourceChanged,
        EditedLoadFailed,
        StructureChanged,
        LabelChanged,
        NoChange,
        // F-10: produced by tests/markdown.rs.
        SourceViewMismatch,
        MarkdownEnvelope,
        SpanChanged,
    ];
    let all = produced
        .iter()
        .chain(&DEFENSIVE)
        .map(|r| r.as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(all.len(), produced.len() + DEFENSIVE.len());
    // An exhaustive match: a new reason fails to compile here until it is listed.
    for reason in produced.iter().chain(&DEFENSIVE) {
        match reason {
            UnknownFile | FileRequired | UnknownLabel | AmbiguousLabel | LineOutsideRules
            | LineAmbiguous | AddressMismatch | NonRuleSentence | NoUsableSpan | FindNotFound
            | FindAmbiguous | EditOutsideRule | OverlappingEdits | SourceChanged
            | EditedLoadFailed | StructureChanged | LabelChanged | NoChange | PatchRejected
            | SourceViewMismatch | MarkdownEnvelope | SpanChanged => {}
        }
    }
}

// ---------------------------------------------------------------------------------------
// Spans.

/// The location fallback (used when a sentence has no offset attributes) names the same
/// bytes as the offsets, for every authored sentence of the fixtures.
#[test]
fn the_location_fallback_gives_the_offset_span() {
    let mut checked = 0;
    for name in ["calc", "register", "loop"] {
        let spec = Spec::fixture(name);
        let text =
            fs::read_to_string(spec.manifest.directory.join(&spec.manifest.spec.entry)).unwrap();
        for (_, sentence) in spec.loaded.baseline.authored_sentences() {
            let attributes = sentence.attributes();
            let start = attributes
                .value(AttributeKey::SentenceStartOffset)
                .and_then(Value::as_u64);
            let end = attributes
                .value(AttributeKey::SentenceEndOffset)
                .and_then(Value::as_u64);
            let (Some(start), Some(end)) = (start, end) else {
                continue;
            };
            let span = start as usize..end as usize;
            assert_eq!(sentence_span(sentence, &text), Some(span.clone()));
            assert_eq!(
                location_span(attributes.location().unwrap(), &text),
                Some(span),
                "{name}: {:?}",
                attributes.location()
            );
            checked += 1;
        }
    }
    assert!(checked > 20, "{checked}");
}

/// The edited sources differ from the originals exactly at the found text.
#[test]
fn edited_sources_are_the_originals_with_the_found_text_replaced() {
    let spec = Spec::fixture("register");
    let resolved = fixture_mutation(&spec, &fixture_list("register"), "put-and-get-offset");
    let text = fs::read_to_string(flow("register").join("register.k")).unwrap();
    let expected = BTreeMap::from([(
        "register.k".to_owned(),
        text.replace("_ => I </reg>", "_ => I +Int 1 </reg>")
            .replace("get => I ...", "get => I -Int 1 ..."),
    )]);
    assert_eq!(resolved.edited_sources, expected);
}

/// The example of the crate README's `MUTATIONS.toml` section resolves on the calc fixture.
#[test]
fn the_readme_example_resolves() {
    let readme = include_str!("../README.md");
    let section = &readme[readme.find("## `MUTATIONS.toml`").unwrap()..];
    let block = &section[section.find("```toml\n").unwrap() + 8..];
    let block = &block[..block.find("```").unwrap()];
    let list = MutationList::decode(block).unwrap();
    let spec = Spec::fixture("calc");
    let resolved = spec.resolve(&list.mutations[0]).unwrap();
    assert_eq!(
        shape(&resolved),
        [("replace", at("CALC", 1)), ("delete", at("CALC", 2))]
    );
}

/// kink-corpus's overlay: empty, it is `load_source`; an entry replaces that file's text
/// (and its recorded digest); an entry the load never reads is an error.
#[test]
fn the_resolver_overlay_replaces_only_the_files_it_names() {
    let spec = Spec::fixture("calc");
    let source = corpus_source(&spec.manifest);
    let plain = load_source_with_overlay(&source, &BTreeMap::new()).unwrap();
    assert_eq!(plain.files, spec.loaded.files);
    assert!(plain.baseline.definition() == spec.loaded.baseline.definition());
    let text = fs::read_to_string(flow("calc").join("calc.k")).unwrap();
    let edited_text = text.replace("I1 *Int I2", "I1 +Int I2");
    let edited = load_source_with_overlay(
        &source,
        &BTreeMap::from([("calc.k".to_owned(), edited_text.clone())]),
    )
    .unwrap();
    assert_eq!(edited.files.len(), 1);
    assert_eq!(edited.files[0].name, "calc.k");
    assert_eq!(
        edited.files[0].sha256,
        kink_patch::sha256(edited_text.as_bytes())
    );
    assert_ne!(edited.files[0].sha256, spec.loaded.files[0].sha256);
    let error = load_source_with_overlay(
        &source,
        &BTreeMap::from([("nope.k".to_owned(), String::new())]),
    )
    .err()
    .unwrap();
    assert!(error.to_string().starts_with("nope.k: "), "{error}");
}
