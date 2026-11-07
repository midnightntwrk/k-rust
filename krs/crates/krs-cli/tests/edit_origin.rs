//! The generated-only edit judge over K that `krs emit-k` writes: an edit that changes only
//! nodes KRS inserted is refused, naming the sentence's Rust item, what KRS inserted and the
//! authored node to edit instead with its Rust bytes; an edit of authored syntax (a `k::bits!`
//! template's literal or field read, an `else`'s negation, an operator, a constant at one use,
//! a `..` the author wrote, a whole rule, a rule's label) goes to the re-derivation, which the
//! judge never answers for; a mutation whose tokens are the baseline's, a change outside every
//! sentence, an edit of a declaration and an edit inside a lookup-guard or local-function family
//! are refused. A mutation is judged by the tokens it changes, however its find is written.
//!
//! The re-derivation then accepts a sentence the judge hands on only when it is what KRS emits
//! for its edited authored content: every sentence is its own re-derivation, a derived test
//! must follow the edited construct, the lift refuses what no authored syntax writes (a function
//! KRS lifts out of a sentence, one equation of a function shorthand moved to another function),
//! an edit beside a local function is accepted when the function derives as before, a
//! mutation that changes nothing is refused, and the story's mutations are accepted.

use std::fs;
use std::path::{Path, PathBuf};

use krs_compiler::{
    DEFINITION_ARTIFACT, EditJudgement, InsertedNodeRef, KEdit, MutationVerdict, SentenceVerdict,
    SourceMap, judge_edits,
};
use krs_ir::InsertedNode;
use krs_k_rust::lift::{Accepted, LiftRefusal, MutantChecker, MutationCheck, NotJudged, Refusal};
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// The package `inserted_nodes.rs` takes its census of.
const PACKAGE: &str = include_str!("fixtures/inserted-nodes/src/lib.rs");

/// The package of the edits beside a local function, of a machine-form map frame and of
/// equation heads.
const EDITS: &str = include_str!("fixtures/edit-origin/src/lib.rs");

/// The introduction's specification.
const STORY: &str = include_str!("../../../../docs-site/story/plus/src/lib.rs");

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

fn package(root: &Path, name: &str, namespace: &str, library: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// The emitted `definition.k` and its source map.
struct Emitted {
    definition: String,
    map: SourceMap,
    library: &'static str,
}

/// Emits the `main` definition of a package holding `library`.
fn emit(name: &str, namespace: &str, library: &'static str) -> Emitted {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), name, namespace, library);
    let output = temporary.path().join("emitted");
    let mut process = krs_command!();
    fixture_build_env(&mut process, target.path());
    let result = process
        .args(["emit-k", "--manifest-path"])
        .arg(&manifest)
        .args(["--package", name, "--definition", "main", "--output"])
        .arg(&output)
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.path().join("stages"))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    Emitted {
        definition: fs::read_to_string(output.join("definition.k")).unwrap(),
        map: serde_json::from_str(&fs::read_to_string(output.join("sources.json")).unwrap())
            .unwrap(),
        library,
    }
}

impl Emitted {
    /// The bytes of the one sentence whose text starts with `head`.
    fn sentence(&self, head: &str) -> std::ops::Range<usize> {
        let found = self
            .map
            .entries()
            .iter()
            .filter(|entry| entry.depth() == 1)
            .filter_map(|entry| entry.generated())
            .filter(|generated| generated.artifact() == DEFINITION_ARTIFACT)
            .map(|generated| {
                usize::try_from(generated.start_byte()).unwrap()
                    ..usize::try_from(generated.end_byte()).unwrap()
            })
            .filter(|range| {
                self.definition[range.clone()]
                    .trim_start()
                    .starts_with(head)
            })
            .collect::<Vec<_>>();
        assert_eq!(found.len(), 1, "one sentence starts with {head:?}");
        found[0].clone()
    }

    /// The edit writing `replacement` in place of the one occurrence of `find` in the sentence
    /// starting with `head`.
    fn edit<'a>(&self, head: &str, find: &str, replacement: &'a str) -> KEdit<'a> {
        let sentence = self.sentence(head);
        let text = &self.definition[sentence.clone()];
        let offset = text
            .find(find)
            .unwrap_or_else(|| panic!("{find:?} in {text:?}"));
        assert_eq!(
            text.rfind(find),
            Some(offset),
            "{find:?} occurs once in {text:?}"
        );
        let start = sentence.start + offset;
        KEdit::new(start..start + find.len(), replacement)
    }

    fn judge(&self, edits: &[KEdit<'_>]) -> EditJudgement {
        judge_edits(&self.definition, &self.map, DEFINITION_ARTIFACT, edits).unwrap()
    }

    fn text(&self, range: &std::ops::Range<usize>) -> &str {
        &self.definition[range.clone()]
    }

    /// Each named node: its text, its kind, its nearest authored node's text and Rust text.
    fn named(
        &self,
        nodes: &[InsertedNodeRef],
    ) -> Vec<(String, InsertedNode, Option<String>, Option<String>)> {
        nodes
            .iter()
            .map(|node| {
                let authored = node.nearest_authored.as_ref();
                (
                    self.text(&node.emitted).to_owned(),
                    node.kind,
                    authored
                        .and_then(|authored| authored.emitted.as_ref())
                        .map(|range| self.text(range).to_owned()),
                    authored
                        .and_then(|authored| authored.source.as_ref())
                        .map(|range| {
                            assert_eq!(range.file.package_relative_path(), "src/lib.rs");
                            self.library[range.start_byte as usize..range.end_byte as usize]
                                .to_owned()
                        }),
                )
            })
            .collect()
    }

    /// The one changed sentence's Rust item and verdict.
    fn single(judgement: &EditJudgement) -> (&str, &SentenceVerdict) {
        assert!(judgement.outside.is_empty(), "{judgement:#?}");
        assert_eq!(judgement.sentences.len(), 1, "{judgement:#?}");
        let sentence = &judgement.sentences[0];
        (
            sentence.item.as_ref().map_or("", |item| item.item_name()),
            &sentence.verdict,
        )
    }

    /// The edit is refused because it changes only KRS's nodes; returns them named.
    fn inserted_only(
        &self,
        item: &str,
        edits: &[KEdit<'_>],
    ) -> Vec<(String, InsertedNode, Option<String>, Option<String>)> {
        let judgement = self.judge(edits);
        assert_eq!(judgement.verdict(), MutationVerdict::Refused);
        let (named_item, verdict) = Self::single(&judgement);
        assert_eq!(named_item, item);
        let SentenceVerdict::InsertedOnly { nodes } = verdict else {
            panic!("inserted only: {judgement:#?}");
        };
        self.named(nodes)
    }

    /// The edit goes to the re-derivation, which the judge does not answer for; returns the
    /// text of each container.
    fn to_rederivation(&self, item: &str, edits: &[KEdit<'_>]) -> Vec<String> {
        let judgement = self.judge(edits);
        assert_eq!(judgement.verdict(), MutationVerdict::NeedsRederivation);
        let (named_item, verdict) = Self::single(&judgement);
        assert_eq!(named_item, item);
        let SentenceVerdict::NeedsRederivation { containers } = verdict else {
            panic!("needs re-derivation: {judgement:#?}");
        };
        containers
            .iter()
            .map(|container| self.text(&container.emitted).to_owned())
            .collect()
    }
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One pass over the fixture's families."
)]
fn edits_of_inserted_nodes_are_refused_and_authored_edits_need_rederivation() {
    let emitted = emit("inserted-nodes", "ORG-KRS-INSERTED", PACKAGE);

    // Inserted only: the refusal names the item, the kind, and the authored node with its Rust.
    // Naming the whole condition as the find, its right operand's brackets dropped, removes
    // only the conjunction's tokens too.
    let condition = "(A:Int =/=Int 0) andThenBool ((10 /Int A:Int) >Int 1)";
    for edit in [
        emitted.edit("rule [div]", "(A:Int =/=Int 0) andThenBool ", ""),
        emitted.edit("rule [div]", condition, "(10 /Int A:Int) >Int 1"),
    ] {
        assert_eq!(
            emitted.inserted_only("div", &[edit]),
            [(
                condition.to_owned(),
                InsertedNode::DefinednessTest,
                Some("10 /Int A:Int".to_owned()),
                Some("/".to_owned()),
            )]
        );
    }
    assert_eq!(
        emitted.inserted_only(
            "look",
            &[emitted.edit(
                "rule [look]",
                "A:Int in_keys(M:Map)",
                "A:Int notin_keys(M:Map)"
            )]
        ),
        [(
            "A:Int in_keys(M:Map)".to_owned(),
            InsertedNode::DefinednessTest,
            Some("{M:Map [ A:Int ]}:>Int".to_owned()),
            Some("[a]".to_owned()),
        )]
    );
    assert_eq!(
        emitted.inserted_only(
            "bits",
            &[emitted.edit(
                "rule [bits]",
                "bitRangeInt(Bits:Int, 0, 3)",
                "bitRangeInt(Y:Int, 0, 3)"
            )]
        ),
        [(
            "Bits:Int".to_owned(),
            InsertedNode::GeneratedBinder,
            Some("bitRangeInt(Bits:Int, 0, 3)".to_owned()),
            Some("a".to_owned()),
        )]
    );
    assert_eq!(
        emitted.inserted_only(
            "read",
            &[emitted.edit(
                "rule [read]",
                "read A:Int => skip ... </k>",
                "read A:Int => skip </k>"
            )]
        ),
        [(
            " ...".to_owned(),
            InsertedNode::CellFrame,
            // The authored node of the frame's Rust that holds it: the cell the rule reads.
            Some("    <k> read A:Int => skip ... </k>".to_owned()),
            Some("Read(a)".to_owned()),
        )]
    );
    let stdin = emitted.inserted_only(
        "input",
        &[emitted.edit("rule [input]", ".List ... </input>", ".List </input>")],
    );
    assert_eq!(stdin.len(), 1);
    assert_eq!(
        (stdin[0].1, stdin[0].3.as_deref()),
        (InsertedNode::CellFrame, Some("input"))
    );
    let guard = emitted.inserted_only("key", &[emitted.edit("rule [key]", "==K", "=/=K")]);
    assert_eq!(guard.len(), 1);
    assert_eq!(guard[0].1, InsertedNode::LookupGuard);
    let update = emitted.inserted_only(
        "save",
        &[emitted.edit("rule [save]", "( 1 #as FPc:Int )", "( 1 #as P:Int )")],
    );
    assert_eq!(update.len(), 1);
    assert_eq!(
        (update[0].0.as_str(), update[0].1),
        ("( 1 #as FPc:Int )", InsertedNode::GeneratedBinder)
    );

    // Authored: renderings of authored syntax and frames the author wrote need the
    // re-derivation, at the node the edit changes.
    let bits = "rule [bits]";
    assert_eq!(
        emitted.to_rederivation(
            "bits",
            &[emitted.edit(
                bits,
                "(bitRangeInt(Bits:Int, 3, 1)) ==Int 0",
                "(bitRangeInt(Bits:Int, 3, 1)) ==Int 1"
            )]
        ),
        ["0"]
    );
    assert_eq!(
        emitted.to_rederivation(
            "bits",
            &[emitted.edit(
                bits,
                "bitRangeInt(Bits:Int, 0, 3)",
                "bitRangeInt(Bits:Int, 0, 4)"
            )]
        ),
        ["3"]
    );
    let clamp = "rule clamp ( Value:Int ) => Value";
    assert_eq!(
        emitted.to_rederivation(
            "clamp_2",
            &[emitted.edit(
                clamp,
                "notBool (Value:Int <Int 0)",
                "notBool (Value:Int <Int 1)"
            )]
        ),
        ["0"]
    );
    assert_eq!(
        emitted.to_rederivation("clamp_2", &[emitted.edit(clamp, "+Int 9", "+Int 10")]),
        ["9"]
    );
    let div = "rule [div]";
    assert_eq!(
        emitted.to_rederivation("div", &[emitted.edit(div, ">Int 1", ">=Int 1")]),
        ["(10 /Int A:Int) >Int 1"]
    );
    assert_eq!(
        emitted.to_rederivation("div", &[emitted.edit(div, ".K ... </k>", ".K </k>")]),
        [" ..."]
    );
    let stop = emitted.sentence("rule [stop]");
    let whole = emitted.text(&stop).trim();
    let start = stop.start + emitted.text(&stop).find(whole).unwrap();
    assert_eq!(
        emitted.to_rederivation("stop", &[KEdit::new(start..start + whole.len(), "")]),
        [emitted.text(&stop)]
    );
    // `notBool` written before the bracketed authored condition may negate it, or the
    // conjunction around it: only the parse tells, so the container is the whole condition.
    assert_eq!(
        emitted.to_rederivation(
            "div",
            &[emitted.edit(div, "andThenBool ((10", "andThenBool notBool ((10")]
        ),
        [condition]
    );
    // Tokens written after the rule's last token continue it, before or after its newline.
    let rule = emitted.sentence(div);
    for point in [rule.end - 1, rule.end] {
        assert_eq!(
            emitted.to_rederivation(
                "div",
                &[KEdit::new(point..point, "\n  rule [new]: <k> 1 => 2 </k>")]
            ),
            [emitted.text(&rule)]
        );
    }
    // An authored construct edited while its test is kept is not accepted here: the
    // re-derivation compares the test with the one KRS derives from the edited construct.
    assert_eq!(
        emitted.to_rederivation(
            "div",
            &[emitted.edit(div, "(10 /Int A:Int)", "(10 /Int (A:Int +Int 1))")]
        ),
        ["A:Int"]
    );

    // A local function's equation and a construct a lookup guard holds are not judged.
    let local = "rule krsLocal_f92565059015b62bf220ca46 ( A:Int ) => true";
    for (item, edit, kind) in [
        (
            "pick",
            emitted.edit(local, "( 5 :=K", "( 6 :=K"),
            InsertedNode::LocalFunction,
        ),
        (
            "key",
            emitted.edit("rule [key]", "(Kk:Map [ A:Int ])", "(Kk:Map [ 0 ])"),
            InsertedNode::LookupGuard,
        ),
    ] {
        let judgement = emitted.judge(&[edit]);
        assert_eq!(judgement.verdict(), MutationVerdict::Refused);
        let (named_item, verdict) = Emitted::single(&judgement);
        assert_eq!(named_item, item);
        let SentenceVerdict::FamilyNotJudged { nodes } = verdict else {
            panic!("not judged: {judgement:#?}");
        };
        assert!(nodes.iter().all(|node| node.kind == kind), "{nodes:#?}");
    }

    // A label is the rule's own token, which the re-derivation reads with the whole rule; a
    // rewrite of a sentence by itself and a comment change no token; a change outside every
    // sentence and an edit of a declaration are refused.
    let clamp_1 = emitted.sentence("rule clamp ( Value:Int ) => 0");
    assert_eq!(
        emitted.to_rederivation(
            "clamp_1",
            &[emitted.edit(
                "rule clamp ( Value:Int ) => 0",
                "[label(org_krs_inserted--clamp_1)]",
                "[label(org_krs_inserted--clamp_0)]",
            )]
        ),
        [emitted.text(&clamp_1)]
    );
    let same = emitted.edit(div, ">Int 1", ">Int 1");
    assert_eq!(
        emitted.judge(&[same]).verdict(),
        MutationVerdict::ChangesNoNode
    );
    let comment = "// KRS inserted-nodes/src/lib.rs: div";
    let start = emitted.definition.find(comment).unwrap();
    let judgement = emitted.judge(&[KEdit::new(start..start + comment.len(), "// div")]);
    assert_eq!(judgement.verdict(), MutationVerdict::ChangesNoNode);
    let imports = "  imports SET\n";
    let point = emitted.definition.find(imports).unwrap() + imports.len();
    let judgement = emitted.judge(&[KEdit::new(point..point, "  rule [new]: <k> 1 => 2 </k>\n")]);
    assert_eq!(judgement.verdict(), MutationVerdict::Refused);
    assert_eq!(judgement.outside.len(), 1);
    let judgement = emitted.judge(&[emitted.edit("configuration", "( 0 ):Value", "( 1 ):Value")]);
    assert_eq!(judgement.verdict(), MutationVerdict::Refused);
    assert_eq!(Emitted::single(&judgement).1, &SentenceVerdict::NotARule);
}

/// The introduction's three mutations each change an authored node of one equation.
#[test]
fn story_mutations_need_rederivation() {
    let emitted = emit("story-plus", "NAT", STORY);
    let zero = "rule plus ( zero , N:Nat )";
    let succ = "rule plus ( s ( M:Nat ) , N:Nat )";
    for (item, edit, container) in [
        (
            "plus_zero",
            emitted.edit(zero, "=> N:Nat", "=> zero"),
            "N:Nat",
        ),
        (
            "plus_succ",
            emitted.edit(
                succ,
                "s ( plus ( M:Nat , N:Nat ) )",
                "plus ( M:Nat , N:Nat )",
            ),
            "s ( plus ( M:Nat , N:Nat ) )",
        ),
        (
            "plus_succ",
            emitted.edit(succ, "s ( plus ( M:Nat , N:Nat ) )", "s ( N:Nat )"),
            "plus ( M:Nat , N:Nat )",
        ),
    ] {
        assert_eq!(emitted.to_rederivation(item, &[edit]), [container]);
    }
}

/// The in-process baseline of a package, as `krs emit-k` builds it
/// ([`krs_cli::CollectedDefinition::emit_k_retained`]): its lowering with what the
/// re-derivation keeps, its Definition IR and its K.
struct Baseline {
    retained: krs_compiler::RetainedLowering,
    lowered: krs_compiler::LoweredDefinition,
    emitted: krs_cli::EmittedDefinition,
    view: Emitted,
}

/// Collects, lowers and emits the `main` definition of a package holding `library` in process.
fn baseline(name: &str, namespace: &str, library: &'static str) -> Baseline {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), name, namespace, library);
    let request = krs_cli::CommandRequest {
        command: krs_cli::Command::Check {
            backend: None,
            partition: false,
        },
        manifest_path: manifest,
        root: krs_cli::FacetSelector {
            package: krs_cli::PackageSelector::Name(name.into()),
            definition: "main".into(),
        },
        dependencies: Vec::new(),
        cfg: Vec::new(),
        registration: krs_cli::RegistrationMode::Inventory,
        no_reuse: true,
        message_format: krs_cli::MessageFormat::Human,
        profile: None,
    };
    let collected = krs_cli::collect_descriptors(&request, Some(target.path())).unwrap();
    let krs_cli::RetainedEmission {
        emitted,
        retained,
        lowered,
    } = collected.emit_k_retained(collected.bundle.clone()).unwrap();
    let view = Emitted {
        definition: emitted.definition.clone(),
        map: emitted.source_map.clone(),
        library,
    };
    Baseline {
        retained,
        lowered,
        emitted,
        view,
    }
}

impl Baseline {
    fn checker(&self) -> MutantChecker<'_> {
        let rederivation = krs_compiler::Rederivation::new(&self.retained, &self.lowered).unwrap();
        MutantChecker::new(
            rederivation,
            &self.emitted.definition,
            &self.emitted.source_map,
        )
        .unwrap()
    }

    /// The first line of the sentence `key`, which names it.
    fn head(&self, key: &krs_ir::SourceMapKey) -> String {
        let entry = self
            .emitted
            .source_map
            .entries()
            .iter()
            .find(|entry| entry.key() == key)
            .unwrap();
        let generated = entry.generated().unwrap();
        let start = usize::try_from(generated.start_byte()).unwrap();
        let end = usize::try_from(generated.end_byte()).unwrap();
        self.emitted.definition[start..end]
            .trim()
            .lines()
            .next()
            .unwrap()
            .to_owned()
    }

    /// The check of one mutation of the sentence starting with `head`: each edit writes its
    /// replacement in place of the one occurrence of its find.
    fn check(&self, head: &str, edits: &[(&str, &str)]) -> MutationCheck {
        let edits = edits
            .iter()
            .map(|(find, replacement)| self.view.edit(head, find, replacement))
            .collect::<Vec<_>>();
        self.checker().check(&edits).unwrap()
    }
}

/// The one sentence a check judged, and its outcome.
fn outcome(check: &MutationCheck) -> &Result<Accepted, Refusal> {
    assert_eq!(
        check.judgement.verdict(),
        MutationVerdict::NeedsRederivation,
        "{:#?}",
        check.judgement
    );
    assert_eq!(check.sentences.len(), 1, "{check:#?}");
    &check.sentences[0].outcome
}

fn accepted(check: &MutationCheck) -> &Accepted {
    match outcome(check) {
        Ok(accepted) => {
            assert!(!accepted.unchanged, "{check:#?}");
            assert!(check.accepted());
            accepted
        }
        Err(refusal) => panic!("refused: {refusal}"),
    }
}

/// The derived and the mutant's tests of a refusal for a derived node that does not follow the
/// edit.
fn mismatch(check: &MutationCheck) -> (Vec<String>, Vec<String>) {
    assert!(!check.accepted());
    match outcome(check) {
        Err(Refusal::DerivedMismatch {
            derived_tests,
            mutant_tests,
            ..
        }) => (derived_tests.clone(), mutant_tests.clone()),
        other => panic!("not a derived mismatch: {other:?}"),
    }
}

/// Rendering one sentence alone, with the baseline's naming and index, gives the bytes `emit_k`
/// wrote for it, for every sentence of the census fixture and of the story; and the in-process
/// emission is the K `krs emit-k` writes.
#[test]
fn one_sentence_rendered_alone_is_emit_k_s_bytes() {
    for (name, namespace, library) in [
        ("inserted-nodes", "ORG-KRS-INSERTED", PACKAGE),
        ("story-plus", "NAT", STORY),
    ] {
        let baseline = baseline(name, namespace, library);
        assert_eq!(
            baseline.emitted.definition,
            emit(name, namespace, library).definition
        );
        let rederivation =
            krs_compiler::Rederivation::new(&baseline.retained, &baseline.lowered).unwrap();
        let mut rendered = 0;
        for entry in baseline.emitted.source_map.entries() {
            let Some(generated) = entry.generated() else {
                continue;
            };
            if entry.depth() != 1 || generated.artifact() != DEFINITION_ARTIFACT {
                continue;
            }
            let start = usize::try_from(generated.start_byte()).unwrap();
            let end = usize::try_from(generated.end_byte()).unwrap();
            assert_eq!(
                rederivation.render_baseline(entry.key()).unwrap(),
                baseline.emitted.definition[start..end],
                "{name}: {:?}",
                entry.key()
            );
            rendered += 1;
        }
        assert!(rendered > 10, "{name}: {rendered} sentences");
    }
}

/// The fixed point: every rule sentence, read back from its own K with the whole sentence as the
/// container, lifted and derived again, is the sentence itself; the sentences whose derivation
/// reads more than the sentence (a lookup guard, a local function) or that read a stream cell are
/// not judged.
#[test]
fn every_sentence_is_its_own_rederivation() {
    for (name, namespace, library, not_judged) in [
        (
            "inserted-nodes",
            "ORG-KRS-INSERTED",
            PACKAGE,
            &[
                "rule [elem]:",
                "rule [input]:",
                "rule [key]:",
                "rule krsLocal_f92565059015b62bf220ca46 ( A:Int ) => false",
                "rule krsLocal_f92565059015b62bf220ca46 ( A:Int ) => true",
                "rule pick A:Int => flag krsLocal_f92565059015b62bf220ca46 ( A:Int ) [label(org_krs_inserted--pick)]",
                "rule [part]:",
                "rule [proj]:",
            ][..],
        ),
        ("story-plus", "NAT", STORY, &[][..]),
        (
            "edit-origin",
            "ORG-KRS-EDITS",
            EDITS,
            &[
                "rule krsLocal_635bd5991636fe175a0c35d6 ( A:Arg ) => true",
                "rule krsLocal_635bd5991636fe175a0c35d6 ( A:Arg ) => false",
                "rule [probe]:",
            ][..],
        ),
    ] {
        let baseline = baseline(name, namespace, library);
        let checker = baseline.checker();
        let mut refused = Vec::new();
        let mut reasons = Vec::new();
        let mut judged = 0;
        for key in checker.rule_sentences() {
            let head = baseline.head(&key);
            match checker.fixed_point(&key) {
                Ok(accepted) => {
                    assert!(accepted.unchanged, "{name}: {head}");
                    judged += 1;
                }
                Err(Refusal::NotJudged(reason)) => {
                    reasons.push(format!("{head}: {reason}"));
                    refused.push(head);
                }
                Err(refusal) => panic!("{name}: {head}: {refusal}"),
            }
        }
        assert_eq!(refused, not_judged, "{name}: {reasons:#?}");
        assert!(judged >= 2, "{name}");
    }
}

/// The configuration-cells gate's harts library, `hart`'s group and rules.
const GROUP_HARTS_HART: &str =
    include_str!("../../../tests/configuration-cells/packages/group-harts/hart/src/lib.rs");

/// The configuration-cells gate's `group-harts` package `holder`, whose source is `source` and
/// which composes the harts library, as one package with the library: `holder`'s source without
/// its crate documentation and with the library's items in scope.
fn harts_package(source: &str, imports: &str, own: &str) -> &'static str {
    assert!(source.contains(imports));
    let holder = source
        .replace(imports, own)
        .lines()
        .filter(|line| !line.starts_with("//!"))
        .collect::<Vec<_>>()
        .join("\n");
    Box::leak(format!("{GROUP_HARTS_HART}\n{holder}\n").into_boxed_str())
}

/// `smp`'s collection of harts with the harts library ([`harts_package`]).
fn smp_package() -> &'static str {
    harts_package(
        include_str!("../../../tests/configuration-cells/packages/group-harts/smp/src/lib.rs"),
        "use hart::{BusOp, Hart, Job, Jobs, Op, Prog, Regs};\nuse k::builtin::{Int, Map, int, map};\n",
        "use k::builtin::{Map, map};\n",
    )
}

/// `nested`'s clusters of harts with the harts library ([`harts_package`]).
fn nested_package() -> &'static str {
    harts_package(
        include_str!("../../../tests/configuration-cells/packages/group-harts/nested/src/lib.rs"),
        "use hart::{BusOp, Hart, Instr, Job, Jobs, Op, Prog, Regs};\nuse k::Term;\nuse k::builtin::{Int, Map, int, map};\n",
        "use k::Term;\nuse k::builtin::{Map, map};\n",
    )
}

/// Each rule sentence of `baseline` with its fixed point's outcome: judged (and its own
/// re-derivation), or why it is not judged.
fn fixed_points(baseline: &Baseline) -> Vec<String> {
    let checker = baseline.checker();
    let mut outcomes = Vec::new();
    for key in checker.rule_sentences() {
        let head = baseline.head(&key);
        match checker.fixed_point(&key) {
            Ok(accepted) => {
                assert!(accepted.unchanged, "{head}");
                outcomes.push(format!("{head} judged"));
            }
            Err(Refusal::NotJudged(reason)) => outcomes.push(format!("{head} {reason}")),
            Err(refusal) => panic!("{head}: {refusal}"),
        }
    }
    outcomes
}

/// The fixed point of the rules of a definition whose rules for `Hart` lie in the instances of a
/// Map collection: each rule that names the hart's cells inside the instance's cell is its own
/// re-derivation. The sentences left are the `#[k::context]`s, which the check does not read, and
/// those that hold an optional cell or an instance record (`smp`'s rules over its collection, or
/// a hart's jobs), which the lift does not read.
#[test]
fn every_rule_about_one_instance_is_its_own_rederivation() {
    let baseline = baseline("group-harts", "KRS-HARTS", smp_package());
    expect_test::expect![[r#"
        [
            "rule [guard]: judged",
            "context [guard-operand]: this sentence is not judged",
            "rule [here]: judged",
            "rule [hop]: judged",
            "context [hop-operand]: this sentence is not judged",
            "rule [inc]: judged",
            "rule [join]: an optional or collection cell is not judged",
            "rule [load]: judged",
            "rule [next]: judged",
            "rule [post]: an optional or collection cell is not judged",
            "rule [read]: an optional or collection cell is not judged",
            "rule [release]: an optional or collection cell is not judged",
            "rule [report]: an optional or collection cell is not judged",
            "rule [reserve]: an optional or collection cell is not judged",
            "rule [spawn]: an optional or collection cell is not judged",
            "rule [store]: judged",
            "rule [swap]: judged",
            "rule [tick]: judged",
            "rule [wait]: judged",
            "rule [work]: an optional or collection cell is not judged",
            "rule [write]: an optional or collection cell is not judged",
        ]
    "#]]
    .assert_debug_eq(&fixed_points(&baseline));
}

/// The same fixed point where the harts lie in the instances of a Map collection inside each
/// instance of another, `nested`'s clusters: a rule for `Hart` is a local step of one hart of one
/// cluster. `leap` passes `pcPlus` the keys of its hart and its cluster, so KRS adds the key cell
/// of each, `<cid>` in the cluster's cell and `<id>` in the hart's; those cells are KRS's
/// placement of the rule, not a change of its footprint, and the rule is its own
/// re-derivation.
#[test]
fn every_rule_about_one_nested_instance_is_its_own_rederivation() {
    let baseline = baseline("group-harts-nested", "KRS-HARTS-NESTED", nested_package());
    expect_test::expect![[r#"
        [
            "rule [guard]: judged",
            "context [guard-operand]: this sentence is not judged",
            "rule [here]: judged",
            "rule [hop]: judged",
            "context [hop-operand]: this sentence is not judged",
            "rule [inc]: judged",
            "rule [join]: an optional or collection cell is not judged",
            "rule [[ pcPlus ( N:Int ) #instance ( Krs_KeyCluster:Int , Krs_KeyHart:Int ) => P:Int +Int N:Int ]] a function context is not judged",
            "rule [leap]: judged",
            "rule [load]: judged",
            "rule [next]: judged",
            "rule [post]: an optional or collection cell is not judged",
            "rule [read]: an optional or collection cell is not judged",
            "rule [release]: an optional or collection cell is not judged",
            "rule [report]: an optional or collection cell is not judged",
            "rule [reserve]: an optional or collection cell is not judged",
            "rule [spawn]: an optional or collection cell is not judged",
            "rule [store]: judged",
            "rule [swap]: judged",
            "rule [tick]: judged",
            "rule [wait]: judged",
            "rule [work]: an optional or collection cell is not judged",
            "rule [write]: an optional or collection cell is not judged",
        ]
    "#]].assert_debug_eq(&fixed_points(&baseline));
}

/// What an edit of a rule about one instance of a Map collection changes decides whether it is
/// judged. The rule's footprint is the cells and instances it reads or writes, where the emitter
/// places them: a cell added inside the instance or outside it, a cell moved out of the
/// instance, and the instance's cell dropped each change it, and are refused. A closed frame of
/// the instance's cell keeps the cells but states that the instance has no other cells, which
/// no rule for `Hart` emits, and is refused. Writing the key other than as the subject matched it is a write of
/// the instance's identity, which KRS refuses in the Rust source with the same reason; matching
/// another literal key is no write but a change of the pattern (`id: 1` in Rust), judged as any
/// other. In `nested`, an edit of the argument `leap` gives `pcPlus` is judged beside the key
/// cells and the key arguments KRS adds, and an edit of a key argument is refused: KRS derives
/// the keys the rule passes, and the mutant's are not those.
#[test]
fn an_edit_of_a_rule_about_one_instance_is_judged_by_its_footprint() {
    let smp = baseline("group-harts", "KRS-HARTS", smp_package());
    let footprint = |check: &MutationCheck| {
        assert!(
            matches!(
                outcome(check),
                Err(Refusal::NotJudged(NotJudged::Skeleton(what))) if what == "the cells the rule mentions"
            ),
            "{check:#?}"
        );
    };
    let inc = "rule [inc]";
    let pc = "<pc> Pc:Int => Pc:Int +Int 1 </pc>";
    // A cell added inside the hart.
    footprint(&smp.check(
        inc,
        &[(
            pc,
            "<pc> Pc:Int => Pc:Int +Int 1 </pc>\n        <id> 0 </id>",
        )],
    ));
    // A cell added outside the hart.
    footprint(&smp.check(
        inc,
        &[(
            "</hart>",
            "</hart>\n    <nextId> N:Int => N:Int +Int 1 </nextId>",
        )],
    ));
    // The program counter moved out of the hart.
    footprint(&smp.check(inc, &[(pc, ""), ("</hart>", &format!("</hart>\n    {pc}"))]));
    // The hart's cell dropped.
    footprint(&smp.check(inc, &[("<hart>", ""), ("...\n    </hart>", "")]));
    // The hart's cell closed.
    let closed = smp.check(inc, &[("...\n    </hart>", "</hart>")]);
    assert!(!closed.accepted(), "{closed:#?}");
    // The key written as another than the subject matched.
    let rekeyed = smp.check("rule [tick]", &[("<id> 0 </id>", "<id> 0 => 1 </id>")]);
    match outcome(&rekeyed) {
        Err(Refusal::Krs(error)) => match error.as_ref() {
            krs_compiler::DescriptorLoweringError::GroupInstance { code, reason, .. } => {
                assert_eq!(*code, krs_diagnostic::codes::analysis::MAP_COLLECTION_KEY);
                assert_eq!(
                    *reason,
                    krs_ir::subject::key_write_reason("Hart", "hart", "id", "id")
                );
            }
            other => panic!("{other:?}"),
        },
        other => panic!("{other:?}"),
    }
    // Another literal key matched.
    accepted(&smp.check("rule [tick]", &[("<id> 0 </id>", "<id> 1 </id>")]));

    let nested = baseline("group-harts-nested", "KRS-HARTS-NESTED", nested_package());
    let leap = "rule [leap]";
    let check = nested.check(leap, &[("pcPlus ( N:Int )", "pcPlus ( N:Int +Int 1 )")]);
    let lifted = accepted(&check).pre_derivation.as_ref().unwrap();
    assert_eq!(lifted.id().item_name(), "leap");
    let check = nested.check(leap, &[("Krs_KeyHart:Int )", "Krs_KeyHart:Int +Int 1 )")]);
    assert!(!check.accepted(), "{check:#?}");
}

/// The cases of a derived node that must follow the edit, on the census fixture's `div`
/// (`requires (A:Int =/=Int 0) andThenBool ((10 /Int A:Int) >Int 1)`).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One case per line of the design's table."
)]
fn derived_nodes_follow_the_edit() {
    let baseline = baseline("inserted-nodes", "ORG-KRS-INSERTED", PACKAGE);
    let div = "rule [div]";

    // The divisor edited and its test kept: KRS derives the test of the new divisor.
    let check = baseline.check(div, &[("10 /Int A:Int", "10 /Int (A:Int +Int 1)")]);
    assert_eq!(
        mismatch(&check),
        (
            vec!["(A:Int +Int 1) =/=Int 0".to_owned()],
            vec!["A:Int =/=Int 0".to_owned()]
        )
    );
    // With the derived test written in the same mutation: accepted.
    accepted(&baseline.check(
        div,
        &[
            ("(A:Int =/=Int 0)", "((A:Int +Int 1) =/=Int 0)"),
            ("10 /Int A:Int", "10 /Int (A:Int +Int 1)"),
        ],
    ));
    // Unbracketed, K reads `((10 /Int A) +Int 1) >Int 1`: the division and its test are unchanged.
    accepted(&baseline.check(
        div,
        &[("(10 /Int A:Int) >Int 1", "(10 /Int A:Int +Int 1) >Int 1")],
    ));
    // A literal divisor decides the fact: KRS states no test, so the kept one is refused.
    assert_eq!(
        mismatch(&baseline.check(div, &[("10 /Int A:Int", "10 /Int 2")])),
        (Vec::new(), vec!["A:Int =/=Int 0".to_owned()])
    );
    // An authored operator.
    accepted(&baseline.check(div, &[(">Int 1", ">=Int 1")]));
    // A frame the author wrote, deleted: the closed machine-form match.
    accepted(&baseline.check(div, &[(".K ... </k>", ".K </k>")]));
    // A frame KRS adds to a block-form rule, deleted with an authored edit in the same clause:
    // the judge hands the clause on, and the lift keeps the frame KRS adds.
    let check = baseline.check("rule [read]", &[("skip ...", "stop")]);
    assert!(
        matches!(
            outcome(&check),
            Err(Refusal::NotJudged(NotJudged::Skeleton(what))) if what == "a cell's frame"
        ),
        "{check:#?}"
    );
    // A new division written into a condition without its test: refused, showing the test.
    let clamp = "rule clamp ( Value:Int ) => Value";
    let (derived, kept) = mismatch(&baseline.check(
        clamp,
        &[(
            "notBool (Value:Int <Int 0)",
            "(notBool (Value:Int <Int 0)) andThenBool ((10 /Int Value:Int) >Int 0)",
        )],
    ));
    assert_eq!(
        (derived, kept),
        (vec!["Value:Int =/=Int 0".to_owned()], Vec::new())
    );
    // A field read edited with a name the rule binds nowhere: refused by the lift.
    let check = baseline.check(
        "rule [bits]",
        &[(
            "read bitRangeInt(Bits:Int, 0, 3)",
            "read bitRangeInt(Y:Int, 0, 4)",
        )],
    );
    assert!(
        matches!(outcome(&check), Err(Refusal::Lift(LiftRefusal::Unbound(name))) if name == "Y"),
        "{check:#?}"
    );
    // A name KRS made for a template's bits, read where KRS does not write it: refused by the
    // lift, since no Rust spelling names it.
    let check = baseline.check(
        "rule [bits]",
        &[("read bitRangeInt(Bits:Int, 0, 3)", "read Bits:Int")],
    );
    assert!(
        matches!(
            outcome(&check),
            Err(Refusal::Lift(LiftRefusal::NotAdmitted(_)))
        ),
        "{check:#?}"
    );
    // A function KRS lifts out of another sentence, applied where no source applies it: refused
    // by the lift, which names only what a source names.
    let check = baseline.check(
        clamp,
        &[(
            "notBool (Value:Int <Int 0)",
            "krsLocal_f92565059015b62bf220ca46 ( Value:Int )",
        )],
    );
    assert!(
        matches!(
            outcome(&check),
            Err(Refusal::Lift(LiftRefusal::UnknownLabel(label))) if label.starts_with("krsLocal_")
        ),
        "{check:#?}"
    );
    // A label no KRS construct renders: refused by the lift.
    let check = baseline.check(div, &[("(10 /Int A:Int)", "(randInt(10) /Int A:Int)")]);
    assert!(
        matches!(
            outcome(&check),
            Err(Refusal::Lift(LiftRefusal::UnknownLabel(_)))
        ),
        "{check:#?}"
    );
    // A binder renamed at every occurrence changes nothing.
    let check = baseline.check(
        div,
        &[
            ("div A:Int", "div B:Int"),
            ("(A:Int =/=Int 0)", "(B:Int =/=Int 0)"),
            ("10 /Int A:Int", "10 /Int B:Int"),
        ],
    );
    assert!(check.unchanged() && !check.accepted(), "{check:#?}");
    // A label is aside: a mutation that changes only a label changes nothing.
    let label = "rule clamp ( Value:Int ) => 0";
    let check = baseline.check(
        label,
        &[(
            "[label(org_krs_inserted--clamp_1)]",
            "[label(org_krs_inserted--clamp_0)]",
        )],
    );
    assert!(check.unchanged() && !check.accepted(), "{check:#?}");
    // Another attribute's edit is not judged.
    let check = baseline.check(
        label,
        &[(
            "[label(org_krs_inserted--clamp_1)]",
            "[label(org_krs_inserted--clamp_1), priority(40)]",
        )],
    );
    assert!(
        matches!(
            outcome(&check),
            Err(Refusal::NotJudged(NotJudged::Attributes))
        ),
        "{check:#?}"
    );
    // A whole rule deleted is the source without it, with no pre-derivation sentence.
    let check = baseline.check(
        "rule [stop]",
        &[("rule [stop]:\n    <k> stop => .K </k>", "")],
    );
    let deleted = accepted(&check);
    assert!(deleted.deleted && deleted.pre_derivation.is_none());
    // An edit inside a local function's body is not judged.
    let check = baseline.check(
        "rule krsLocal_f92565059015b62bf220ca46 ( A:Int ) => true",
        &[("5 :=K 10 /Int A:Int", "5 :=K 11 /Int A:Int")],
    );
    assert!(!check.accepted());
    assert!(
        check
            .judgement
            .sentences
            .iter()
            .any(|sentence| matches!(sentence.verdict, SentenceVerdict::FamilyNotJudged { .. })),
        "{check:#?}"
    );
}

/// An edit beside a local function, a deleted machine-form map frame, and equation heads: an
/// equation item writes its head in its own pattern, so its head may move to another function,
/// and a function shorthand writes every equation's head at the function's declaration, so one
/// equation's head may not.
#[test]
fn edits_beside_local_functions_frames_and_heads() {
    let baseline = baseline("edit-origin", "ORG-KRS-EDITS", EDITS);
    // A frame the author wrote at a map read, deleted: the closed map match.
    accepted(&baseline.check("rule [go]", &[("V:Int ... </mem>", "V:Int </mem>")]));
    // An edit of another cell than the one whose result KRS lifts into a function: the function
    // derives as the baseline's, and the sentence is accepted.
    accepted(&baseline.check("rule [probe]", &[("_ => 1", "_ => 2")]));
    // An equation item's head moved to another function of the same signature.
    let check = baseline.check(
        "rule double ( Value:Int )",
        &[("double ( Value:Int )", "halve ( Value:Int )")],
    );
    let lifted = accepted(&check).pre_derivation.as_ref().unwrap();
    assert_eq!(lifted.id().item_name(), "double_value");
    // A function shorthand's equation moved to another function: refused by the lift.
    let check = baseline.check(
        "rule twice ( Value:Int )",
        &[("twice ( Value:Int )", "double ( Value:Int )")],
    );
    assert!(
        matches!(
            outcome(&check),
            Err(Refusal::Lift(LiftRefusal::NotAdmitted(what))) if what.contains("head of an equation")
        ),
        "{check:#?}"
    );
}

/// The story's mutations a, b and c are accepted: each is the emission of the Rust edit the
/// introduction describes.
#[test]
fn story_mutations_are_accepted() {
    let baseline = baseline("story-plus", "NAT", STORY);
    let zero = "rule plus ( zero , N:Nat )";
    let succ = "rule plus ( s ( M:Nat ) , N:Nat )";
    for (head, find, replacement) in [
        (zero, "=> N:Nat", "=> zero"),
        (
            succ,
            "s ( plus ( M:Nat , N:Nat ) )",
            "plus ( M:Nat , N:Nat )",
        ),
        (succ, "s ( plus ( M:Nat , N:Nat ) )", "s ( N:Nat )"),
    ] {
        let check = baseline.check(head, &[(find, replacement)]);
        let lifted = accepted(&check).pre_derivation.as_ref().unwrap();
        assert_eq!(
            lifted.id().item_name(),
            if head == zero {
                "plus_zero"
            } else {
                "plus_succ"
            }
        );
    }
}
