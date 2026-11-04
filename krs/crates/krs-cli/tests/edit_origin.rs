//! The generated-only edit judge over K that `krs emit-k` writes: an edit that changes only
//! nodes KRS inserted is refused, naming the sentence's Rust item, what KRS inserted and the
//! authored node to edit instead with its Rust bytes; an edit of authored syntax (a `k::bits!`
//! template's literal or field read, an `else`'s negation, an operator, a constant at one use,
//! a `..` the author wrote, a whole rule, a rule's label) goes to the re-derivation, which the
//! judge never answers for; a mutation whose tokens are the baseline's, a change outside every
//! sentence, an edit of a declaration and an edit inside a lookup-guard or local-function family
//! are refused. A mutation is judged by the tokens it changes, however its find is written.

use std::fs;
use std::path::{Path, PathBuf};

use krs_compiler::{
    DEFINITION_ARTIFACT, EditJudgement, InsertedNodeRef, KEdit, MutationVerdict, SentenceVerdict,
    SourceMap, judge_edits,
};
use krs_ir::InsertedNode;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// The package `inserted_nodes.rs` takes its census of.
const PACKAGE: &str = include_str!("fixtures/inserted-nodes/src/lib.rs");

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
                "bitRangeInt(Krs_Bits0:Int, 0, 3)",
                "bitRangeInt(Y:Int, 0, 3)"
            )]
        ),
        [(
            "Krs_Bits0:Int".to_owned(),
            InsertedNode::GeneratedBinder,
            Some("bitRangeInt(Krs_Bits0:Int, 0, 3)".to_owned()),
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
        &[emitted.edit(
            "rule [save]",
            "( 1 #as Krs_UpdateFPc:Int )",
            "( 1 #as P:Int )",
        )],
    );
    assert_eq!(update.len(), 1);
    assert_eq!(
        (update[0].0.as_str(), update[0].1),
        ("( 1 #as Krs_UpdateFPc:Int )", InsertedNode::GeneratedBinder)
    );

    // Authored: renderings of authored syntax and frames the author wrote need the
    // re-derivation, at the node the edit changes.
    let bits = "rule [bits]";
    assert_eq!(
        emitted.to_rederivation(
            "bits",
            &[emitted.edit(
                bits,
                "(bitRangeInt(Krs_Bits0:Int, 3, 1)) ==Int 0",
                "(bitRangeInt(Krs_Bits0:Int, 3, 1)) ==Int 1"
            )]
        ),
        ["0"]
    );
    assert_eq!(
        emitted.to_rederivation(
            "bits",
            &[emitted.edit(
                bits,
                "bitRangeInt(Krs_Bits0:Int, 0, 3)",
                "bitRangeInt(Krs_Bits0:Int, 0, 4)"
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
