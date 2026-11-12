//! `krs kink coverage`'s flips family and `krs kink fuzz --kill <flip-id>`: the condition flips krs
//! derives from the definition (`tests/kink_flips.rs`), handed to kink-flow with the occurrences
//! each changes, deduced unreached or decided by the kill search.
//!
//! The fixture (`fixtures/guard-mutations`) is a small machine whose `boundary` step is four
//! transitions kept apart by complementary conditions, of which `boundary_wake` and
//! `boundary_halted` read `Requested(pending) && halted`, and no rule ever sets `halted`. The
//! corpus never halts, raises one interrupt, decodes one opcode, takes the vector of one high
//! request, and tags, marks and peeks once.

#![cfg(feature = "kink")]

use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::process::Output;
use std::sync::OnceLock;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value, json};

const LIBRARY: &str = include_str!("fixtures/guard-mutations/src/lib.rs");
const NAME: &str = "krs-cli-kink-coverage-flips";

/// The corpus: each case's id and program, in `FLOW.toml` order.
const CASES: [(&str, &str); 7] = [
    ("irq", "raise 1 ; boundary"),
    ("idle", "boundary"),
    ("dec", "exec 3"),
    ("vec", "raise 5 ; vector"),
    ("mark", "mark raise 1"),
    ("tag", "tag raise 1"),
    ("peek", "peek 1"),
];

/// The fixture package with its corpus and a template of the `irq` case, in a fresh directory.
struct Package {
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Package {
    fn new() -> Self {
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let directory = temp_dir();
        let root = directory.path();
        fs::create_dir_all(root.join("src")).unwrap();
        fs::create_dir_all(root.join("kink/cases")).unwrap();
        fs::write(root.join("src/lib.rs"), LIBRARY).unwrap();
        let mut flow = String::from(
            "[spec]\nkrs = { package = \"krs-cli-kink-coverage-flips\", definition = \"main\" }\n",
        );
        for (id, program) in CASES {
            fs::write(
                root.join(format!("kink/cases/{id}.g")),
                format!("{program}\n"),
            )
            .unwrap();
            writeln!(
                flow,
                "\n[[program]]\nid = \"{id}\"\nfile = \"cases/{id}.g\""
            )
            .unwrap();
        }
        fs::write(root.join("kink/FLOW.toml"), flow).unwrap();
        fs::write(
            root.join("kink/TEMPLATES.toml"),
            "[[template]]\nid = \"irq\"\nprogram = \"irq\"\n\n  [[template.hole]]\n  name = \"N\"\n  \
             sort = \"Int\"\n  find = \"1\"\n  literal = \"1\"\n  range = { min = 0, max = 4 }\n",
        )
        .unwrap();
        fs::write(
            root.join("Cargo.toml"),
            format!(
                "[package]\nname = \"{NAME}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"FLIPS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
                serde_json::to_string(krs.to_str().unwrap()).unwrap(),
            ),
        )
        .unwrap();
        Self {
            directory,
            target: shared_fixture_target(),
        }
    }

    /// `krs kink VERB ARGUMENTS` with this package selected, from its directory.
    fn kink(&self, verb: &str, arguments: &[&str]) -> Output {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        process
            .current_dir(self.directory.path())
            .args(["kink", verb])
            .args(arguments)
            .args(["--package", NAME, "--definition", "main"])
            .output()
            .unwrap()
    }
}

fn json_of(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn status(output: &Output) -> Option<i32> {
    output.status.code()
}

/// The fixture package and its first coverage document (a cold run: nothing cached).
fn covered() -> &'static (Package, Value) {
    static COVERED: OnceLock<(Package, Value)> = OnceLock::new();
    COVERED.get_or_init(|| {
        let package = Package::new();
        let output = package.kink("coverage", &[]);
        assert_eq!(
            status(&output),
            Some(0),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let document = json_of(&output);
        (package, document)
    })
}

/// The flips family's item `id`.
fn item<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["families"]["flips"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|item| item["id"] == id)
        .unwrap_or_else(|| panic!("no flip {id}: {:#}", document["families"]["flips"]))
}

/// The rules family's item of the KRS item `name`.
fn rule<'d>(document: &'d Value, name: &str) -> &'d Value {
    document["families"]["rules"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|rule| rule["krs"]["item"] == name)
        .unwrap_or_else(|| panic!("no rule {name}"))
}

/// The flip of the interrupt request across the halted machine's two transitions changes only
/// runs of a halted machine: the corpus never halts, so no case distinguishes it, and every case
/// ran the mutant. Its occurrences are reached: `boundary_wake` tests `Requested(pending)` before
/// `halted`, so the request is evaluated, true for `irq` and false for `idle`; a corpus that
/// reaches an atom without distinguishing its flip is told which values it reached.
#[test]
fn the_interrupt_request_flip_is_undistinguished_on_a_corpus_that_never_halts() {
    let (_, document) = covered();
    let requested = item(document, "flip--boundary_halted+boundary_wake--Requested");
    assert_eq!(requested["status"], "undistinguished", "{requested:#}");
    assert_eq!(requested["killer"], Value::Null, "{requested:#}");
    assert_eq!(requested["text"], "Requested(pending)", "{requested:#}");
    assert_eq!(requested["live_runs"], CASES.len(), "{requested:#}");
    let wake = requested["occurrences"]
        .as_array()
        .unwrap()
        .iter()
        .find(|occurrence| occurrence["rule"] == "rule:crate::boundary_wake")
        .unwrap_or_else(|| panic!("{requested:#}"));
    assert_eq!(wake["path"], "0.0", "{wake:#}");
    assert_eq!(wake["true_by"], json!(["irq"]), "{wake:#}");
    assert_eq!(wake["false_by"], json!(["idle"]), "{wake:#}");
    let target = document["targets"]
        .as_array()
        .unwrap()
        .iter()
        .find(|target| target["item"] == requested["id"])
        .unwrap_or_else(|| panic!("{:#}", document["targets"]));
    assert_eq!(
        target["fuzz"],
        format!(
            "krs kink fuzz --package {NAME} --definition main --template ID --kill \
             flip--boundary_halted+boundary_wake--Requested"
        ),
        "{target:#}"
    );
}

/// The flips of `VectorOf`'s later branches change only what a request below 4 takes; the corpus's
/// one vector is of a request of 5, so no case reaches either: each is deduced unreached, with no
/// mutant run, and waits on its tier-1 obligations.
#[test]
fn a_flip_whose_operands_no_case_reached_is_unreached_with_no_mutant_run() {
    let (_, document) = covered();
    for id in [
        "flip--vector_of_2+vector_of_3+vector_of_4--IntGreaterEqual",
        "flip--vector_of_3+vector_of_4--IntGreaterEqual",
    ] {
        let flip = item(document, id);
        assert_eq!(flip["status"], "unreached", "{flip:#}");
        assert_eq!(flip["live_runs"], 0, "{flip:#}");
        assert_eq!(flip["calls"], 0, "{flip:#}");
        assert_eq!(flip["killer"], Value::Null, "{flip:#}");
        assert!(!flip["waits_on"].as_array().unwrap().is_empty(), "{flip:#}");
        for occurrence in flip["occurrences"].as_array().unwrap() {
            assert_eq!(occurrence["reached_by"], json!([]), "{flip:#}");
            assert_eq!(occurrence["undecided_by"], json!([]), "{flip:#}");
            assert_eq!(occurrence["unplaced"], Value::Null, "{flip:#}");
        }
    }
    // The first branch's flip reaches `p >= 4` in `vector_of_1`, so it runs, and `vec` kills it.
    let first = item(document, "flip--vector_of_1+3--IntGreaterEqual");
    assert_eq!(first["status"], "distinguished", "{first:#}");
    assert_eq!(first["killer"], "vec", "{first:#}");
}

/// A distinguished flip names its killer, the first killing case in the corpus's order: `irq`
/// raises a request the machine dispatches, which the flip of `Dispatches` steps over; the bit
/// flips of the decode table are killed by the one case that decodes; the flips of the
/// `k::matches!` test that keeps the `tag` transitions apart, and of the one `mark_raise` reads,
/// are killed by the case that tags and the case that marks.
#[test]
fn a_distinguished_flip_names_its_killer() {
    let (_, document) = covered();
    for (id, killer) in [
        ("flip--boundary_dispatch+boundary_step--Dispatches", "irq"),
        ("flip--boundary_dispatch+3--halted", "irq"),
        ("flip--mark_held+mark_raise--ime", "mark"),
        ("flip--tag_other+tag_raise--matches", "tag"),
        ("flip--mark_raise--matches", "mark"),
        ("bitflip--decode_dec+decode_inc--bit0", "dec"),
        ("bitflip--decode_dec+decode_inc+decode_load--bit3", "dec"),
    ] {
        let flip = item(document, id);
        assert_eq!(flip["status"], "distinguished", "{flip:#}");
        assert_eq!(flip["killer"], killer, "{flip:#}");
    }
    // A bit flip's occurrences are its arms' matches, reached where the templates matched.
    let bits = item(document, "bitflip--decode_dec+decode_inc--bit0");
    let reached = bits["occurrences"]
        .as_array()
        .unwrap()
        .iter()
        .map(|occurrence| {
            (
                occurrence["rule"].clone(),
                occurrence["reach"].clone(),
                occurrence["reached_by"].clone(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        reached,
        [
            (
                json!("rule:crate::decode_dec"),
                json!("match"),
                json!(["dec"])
            ),
            (json!("rule:crate::decode_inc"), json!("match"), json!([])),
        ],
        "{bits:#}"
    );
}

/// The flip of `mark_held`'s `k::matches!` test changes only runs where `ime` is false, since the
/// test is conjoined with `!ime`; the one case that marks does so with `ime` true, so no case
/// distinguishes it, and every case ran the mutant.
#[test]
fn a_matches_flip_beside_a_false_atom_is_undistinguished() {
    let (_, document) = covered();
    let held = item(document, "flip--mark_held--matches");
    assert_eq!(held["status"], "undistinguished", "{held:#}");
    assert_eq!(held["killer"], Value::Null, "{held:#}");
    assert_eq!(held["live_runs"], CASES.len(), "{held:#}");
}

/// A flip the front end's judge refuses is listed with the judge's reason and next step, and is
/// not counted: the measure is distinguished over the obligations less the refused ones.
#[test]
fn a_refused_flip_is_listed_with_its_reason() {
    let (_, document) = covered();
    let peek = item(document, "flip--peek--IntGreater");
    assert_eq!(peek["status"], "refused", "{peek:#}");
    assert_eq!(peek["judge"], "front-end", "{peek:#}");
    assert_eq!(peek["reason"], "not-judged", "{peek:#}");
    assert!(peek["next"].is_string(), "{peek:#}");
    assert!(
        peek["detail"]
            .as_str()
            .unwrap()
            .contains("a lookup guard KRS inserts"),
        "{peek:#}"
    );
    let family = &document["families"]["flips"];
    assert_eq!(family["run"], true, "{family:#}");
    assert_eq!(
        family["counts"],
        json!({"distinguished": 8, "undistinguished": 2, "unreached": 2, "unknown": 0,
               "refused": 1, "equivalent": 0, "not_generated": 0, "argued": 0}),
        "{family:#}"
    );
    assert_eq!(family["obligations"], 13, "{family:#}");
    assert_eq!(family["counted"], 12, "{family:#}");
}

/// Every occurrence of every flip of the fixture is placed in its sentence's guard row, at the
/// node that renders the flipped atom: the operand at the occurrence's path reads as the flip's
/// atom where the Rust source names it.
#[test]
fn every_occurrence_names_the_guard_node_of_the_flipped_atom() {
    let (_, document) = covered();
    for flip in document["families"]["flips"]["items"].as_array().unwrap() {
        let occurrences = flip["occurrences"].as_array().unwrap();
        assert!(!occurrences.is_empty(), "{flip:#}");
        for occurrence in occurrences {
            assert_eq!(occurrence["unplaced"], Value::Null, "{flip:#}");
            if occurrence["reach"] != "operand" {
                continue;
            }
            let name = occurrence["rule"]
                .as_str()
                .and_then(|id| id.strip_prefix("rule:"))
                .unwrap_or_else(|| panic!("{flip:#}"));
            let operand = rule(document, name)["guard"]["operands"]
                .as_array()
                .unwrap()
                .iter()
                .find(|operand| operand["path"] == occurrence["path"])
                .unwrap_or_else(|| panic!("{flip:#}"));
            assert_eq!(operand["kind"], "atom", "{operand:#}\n{flip:#}");
            // A `k::matches!` test's authored tokens include its binder's occurrence in the
            // left-hand side, so its text is read per sentence; every other atom reads alike.
            if flip["atom"]["head"] != "matches" {
                assert_eq!(
                    operand["krs"]["text"], flip["text"],
                    "{operand:#}\n{flip:#}"
                );
            }
        }
    }
}

/// The coverage output is a function of the definition and the corpus: a second run, deciding
/// every flip from the outcome cache, renders the same verdicts, and a copy of the package in
/// another directory, run cold, gives the same flips (apart from how many runs were live) and
/// the same rendering. Under `--tier 1` the family shows how many obligations it has and no
/// status.
#[test]
fn the_flips_and_their_coverage_are_byte_stable() {
    let (package, document) = covered();
    let warm = package.kink("coverage", &["--output", "verdicts"]);
    assert_eq!(status(&warm), Some(0));
    let copy = Package::new();
    let cold = copy.kink("coverage", &[]);
    assert_eq!(status(&cold), Some(0));
    let without_live = |document: &Value| {
        let mut items = document["families"]["flips"]["items"].clone();
        for item in items.as_array_mut().unwrap() {
            item["live_runs"] = Value::Null;
        }
        serde_json::to_string(&items).unwrap()
    };
    assert_eq!(without_live(&json_of(&cold)), without_live(document));
    let rendered = copy.kink("coverage", &["--output", "verdicts"]);
    assert_eq!(
        String::from_utf8_lossy(&rendered.stdout),
        String::from_utf8_lossy(&warm.stdout)
    );
    assert!(
        String::from_utf8_lossy(&warm.stdout).contains("[[coverage.flip]]"),
        "{}",
        String::from_utf8_lossy(&warm.stdout)
    );

    let tier_one = json_of(&package.kink("coverage", &["--tier", "1"]));
    let family = &tier_one["families"]["flips"];
    assert_eq!(family["run"], false, "{family:#}");
    assert_eq!(family["obligations"], 13, "{family:#}");
    assert_eq!(family["items"], json!([]), "{family:#}");
}

/// `fuzz --kill <flip-id>` resolves a derived flip to its admitted edits and searches for a case
/// that kills it, confirmed by kink's own run; a refused flip's id is refused with the judge's
/// reason; an id that is no flip and no mutation of a list is refused naming both.
#[test]
fn fuzz_kill_resolves_a_flip_id() {
    let (package, _) = covered();
    let output = package.kink(
        "fuzz",
        &[
            "--template",
            "irq",
            "--kill",
            "flip--boundary_dispatch+boundary_step--Dispatches",
            "--cases",
            "4",
        ],
    );
    let document = json_of(&output);
    assert_eq!(status(&output), Some(0), "{document:#}");
    assert_eq!(document["job"]["flip"], true, "{document:#}");
    assert_eq!(document["job"]["outcome"], "fuzzed", "{document:#}");
    assert_eq!(document["program"]["confirmed"], true, "{document:#}");

    let output = package.kink(
        "fuzz",
        &["--template", "irq", "--kill", "flip--peek--IntGreater"],
    );
    let document = json_of(&output);
    assert_eq!(status(&output), Some(2), "{document:#}");
    assert_eq!(document["stopped"], "refused", "{document:#}");
    assert_eq!(document["job"]["status"], "refused", "{document:#}");
    assert_eq!(
        document["job"]["refusal"]["stage"], "mutation",
        "{document:#}"
    );
    assert_eq!(
        document["job"]["refusal"]["reason"], "not-judged",
        "{document:#}"
    );
    assert!(
        document["action"].as_str().unwrap().starts_with(&format!(
            "no mutant stands for a refused flip (`krs kink coverage --package {NAME} \
             --definition main` lists it refused): "
        )),
        "{document:#}"
    );

    let output = package.kink("fuzz", &["--template", "irq", "--kill", "flip--nope"]);
    let document = json_of(&output);
    assert_eq!(status(&output), Some(2), "{document:#}");
    assert_eq!(
        document["job"]["refusal"]["reason"], "unknown-mutation",
        "{document:#}"
    );
    assert_eq!(
        document["job"]["refusal"]["detail"],
        "no condition flip the front end derives has this id (13 flips)",
        "{document:#}"
    );
}
