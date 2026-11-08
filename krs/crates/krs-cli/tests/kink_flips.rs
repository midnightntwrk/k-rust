//! Condition flips of a KRS package (`krs_cli::kink::condition_flips`): every flip obligation of
//! its guard families, spelled as a K patch of `kink/definition.k` and judged by the front end's
//! checks through the corpus's judge cache.
//!
//! The fixture (`fixtures/guard-mutations`) is a small machine whose `boundary` step is four
//! transitions kept apart by complementary conditions, with an `if`/`else` chain, a 4-bit
//! `k::bits!` decode, two transitions kept apart by a `k::matches!` test, two transitions that
//! share a `k::matches!` test and are kept apart by `ime` beside it, and a transition whose
//! condition reads a looked-up value; a variant adds a guarded function only a claim applies. The
//! introduction's story package has no guarded sentence.

#![cfg(feature = "kink")]

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use krs_cli::kink::{
    DerivedFlip, DerivedFlips, FlipStatus, KinkRequest, KinkVerb, condition_flips_reading,
};
use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::Value;

const LIBRARY: &str = include_str!("fixtures/guard-mutations/src/lib.rs");
const STORY: &str = include_str!("../../../../docs-site/story/plus/src/lib.rs");
const STORY_FLOW: &str = include_str!("../../../../docs-site/story/plus/kink/FLOW.toml");
const FLOW: &str = "[spec]\nkrs = { definition = \"main\" }\n";
/// Added to the fixture: a function only a claim applies, an `if`/`else` on an `Int`, so its two
/// equations are a guard family of claim helpers.
const CLAIMED: &str = r#"
/// The vector a claim expects of a raised request.
#[k::function(total, internal)]
pub fn ExpectedVector(p: Term<Int>) -> Term<Int> {
    if p >= 1 { 64 } else { 0 }
}

#[k::claim(all_paths, label = "raise-expected")]
pub fn raise_expected(
    p: Term<Int>,
    k::cells! { k: k::configuration::KCell(CmdSyntax::Raise(p), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(CmdSyntax::Raise(ExpectedVector(p)), ..tail), ..state }
}
"#;

/// A package holding `library` and a corpus manifest `flow`, in a fresh directory.
struct Package {
    name: &'static str,
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Package {
    fn new(name: &'static str, namespace: &str, library: &str, flow: &str) -> Self {
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let directory = temp_dir();
        let root = directory.path();
        fs::create_dir_all(root.join("src")).unwrap();
        fs::create_dir_all(root.join("kink")).unwrap();
        fs::write(root.join("src/lib.rs"), library).unwrap();
        fs::write(root.join("kink/FLOW.toml"), flow).unwrap();
        fs::write(
            root.join("Cargo.toml"),
            format!(
                "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
                serde_json::to_string(krs.to_str().unwrap()).unwrap(),
            ),
        )
        .unwrap();
        Self {
            name,
            directory,
            target: shared_fixture_target(),
        }
    }

    fn path(&self) -> &Path {
        self.directory.path()
    }

    /// The package's condition flips, judged in this process.
    fn flips(&self) -> DerivedFlips {
        self.flips_reading(None)
    }

    /// The package's condition flips, judged in this process reading the authored sources from
    /// `authored` when given, in place of the package's directory.
    fn flips_reading(&self, authored: Option<&Path>) -> DerivedFlips {
        let request = KinkRequest {
            manifest_path: self.path().join("Cargo.toml"),
            root: krs_cli::FacetSelector {
                package: krs_cli::PackageSelector::Name(self.name.into()),
                definition: "main".into(),
            },
            dependencies: Vec::new(),
            cfg: Vec::new(),
            registration: krs_cli::RegistrationMode::Inventory,
            profile: None,
            message_format: krs_cli::MessageFormat::Human,
            corpus: None,
            locked: false,
            verb: KinkVerb::Emit { check: false },
        };
        let mut measurement = krs_ir::measure::Measurement::default();
        condition_flips_reading(
            &request,
            Some(self.target.path()),
            &mut measurement,
            authored,
        )
        .unwrap_or_else(|outcome| panic!("no flips: {:?}", outcome.notes))
    }

    /// `krs kink VERB ARGUMENTS` with this package selected, from its directory.
    fn kink(&self, verb: &str, arguments: &[&str]) -> Value {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        let output = process
            .current_dir(self.path())
            .args(["kink", verb])
            .args(arguments)
            .args(["--package", self.name, "--definition", "main"])
            .output()
            .unwrap();
        serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
            panic!(
                "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            )
        })
    }

    /// The judge cache entries of the corpus, as files.
    fn cache_entries(&self) -> Vec<PathBuf> {
        let mut entries = fs::read_dir(self.path().join("kink/.kink-flow/krs-judge"))
            .map(|entries| {
                entries
                    .map(|entry| entry.unwrap().path())
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        entries.sort();
        entries
    }
}

/// The fixture package and its flips, derived once.
fn fixture() -> &'static (Package, DerivedFlips) {
    static FIXTURE: OnceLock<(Package, DerivedFlips)> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let package = Package::new("krs-cli-kink-flips", "FLIPS", LIBRARY, FLOW);
        let flips = package.flips();
        (package, flips)
    })
}

/// A second copy of the fixture package in another directory, its flips derived once, and the
/// lock its judge-cache test holds.
fn copy() -> &'static (Package, DerivedFlips, Mutex<()>) {
    static COPY: OnceLock<(Package, DerivedFlips, Mutex<()>)> = OnceLock::new();
    COPY.get_or_init(|| {
        let package = Package::new("krs-cli-kink-flips", "FLIPS", LIBRARY, FLOW);
        let flips = package.flips();
        (package, flips, Mutex::new(()))
    })
}

fn flip<'d>(flips: &'d DerivedFlips, id: &str) -> &'d DerivedFlip {
    flips
        .flips
        .iter()
        .find(|flip| flip.id == id)
        .unwrap_or_else(|| panic!("no flip {id}: {:#}", flips.value()))
}

/// Each edit of `flip` as `(rule, find, replace)`.
fn edits(flip: &DerivedFlip) -> Vec<(String, String, String)> {
    flip.edits
        .iter()
        .map(|edit| match &edit.action {
            kink_flow::EditAction::Replace { find, replace } => {
                (edit.rule.clone().unwrap(), find.clone(), replace.clone())
            }
            kink_flow::EditAction::Delete => panic!("a flip deletes no rule"),
        })
        .collect()
}

fn admitted(flip: &DerivedFlip) -> bool {
    matches!(flip.status, FlipStatus::Admitted { .. })
}

fn triples(rows: &[(&str, &str, &str)]) -> Vec<(String, String, String)> {
    rows.iter()
        .map(|(rule, find, replace)| ((*rule).into(), (*find).into(), (*replace).into()))
        .collect()
}

/// A flip that swaps two encodings of the decode table, and a flip of an `if`/`else` chain's first
/// condition in every branch that renders it, are definitions KRS admits: the K patch of each is
/// the emission of a Rust source (the two templates' bit 0 exchanged; `if !(p >= 4)`).
#[test]
fn a_bit_pair_flip_and_a_chain_flip_are_judged() {
    let (_, flips) = fixture();
    let bits = flip(flips, "bitflip--decode_dec+decode_inc--bit0");
    assert!(admitted(bits), "{:#}", flips.value());
    assert_eq!(
        edits(bits),
        triples(&[
            (
                "flips--decode_dec",
                "(bitRangeInt(Bits:Int, 0, 1)) ==Int 1",
                "(bitRangeInt(Bits:Int, 0, 1)) ==Int 0"
            ),
            (
                "flips--decode_inc",
                "(bitRangeInt(Bits:Int, 0, 1)) ==Int 0",
                "(bitRangeInt(Bits:Int, 0, 1)) ==Int 1"
            ),
        ])
    );
    let chain = flip(flips, "flip--vector_of_1+3--IntGreaterEqual");
    assert!(admitted(chain), "{:#}", flips.value());
    assert!(chain.whole);
    assert_eq!(
        edits(chain),
        triples(&[
            (
                "flips--vector_of_1",
                "P:Int >=Int 4",
                "(notBool (P:Int >=Int 4))"
            ),
            (
                "flips--vector_of_2",
                "notBool (P:Int >=Int 4)",
                "P:Int >=Int 4"
            ),
            (
                "flips--vector_of_3",
                "notBool (P:Int >=Int 4)",
                "P:Int >=Int 4"
            ),
            (
                "flips--vector_of_4",
                "notBool (P:Int >=Int 4)",
                "P:Int >=Int 4"
            ),
        ])
    );
    // The flip of the interrupt request across the halted machine's two transitions, which a
    // corpus that never halts cannot tell apart.
    let requested = flip(flips, "flip--boundary_halted+boundary_wake--Requested");
    assert!(admitted(requested), "{:#}", flips.value());
    assert_eq!(
        edits(requested),
        triples(&[
            (
                "boundary-halted",
                "notBool requested ( Pending:Int )",
                "requested ( Pending:Int )"
            ),
            (
                "boundary-wake",
                "requested ( Pending:Int )",
                "(notBool (requested ( Pending:Int )))"
            ),
        ])
    );
    // Every flip of the fixture but the one the next test names is admitted: the generator and
    // KRS's admission agree.
    let refused = flips
        .flips
        .iter()
        .filter(|flip| !admitted(flip))
        .map(|flip| flip.id.as_str())
        .collect::<Vec<_>>();
    assert_eq!(refused, ["flip--peek--IntGreater"], "{:#}", flips.value());
}

/// A flip the judge refuses is reported with the judge's reason and detail, not dropped: the
/// condition of `peek` shares its `requires` with the lookup guard KRS writes for `ix[a]`, whose
/// derivation reads more than the edited atom, so the edit is not judged.
#[test]
fn a_flip_the_judge_refuses_is_reported_with_its_reason() {
    let (_, flips) = fixture();
    let peek = flip(flips, "flip--peek--IntGreater");
    let FlipStatus::Refused {
        reason,
        next,
        detail,
    } = &peek.status
    else {
        panic!("{:#}", flips.value());
    };
    assert_eq!(reason, "not-judged");
    assert!(next.is_some());
    assert!(detail.contains("a lookup guard KRS inserts"), "{detail}");
    assert!(
        detail.starts_with("`peek` (crate::peek, src/lib.rs:"),
        "{detail}"
    );
}

/// The two transitions kept apart by a `k::matches!` test that binds nothing have the flip of that
/// test, an atom like any other: a `:=K` whose pattern names only `_` is a Boolean test, which a
/// source writes as `k::matches!(..)` or `!k::matches!(..)`, so the test moved out of `notBool` in
/// `tag_other` and into it in `tag_raise` is a definition KRS admits.
#[test]
fn a_flip_of_a_matches_test_that_binds_nothing_is_admitted() {
    let (_, flips) = fixture();
    let tag = flip(flips, "flip--tag_other+tag_raise--matches");
    assert!(admitted(tag), "{:#}", flips.value());
    assert!(tag.whole);
    assert_eq!(
        edits(tag),
        triples(&[
            (
                "tag-other",
                "notBool ( raise _ :=K Next:Cmd )",
                "( raise _ :=K Next:Cmd )"
            ),
            (
                "tag-raise",
                "( raise _ :=K Next:Cmd )",
                "(notBool (( raise _ :=K Next:Cmd )))"
            ),
        ])
    );
}

/// A condition that conjoins a `k::matches!` test with another atom is flipped in that atom, the
/// test left as written: the `mark` transitions share the test and are kept apart by `ime`, and
/// the flip of `ime` is a definition KRS admits (`k::matches!(next, Raise { .. }) && !ime` and
/// `... && ime` exchanged). In `mark_raise` the edit's `find` holds the rendered test, since
/// `Ime:Bool` alone also occurs in the sentence's `<ime>` cell. The shared test is flipped in each
/// transition alone, and, as the `tag` pair's, is a definition KRS admits
/// (`!k::matches!(next, Raise { .. }) && ime` in `mark_raise`, `... && !ime` in `mark_held`).
#[test]
fn a_flip_beside_a_matches_test_is_admitted() {
    let (_, flips) = fixture();
    let ime = flip(flips, "flip--mark_held+mark_raise--ime");
    assert!(admitted(ime), "{:#}", flips.value());
    assert!(ime.whole);
    assert_eq!(
        edits(ime),
        triples(&[
            ("mark-held", "notBool Ime:Bool", "Ime:Bool"),
            (
                "mark-raise",
                "( raise _ :=K Next:Cmd ) andThenBool Ime:Bool",
                "( raise _ :=K Next:Cmd ) andThenBool (notBool (Ime:Bool))"
            ),
        ])
    );
    for (id, rule) in [
        ("flip--mark_held--matches", "mark-held"),
        ("flip--mark_raise--matches", "mark-raise"),
    ] {
        let matches = flip(flips, id);
        assert!(admitted(matches), "{:#}", flips.value());
        assert!(!matches.whole);
        assert_eq!(
            edits(matches),
            triples(&[(
                rule,
                "( raise _ :=K Next:Cmd )",
                "(notBool (( raise _ :=K Next:Cmd )))"
            )])
        );
    }
}

/// Generation and judgement are functions of the definition: a second copy of the package, built
/// and judged with a cache of its own, gives byte-identical flips.
#[test]
fn generation_is_byte_stable() {
    let (_, flips) = fixture();
    let (_, again, _) = copy();
    assert_eq!(
        serde_json::to_string(&again.value()).unwrap(),
        serde_json::to_string(&flips.value()).unwrap()
    );
    assert_eq!(flips.families, 6, "{:#}", flips.value());
    assert_eq!(flips.flips.len(), 13, "{:#}", flips.value());
}

/// A flip that changes only claim helpers is not generated, and is neither spelled nor judged:
/// the equations of `ExpectedVector`, which only a claim applies, are no obligation of any
/// coverage family, so the flip of its condition is a `claim-helper` entry under
/// `not_generated`, and the fixture's flips and other entries are the same as without it.
#[test]
fn a_flip_of_claim_helpers_alone_is_not_generated() {
    let (_, base) = fixture();
    let package = Package::new(
        "krs-cli-kink-flips",
        "FLIPS",
        &format!("{LIBRARY}{CLAIMED}"),
        FLOW,
    );
    let flips = package.flips();
    let helpers = ["flips--expected_vector_1", "flips--expected_vector_2"];
    assert!(
        flips.flips.iter().all(|flip| flip
            .sentences
            .iter()
            .all(|sentence| !helpers.contains(&sentence.label.as_str()))),
        "{:#}",
        flips.value()
    );
    let ids = |flips: &DerivedFlips| {
        flips
            .flips
            .iter()
            .map(|flip| flip.id.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(ids(&flips), ids(base), "{:#}", flips.value());
    // One judge cache entry per flip: the helper's flip was not judged.
    assert_eq!(package.cache_entries().len(), flips.flips.len());
    assert_eq!(flips.families, base.families + 1, "{:#}", flips.value());
    let (claimed, others): (Vec<_>, Vec<_>) = flips
        .not_generated
        .iter()
        .cloned()
        .partition(|not| not.reason == "claim-helper");
    assert_eq!(others, base.not_generated, "{:#}", flips.value());
    let [claimed] = claimed.as_slice() else {
        panic!("{:#}", flips.value());
    };
    let id = claimed.id.as_deref().unwrap();
    assert_eq!(claimed.sentences, helpers, "{:#}", flips.value());
    assert!(claimed.atom.is_some());
    assert_eq!(claimed.pair, None);
    assert!(
        claimed.detail.starts_with(&format!(
            "`{id}` changes only claim helpers (`flips--expected_vector_1`, \
             `flips--expected_vector_2`, equations of `ExpectedVector`, "
        )),
        "{}",
        claimed.detail
    );
    // The entry names its flip as kink-flow names one it moves out of scope; the generator's
    // own entries name none.
    let value = flips.value();
    for entry in value["not_generated"].as_array().unwrap() {
        if entry["reason"] == "claim-helper" {
            assert_eq!(entry["id"], id, "{entry:#}");
        } else {
            assert_eq!(entry.get("id"), None, "{entry:#}");
        }
    }
}

/// The front end's judgements are read back from the corpus's judge cache, by the flips and by
/// `check --mutations` alike: an entry rewritten in place is what the next command reports.
#[test]
fn judgements_come_from_the_judge_cache() {
    let (package, flips, lock) = copy();
    let _turn = lock
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let tamper = |marker: &str| {
        let mut changed = 0;
        for entry in package.cache_entries() {
            let text = fs::read_to_string(&entry).unwrap();
            if text.contains("a lookup guard KRS inserts") {
                fs::write(&entry, text.replace("a lookup guard KRS inserts", marker)).unwrap();
                changed += 1;
            }
        }
        changed
    };
    // The flips: one entry per judged flip, read back as the judge gave it, and the refused one
    // read back as stored.
    assert_eq!(package.cache_entries().len(), flips.flips.len());
    assert_eq!(package.flips().value(), flips.value());
    assert_eq!(tamper("a stored lookup guard"), 1);
    let again = package.flips();
    let FlipStatus::Refused { detail, .. } = &flip(&again, "flip--peek--IntGreater").status else {
        panic!("{:#}", again.value());
    };
    assert!(detail.contains("a stored lookup guard"), "{detail}");

    // `check --mutations` of the same patch: the krs executable is another build, so it judges
    // the mutation once and writes its own entry, which the next check reads.
    let peek = flip(flips, "flip--peek--IntGreater");
    let mut list = String::from(
        "[[mutation]]\nid = \"peek\"\nmisunderstanding = \"the looked-up value's bound is the \
         other way\"\n",
    );
    for (rule, find, replace) in edits(peek) {
        for (key, value) in [
            ("\n[[mutation.edit]]\nrule", rule),
            ("find", find),
            ("replace", replace),
        ] {
            list += key;
            list += " = ";
            list += &serde_json::to_string(&value).unwrap();
            list += "\n";
        }
    }
    fs::create_dir_all(package.path().join("kink/mutations")).unwrap();
    fs::write(package.path().join("kink/mutations/peek.toml"), list).unwrap();
    let refusal = |document: &Value| {
        document["mutations"][0]["refusals"][0]["detail"]
            .as_str()
            .unwrap_or_else(|| panic!("{document:#}"))
            .to_owned()
    };
    let checked = package.kink("check", &[]);
    assert!(
        refusal(&checked).contains("a lookup guard KRS inserts"),
        "{checked:#}"
    );
    assert_eq!(package.cache_entries().len(), flips.flips.len() + 1);
    assert_eq!(tamper("a checked lookup guard"), 1);
    let checked = package.kink("check", &[]);
    assert!(
        refusal(&checked).contains("a checked lookup guard"),
        "{checked:#}"
    );
}

/// A cache entry holds what a judgement of its key gives, so a judgement that cannot read an
/// authored source is not written: with `src/lib.rs` read from another revision than the build's,
/// the flips are judged, their Rust locations without positions, and no entry is written; the next
/// judgement, reading the build's revision, is written with its positions.
#[test]
fn a_judgement_that_cannot_read_its_source_is_not_cached() {
    let package = Package::new("krs-cli-kink-flips", "FLIPS", LIBRARY, FLOW);
    let elsewhere = temp_dir();
    fs::create_dir_all(elsewhere.path().join("src")).unwrap();
    fs::write(
        elsewhere.path().join("src/lib.rs"),
        format!("// another revision\n{LIBRARY}"),
    )
    .unwrap();
    let unread = package.flips_reading(Some(elsewhere.path()));
    assert!(!unread.flips.is_empty(), "{:#}", unread.value());
    assert_eq!(package.cache_entries(), Vec::<PathBuf>::new());

    let read = package.flips();
    let outcomes = |flips: &DerivedFlips| {
        flips
            .flips
            .iter()
            .map(|flip| (flip.id.clone(), admitted(flip)))
            .collect::<Vec<_>>()
    };
    assert_eq!(outcomes(&unread), outcomes(&read));
    let entries = package.cache_entries();
    assert_eq!(entries.len(), read.flips.len());
    let mut positioned = 0;
    for entry in entries {
        let stored: Value = serde_json::from_str(&fs::read_to_string(&entry).unwrap()).unwrap();
        for edit in stored["judged"]["edits"].as_array().unwrap() {
            if edit["judged"] != "authored" && edit["judged"] != "inserted" {
                continue;
            }
            for span in edit["rust"].as_array().unwrap() {
                assert!(
                    span["line"].is_u64() && span["text"].is_string(),
                    "{stored:#}"
                );
                positioned += 1;
            }
        }
    }
    assert!(positioned > 0);
}

/// The story's rules have no guard and no `k::bits!` argument, so it has no flip, and says so.
#[test]
fn the_story_has_no_flip_and_says_why() {
    let package = Package::new("story-plus", "NAT", STORY, STORY_FLOW);
    let flips = package.flips();
    assert_eq!(flips.families, 0);
    assert!(flips.flips.is_empty());
    assert!(flips.not_generated.is_empty());
    assert_eq!(
        flips.none_reason().as_deref(),
        Some(
            "no sentence of the definition has a guard or a k::bits! argument, so no sentences \
             are kept apart by a condition a flip could negate"
        )
    );
    assert_eq!(flips.value()["none"], flips.none_reason().unwrap().as_str());
}
