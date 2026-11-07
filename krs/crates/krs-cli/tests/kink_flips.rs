//! Condition flips of a KRS package (`krs_cli::kink::condition_flips`): every flip obligation of
//! its guard families, spelled as a K patch of `kink/definition.k` and judged by the front end's
//! checks through the corpus's judge cache.
//!
//! The fixture (`fixtures/guard-mutations`) is a small machine whose `boundary` step is four
//! transitions kept apart by complementary conditions, with an `if`/`else` chain, a 4-bit
//! `k::bits!` decode, two transitions kept apart by a `k::matches!` test, and a transition whose
//! condition reads a looked-up value. The introduction's story package has no guarded sentence.

#![cfg(feature = "kink")]

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use krs_cli::kink::{
    DerivedFlip, DerivedFlips, FlipStatus, KinkRequest, KinkVerb, condition_flips,
};
use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::Value;

const LIBRARY: &str = include_str!("fixtures/guard-mutations/src/lib.rs");
const STORY: &str = include_str!("../../../../docs-site/story/plus/src/lib.rs");
const STORY_FLOW: &str = include_str!("../../../../docs-site/story/plus/kink/FLOW.toml");
const FLOW: &str = "[spec]\nkrs = { definition = \"main\" }\n";

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
        condition_flips(&request, Some(self.target.path()), &mut measurement)
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
    // Every flip of the fixture but the two the next test names is admitted: the generator and
    // KRS's admission agree.
    let refused = flips
        .flips
        .iter()
        .filter(|flip| !admitted(flip))
        .map(|flip| flip.id.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        refused,
        [
            "flip--peek--IntGreater",
            "flip--tag_other+tag_raise--matches"
        ],
        "{:#}",
        flips.value()
    );
}

/// A flip the judge refuses is reported with the judge's reason and detail, not dropped: the
/// condition of `peek` shares its `requires` with the lookup guard KRS writes for `ix[a]`, whose
/// derivation reads more than the edited atom, so the edit is not judged. The two transitions kept
/// apart by a `k::matches!` test that binds nothing have the flip of that test, an atom like any
/// other; the judge cannot yet read the edited `:=K` back to a Rust source, so it is not judged
/// either.
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
    let tag = flip(flips, "flip--tag_other+tag_raise--matches");
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
    let FlipStatus::Refused { reason, detail, .. } = &tag.status else {
        panic!("{:#}", flips.value());
    };
    assert_eq!(reason, "not-judged");
    assert!(detail.contains("does not read a new `:=K`"), "{detail}");
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
    assert_eq!(flips.families, 5, "{:#}", flips.value());
    assert_eq!(flips.flips.len(), 10, "{:#}", flips.value());
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
    // The flips: one entry per judged flip, and the refused one read back as stored.
    assert_eq!(package.cache_entries().len(), flips.flips.len());
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
