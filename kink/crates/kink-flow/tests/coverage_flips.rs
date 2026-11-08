//! The flips family of `coverage` (tier 2): a front end's derived flips, each deduced unreached
//! with no mutant run or run by the kill search, on the guards fixture, whose corpus never halts
//! (so `I` is never reached in `wake` and `halted`) and writes only address 0 (so swapping `low`
//! and `high` changes no result); and the coverage lock (`--lock`, `--locked`), which records each
//! distinguished flip's killer by the killer-record rule.

mod flow_support;

use flow_support::{copy_dir, flow};
use kink_flow::{
    CommandFiles, EditAction, EditSpec, FlowCommand, FlowManifest, FrontEnd,
    cli::{EXIT_NO, EXIT_UNASKED, EXIT_YES, dispatch},
    flips::{Derived, DerivedEntry, DerivedList, Judged, Occurrence, Reach},
    lock::stale_lines,
    verdicts::verdicts,
};
use kink_patch::SentenceRef;
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};

/// A private copy of the guards fixture for one test, its `write` program writing address 0.
fn guards(test: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-coverage-flips-{}", std::process::id()))
        .join(test)
        .join("guards");
    let _ = fs::remove_dir_all(&dir);
    copy_dir(&flow("guards"), &dir);
    fs::write(dir.join("programs/write.guards"), "write(0)\n").unwrap();
    dir
}

/// `coverage` on `dir` with `options`, for a front end that derives `derived`.
fn coverage(dir: &Path, options: &[&str], derived: Derived<'_>) -> (Value, u8) {
    let options = options.iter().map(|o| (*o).to_owned()).collect::<Vec<_>>();
    let command = FlowCommand::parse("coverage", CommandFiles::default(), &options).unwrap();
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let front = FrontEnd {
        derived,
        ..FrontEnd::default()
    };
    dispatch(manifest, command, front).expect("the command's thread does not panic")
}

/// [`coverage`] with a front end that also marks `helpers` (each a label of module `GUARDS`) as
/// claim helpers.
fn coverage_marked(
    dir: &Path,
    options: &[&str],
    derived: Derived<'_>,
    helpers: &[&str],
) -> (Value, u8) {
    let options = options.iter().map(|o| (*o).to_owned()).collect::<Vec<_>>();
    let command = FlowCommand::parse("coverage", CommandFiles::default(), &options).unwrap();
    let manifest = FlowManifest::read(&dir.join("FLOW.toml"))
        .unwrap()
        .with_claim_helpers(
            helpers
                .iter()
                .map(|label| ("GUARDS".to_owned(), (*label).to_owned())),
        );
    let front = FrontEnd {
        derived,
        ..FrontEnd::default()
    };
    dispatch(manifest, command, front).expect("the command's thread does not panic")
}

/// The sentence of the rule labelled `label` in `document`'s rules family.
fn sentence(document: &Value, label: &str) -> SentenceRef {
    let item = document["families"]["rules"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|item| {
            item["label"]
                .as_str()
                .is_some_and(|l| l == label || l.ends_with(&format!(".{label}")))
        })
        .unwrap_or_else(|| panic!("no rule {label}: {document:#}"));
    SentenceRef {
        module: item["module"].as_str().unwrap().to_owned(),
        index: u32::try_from(item["index"].as_u64().unwrap()).unwrap(),
    }
}

fn edit(rule: &str, find: &str, replace: &str) -> EditSpec {
    EditSpec {
        file: None,
        rule: Some(rule.to_owned()),
        line: None,
        action: EditAction::Replace {
            find: find.to_owned(),
            replace: replace.to_owned(),
        },
    }
}

/// An admitted Boolean flip of `text`, with its edits and the operand nodes it changes.
fn flip(
    document: &Value,
    id: &str,
    text: &str,
    edits: Vec<EditSpec>,
    occurrences: &[(&str, &str)],
) -> DerivedEntry {
    DerivedEntry {
        id: id.to_owned(),
        operator: "flip".to_owned(),
        text: text.to_owned(),
        atom: json!({"kind": "boolean", "head": text}),
        occurrences: occurrences
            .iter()
            .map(|(label, path)| Occurrence {
                sentence: sentence(document, label),
                reach: Reach::Operand {
                    path: (*path).to_owned(),
                },
            })
            .collect(),
        judged: Judged::Admitted { edits },
    }
}

/// The edits of the whole flip of `H` across the four step rules: `dispatch` and `wake` swap, as
/// do `run` and `halted`.
fn h_edits() -> Vec<EditSpec> {
    vec![
        edit("dispatch", "notBool H andThenBool I", "H andThenBool I"),
        edit(
            "run",
            "notBool H andThenBool notBool I",
            "H andThenBool notBool I",
        ),
        edit("wake", "H andThenBool I", "notBool H andThenBool I"),
        edit(
            "halted",
            "H andThenBool notBool I",
            "notBool H andThenBool notBool I",
        ),
    ]
}

/// The edits of the flip of `I` across `wake` and `halted`, which only a halted machine reaches.
fn i_edits() -> Vec<EditSpec> {
    vec![
        edit("wake", "H andThenBool I", "H andThenBool notBool I"),
        edit("halted", "H andThenBool notBool I", "H andThenBool I"),
    ]
}

fn h_flip(document: &Value) -> DerivedEntry {
    flip(
        document,
        "flip--dispatch+run+wake+halted--H",
        "H",
        h_edits(),
        &[
            ("dispatch", "0.0.0"),
            ("run", "0.0.0"),
            ("wake", "0.0"),
            ("halted", "0.0"),
        ],
    )
}

fn i_flip(document: &Value) -> DerivedEntry {
    flip(
        document,
        "flip--halted+wake--I",
        "I",
        i_edits(),
        &[("wake", "0.1"), ("halted", "0.1.0")],
    )
}

/// The rules family as kink-flow's own front end reports it: what the derived lists name.
fn baseline(dir: &Path) -> Value {
    let (document, status) = coverage(dir, &["--tier", "1"], Derived::default());
    assert_eq!(status, EXIT_YES, "{document:#}");
    document
}

fn item<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["families"]["flips"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|item| item["id"] == id)
        .unwrap_or_else(|| panic!("no flip {id}: {document:#}"))
}

fn target<'d>(document: &'d Value, id: &str) -> Option<&'d Value> {
    document["targets"]
        .as_array()
        .unwrap()
        .iter()
        .find(|target| target["family"] == "flips" && target["item"] == id)
}

/// The outcome files the cache holds.
fn outcome_files(dir: &Path) -> usize {
    let outcomes = dir.join(".kink-flow").join("outcomes");
    fs::read_dir(&outcomes).map_or(0, |contexts| {
        contexts
            .flatten()
            .map(|context| fs::read_dir(context.path()).map_or(0, Iterator::count))
            .sum()
    })
}

/// The id of the flip of `H`, which `irq` and `idle` both distinguish (`irq` first in the
/// search's order).
const H: &str = "flip--dispatch+run+wake+halted--H";
/// The id of the flip of `I`, which no program reaches.
const I: &str = "flip--halted+wake--I";

/// The parser: `--lock FILE` once, `--locked` once and only with `--lock`, and neither with
/// `--tier 1` nor with `--depth`, which run other settings than the manifest's; `--depth` a
/// positive integer.
#[test]
fn the_coverage_lock_options_parse() {
    let parse = |args: &[&str]| {
        FlowCommand::parse(
            "coverage",
            CommandFiles::default(),
            &args.iter().map(|a| (*a).to_owned()).collect::<Vec<_>>(),
        )
    };
    let FlowCommand::Coverage { options, .. } =
        parse(&["--locked", "--lock", "coverage.lock"]).unwrap()
    else {
        panic!("coverage");
    };
    assert_eq!(
        (options.lock, options.locked, options.depth),
        (Some(PathBuf::from("coverage.lock")), true, None)
    );
    let FlowCommand::Coverage { options, .. } = parse(&["--depth", "2", "--lock", "c"]).unwrap()
    else {
        panic!("coverage");
    };
    assert_eq!(options.depth.map(std::num::NonZeroU64::get), Some(2));
    assert_eq!(
        parse(&["--locked"]).unwrap_err(),
        "--locked compares the run with its lock: give --lock FILE"
    );
    for args in [
        &["--lock", "c", "--locked", "--tier", "1"][..],
        &["--lock", "c", "--locked", "--depth", "1"][..],
    ] {
        let error = parse(args).unwrap_err();
        assert!(
            error.starts_with("--locked compares a run of the manifest's own settings"),
            "{error}"
        );
    }
    assert_eq!(
        parse(&["--depth", "0"]).unwrap_err(),
        "--depth \"0\": expected a positive integer"
    );
    assert_eq!(
        parse(&["--lock", "a", "--lock", "b"]).unwrap_err(),
        "--lock specified more than once"
    );
}

/// A coverage lock that does not decode refuses the command before admission: not TOML, a run's
/// lock (another document), or a repeated flip. Exit 2, `lock.outcome` refused, the rendering's
/// `[lock]` section, no program, and the file is left as it was.
#[test]
fn an_undecodable_coverage_lock_refuses_the_command() {
    let dir = guards("undecodable");
    let lock = dir.join("coverage.lock");
    let flip = "[[flip]]\nid = \"f\"\nstatus = \"unreached\"\n";
    for (text, detail) in [
        ("not = toml = at all\n".to_owned(), "is not TOML"),
        (
            "schema = \"kink-flow-verdicts\"\nversion = 21\ndocument = \"run\"\n".to_owned(),
            "its document is not \"coverage\"",
        ),
        (
            format!(
                "schema = \"kink-flow-verdicts\"\nversion = 21\ndocument = \"coverage\"\n\n\
                 {flip}\n{flip}"
            ),
            "the flip \"f\" is listed twice",
        ),
    ] {
        fs::write(&lock, &text).unwrap();
        let (document, status) = coverage(
            &dir,
            &["--lock", lock.to_str().unwrap()],
            Derived::default(),
        );
        assert_eq!(status, EXIT_UNASKED, "{document:#}");
        assert_eq!(document["lock"]["outcome"], "refused", "{document:#}");
        let message = document["lock"]["detail"].as_str().unwrap();
        assert!(message.contains(detail), "{message}");
        assert!(document.get("programs").is_none(), "{document:#}");
        let rendering = verdicts(&document).unwrap();
        assert!(
            rendering.ends_with("\n[lock]\noutcome = \"refused\"\n"),
            "{rendering}"
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), text);
    }
}

mod kink_tier {
    use super::*;

    /// A flip none of whose occurrences any comparable program reached is `unreached` with no
    /// mutant run: no campaign call, no outcome record, and its target names the open
    /// requirements that explain it.
    #[test]
    #[ignore = "kink"]
    fn an_occurrence_no_program_reached_is_unreached_with_no_mutant_run() {
        let dir = guards("unreached");
        let rules = baseline(&dir);
        let list = DerivedList {
            entries: vec![i_flip(&rules)],
            ..DerivedList::default()
        };
        let (document, status) = coverage(&dir, &[], Derived::Flips(&list));
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(document["settings"]["tiers"], json!([1, 2]));
        let family = &document["families"]["flips"];
        assert_eq!(family["run"], true, "{family:#}");
        let flip = item(&document, "flip--halted+wake--I");
        assert_eq!(flip["status"], "unreached", "{flip:#}");
        for occurrence in flip["occurrences"].as_array().unwrap() {
            assert_eq!(occurrence["reached_by"], json!([]), "{flip:#}");
            assert_eq!(occurrence["undecided_by"], json!([]), "{flip:#}");
            assert_eq!(occurrence["unplaced"], Value::Null, "{flip:#}");
        }
        assert!(flip["digest"].is_string(), "{flip:#}");
        // Zero mutant runs: no live run, no call, nothing searched, no record written.
        assert_eq!(flip["live_runs"], 0);
        assert_eq!(flip["calls"], 0);
        assert_eq!(family["search"]["live_runs"], 0, "{family:#}");
        assert_eq!(family["search"]["outcome_cache"]["records_written"], 0);
        assert_eq!(outcome_files(&dir), 0);
        // It waits on the open requirements of `I` in both sentences.
        let waits = flip["waits_on"].as_array().unwrap();
        assert!(
            waits
                .iter()
                .all(|id| id.as_str().unwrap().starts_with("requirement:")),
            "{flip:#}"
        );
        assert!(waits.len() >= 2, "{flip:#}");
        let target = target(&document, "flip--halted+wake--I").expect("an open target");
        assert!(
            target["text"]
                .as_str()
                .unwrap()
                .starts_with("a case that reaches I in "),
            "{target:#}"
        );
        assert_eq!(family["counts"]["unreached"], 1);
        assert_eq!(family["measure"], json!(0.0));
        assert_eq!(document["summary"]["per_family"]["flips"]["open"], 1);
    }

    /// Every status but `unreached` comes from the kill search: a reached flip is distinguished
    /// with its killer, the first killing program in the search's order; a flip whose
    /// occurrences the guard rows cannot place is undecided, so it runs; a reached flip no
    /// program tells apart is undistinguished, with a target naming the values the corpus
    /// reached and the programs that reached them; a refused flip runs nothing.
    #[test]
    #[ignore = "kink"]
    fn the_search_decides_every_flip_it_cannot_deduce() {
        let dir = guards("statuses");
        let rules = baseline(&dir);
        let mut unplaced = i_flip(&rules);
        unplaced.id = "flip--halted+wake--I-unplaced".to_owned();
        for occurrence in &mut unplaced.occurrences {
            occurrence.reach = Reach::Operand {
                path: "0.9".to_owned(),
            };
        }
        let list = DerivedList {
            entries: vec![
                h_flip(&rules),
                i_flip(&rules),
                unplaced,
                flip(
                    &rules,
                    "flip--high+low--A",
                    "A <Int 32768",
                    vec![
                        edit("low", "A <Int 32768", "A >=Int 32768"),
                        edit("high", "A >=Int 32768", "A <Int 32768"),
                    ],
                    &[("low", "0"), ("high", "0")],
                ),
                DerivedEntry {
                    id: "flip--refused".to_owned(),
                    operator: "flip".to_owned(),
                    text: "matches!(x)".to_owned(),
                    atom: json!({"kind": "boolean", "head": "matches"}),
                    occurrences: Vec::new(),
                    judged: Judged::Refused {
                        reason: "not-judged".to_owned(),
                        next: Some("write the test as a guard".to_owned()),
                        detail: "a k::matches! test".to_owned(),
                    },
                },
            ],
            not_generated: vec![json!({"reason": "theory-separated"})],
            none: None,
        };
        let (document, status) = coverage(&dir, &[], Derived::Flips(&list));
        assert_eq!(status, EXIT_YES, "{document:#}");
        let distinguished = item(&document, "flip--dispatch+run+wake+halted--H");
        assert_eq!(
            distinguished["status"], "distinguished",
            "{distinguished:#}"
        );
        assert_eq!(distinguished["killer"], "irq", "{distinguished:#}");
        assert!(distinguished["live_runs"].as_u64().unwrap() >= 1);
        for occurrence in distinguished["occurrences"].as_array().unwrap() {
            assert_eq!(occurrence["unplaced"], Value::Null, "{distinguished:#}");
            assert_eq!(
                occurrence["reached_by"],
                json!(["irq", "idle"]),
                "{distinguished:#}"
            );
        }
        assert!(target(&document, "flip--dispatch+run+wake+halted--H").is_none());
        assert_eq!(
            item(&document, "flip--halted+wake--I")["status"],
            "unreached"
        );
        // The unplaced flip has the unreached flip's patch, but runs, and no program tells its
        // mutant apart.
        let runs = item(&document, "flip--halted+wake--I-unplaced");
        assert_eq!(runs["status"], "undistinguished", "{runs:#}");
        assert!(runs["live_runs"].as_u64().unwrap() >= 1, "{runs:#}");
        assert!(
            runs["occurrences"]
                .as_array()
                .unwrap()
                .iter()
                .all(|o| o["unplaced"].is_string()),
            "{runs:#}"
        );
        let swap = item(&document, "flip--high+low--A");
        assert_eq!(swap["status"], "undistinguished", "{swap:#}");
        let swap_target = target(&document, "flip--high+low--A").expect("an open target");
        let text = swap_target["text"].as_str().unwrap();
        // `high`'s occurrence is reached at the low store too, where `low` applied and `high`'s
        // condition was entered untried.
        assert!(
            text.starts_with("a case whose result changes when A <Int 32768 is negated in "),
            "{swap_target:#}"
        );
        assert!(
            text.ends_with(
                "; the corpus reached it true in GUARDS.low (write) and false in GUARDS.high \
                 (write)"
            ),
            "{swap_target:#}"
        );
        assert_eq!(swap_target["programs"], json!(["write"]));
        assert_eq!(
            swap_target["fuzz"],
            "kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID --kill flip--high+low--A"
        );
        let refused = item(&document, "flip--refused");
        assert_eq!(refused["status"], "refused");
        assert_eq!(refused["judge"], "front-end");
        assert_eq!(refused["reason"], "not-judged");
        assert_eq!(refused["live_runs"], 0);
        let family = &document["families"]["flips"];
        assert_eq!(
            family["counts"],
            json!({"distinguished": 1, "undistinguished": 2, "unreached": 1, "unknown": 0,
                   "refused": 1, "equivalent": 0, "not_generated": 1, "argued": 0})
        );
        assert_eq!(family["obligations"], 5);
        assert_eq!(family["measure"], json!(0.25));
        assert_eq!(
            document["summary"]["per_family"]["flips"],
            json!({"obligations": 4, "covered": 1, "argued": 0, "open": 3})
        );
        // The verdicts rendering lists each flip's status, a distinguished one's killer and a
        // refused one's reason.
        let verdicts = kink_flow::verdicts::verdicts(&document).unwrap();
        assert!(
            verdicts.ends_with(
                "\n[flips]\nrun = true\n\
                 \n[[flip]]\nid = \"flip--dispatch+run+wake+halted--H\"\nstatus = \"distinguished\"\nkiller = \"irq\"\n\
                 \n[[flip]]\nid = \"flip--halted+wake--I\"\nstatus = \"unreached\"\n\
                 \n[[flip]]\nid = \"flip--halted+wake--I-unplaced\"\nstatus = \"undistinguished\"\n\
                 \n[[flip]]\nid = \"flip--high+low--A\"\nstatus = \"undistinguished\"\n\
                 \n[[flip]]\nid = \"flip--refused\"\nstatus = \"refused\"\nreason = \"not-judged\"\n"
            ),
            "{verdicts}"
        );
        assert!(
            verdicts.contains("\n[settings]\ntiers = [1, 2]\n"),
            "{verdicts}"
        );
        // A second command decides every flip from the outcome cache, with the same statuses.
        let (again, status) = coverage(&dir, &[], Derived::Flips(&list));
        assert_eq!(status, EXIT_YES, "{again:#}");
        assert_eq!(again["families"]["flips"]["search"]["live_runs"], 0);
        assert_eq!(kink_flow::verdicts::verdicts(&again).unwrap(), verdicts);
    }

    /// A derived flip equal to an authored mutation (the same patch) shares its outcome records:
    /// after `run` judges the authored one, `coverage` decides the flip from the cache.
    #[test]
    #[ignore = "kink"]
    fn a_derived_flip_equal_to_an_authored_mutation_shares_its_outcomes() {
        let dir = guards("shared");
        let rules = baseline(&dir);
        let mut list = String::from(
            "[[mutation]]\nid = \"swap-halted\"\nmisunderstanding = \"the halted flag is read \
             the wrong way round\"\n",
        );
        for edit in h_edits() {
            let (EditAction::Replace { find, replace }, Some(rule)) = (&edit.action, &edit.rule)
            else {
                unreachable!()
            };
            list.push_str(&format!(
                "\n[[mutation.edit]]\nrule = \"{rule}\"\nfind = \"{find}\"\nreplace = \"{replace}\"\n"
            ));
        }
        fs::write(dir.join("MUTATIONS.toml"), list).unwrap();
        let command = FlowCommand::parse(
            "run",
            CommandFiles {
                mutations: Some(dir.join("MUTATIONS.toml")),
                ..CommandFiles::default()
            },
            &[],
        )
        .unwrap();
        let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        let (run, status) = dispatch(manifest, command, FrontEnd::default()).unwrap();
        assert_eq!(status, EXIT_YES, "{run:#}");
        let row = &run["mutations"][0];
        assert_eq!(row["status"], "killed", "{row:#}");
        assert_eq!(row["killer"], "irq", "{row:#}");
        let derived = DerivedList {
            entries: vec![h_flip(&rules)],
            ..DerivedList::default()
        };
        let (document, status) = coverage(&dir, &[], Derived::Flips(&derived));
        assert_eq!(status, EXIT_YES, "{document:#}");
        let flip = item(&document, "flip--dispatch+run+wake+halted--H");
        assert_eq!(flip["status"], "distinguished", "{flip:#}");
        assert_eq!(flip["killer"], "irq");
        assert_eq!(flip["digest"], row["digest"]);
        assert_eq!(flip["killer_source"], "outcome-cache", "{flip:#}");
        assert_eq!(flip["live_runs"], 0, "{flip:#}");
        let search = &document["families"]["flips"]["search"];
        assert_eq!(
            search["outcome_cache"]["mutations_from_cache"], 1,
            "{search:#}"
        );
        assert_eq!(search["outcome_cache"]["records_written"], 0, "{search:#}");
    }

    /// `--tier 1` runs no mutant: the flips family shows only its number of obligations, with
    /// no status, whatever the cache holds; a front end that derives no flips gives its reason.
    #[test]
    #[ignore = "kink"]
    fn tier_one_runs_no_flip() {
        let dir = guards("tier-one");
        let rules = baseline(&dir);
        let list = DerivedList {
            entries: vec![h_flip(&rules), i_flip(&rules)],
            ..DerivedList::default()
        };
        let (document, status) = coverage(&dir, &["--tier", "1"], Derived::Flips(&list));
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(document["settings"]["tiers"], json!([1]));
        assert_eq!(
            document["families"]["flips"],
            json!({"tier": 2, "run": false, "obligations": 2, "items": [],
                   "reason": kink_flow::flips::FLIPS_TIER_ONE})
        );
        assert_eq!(outcome_files(&dir), 0);
        assert!(document["summary"]["per_family"].get("flips").is_none());
        let verdicts = kink_flow::verdicts::verdicts(&document).unwrap();
        assert!(verdicts.ends_with("\n[flips]\nrun = false\n"), "{verdicts}");
        assert_eq!(
            rules["families"]["flips"]["reason"],
            kink_flow::flips::DERIVES_NONE
        );
    }

    /// The flip of `H` in `dispatch` and `wake` alone, the two rules `H` keeps apart when `I`
    /// holds.
    fn d_flip(document: &Value) -> DerivedEntry {
        flip(
            document,
            D,
            "H",
            vec![
                edit("dispatch", "notBool H andThenBool I", "H andThenBool I"),
                edit("wake", "H andThenBool I", "notBool H andThenBool I"),
            ],
            &[("dispatch", "0.0.0"), ("wake", "0.0")],
        )
    }

    /// The id of [`d_flip`].
    const D: &str = "flip--dispatch+wake--H";

    /// Every family shares one static scope, which sets sentences aside, not flips. With
    /// `dispatch` marked a claim helper, its rules item is `claim-helper` although programs fire
    /// it, and is no obligation; the flip of `H`, which also changes `run`, `wake` and `halted`,
    /// stays an obligation of those, with only their occurrences, which the unreached deduction
    /// reads, and runs with all its edits; so does the flip of `H` in `dispatch` and `wake`
    /// alone, through its occurrence in `wake`. With `wake` marked as well, that flip changes
    /// only claim helpers and is moved to `not_generated` with reason `claim-helper` before any
    /// run, so it is neither counted nor run nor a target, under tier 2 and in tier 1's count,
    /// and a kill job of it is refused as an unknown mutation that says why it is not generated;
    /// the flip of `I`, which still changes `halted`, keeps its status with only that occurrence.
    #[test]
    #[ignore = "kink"]
    fn a_flip_of_a_claim_helper_is_not_generated_whatever_programs_did() {
        let dir = guards("claim-helper");
        let rules = baseline(&dir);
        let at = sentence(&rules, "dispatch");
        let at = json!({"module": at.module, "index": at.index});
        let list = DerivedList {
            entries: vec![h_flip(&rules), i_flip(&rules), d_flip(&rules)],
            ..DerivedList::default()
        };
        let ids = |family: &Value| -> Vec<String> {
            family["items"]
                .as_array()
                .unwrap()
                .iter()
                .map(|item| item["id"].as_str().unwrap().to_owned())
                .collect()
        };
        let occurrences = |document: &Value, id: &str| -> Vec<Value> {
            item(document, id)["occurrences"]
                .as_array()
                .unwrap()
                .iter()
                .map(|occurrence| occurrence["index"].clone())
                .collect()
        };
        let index = |label: &str| json!(sentence(&rules, label).index);

        let (document, status) = coverage_marked(&dir, &[], Derived::Flips(&list), &["dispatch"]);
        assert_eq!(status, EXIT_YES, "{document:#}");
        let helper = document["families"]["rules"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|item| item["module"] == at["module"] && item["index"] == at["index"])
            .unwrap();
        assert_eq!(helper["status"], "claim-helper", "{helper:#}");
        assert_eq!(helper["obligation"], false, "{helper:#}");
        assert_ne!(helper["fired_by"], json!([]), "{helper:#}");
        let family = &document["families"]["flips"];
        assert_eq!(ids(family), [H, I, D], "{family:#}");
        assert_eq!(family["obligations"], 3, "{family:#}");
        assert_eq!(family["counts"]["not_generated"], 0, "{family:#}");
        assert_eq!(item(&document, H)["status"], "distinguished", "{family:#}");
        assert_eq!(
            occurrences(&document, H),
            [index("run"), index("wake"), index("halted")],
            "{family:#}"
        );
        assert_eq!(item(&document, I)["status"], "unreached", "{family:#}");
        assert_eq!(item(&document, D)["status"], "distinguished", "{family:#}");
        assert_eq!(occurrences(&document, D), [index("wake")], "{family:#}");

        let helpers = ["dispatch", "wake"];
        let (document, status) = coverage_marked(&dir, &[], Derived::Flips(&list), &helpers);
        assert_eq!(status, EXIT_YES, "{document:#}");
        let family = &document["families"]["flips"];
        assert_eq!(ids(family), [H, I], "{family:#}");
        assert_eq!(item(&document, I)["status"], "unreached", "{family:#}");
        assert_eq!(occurrences(&document, I), [index("halted")], "{family:#}");
        assert_eq!(family["obligations"], 2, "{family:#}");
        assert_eq!(family["counts"]["not_generated"], 1, "{family:#}");
        let not = &family["not_generated"][0];
        assert_eq!(
            (&not["reason"], &not["id"], &not["sentences"]),
            (
                &json!("claim-helper"),
                &json!(D),
                &json!(["GUARDS.dispatch", "GUARDS.wake"])
            ),
            "{not:#}"
        );
        assert!(
            not["detail"].as_str().unwrap().starts_with(&format!(
                "`{D}` changes only sentences that are no obligation of any coverage family: \
                 GUARDS.dispatch (claim-helper), GUARDS.wake (claim-helper) (claim-helper: "
            )),
            "{not:#}"
        );
        assert!(target(&document, D).is_none(), "{document:#}");

        let (tier_one, status) =
            coverage_marked(&dir, &["--tier", "1"], Derived::Flips(&list), &helpers);
        assert_eq!(status, EXIT_YES, "{tier_one:#}");
        assert_eq!(tier_one["families"]["flips"]["obligations"], 2);

        fs::write(
            dir.join("TEMPLATES.toml"),
            "[[template]]\nid = \"t\"\nprogram = \"irq\"\n",
        )
        .unwrap();
        let command = FlowCommand::parse(
            "fuzz",
            CommandFiles {
                templates: Some(dir.join("TEMPLATES.toml")),
                ..CommandFiles::default()
            },
            &["--template", "t", "--kill", D]
                .iter()
                .map(|o| (*o).to_owned())
                .collect::<Vec<_>>(),
        )
        .unwrap();
        let manifest = FlowManifest::read(&dir.join("FLOW.toml"))
            .unwrap()
            .with_claim_helpers(
                helpers
                    .iter()
                    .map(|label| ("GUARDS".to_owned(), (*label).to_owned())),
            );
        let front = FrontEnd {
            derived: Derived::Flips(&list),
            ..FrontEnd::default()
        };
        let (fuzzed, status) = dispatch(manifest, command, front).unwrap();
        assert_eq!(status, EXIT_UNASKED, "{fuzzed:#}");
        let refusal = &fuzzed["job"]["refusal"];
        assert_eq!(refusal["reason"], "unknown-mutation", "{fuzzed:#}");
        assert!(
            refusal["detail"]
                .as_str()
                .unwrap()
                .contains("it is not generated (claim-helper)"),
            "{fuzzed:#}"
        );
        assert!(fuzzed["template"].is_null(), "{fuzzed:#}");
    }

    /// The flips of `H` and `I`.
    fn h_and_i(rules: &Value) -> DerivedList {
        DerivedList {
            entries: vec![h_flip(rules), i_flip(rules)],
            ..DerivedList::default()
        }
    }

    /// `text` with the `[[flip]]` row of `id` given `key = "value"` in place of its own (or
    /// added after its status).
    fn with_row_key(text: &str, id: &str, key: &str, value: &str) -> String {
        let start = text
            .find(&format!("\n[[flip]]\nid = \"{id}\"\n"))
            .unwrap_or_else(|| panic!("no row {id}: {text}"));
        let end = text[start + 1..]
            .find("\n[[flip]]")
            .map_or(text.len(), |at| start + 1 + at);
        let mut row = text[start..end]
            .lines()
            .filter(|line| !line.starts_with(&format!("{key} = ")))
            .collect::<Vec<_>>()
            .join("\n");
        row.push_str(&format!("\n{key} = \"{value}\"\n"));
        format!("{}{row}{}", &text[..start], &text[end..])
    }

    /// A distinguished flip's killer is the lock's while it still kills: `idle` recorded stays
    /// the killer although `irq` comes first in the search's order. A recorded killer that no
    /// longer kills (`write`) or is no longer in the corpus is replaced by the first killer in the
    /// search's order, the coverage witnesses first, and the lock is rewritten with it. A flip
    /// decided with no run keeps no killer. The lock is the `--output verdicts` rendering.
    #[test]
    #[ignore = "kink"]
    fn a_distinguished_flips_killer_is_the_recorded_one_while_it_kills() {
        let dir = guards("killer");
        let rules = baseline(&dir);
        let list = h_and_i(&rules);
        let lock = dir.join("coverage.lock");
        let options = ["--lock", lock.to_str().unwrap()];
        let run = || {
            let (document, status) = coverage(&dir, &options, Derived::Flips(&list));
            assert_eq!(status, EXIT_YES, "{document:#}");
            document
        };

        // No record: the first killer in the search's order, and the lock is created.
        let first = run();
        let h = item(&first, H);
        assert_eq!(
            (&h["killer"], &h["recorded_killer"], &h["killer_change"]),
            (&json!("irq"), &Value::Null, &json!("no-record")),
            "{h:#}"
        );
        assert_eq!(first["lock"]["status"], "created", "{:#}", first["lock"]);
        let recorded = fs::read_to_string(&lock).unwrap();
        assert_eq!(recorded, verdicts(&first).unwrap());
        assert!(
            recorded.contains(&format!(
                "\n[[flip]]\nid = \"{H}\"\nstatus = \"distinguished\"\nkiller = \"irq\"\n"
            )),
            "{recorded}"
        );

        // `idle` also distinguishes the mutant: recorded, it stays the killer, from the
        // one-program call over it, and the lock does not move.
        let idle = with_row_key(&recorded, H, "killer", "idle");
        fs::write(&lock, &idle).unwrap();
        let kept = run();
        let h = item(&kept, H);
        assert_eq!(
            (&h["killer"], &h["killer_source"], &h["killer_change"]),
            (&json!("idle"), &json!("record"), &Value::Null),
            "{h:#}"
        );
        assert_eq!(h["recorded_killer"], "idle");
        assert_eq!(kept["lock"]["status"], "unchanged", "{:#}", kept["lock"]);
        assert_eq!(fs::read_to_string(&lock).unwrap(), idle);

        // `write` never steps, so it does not distinguish the mutant; `gone` is no program.
        for (killer, change) in [("write", "no-longer-kills"), ("gone", "not-in-corpus")] {
            fs::write(&lock, with_row_key(&recorded, H, "killer", killer)).unwrap();
            let replaced = run();
            let h = item(&replaced, H);
            assert_eq!(
                (&h["killer"], &h["recorded_killer"], &h["killer_change"]),
                (&json!("irq"), &json!(killer), &json!(change)),
                "{h:#}"
            );
            assert_eq!(replaced["lock"]["status"], "written");
            assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
        }

        // A killer recorded for the unreached flip is not run, and the rendering names none.
        fs::write(&lock, with_row_key(&recorded, I, "killer", "irq")).unwrap();
        let unreached = run();
        let i = item(&unreached, I);
        assert_eq!(
            (
                &i["status"],
                &i["killer"],
                &i["recorded_killer"],
                &i["killer_change"]
            ),
            (
                &json!("unreached"),
                &Value::Null,
                &json!("irq"),
                &json!("not-run")
            ),
            "{i:#}"
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
    }

    /// The lock is left as it is by a command that runs other settings than the manifest's:
    /// `--tier 1` (no flip runs) and a `--depth` other than `[coverage] depth`, which still reads
    /// the recorded killers. A refused specification leaves it too.
    #[test]
    #[ignore = "kink"]
    fn the_lock_is_unchanged_under_tier_one_and_another_depth() {
        let dir = guards("partial");
        let rules = baseline(&dir);
        let list = h_and_i(&rules);
        let lock = dir.join("coverage.lock");
        let run = |extra: &[&str]| {
            let mut options = vec!["--lock", lock.to_str().unwrap()];
            options.extend_from_slice(extra);
            coverage(&dir, &options, Derived::Flips(&list))
        };
        // A lock recording `idle` as `H`'s killer, which a run with the manifest's settings would
        // keep but rewrite (its header and open obligations are a hand's).
        let text = format!(
            "schema = \"kink-flow-verdicts\"\nversion = 21\ndocument = \"coverage\"\n\n\
             [[flip]]\nid = \"{H}\"\nstatus = \"distinguished\"\nkiller = \"idle\"\n"
        );
        fs::write(&lock, &text).unwrap();

        let (tier_one, status) = run(&["--tier", "1"]);
        assert_eq!(status, EXIT_YES, "{tier_one:#}");
        assert_eq!(
            (&tier_one["lock"]["status"], &tier_one["lock"]["reason"]),
            (&json!("not-written"), &json!("tier-1"))
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), text);

        // A refused specification (an `mcdc` name that selects no rule) leaves the lock.
        let manifest = dir.join("FLOW.toml");
        let original = fs::read_to_string(&manifest).unwrap();
        fs::write(
            &manifest,
            format!("{original}\n[coverage]\nmcdc = [\"GUARDS.nowhere\"]\n"),
        )
        .unwrap();
        let (refused, status) = run(&[]);
        assert_eq!(status, EXIT_UNASKED, "{refused:#}");
        assert_eq!(refused["spec"]["reason"], "mcdc-stale");
        assert_eq!(refused["lock"]["reason"], "refused");
        assert_eq!(fs::read_to_string(&lock).unwrap(), text);

        // `[coverage] depth = 2`, explored at `--depth 1`.
        fs::write(&manifest, format!("{original}\n[coverage]\ndepth = 2\n")).unwrap();
        let (explored, status) = run(&["--depth", "1"]);
        assert_eq!(status, EXIT_YES, "{explored:#}");
        assert_eq!(explored["settings"]["depth"], 1);
        assert_eq!(
            (&explored["lock"]["status"], &explored["lock"]["reason"]),
            (&json!("not-written"), &json!("depth"))
        );
        let h = item(&explored, H);
        assert_eq!(
            (&h["killer"], &h["killer_change"]),
            (&json!("idle"), &Value::Null)
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), text);
    }

    /// `--locked` writes nothing: an absent lock, or one the command would change, is a finding
    /// (exit 1, `stale`), and each change is named, as `kink-flow` prints it on stderr: a flip's
    /// killer and status, an obligation that is no longer open, and a header from another Z3
    /// build, which is stale although every row agrees. An unchanged lock gives the statuses'
    /// exit.
    #[test]
    #[ignore = "kink"]
    fn locked_names_each_change_and_exits_one() {
        let dir = guards("locked");
        let rules = baseline(&dir);
        let list = h_and_i(&rules);
        let lock = dir.join("coverage.lock");
        let path = lock.to_str().unwrap();
        let run = |locked: bool| {
            let mut options = vec!["--lock", path];
            if locked {
                options.push("--locked");
            }
            coverage(&dir, &options, Derived::Flips(&list))
        };
        let (absent, status) = run(true);
        assert_eq!(status, EXIT_NO, "{absent:#}");
        assert_eq!(
            (&absent["lock"]["status"], &absent["lock"]["header"]),
            (&json!("stale"), &json!(true))
        );
        assert!(!lock.exists());
        let (written, status) = run(false);
        assert_eq!(status, EXIT_YES, "{written:#}");
        let recorded = fs::read_to_string(&lock).unwrap();
        let (unchanged, status) = run(true);
        assert_eq!(status, EXIT_YES, "{unchanged:#}");
        assert_eq!(unchanged["lock"]["status"], "unchanged");
        assert_eq!(unchanged["lock"]["changes"], json!([]));
        assert_eq!(unchanged["lock"]["open_changes"], json!([]));

        let edited = with_row_key(&recorded, H, "killer", "gone");
        let edited = with_row_key(&edited, I, "status", "distinguished");
        let edited = edited.replacen(
            "\n[rules]\nopen = [\n",
            "\n[rules]\nopen = [\n  \"rule:gone\",\n",
            1,
        );
        assert!(edited.contains("\"rule:gone\""), "{edited}");
        fs::write(&lock, &edited).unwrap();
        let (stale, status) = run(true);
        assert_eq!(status, EXIT_NO, "{stale:#}");
        assert_eq!(stale["lock"]["status"], "stale");
        assert_eq!(stale["lock"]["header"], false, "{:#}", stale["lock"]);
        assert_eq!(
            stale["lock"]["open_changes"],
            json!([{"family": "rules", "obligation": "rule:gone", "recorded": "open", "now": null}])
        );
        assert_eq!(
            stale_lines(&stale),
            [
                format!("{path}: rules: rule:gone is no longer open"),
                format!("{path}: {H}: killer gone -> irq (gone: not-in-corpus)"),
                format!("{path}: {I}: distinguished -> unreached"),
            ]
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), edited);

        // A lock recorded on another Z3 build differs in its header alone, and each moved build
        // line is named. Under the Z3 profile the rendering names the build (`z3_version`, and
        // `z3_library_sha256` where the build knows its library); without it, it names none, so
        // the recorded line is one the rendering does not have.
        let other_build = match recorded
            .lines()
            .find(|line| line.starts_with("z3_library_sha256 = "))
        {
            Some(line) => recorded.replacen(line, "z3_library_sha256 = \"another-build\"", 1),
            None => recorded.replacen(
                "\nprofile = ",
                "\nz3_library_sha256 = \"another-build\"\nprofile = ",
                1,
            ),
        };
        assert_ne!(other_build, recorded);
        fs::write(&lock, &other_build).unwrap();
        let (stale, status) = run(true);
        assert_eq!(status, EXIT_NO, "{stale:#}");
        assert_eq!(
            (&stale["lock"]["status"], &stale["lock"]["header"]),
            (&json!("stale"), &json!(true))
        );
        assert_eq!(stale["lock"]["changes"], json!([]));
        assert_eq!(stale["lock"]["open_changes"], json!([]));
        let header_changes = stale["lock"]["header_changes"].as_array().unwrap();
        assert_eq!(header_changes.len(), 1, "{:#}", stale["lock"]);
        assert_eq!(header_changes[0]["key"], "z3_library_sha256");
        assert_eq!(header_changes[0]["recorded"], "another-build");
        let lines = stale_lines(&stale);
        assert_eq!(lines.len(), 1, "{lines:#?}");
        assert!(
            lines[0].starts_with(&format!(
                "{path}: the header's z3_library_sha256 differs: recorded \"another-build\", now "
            )) && lines[0].ends_with(" (another Z3 build)"),
            "{lines:#?}"
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), other_build);

        // The binary names each change on stderr: kink-flow's own front end derives no flips,
        // so the recorded flips would be removed.
        fs::write(&lock, &recorded).unwrap();
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_kink-flow"))
            .args([
                "coverage",
                "FLOW.toml",
                "--lock",
                "coverage.lock",
                "--locked",
            ])
            .current_dir(&dir)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(EXIT_NO)));
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains(&format!(
                "kink-flow: coverage.lock: {H}: removed, was distinguished"
            )),
            "{stderr}"
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
    }
}

/// `fuzz --kill FLIP` where no list holds the id: a flip the front end's judge refused is refused
/// at stage `mutation` with the judge's reason and next step, and an id that is no derived flip
/// either names what the list and the derived flips hold; kink-flow's own front end derives none
/// and says why. None of these reads a template's program, so nothing runs.
#[test]
fn a_kill_job_of_a_refused_or_unknown_flip_is_refused() {
    let dir = guards("fuzz-derived");
    fs::write(
        dir.join("TEMPLATES.toml"),
        "[[template]]\nid = \"t\"\nprogram = \"irq\"\n",
    )
    .unwrap();
    let list = DerivedList {
        entries: vec![DerivedEntry {
            id: "flip--wake--I".to_owned(),
            operator: "flip".to_owned(),
            text: "I".to_owned(),
            atom: json!({"kind": "boolean", "head": "I"}),
            occurrences: Vec::new(),
            judged: Judged::Refused {
                reason: "not-judged".to_owned(),
                next: Some("report the flip".to_owned()),
                detail: "the edit is not read back".to_owned(),
            },
        }],
        not_generated: vec![json!({"reason": "claim-helper", "id": "flip--gone",
                                    "detail": "it changes a claim helper"})],
        none: None,
    };
    let fuzz = |id: &str, derived: Derived<'_>| {
        let command = FlowCommand::parse(
            "fuzz",
            CommandFiles {
                templates: Some(dir.join("TEMPLATES.toml")),
                ..CommandFiles::default()
            },
            &["--template", "t", "--kill", id]
                .iter()
                .map(|o| (*o).to_owned())
                .collect::<Vec<_>>(),
        )
        .unwrap();
        let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        let front = FrontEnd {
            derived,
            ..FrontEnd::default()
        };
        dispatch(manifest, command, front).expect("the command's thread does not panic")
    };
    let (document, status) = fuzz("flip--wake--I", Derived::Flips(&list));
    assert_eq!(status, kink_flow::cli::EXIT_UNASKED, "{document:#}");
    assert_eq!(document["version"], 15, "{document:#}");
    let job = &document["job"];
    assert_eq!(
        (&job["kind"], &job["flip"], &job["status"], &job["outcome"]),
        (
            &json!("kill"),
            &json!(true),
            &json!("refused"),
            &json!("refused")
        ),
        "{document:#}"
    );
    assert_eq!(job["refusal"]["stage"], "mutation", "{document:#}");
    assert_eq!(job["refusal"]["reason"], "not-judged", "{document:#}");
    assert_eq!(
        job["refusal"]["detail"], "the edit is not read back",
        "{document:#}"
    );
    assert!(
        document["action"]
            .as_str()
            .unwrap()
            .ends_with(": report the flip"),
        "{document:#}"
    );
    assert!(document["template"].is_null(), "{document:#}");

    let (document, _) = fuzz("flip--nope", Derived::Flips(&list));
    assert_eq!(document["job"]["flip"], false, "{document:#}");
    assert_eq!(
        document["job"]["refusal"]["reason"], "unknown-mutation",
        "{document:#}"
    );
    assert_eq!(
        document["job"]["refusal"]["detail"],
        "no condition flip the front end derives has this id (1 flip)",
        "{document:#}"
    );
    let (document, _) = fuzz("flip--gone", Derived::Flips(&list));
    assert_eq!(
        document["job"]["refusal"]["detail"],
        "no condition flip the front end derives has this id (1 flip): it is not generated \
         (claim-helper): it changes a claim helper",
        "{document:#}"
    );
    let (document, _) = fuzz("flip--nope", Derived::default());
    assert_eq!(
        document["job"]["refusal"]["detail"],
        format!("no flip has this id: {}", kink_flow::flips::DERIVES_NONE),
        "{document:#}"
    );
}
