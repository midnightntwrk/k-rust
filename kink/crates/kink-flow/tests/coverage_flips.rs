//! The flips family of `coverage` (tier 2): a front end's derived flips, each deduced unreached
//! with no mutant run or run by the kill search, on the guards fixture, whose corpus never halts
//! (so `I` is never reached in `wake` and `halted`) and writes only address 0 (so swapping `low`
//! and `high` changes no result).

mod flow_support;

use flow_support::{copy_dir, flow};
use kink_flow::{
    CommandFiles, EditAction, EditSpec, FlowCommand, FlowManifest, FrontEnd,
    cli::{EXIT_YES, dispatch},
    flips::{Derived, DerivedEntry, DerivedList, Judged, Occurrence, Reach},
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
        assert!(
            text.starts_with("a case whose result changes when A <Int 32768 is negated in "),
            "{swap_target:#}"
        );
        assert!(
            text.ends_with("; the corpus reached it true in GUARDS.low (write)"),
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
                   "refused": 1, "equivalent": 0, "not_generated": 1})
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
}
