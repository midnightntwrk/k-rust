//! Argued obligations (`[[coverage.argued]]`): an obligation of any family that no program covers
//! and the corpus's author argues stays in its family's obligations with status `argued` and its
//! argument, is neither covered nor open, and gives no target; an entry no family lists refuses
//! the command; an argument whose item a program covers is needless, a finding; and the verdicts
//! rendering, so the coverage lock, lists the argued ids. The guards fixture's corpus never halts,
//! so `wake` is matched and never fires, its condition never holds, the flip of `I` is unreached,
//! and no program writes the production `nop` a test adds.

mod flow_support;

use flow_support::{copy_dir, flow};
use kink_flow::{
    CommandFiles, EditAction, EditSpec, FlowCommand, FlowManifest, FrontEnd, ManifestFile,
    cli::{EXIT_NO, EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, dispatch},
    coverage::text,
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

/// A private copy of the guards fixture for one test.
fn guards(test: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-coverage-argued-{}", std::process::id()))
        .join(test)
        .join("guards");
    let _ = fs::remove_dir_all(&dir);
    copy_dir(&flow("guards"), &dir);
    dir
}

/// `dir`'s manifest with `entries` (`(item, argument)`) as its `[[coverage.argued]]`, replacing
/// the ones it had and its `[[coverage.invariant]]` tables.
fn argue(dir: &Path, entries: &[(&str, &str)]) {
    let entries = entries
        .iter()
        .map(|(item, argument)| (*item, *argument, None))
        .collect::<Vec<_>>();
    argue_on(dir, &[], &entries);
}

/// `dir`'s manifest with `invariants` (`(name, function, cells)`) as its
/// `[[coverage.invariant]]` and `entries` (`(item, argument, invariant)`) as its
/// `[[coverage.argued]]`, replacing the ones it had.
fn argue_on(
    dir: &Path,
    invariants: &[(&str, &str, &[&str])],
    entries: &[(&str, &str, Option<&str>)],
) {
    let path = dir.join("FLOW.toml");
    let text = fs::read_to_string(&path).unwrap();
    let first = ["\n[[coverage.invariant]]", "\n[[coverage.argued]]"]
        .iter()
        .filter_map(|table| text.find(table))
        .min();
    let mut text = match first {
        Some(at) => text[..=at].to_owned(),
        None => text,
    };
    let string = |text: &str| toml::Value::String(text.to_owned()).to_string();
    for (name, function, cells) in invariants {
        text.push_str(&format!(
            "\n[[coverage.invariant]]\nname = {}\nfunction = {}\ncells = [{}]\n",
            string(name),
            string(function),
            cells
                .iter()
                .map(|cell| string(cell))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    for (item, argument, invariant) in entries {
        text.push_str(&format!(
            "\n[[coverage.argued]]\nitem = {}\nargument = {}\n",
            string(item),
            string(argument)
        ));
        if let Some(invariant) = invariant {
            text.push_str(&format!("invariant = {}\n", string(invariant)));
        }
    }
    fs::write(&path, text).unwrap();
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

/// The id of the flip of `I`, which no program of the fixture reaches.
const I: &str = "flip--halted+wake--I";
/// The id of the flip of `H`, which `irq` distinguishes.
const H: &str = "flip--dispatch+run+wake+halted--H";
const WAKE: &str = "rule:GUARDS.wake";
const DISPATCH: &str = "rule:GUARDS.dispatch";
const WAKE_HELD: &str = "requirement:GUARDS.wake:held";

/// The flips of `I` and, with `h`, of `H`, over the rules of `document`.
fn flips(document: &Value, h: bool) -> DerivedList {
    let occurrence = |label: &str, path: &str| Occurrence {
        sentence: sentence(document, label),
        reach: Reach::Operand {
            path: path.to_owned(),
        },
    };
    let mut entries = vec![DerivedEntry {
        id: I.to_owned(),
        operator: "flip".to_owned(),
        text: "I".to_owned(),
        atom: json!({"kind": "boolean", "head": "I"}),
        occurrences: vec![occurrence("wake", "0.1"), occurrence("halted", "0.1.0")],
        judged: Judged::Admitted {
            edits: vec![
                edit("wake", "H andThenBool I", "H andThenBool notBool I"),
                edit("halted", "H andThenBool notBool I", "H andThenBool I"),
            ],
        },
    }];
    if h {
        entries.insert(
            0,
            DerivedEntry {
                id: H.to_owned(),
                operator: "flip".to_owned(),
                text: "H".to_owned(),
                atom: json!({"kind": "boolean", "head": "H"}),
                occurrences: vec![
                    occurrence("dispatch", "0.0.0"),
                    occurrence("run", "0.0.0"),
                    occurrence("wake", "0.0"),
                    occurrence("halted", "0.0"),
                ],
                judged: Judged::Admitted {
                    edits: vec![
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
                    ],
                },
            },
        );
    }
    DerivedList {
        entries,
        ..DerivedList::default()
    }
}

/// The item of `family` whose id is `id`.
fn item<'d>(document: &'d Value, family: &str, id: &str) -> &'d Value {
    document["families"][family]["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|item| item["id"] == id)
        .unwrap_or_else(|| panic!("no {family} item {id}: {document:#}"))
}

/// Add to the fixture at `dir` a program production `nop()` that no program writes and no rule
/// names, so the syntax family has an unreached item.
fn with_nop(dir: &Path) {
    let path = dir.join("guards.k");
    let text = fs::read_to_string(&path).unwrap();
    let write = "| write(Int)       [symbol(write)]\n";
    assert!(text.contains(write), "{text}");
    let text = text.replace(
        write,
        &format!("{write}               | nop()             [symbol(nop)]\n"),
    );
    fs::write(&path, text).unwrap();
}

fn decode(text: &str) -> Result<ManifestFile, String> {
    let manifest = format!("[spec]\nentry = \"x.k\"\nmain_module = \"X\"\n{text}");
    ManifestFile::decode(&manifest, Path::new(".")).map_err(|e| e.to_string())
}

/// `[[coverage.argued]]` decodes to its entries in the order written; an entry has exactly
/// `item` and `argument`, an argument that is not blank, and names an item once.
#[test]
fn argued_entries_decode_and_their_mistakes_are_refused() {
    let file = decode(
        "[[coverage.argued]]\nitem = \"rule:b\"\nargument = \"no state reaches it\"\n\
         [[coverage.argued]]\nitem = \"rule:a\"\nargument = \"defensive\"\n",
    )
    .unwrap();
    let argued = file
        .coverage
        .argued
        .iter()
        .map(|a| (a.item.as_str(), a.argument.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(
        argued,
        [("rule:b", "no state reaches it"), ("rule:a", "defensive")]
    );
    assert!(file.coverage.declared);
    assert!(decode("").unwrap().coverage.argued.is_empty());
    for (text, error) in [
        (
            "[[coverage.argued]]\nitem = \"rule:a\"\n",
            "coverage.argued[0].argument: missing required key",
        ),
        (
            "[[coverage.argued]]\nitem = \"rule:a\"\nargument = \"  \"\n",
            "coverage.argued[0].argument: is blank: say why no program covers the item",
        ),
        (
            "[[coverage.argued]]\nitem = \"\"\nargument = \"x\"\n",
            "coverage.argued[0].item: must not be empty",
        ),
        (
            "[[coverage.argued]]\nitem = \"rule:a\"\nargument = \"x\"\nwhy = \"y\"\n",
            "coverage.argued[0].why: unknown key",
        ),
        (
            "[[coverage.argued]]\nitem = \"rule:a\"\nargument = \"x\"\n\
             [[coverage.argued]]\nitem = \"rule:a\"\nargument = \"y\"\n",
            "coverage.argued[1].item: `rule:a` is argued twice (coverage.argued[0] argues it \
             first)",
        ),
        (
            "[coverage]\nargued = \"rule:a\"\n",
            "coverage.argued: expected [[coverage.argued]] tables",
        ),
    ] {
        assert_eq!(decode(text).unwrap_err(), error, "{text}");
    }
}

/// `[[coverage.invariant]]` decodes to its tables in the order written, and an argued entry's
/// `invariant` to the name it gives; a table has exactly `name`, `function` and `cells`, none
/// blank, a name no other table has and a nonempty list of cells without repeats, and an entry names a table
/// the manifest declares.
#[test]
fn invariants_decode_and_their_mistakes_are_refused() {
    let table = "[[coverage.invariant]]\nname = \"never-halted\"\nfunction = \"neverHalted\"\n\
                 cells = [\"k\", \"halted\"]\n";
    let entry = "[[coverage.argued]]\nitem = \"rule:a\"\nargument = \"x\"\n";
    let file = decode(&format!(
        "{table}{entry}invariant = \"never-halted\"\n\
         [[coverage.argued]]\nitem = \"rule:b\"\nargument = \"y\"\n"
    ))
    .unwrap();
    let invariants = &file.coverage.invariants;
    assert_eq!(invariants.len(), 1);
    assert_eq!(
        (
            invariants[0].name.as_str(),
            invariants[0].function.as_str(),
            invariants[0].cells.as_slice()
        ),
        (
            "never-halted",
            "neverHalted",
            &["k".to_owned(), "halted".to_owned()][..]
        )
    );
    let named = file
        .coverage
        .argued
        .iter()
        .map(|a| a.invariant.as_deref())
        .collect::<Vec<_>>();
    assert_eq!(named, [Some("never-halted"), None]);
    assert!(decode("").unwrap().coverage.invariants.is_empty());
    for (text, error) in [
        (
            "[[coverage.invariant]]\nname = \"i\"\ncells = [\"k\"]\n".to_owned(),
            "coverage.invariant[0].function: missing required key",
        ),
        (
            "[[coverage.invariant]]\nname = \"i\"\nfunction = \"f\"\n".to_owned(),
            "coverage.invariant[0].cells: missing required key",
        ),
        (
            "[[coverage.invariant]]\nfunction = \"f\"\ncells = [\"k\"]\n".to_owned(),
            "coverage.invariant[0].name: missing required key",
        ),
        (
            "[[coverage.invariant]]\nname = \" \"\nfunction = \"f\"\ncells = [\"k\"]\n".to_owned(),
            "coverage.invariant[0].name: is blank",
        ),
        (
            "[[coverage.invariant]]\nname = \"i\"\nfunction = \"\\t\"\ncells = [\"k\"]\n"
                .to_owned(),
            "coverage.invariant[0].function: is blank",
        ),
        (
            "[[coverage.invariant]]\nname = \"i\"\nfunction = \"f\"\ncells = []\n".to_owned(),
            "coverage.invariant[0].cells: names no cell: an invariant reads the cells its \
             function takes, one per parameter",
        ),
        (
            "[[coverage.invariant]]\nname = \"i\"\nfunction = \"f\"\ncells = [\"k\", \"k\"]\n"
                .to_owned(),
            "coverage.invariant[0].cells: names `k` twice",
        ),
        (
            "[[coverage.invariant]]\nname = \"i\"\nfunction = \"f\"\ncells = \"k\"\n".to_owned(),
            "coverage.invariant[0].cells: expected an array of cell names",
        ),
        (
            format!("{table}proof = {{ k2lean = \"../lean\" }}\n"),
            "coverage.invariant[0].proof: unknown key",
        ),
        (
            format!("{table}{table}"),
            "coverage.invariant[1].name: `never-halted` is declared twice \
             (coverage.invariant[0] declares it first)",
        ),
        (
            format!("{entry}invariant = \"never-halted\"\n"),
            "coverage.argued[0].invariant: `never-halted` names no [[coverage.invariant]] table",
        ),
        (
            format!("{table}{entry}invariant = 1\n"),
            "coverage.argued[0].invariant: expected a string",
        ),
        (
            "[coverage]\ninvariant = \"i\"\n".to_owned(),
            "coverage.invariant: expected [[coverage.invariant]] tables",
        ),
    ] {
        assert_eq!(decode(&text).unwrap_err(), error, "{text}");
    }
}

mod kink_tier {
    use super::*;

    /// An argued rule, requirement, syntax production and flip each have status `argued`, the
    /// status they would have as `unargued_status` and their argument; each stays in its
    /// family's obligations, is neither covered nor open, and gives no target, so the measure is
    /// the same and the summary counts them apart.
    #[test]
    #[ignore = "kink"]
    fn argued_items_are_counted_and_not_open() {
        let dir = guards("counted");
        with_nop(&dir);
        let (baseline, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_YES, "{baseline:#}");
        let list = flips(&baseline, false);
        let (before, status) = coverage(&dir, &[], Derived::Flips(&list));
        assert_eq!(status, EXIT_YES, "{before:#}");
        let argued = [
            (WAKE, "the corpus never halts the machine"),
            (WAKE_HELD, "the corpus never halts the machine"),
            ("syntax:nop", "no program needs a step that does nothing"),
            (I, "only a halted machine reads the interrupt flag"),
        ];
        argue(&dir, &argued);
        let (after, status) = coverage(&dir, &[], Derived::Flips(&list));
        assert_eq!(status, EXIT_YES, "{after:#}");
        assert_eq!(after["version"], 19);
        for ((id, argument), (family, unargued)) in argued.iter().zip([
            ("rules", "matched"),
            ("requirements", "open"),
            ("syntax", "unreached"),
            ("flips", "unreached"),
        ]) {
            let item = item(&after, family, id);
            assert_eq!(
                (&item["status"], &item["unargued_status"], &item["argument"]),
                (&json!("argued"), &json!(unargued), &json!(argument)),
                "{item:#}"
            );
            assert!(item["argument_needless"].is_null(), "{item:#}");
            if family != "flips" {
                assert_eq!(item["covered"], false, "{item:#}");
            }
            let was = &before["summary"]["per_family"][family];
            let now = &after["summary"]["per_family"][family];
            assert_eq!(
                (&now["obligations"], &now["covered"]),
                (&was["obligations"], &was["covered"]),
                "{family}"
            );
            assert_eq!(now["argued"], 1, "{family}");
            assert_eq!(
                now["open"].as_u64().unwrap() + 1,
                was["open"].as_u64().unwrap(),
                "{family}"
            );
            assert_eq!(
                after["families"][family]["measure"], before["families"][family]["measure"],
                "{family}"
            );
            assert_eq!(after["families"][family]["argued"], 1, "{family}");
            assert_eq!(after["families"][family]["counts"]["argued"], 1, "{family}");
            assert!(
                after["targets"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|target| target["item"] != *id),
                "{id} is no target: {:#}",
                after["targets"]
            );
        }
        // The status each argued item had leaves its count.
        let counts = |document: &Value, family: &str, key: &str| {
            document["families"][family]["counts"][key]
                .as_u64()
                .unwrap()
        };
        assert_eq!(
            counts(&after, "rules", "matched") + 1,
            counts(&before, "rules", "matched")
        );
        assert_eq!(
            counts(&after, "requirements", "open") + 1,
            counts(&before, "requirements", "open")
        );
        assert_eq!(
            counts(&after, "syntax", "unreached") + 1,
            counts(&before, "syntax", "unreached")
        );
        assert_eq!(
            after["families"]["syntax"]["counts"]["productions"]["argued"],
            1
        );
        assert_eq!(counts(&after, "flips", "unreached"), 0);
        let summary = &after["summary"];
        assert_eq!(summary["argued"], 4, "{summary:#}");
        assert_eq!(summary["covered"], before["summary"]["covered"]);
        assert_eq!(
            summary["open"].as_u64().unwrap() + 4,
            before["summary"]["open"].as_u64().unwrap()
        );
        assert_eq!(
            summary["open"],
            json!(after["targets"].as_array().unwrap().len())
        );
        assert_eq!(summary["needless_arguments"], json!([]));
        assert_eq!(
            after["settings"]["argued"][0],
            json!({"item": WAKE, "argument": argued[0].1, "invariant": null})
        );
        // The text names each argued item with its argument.
        let text = text(&after).unwrap();
        assert!(
            text.contains(&format!(
                "argued:\n  {WAKE} [text]: the corpus never halts the machine\n"
            )),
            "{text}"
        );
        assert!(
            text.contains(&format!(
                "  {I} [text]: only a halted machine reads the interrupt flag\n"
            )),
            "{text}"
        );
        assert!(text.starts_with(&format!(
            "coverage: {} covered, 4 argued, {} open; 3 programs, 3 comparable\n",
            summary["covered"], summary["open"]
        )));
        // Deriving again gives the same document.
        let mut again = after.clone();
        kink_flow::coverage::derive(&mut again, &kink_flow::KinkFlowSpelling);
        assert_eq!(again, after);
    }

    /// An entry no family lists refuses the command at stage `coverage`, naming it, before any
    /// mutant runs. A flip's id is listed where the front end derives the flip, under tier 1 as
    /// under tier 2, and by no family where it derives none.
    #[test]
    #[ignore = "kink"]
    fn a_stale_id_is_refused() {
        let dir = guards("stale");
        let (baseline, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_YES, "{baseline:#}");
        let list = flips(&baseline, false);
        argue(
            &dir,
            &[
                ("rule:GUARDS.gone", "renamed"),
                (WAKE, "the corpus never halts the machine"),
            ],
        );
        let (refused, status) = coverage(&dir, &[], Derived::Flips(&list));
        assert_eq!(status, EXIT_UNASKED, "{refused:#}");
        let spec = &refused["spec"];
        assert_eq!(
            (&spec["outcome"], &spec["stage"], &spec["reason"]),
            (
                &json!("refused"),
                &json!("coverage"),
                &json!("argued-stale")
            ),
            "{spec:#}"
        );
        let detail = spec["detail"].as_str().unwrap();
        assert!(
            detail.contains("`rule:GUARDS.gone`: no family lists it"),
            "{detail}"
        );
        assert!(!detail.contains(WAKE), "{detail}");
        assert!(refused["families"].is_null(), "{refused:#}");
        assert!(verdicts(&refused).unwrap().contains(
            "\n[spec]\noutcome = \"refused\"\nstage = \"coverage\"\nreason = \"argued-stale\"\n"
        ));

        argue(
            &dir,
            &[(I, "only a halted machine reads the interrupt flag")],
        );
        for tier in [&[][..], &["--tier", "1"][..]] {
            let (document, status) = coverage(&dir, tier, Derived::Flips(&list));
            assert_eq!(status, EXIT_YES, "{tier:?}: {document:#}");
        }
        let (refused, status) = coverage(&dir, &[], Derived::default());
        assert_eq!(status, EXIT_UNASKED, "{refused:#}");
        let detail = refused["spec"]["detail"].as_str().unwrap();
        assert!(
            detail.contains(&format!(
                "`{I}`: no family lists it ({})",
                kink_flow::flips::DERIVES_NONE
            )),
            "{detail}"
        );
    }

    /// An argued item a program covers keeps its covered status and its argument, and the
    /// argument is needless: the summary lists it, the text says to remove it, and the command
    /// exits 1, since the argument kept would turn the item's next regression into `argued`
    /// instead of `open`. The requirement argued while no program halts becomes covered once a
    /// program halts with the interrupt flag set; a fired rule and a distinguished flip are
    /// covered from the start.
    #[test]
    #[ignore = "kink"]
    fn an_argued_item_that_becomes_covered_is_a_needless_argument() {
        let dir = guards("needless");
        let (baseline, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_YES, "{baseline:#}");
        let list = flips(&baseline, true);
        argue(&dir, &[(WAKE_HELD, "the corpus never halts the machine")]);
        let (argued, status) = coverage(&dir, &["--tier", "1"], Derived::Flips(&list));
        assert_eq!(status, EXIT_YES, "{argued:#}");
        assert_eq!(item(&argued, "requirements", WAKE_HELD)["status"], "argued");

        fs::write(dir.join("programs/wake.guards"), "step(true, true)\n").unwrap();
        let manifest = dir.join("FLOW.toml");
        let text_before = fs::read_to_string(&manifest).unwrap();
        let at = text_before.find("\n[[coverage.argued]]").unwrap();
        fs::write(
            &manifest,
            format!(
                "{}\n[[program]]\nid = \"wake\"\nfile = \"programs/wake.guards\"\n{}",
                &text_before[..at],
                &text_before[at..]
            ),
        )
        .unwrap();
        argue(
            &dir,
            &[
                (WAKE_HELD, "the corpus never halts the machine"),
                (DISPATCH, "a defensive rule"),
                (H, "a defensive flip"),
            ],
        );
        let (covered, status) = coverage(&dir, &[], Derived::Flips(&list));
        assert_eq!(status, EXIT_NO, "{covered:#}");
        for (family, id, status) in [
            ("requirements", WAKE_HELD, "covered"),
            ("rules", DISPATCH, "fired"),
            ("flips", H, "distinguished"),
        ] {
            let item = item(&covered, family, id);
            assert_eq!(
                (&item["status"], &item["argument_needless"]),
                (&json!(status), &json!("covered")),
                "{item:#}"
            );
            assert!(item["argument"].is_string(), "{item:#}");
            assert!(item["unargued_status"].is_null(), "{item:#}");
        }
        let summary = &covered["summary"];
        assert_eq!(summary["argued"], 0, "{summary:#}");
        assert_eq!(
            summary["needless_arguments"],
            json!([
                {"family": "rules", "item": DISPATCH, "reason": "covered"},
                {"family": "requirements", "item": WAKE_HELD, "reason": "covered"},
                {"family": "flips", "item": H, "reason": "covered"},
            ])
        );
        let text = text(&covered).unwrap();
        assert!(
            text.contains(&format!(
                "needless arguments:\n  {DISPATCH}: a program covers it; remove its \
                 [[coverage.argued]] entry\n"
            )),
            "{text}"
        );
    }

    /// The verdicts rendering lists each family's argued ids and an argued flip's status, so
    /// that a coverage lock moves when an argument is added or removed: `--locked` names the
    /// change, and a run rewrites the lock.
    #[test]
    #[ignore = "kink"]
    fn the_rendering_and_the_lock_move_when_an_argument_is_added() {
        let dir = guards("lock");
        let (baseline, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_YES, "{baseline:#}");
        let list = flips(&baseline, false);
        let lock = dir.join("coverage.lock");
        let path = lock.to_str().unwrap();
        let run = |locked: bool| {
            let mut options = vec!["--lock", path];
            if locked {
                options.push("--locked");
            }
            coverage(&dir, &options, Derived::Flips(&list))
        };
        let (plain, status) = run(false);
        assert_eq!(status, EXIT_YES, "{plain:#}");
        let recorded = fs::read_to_string(&lock).unwrap();
        assert_eq!(recorded, verdicts(&plain).unwrap());
        assert!(recorded.contains("\nversion = 22\n"), "{recorded}");
        assert!(
            recorded.contains(&format!("\n[rules]\nopen = [\n  \"{WAKE}\",\n")),
            "{recorded}"
        );
        assert!(
            !recorded.contains(&format!("argued = [\n  \"{WAKE}\",\n")),
            "{recorded}"
        );

        argue(
            &dir,
            &[
                (WAKE, "the corpus never halts the machine"),
                (I, "unreachable"),
            ],
        );
        let (stale, status) = run(true);
        assert_eq!(status, EXIT_NO, "{stale:#}");
        assert_eq!(stale["lock"]["status"], "stale");
        assert_eq!(
            stale["lock"]["open_changes"],
            json!([{"family": "rules", "obligation": WAKE, "recorded": "open", "now": "argued"}])
        );
        assert_eq!(
            stale_lines(&stale),
            [
                format!("{path}: rules: {WAKE} is argued (was open)"),
                format!("{path}: {I}: unreached -> argued"),
            ]
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
        let (argued, status) = run(false);
        assert_eq!(status, EXIT_YES, "{argued:#}");
        assert_eq!(argued["lock"]["status"], "written");
        let rewritten = fs::read_to_string(&lock).unwrap();
        assert!(
            rewritten.contains(&format!(
                "\n[rules]\nopen = [\n  \"rule:GUARDS.halted\",\n  \"rule:GUARDS.high\",\n]\n\
                 argued = [\n  \"{WAKE}\",\n]\n"
            )),
            "{rewritten}"
        );
        assert!(
            rewritten.contains(&format!("\n[[flip]]\nid = \"{I}\"\nstatus = \"argued\"\n")),
            "{rewritten}"
        );
        // An argument's text is no verdict: rewording it leaves the rendering as it is.
        argue(
            &dir,
            &[(WAKE, "no program halts the machine"), (I, "unreachable")],
        );
        let (reworded, status) = run(true);
        assert_eq!(status, EXIT_YES, "{reworded:#}");
        assert_eq!(reworded["lock"]["status"], "unchanged");

        // Removing the arguments opens the items again.
        argue(&dir, &[]);
        let (removed, status) = run(true);
        assert_eq!(status, EXIT_NO, "{removed:#}");
        assert_eq!(
            stale_lines(&removed),
            [
                format!("{path}: rules: {WAKE} is open (was argued)"),
                format!("{path}: {I}: argued -> unreached"),
            ]
        );
    }

    /// The invariant the guards fixture's refusals name, which its definition does not hold.
    const NEVER_HALTED: (&str, &str, &[&str]) = ("never-halted", "neverHalted", &["k"]);

    /// The invariant fixture's invariants: `a` is at most `b`, and no key of `memory` lies in the
    /// ROM region below `romEnd`, as its violation (`false` where some binding is in the region,
    /// `true` otherwise) and as a fold over its keys.
    const ORDERED: (&str, &str, &[&str]) = ("ordered", "ordered", &["a", "b"]);
    const OUTSIDE_ROM: (&str, &str, &[&str]) = ("outside-rom", "outsideRom", &["memory", "romEnd"]);
    const OUTSIDE_ROM_KEYS: (&str, &str, &[&str]) =
        ("outside-rom-keys", "outsideRomKeys", &["memory", "romEnd"]);
    const BUMP: &str = "rule:INVARIANT.bump";
    const BUMP_HELD: &str = "requirement:INVARIANT.bump:held";
    const READZ_REFUTED: &str = "requirement:INVARIANT.readz:refuted";
    const READZ_ROM_HELD: &str = "requirement:INVARIANT.readzRom:held";
    /// The equation of `ordered`, which no rule applies.
    const ORDERED_EQUATION: &str = "rule:invariant.k:63";

    /// A private copy of the invariant fixture for one test.
    fn invariant(test: &str) -> PathBuf {
        let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("kink-flow-coverage-argued-{}", std::process::id()))
            .join(test)
            .join("invariant");
        let _ = fs::remove_dir_all(&dir);
        copy_dir(&flow("invariant"), &dir);
        dir
    }

    /// The same order with its cells swapped, `b <=Int a`, the memory invariant under another
    /// function, and a claim false of every state.
    const REVERSED: (&str, &str, &[&str]) = ("reversed", "ordered", &["b", "a"]);
    const OUTSIDE_ROM_TOO: (&str, &str, &[&str]) =
        ("outside-rom-too", "outsideRomToo", &["memory", "romEnd"]);
    const NEVER: (&str, &str, &[&str]) = ("never", "never", &["a"]);

    /// The cause of a connection the portable profile leaves to a solver it does not have.
    #[cfg(not(feature = "z3"))]
    const NO_SOLVER: &str = "no solver decides the simplified predicate";

    /// An argued item's invariant is checked by its connection, through kink-flow's K front end
    /// (the function by its K label, the cells by their K names, `settings.invariants[].identity`):
    /// - `readzRom`'s `inRom(E, A)` under the violation form over `memory`'s bindings: its `false`
    ///   equation applies at the binding the rule matches under the item's condition, so the
    ///   connection holds. The corpus only idles, so no run steps a rule that can step where
    ///   `readzRom` matches, and the invariant holds at the initial state and the end: the
    ///   evidence is vacuous, and the item is `connected`;
    /// - the invariant as a fold over `keys_list(memory)` does not unfold there, so `readz`'s refuted
    ///   condition is undecided, with the cause;
    /// - a firing of `bump`, the one fact that covers `rule:bump`, needs `A >Int B`: under the Z3
    ///   profile, under `a <=Int b` it has no model at the left-hand side (the connection holds),
    ///   and under the same order with its cells swapped, `b <=Int a`, `requirement:bump:held`
    ///   has one, so that argument fails, `rule:bump` is `connected` (its evidence is vacuous),
    ///   and the command exits 1. The portable profile has no solver to decide either: both
    ///   connections are undecided, so `rule:bump` is `unchecked`; `b <=Int a` is false at the
    ///   initial state, so the evidence refutes `requirement:bump:held`, and the command exits 1
    ///   too. Either way the refuted item is open again with its target and `argument_failed`.
    ///
    /// A second run reads every answer the memo keeps from it, and the portable profile's
    /// undecided answers are not kept; another function, and another definition, each ask again.
    /// An invariant false of every state excludes everything (the simplification alone shows it),
    /// and its evidence fails at the initial state: the argument is refuted (exit 1).
    #[test]
    #[ignore = "kink"]
    fn an_invariants_connection_holds_fails_or_is_undecided() {
        let dir = invariant("connection");
        let entries = |walk: (&'static str, &'static str, &'static [&'static str])| {
            vec![
                (BUMP, "no state has a above b", Some(ORDERED.0)),
                (BUMP_HELD, "no state has a above b", Some(REVERSED.0)),
                (READZ_ROM_HELD, "memory holds no ROM address", Some(walk.0)),
                (
                    READZ_REFUTED,
                    "memory holds no ROM address",
                    Some(OUTSIDE_ROM_KEYS.0),
                ),
            ]
        };
        argue_on(
            &dir,
            &[ORDERED, REVERSED, OUTSIDE_ROM, OUTSIDE_ROM_KEYS],
            &entries(OUTSIDE_ROM),
        );
        let (document, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_NO, "{document:#}");
        assert_eq!(document["version"], 19);
        let check = |id: &str| &item(&document, "requirements", id)["argument_check"];
        let walk = check(READZ_ROM_HELD);
        assert_eq!(
            (
                &walk["invariant"],
                &walk["standing"],
                &walk["connection"]["status"]
            ),
            (&json!("outside-rom"), &json!("connected"), &json!("holds")),
            "{walk:#}"
        );
        assert_eq!(walk["reason"], Value::Null, "{walk:#}");
        assert_eq!(walk["connection"]["model"], Value::Null);
        assert_eq!(walk["connection"]["cached"], false);
        assert_eq!(
            (
                &walk["evidence"]["status"],
                &walk["evidence"]["rules"],
                &walk["evidence"]["steps"],
                &walk["evidence"]["programs"],
            ),
            (
                &json!("vacuous"),
                &json!(["INVARIANT.readz", "INVARIANT.readzRom"]),
                &json!(0),
                &json!(["idle"]),
            ),
            "{walk:#}"
        );
        let axioms = walk["connection"]["axioms"].as_array().unwrap();
        assert!(!axioms.is_empty(), "{walk:#}");
        assert!(
            axioms.iter().all(|axiom| axiom["answer"] == "connected"),
            "{walk:#}"
        );
        let fold = check(READZ_REFUTED);
        assert_eq!(
            (&fold["standing"], &fold["connection"]["status"]),
            (&json!("unchecked"), &json!("undecided")),
            "{fold:#}"
        );
        assert!(fold["connection"]["reason"].is_string(), "{fold:#}");
        let fired = &item(&document, "rules", BUMP)["argument_check"];
        assert!(
            fired["connection"]["axioms"]
                .as_array()
                .unwrap()
                .iter()
                .all(|axiom| axiom["valuation"] == "held"),
            "{fired:#}"
        );
        let summary = &document["summary"];
        let text = text(&document).unwrap();
        let held = item(&document, "requirements", BUMP_HELD);
        assert_eq!(held["status"], "open", "{held:#}");
        assert!(held.get("argument_check").is_none(), "{held:#}");
        assert!(
            document["targets"]
                .as_array()
                .unwrap()
                .iter()
                .any(|target| target["item"] == BUMP_HELD),
            "{:#}",
            document["targets"]
        );
        #[cfg(feature = "z3")]
        {
            assert_eq!(
                (&fired["standing"], &fired["connection"]["status"]),
                (&json!("connected"), &json!("holds")),
                "{fired:#}"
            );
            assert!(
                text.contains(&format!(
                    "  {BUMP} [connected, invariant ordered]: no state has a above b\n"
                )),
                "{text}"
            );
            let failed = &held["argument_failed"];
            assert_eq!(failed["check"], "connection", "{held:#}");
            let detail = failed["detail"].as_str().unwrap();
            assert!(
                detail.contains("satisfies the invariant `reversed`")
                    && detail.ends_with("so the invariant does not exclude the item"),
                "{detail}"
            );
            assert_eq!(
                summary["failed_arguments"],
                json!([{"family": "requirements", "item": BUMP_HELD, "check": "connection",
                        "detail": detail}])
            );
            assert_eq!(
                summary["argued_by_standing"],
                json!({"text": 0, "connected": 2, "checked_on_runs": 0, "proved": 0,
                       "unchecked": 1})
            );
            // One evidence run per invariant whose argued item's connection does not fail.
            assert_eq!(summary["invariant_runs"], json!({"run": 3, "cached": 0}));
            assert!(
                text.contains(&format!(
                    "failed arguments:\n  {BUMP_HELD} [the connection fails]: {detail}; it is \
                     open again\n"
                )),
                "{text}"
            );
        }
        #[cfg(not(feature = "z3"))]
        {
            assert_eq!(fired["standing"], "unchecked", "{fired:#}");
            assert!(
                text.contains(&format!(
                    "  {BUMP} [unchecked, invariant ordered]: no state has a above b\n"
                )),
                "{text}"
            );
            for connection in [&fired["connection"], &fold["connection"]] {
                assert_eq!(
                    (&connection["status"], &connection["reason"]),
                    (&json!("undecided"), &json!(NO_SOLVER)),
                    "{connection:#}"
                );
            }
            // Undecided, the connection refutes nothing; `b <=Int a` is false at the initial
            // state, and the evidence does.
            let failed = &held["argument_failed"];
            assert_eq!(
                (&failed["check"], &failed["detail"]),
                (
                    &json!("evidence"),
                    &json!(
                        "the invariant `reversed` is false in the run of the program `idle`, at \
                         its initial state, where the cells hold \
                         Lbl'-LT-'b'-GT-'{}(\\dv{SortInt{}}(\"1\")) and \
                         Lbl'-LT-'a'-GT-'{}(\\dv{SortInt{}}(\"0\")), so it is no invariant of \
                         the definition"
                    )
                ),
                "{held:#}"
            );
            assert_eq!(
                summary["argued_by_standing"],
                json!({"text": 0, "connected": 1, "checked_on_runs": 0, "proved": 0,
                       "unchecked": 2})
            );
            assert_eq!(summary["invariant_runs"], json!({"run": 4, "cached": 0}));
        }

        let invariants = document["settings"]["invariants"].as_array().unwrap();
        let cell = |name: &str| {
            json!([
                "Lbl'-LT-'generatedTop'-GT-'",
                "Lbl'-LT-'t'-GT-'",
                format!("Lbl'-LT-'{name}'-GT-'")
            ])
        };
        let identity = &invariants[0]["identity"];
        assert_eq!(
            (&identity["symbol"], &identity["cells"]),
            (&json!("Lblordered"), &json!([cell("a"), cell("b")])),
            "{identity:#}"
        );
        assert_eq!(
            identity["definition"], document["spec"]["execution_digest"],
            "{identity:#}"
        );
        assert_eq!(
            invariants[1]["identity"]["cells"],
            json!([cell("b"), cell("a")])
        );
        assert_eq!(
            invariants[2]["identity"]["cells"],
            json!([cell("memory"), cell("romEnd")])
        );

        // A second run reads every kept answer from the memo.
        let (again, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        let connection = |document: &Value, family: &str, id: &str| {
            item(document, family, id)["argument_check"]["connection"].clone()
        };
        let walk = |document: &Value| connection(document, "requirements", READZ_ROM_HELD);
        assert_eq!(
            (&walk(&again)["status"], &walk(&again)["cached"]),
            (&json!("holds"), &json!(true)),
            "{again:#}"
        );
        // A connected answer is kept; an answer for want of a solver is asked again.
        assert_eq!(
            connection(&again, "rules", BUMP)["cached"],
            json!(cfg!(feature = "z3")),
            "{again:#}"
        );
        assert_eq!(
            again["summary"]["failed_arguments"],
            summary["failed_arguments"]
        );
        // Every program's evidence is read from the memo.
        let runs = &summary["invariant_runs"];
        assert_eq!(
            again["summary"]["invariant_runs"],
            json!({"run": 0, "cached": runs["run"]})
        );

        // Another function with the same equations is another question.
        argue_on(
            &dir,
            &[ORDERED, REVERSED, OUTSIDE_ROM_TOO, OUTSIDE_ROM_KEYS],
            &entries(OUTSIDE_ROM_TOO),
        );
        let (other, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(
            (&walk(&other)["status"], &walk(&other)["cached"]),
            (&json!("holds"), &json!(false)),
            "{other:#}"
        );
        // So is the same function of another definition.
        let source = dir.join("invariant.k");
        let k = fs::read_to_string(&source).unwrap();
        let equation = "rule outsideRomToo(M, E) => outsideRom(M, E)";
        assert!(k.contains(equation), "{k}");
        fs::write(
            &source,
            k.replace(
                equation,
                "rule outsideRomToo(M, E) => outsideRom(M, E) andBool true",
            ),
        )
        .unwrap();
        let (edited, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(
            (&walk(&edited)["status"], &walk(&edited)["cached"]),
            (&json!("holds"), &json!(false)),
            "{edited:#}"
        );

        // An invariant false of every state excludes everything, and is false at the initial
        // state: its evidence fails there, so the argument is refuted.
        argue_on(
            &dir,
            &[NEVER],
            &[(BUMP, "no state is ever reached", Some(NEVER.0))],
        );
        let (never, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_NO, "{never:#}");
        let bump = item(&never, "rules", BUMP);
        assert_eq!(bump["status"], "unmatched", "{bump:#}");
        let failed = &bump["argument_failed"];
        assert_eq!(failed["check"], "evidence", "{bump:#}");
        let zero = "Lbl'-LT-'a'-GT-'{}(\\dv{SortInt{}}(\"0\"))";
        assert_eq!(
            failed["detail"],
            format!(
                "the invariant `never` is false in the run of the program `idle`, at its initial \
                 state, where the cells hold {zero}, so it is no invariant of the definition"
            )
        );
        let check = &never[kink_flow::coverage::ARGUMENT_CHECKS][BUMP];
        assert_eq!(check["connection"]["status"], "holds", "{check:#}");
        assert_eq!(
            check["evidence"]["failure"],
            json!({"program": "idle", "at": "initial", "rule": null, "index": null,
                   "cells": [zero], "cells_missing": null})
        );
    }

    /// `dir`'s manifest with the programs `programs` (`(id, text)`) after its own.
    fn with_programs(dir: &Path, programs: &[(&str, &str)]) {
        let path = dir.join("FLOW.toml");
        let text = fs::read_to_string(&path).unwrap();
        let idle = "text = \"idle\"\n";
        assert!(text.contains(idle), "{text}");
        let added = programs
            .iter()
            .map(|(id, program)| format!("\n[[program]]\nid = \"{id}\"\ntext = \"{program}\"\n"))
            .collect::<String>();
        fs::write(&path, text.replacen(idle, &format!("{idle}{added}"), 1)).unwrap();
    }

    /// An argued item's evidence reads its invariant on every comparable program's run: at the
    /// initial state, before each step of a rule that can step where the item's rule matches (for
    /// `readzRom`, `readz` and `readzRom`), and at each end.
    /// - `read(8)` steps `readz` at a memory with no ROM address, so the invariant holds at every state
    ///   read, one of them before a step: `requirement:readzRom:held` is `checked-on-runs` (its
    ///   connection holds in both profiles); no program bumps, so the evidence of `rule:bump` is
    ///   vacuous, and it is `connected` under the Z3 profile, `unchecked` (exit 3) under the
    ///   portable one, whose connection is undecided;
    /// - a second run reads each program's evidence from the memo;
    /// - `write(2, 1) ; read(8)` stores at the ROM address 2 and then reads 8: the walk is false
    ///   before the step of `readz`, at its first arrival, so the evidence fails there, naming the
    ///   program, the rule, the arrival and the cells, and the argument is refuted (exit 1).
    #[test]
    #[ignore = "kink"]
    fn an_invariants_evidence_is_read_where_its_rule_can_match() {
        let dir = invariant("evidence");
        with_programs(&dir, &[("clean", "read(8)")]);
        let entries = [
            (
                READZ_ROM_HELD,
                "memory holds no ROM address",
                Some(OUTSIDE_ROM.0),
            ),
            (BUMP, "no state has a above b", Some(ORDERED.0)),
        ];
        argue_on(&dir, &[OUTSIDE_ROM, ORDERED], &entries);
        let (document, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        let (exit, bumped) = if cfg!(feature = "z3") {
            (EXIT_YES, "connected")
        } else {
            (EXIT_UNANSWERED, "unchecked")
        };
        assert_eq!(status, exit, "{document:#}");
        let walk = &item(&document, "requirements", READZ_ROM_HELD)["argument_check"];
        assert_eq!(walk["standing"], "checked-on-runs", "{walk:#}");
        assert_eq!(
            walk["evidence"],
            json!({
                "status": "holds",
                "rules": ["INVARIANT.readz", "INVARIANT.readzRom"],
                "states": 5,
                "steps": 1,
                "programs": ["idle", "clean"],
                "failure": null,
                "reason": null,
                "cached": false,
            }),
            "{walk:#}"
        );
        let bump = &item(&document, "rules", BUMP)["argument_check"];
        assert_eq!(
            (&bump["standing"], &bump["evidence"]["status"]),
            (&json!(bumped), &json!("vacuous")),
            "{bump:#}"
        );
        let summary = &document["summary"];
        assert_eq!(
            summary["argued_by_standing"],
            json!({"text": 0, "connected": u8::from(cfg!(feature = "z3")), "checked_on_runs": 1,
                   "proved": 0, "unchecked": u8::from(!cfg!(feature = "z3"))})
        );
        assert_eq!(summary["invariant_runs"], json!({"run": 4, "cached": 0}));
        let rendered = text(&document).unwrap();
        assert!(
            rendered.contains(&format!(
                "  {READZ_ROM_HELD} [checked-on-runs, invariant outside-rom]: memory holds no ROM \
                 address\n"
            )),
            "{rendered}"
        );

        // A second run reads every program's evidence from the memo.
        let (again, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, exit, "{again:#}");
        assert_eq!(
            again["summary"]["invariant_runs"],
            json!({"run": 0, "cached": 4})
        );
        let walk = &item(&again, "requirements", READZ_ROM_HELD)["argument_check"];
        assert_eq!(
            (&walk["standing"], &walk["evidence"]["cached"]),
            (&json!("checked-on-runs"), &json!(true)),
            "{walk:#}"
        );

        // A program that stores a ROM address before a read breaks the invariant there.
        with_programs(&dir, &[("dirty", "write(2, 1) ; read(8)")]);
        let (broken, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_NO, "{broken:#}");
        let held = item(&broken, "requirements", READZ_ROM_HELD);
        assert_eq!(held["status"], "open", "{held:#}");
        let failed = &held["argument_failed"];
        assert_eq!(failed["check"], "evidence", "{held:#}");
        let check = &broken[kink_flow::coverage::ARGUMENT_CHECKS][READZ_ROM_HELD];
        let failure = &check["evidence"]["failure"];
        assert_eq!(
            (
                &failure["program"],
                &failure["at"],
                &failure["rule"],
                &failure["index"]
            ),
            (
                &json!("dirty"),
                &json!("step"),
                &json!("INVARIANT.readz"),
                &json!(0)
            ),
            "{check:#}"
        );
        let cells = failure["cells"].as_array().unwrap();
        assert_eq!(
            cells[1], "Lbl'-LT-'romEnd'-GT-'{}(\\dv{SortInt{}}(\"4\"))",
            "{failure:#}"
        );
        assert!(
            cells[0]
                .as_str()
                .is_some_and(|memory| memory.contains("\\dv{SortInt{}}(\"2\")")),
            "{failure:#}"
        );
        let detail = failed["detail"].as_str().unwrap();
        assert!(
            detail.starts_with(
                "the invariant `outside-rom` is false in the run of the program `dirty`, before \
                 the step of `INVARIANT.readz` at its arrival 0, where the cells hold "
            ),
            "{detail}"
        );
        assert_eq!(
            broken["summary"]["failed_arguments"],
            json!([{"family": "requirements", "item": READZ_ROM_HELD, "check": "evidence",
                    "detail": detail}])
        );
        let rendered = text(&broken).unwrap();
        assert!(
            rendered.contains(&format!(
                "failed arguments:\n  {READZ_ROM_HELD} [the evidence fails]: {detail}; it is open \
                 again\n"
            )),
            "{rendered}"
        );
        // `rule:bump` rests on another invariant, which holds wherever it is read.
        assert_eq!(
            item(&broken, "rules", BUMP)["argument_check"]["standing"],
            bumped
        );
    }

    /// `dir`'s copy of the fixture's definition with `find` replaced by `replace`, once.
    fn edit_k(dir: &Path, find: &str, replace: &str) {
        let source = dir.join("invariant.k");
        let k = fs::read_to_string(&source).unwrap();
        assert!(k.contains(find), "{k}");
        fs::write(&source, k.replacen(find, replace, 1)).unwrap();
    }

    /// `dir`'s manifest with `section` (TOML tables) before its programs.
    fn with_section(dir: &Path, section: &str) {
        let path = dir.join("FLOW.toml");
        let text = fs::read_to_string(&path).unwrap();
        let programs = "\n[[program]]\n";
        assert!(text.contains(programs), "{text}");
        fs::write(
            &path,
            text.replacen(programs, &format!("\n{section}{programs}"), 1),
        )
        .unwrap();
    }

    /// The evidence of `id` in `document`, and its status.
    fn evidence_of<'d>(document: &'d Value, id: &str) -> &'d Value {
        &document[kink_flow::coverage::ARGUMENT_CHECKS][id]["evidence"]
    }

    /// An evidence is `incomplete` wherever a state of the item's set is not read, and its
    /// `reason` says which:
    /// - a rule that can step where `readzRom` matches and has no label, whose steps no run can
    ///   observe (the fixture gains one beside `readz`);
    /// - a program that is not comparable (`spin`, which a depth bound cuts): without it the
    ///   evidence of `rule:bump` is vacuous, so it would read as `connected` while one program's
    ///   states were never read;
    /// - a path that ends at an undefined step (`crash` divides by zero), whose last state is no
    ///   end and no point;
    /// - a run of several paths of which one is cut by a bound (`pick` either ends or spins, with
    ///   `[observe]` making it a prefix program): the record keeps only the nearest point at which
    ///   a path stops being explored, so what the other paths hold past theirs is not known, and
    ///   the state the bound cut is not read.
    #[test]
    #[ignore = "kink"]
    fn an_invariants_evidence_is_incomplete_where_a_state_is_not_read() {
        let dir = invariant("incomplete");
        edit_k(
            &dir,
            "endmodule\n\nmodule INVARIANT\n",
            "  syntax Pgm ::= \"spin\" [symbol(spin)] | \"crash\" [symbol(crash)]\n                 \
             | \"pick\" [symbol(pick)]\nendmodule\n\nmodule INVARIANT\n",
        );
        edit_k(
            &dir,
            "  rule [idle]: <k> idle => .K ... </k>\n",
            "  rule [idle]: <k> idle => .K ... </k>\n  rule [spin]: <k> spin => spin ... </k>\n  \
             rule [crash]: <k> crash => .K ... </k> <a> A => A /Int 0 </a>\n  rule [pick]: <k> \
             pick => .K ... </k>\n  rule [pickSpin]: <k> pick => spin ... </k>\n",
        );
        let entries = [
            (BUMP, "no state has a above b", Some(ORDERED.0)),
            (
                READZ_ROM_HELD,
                "memory holds no ROM address",
                Some(OUTSIDE_ROM.0),
            ),
        ];
        argue_on(&dir, &[ORDERED, OUTSIDE_ROM], &entries);
        with_section(&dir, "[budget]\nmax_depth = 20\n");
        let fresh = |programs: &[(&str, &str)], section: Option<&str>| {
            let copy = invariant(&format!("incomplete-{}", programs[0].0));
            fs::remove_dir_all(&copy).unwrap();
            copy_dir(&dir, &copy);
            with_programs(&copy, programs);
            if let Some(section) = section {
                with_section(&copy, section);
            }
            coverage(&copy, &["--tier", "1"], Derived::default()).0
        };
        let incomplete = |document: &Value, id: &str, reason: &str| {
            let evidence = evidence_of(document, id);
            assert_eq!(evidence["status"], "incomplete", "{evidence:#}");
            assert!(
                evidence["reason"]
                    .as_str()
                    .is_some_and(|written| written.contains(reason)),
                "{evidence:#}"
            );
            assert_eq!(
                item(
                    document,
                    if id == BUMP { "rules" } else { "requirements" },
                    id
                )["argument_check"]["standing"],
                "unchecked"
            );
        };

        // The idle corpus reads the order everywhere it must, with no step of `bump`; a rule with
        // no label can step where `readzRom` matches.
        let (idle, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(evidence_of(&idle, BUMP)["status"], "vacuous", "{idle:#}");
        edit_k(
            &dir,
            "  rule [idle]:",
            "  rule <k> read(A) => .K ... </k> <memory> M </memory> requires notBool A in_keys(M)\n  \
             rule [idle]:",
        );
        let (unlabeled, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        incomplete(
            &unlabeled,
            READZ_ROM_HELD,
            "has no label a run observes it by",
        );
        let rules = evidence_of(&unlabeled, READZ_ROM_HELD)["rules"]
            .as_array()
            .unwrap()
            .clone();
        assert!(
            rules.iter().any(|rule| rule == "INVARIANT.readz")
                && rules
                    .iter()
                    .any(|rule| !rule.as_str().unwrap().starts_with("INVARIANT.")),
            "{rules:?}"
        );
        assert_eq!(evidence_of(&unlabeled, BUMP)["status"], "vacuous");

        let spin = fresh(&[("spin", "spin")], None);
        assert_eq!(
            spin["programs"][1]["class"], "unknown",
            "{:#}",
            spin["programs"]
        );
        incomplete(&spin, BUMP, "the program `spin` is unknown");

        let crash = fresh(&[("crash", "crash")], None);
        assert_eq!(
            crash["programs"][1]["class"], "comparable",
            "{:#}",
            crash["programs"]
        );
        incomplete(
            &crash,
            BUMP,
            "in the program `crash`, a path ends at an undefined step, whose state the evidence \
             does not read",
        );

        let pick = fresh(
            &[("pick", "pick")],
            Some(
                "[[observe.point]]\nname = \"spins\"\nbefore = [\"INVARIANT.spin\"]\ncells = \
                 [\"a\"]\nstutter = \"count\"\n",
            ),
        );
        assert_eq!(
            pick["programs"][1]["class"], "comparable-prefix",
            "{:#}",
            pick["programs"]
        );
        incomplete(
            &pick,
            BUMP,
            "in the program `pick`, a bound cut the run at a state the evidence does not read",
        );
        incomplete(
            &pick,
            BUMP,
            "in the program `pick`, before the steps of `INVARIANT.bump`: the run has several \
             paths, and one stops being explored",
        );
    }

    /// An invariant whose value is not known at a state of a run leaves that state undecided, and
    /// the run is still read: `careful` is the violation form over a memory of one binding, and
    /// has no equation for a larger one: it is partial, so after `write(200, 1)` its evaluation
    /// ends at no `Bool` value, before the step of `readz` and at the end. Its one
    /// equation overlaps no other, so it is shown to be a function and its evidence is read. The
    /// evidence is `incomplete`, its reason names the state and why its value is not known, and
    /// the run is neither refused nor failed: the initial state, where the invariant is decided,
    /// is read too.
    #[test]
    #[ignore = "kink"]
    fn an_invariant_undecided_at_a_state_leaves_its_evidence_incomplete() {
        const CAREFUL: (&str, &str, &[&str]) = ("careful", "careful", &["memory", "romEnd"]);
        let dir = invariant("undecided");
        edit_k(
            &dir,
            "  syntax Bool ::= never(Int)",
            "  syntax Bool ::= careful(Map, Int) [function, symbol(careful)]\n  rule careful(M, E) \
             => outsideRom(M, E) requires size(M) <Int 2\n  syntax Bool ::= never(Int)",
        );
        with_programs(&dir, &[("high", "write(200, 1) ; read(8)")]);
        argue_on(
            &dir,
            &[CAREFUL],
            &[(
                READZ_ROM_HELD,
                "memory holds no ROM address",
                Some(CAREFUL.0),
            )],
        );
        let (document, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(
            document["programs"][1]["class"], "comparable",
            "{:#}",
            document["programs"]
        );
        let evidence = evidence_of(&document, READZ_ROM_HELD);
        assert_eq!(evidence["status"], "incomplete", "{evidence:#}");
        assert_eq!(
            evidence["programs"],
            json!(["idle", "high"]),
            "{evidence:#}"
        );
        let reason = evidence["reason"].as_str().unwrap_or_default();
        assert!(
            reason.contains(
                "in the program `high`, before the steps of `INVARIANT.readz`: the invariant's \
                 value is not known at a state: the invariant's evaluation ends at no Bool value"
            ) && reason.contains("in the program `high`, at the end 0: ")
                && !reason.contains("refused")
                && !reason.contains("failed"),
            "{evidence:#}"
        );
        assert_eq!(
            item(&document, "requirements", READZ_ROM_HELD)["argument_check"]["standing"],
            "unchecked"
        );
    }

    /// An invariant whose evaluation does not end leaves its state undecided, and the command
    /// ends: `settled` reads `<k>`, and where it holds `idle`, the corpus's initial state, it
    /// becomes `spin(a)`, whose equation `spin(N) => spin(N +Int 1)` rewrites a ground
    /// application without end and never to a term it reached before, so the simplifier's
    /// iteration budget, which no determined step spends, and its recurrence watch both let it
    /// run. The evaluation at the initial state spends its work bound (kink-native
    /// `invariant::EVALUATION_POLLS`) and is undecided, with a reason naming the bound. The
    /// initial state serves every item, so the cut leaves them all unchecked and the evidence run
    /// is not made. The evidence of `rule:bump` is `incomplete`, never `fails`, the item
    /// `unchecked`, and the command exits 3. Where the bound cuts is not shown to be a function
    /// of the cells alone, so the record is not kept: a second run evaluates the initial state
    /// again, and reads nothing from the memo.
    #[test]
    #[ignore = "kink"]
    fn an_invariant_whose_evaluation_does_not_end_is_undecided_within_its_work_bound() {
        const SETTLED: (&str, &str, &[&str]) = ("settled", "settled", &["k", "a", "b"]);
        let dir = invariant("work-bound");
        edit_k(
            &dir,
            "  syntax Bool ::= never(Int)",
            "  syntax Bool ::= settled(K, Int, Int) [function, symbol(settled)]\n                  \
             | spin(Int) [function, symbol(spin)]\n  rule settled(.K, A, B) => A <=Int B\n  rule \
             settled(idle, A, _) => spin(A)\n  rule settled(_, A, B) => A <=Int B [owise]\n  rule \
             spin(N) => spin(N +Int 1)\n  syntax Bool ::= never(Int)",
        );
        argue_on(
            &dir,
            &[SETTLED],
            &[(BUMP, "no state has a above b", Some(SETTLED.0))],
        );
        let (document, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let check = &item(&document, "rules", BUMP)["argument_check"];
        assert_eq!(check["standing"], "unchecked", "{check:#}");
        assert_eq!(check["function"]["status"], "shown", "{check:#}");
        let evidence = &check["evidence"];
        assert_eq!(
            (
                &evidence["status"],
                &evidence["failure"],
                &evidence["programs"]
            ),
            (&json!("incomplete"), &Value::Null, &json!(["idle"])),
            "{evidence:#}"
        );
        assert_eq!(
            evidence["reason"],
            format!(
                "in the program `idle`, at the initial state: the evaluation spent its work bound \
                 of {} polls before it reached a value; the run is not read, since that leaves \
                 every item unchecked",
                kink_native::invariant::EVALUATION_POLLS
            ),
            "{evidence:#}"
        );
        assert_eq!(evidence["states"], 1, "{evidence:#}");
        assert_eq!(document["summary"]["failed_arguments"], json!([]));
        assert_eq!(
            document["summary"]["invariant_runs"],
            json!({"run": 0, "cached": 0})
        );

        let (again, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_UNANSWERED, "{again:#}");
        assert_eq!(
            again["summary"]["invariant_runs"],
            json!({"run": 0, "cached": 0})
        );
        let computed = evidence_of(&again, BUMP);
        assert_eq!(
            (&computed["reason"], &computed["cached"]),
            (&evidence["reason"], &json!(false)),
            "{computed:#}"
        );
    }

    /// After a cut of the work bound, a state whose items are all unchecked is not evaluated,
    /// so a divergent invariant costs one bound per run, not one per state. `smallMemory` holds
    /// of a memory of one binding and becomes the divergent `spin` on a larger one. The program
    /// `many` writes a second binding and then reads it three times, so `readz` steps three
    /// times on a memory of two bindings: the first state before its step is cut, which leaves
    /// `requirement:readzRom:held`, the one item its rules serve, unchecked; the two later
    /// states and the end are not read, and the reason says so. The evidence is `incomplete`,
    /// the item `unchecked` (exit 3). `idle`'s record, which no cut touched, is kept and read
    /// from the memo on a second run; `many`'s is computed again.
    #[test]
    #[ignore = "kink"]
    fn after_a_cut_the_states_whose_items_are_unchecked_are_not_read() {
        const SMALL: (&str, &str, &[&str]) = ("small-memory", "smallMemory", &["memory"]);
        let dir = invariant("after-a-cut");
        edit_k(
            &dir,
            "  syntax Bool ::= never(Int)",
            "  syntax Bool ::= smallMemory(Map) [function, symbol(smallMemory)]\n                  \
             | spin(Int) [function, symbol(spin)]\n  rule smallMemory(M) => true requires size(M) \
             <Int 2\n  rule smallMemory(M) => spin(size(M)) [owise]\n  rule spin(N) => spin(N \
             +Int 1)\n  syntax Bool ::= never(Int)",
        );
        with_programs(
            &dir,
            &[("many", "write(2, 1) ; read(8) ; read(8) ; read(8)")],
        );
        argue_on(
            &dir,
            &[SMALL],
            &[(READZ_ROM_HELD, "memory stays small", Some(SMALL.0))],
        );
        let (document, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let check = &item(&document, "requirements", READZ_ROM_HELD)["argument_check"];
        assert_eq!(
            (&check["standing"], &check["function"]["status"]),
            (&json!("unchecked"), &json!("shown")),
            "{check:#}"
        );
        let evidence = &check["evidence"];
        assert_eq!(
            (
                &evidence["status"],
                &evidence["failure"],
                &evidence["programs"]
            ),
            (&json!("incomplete"), &Value::Null, &json!(["idle", "many"])),
            "{evidence:#}"
        );
        assert_eq!(
            evidence["reason"],
            format!(
                "in the program `many`, 1 end is not read, since a cut of the work bound leaves \
                 every item unchecked; in the program `many`, before the steps of \
                 `INVARIANT.readz`: the invariant's value is not known at a state: the \
                 evaluation spent its work bound of {} polls before it reached a value; 2 states \
                 are not read, since a cut of the work bound leaves every item they serve \
                 unchecked",
                kink_native::invariant::EVALUATION_POLLS
            ),
            "{evidence:#}"
        );
        assert_eq!(
            document["summary"]["invariant_runs"],
            json!({"run": 2, "cached": 0})
        );
        let (again, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(
            again["summary"]["invariant_runs"],
            json!({"run": 1, "cached": 1})
        );
        assert_eq!(
            evidence_of(&again, READZ_ROM_HELD)["reason"],
            evidence["reason"]
        );
    }

    /// An argued standing rests on every function its connection evaluates, not only on the
    /// invariant's: the connection simplifies the item's valuation too, the rule's guard
    /// functions included, with the backend's choice of matching. `ordered` is shown to be a
    /// function, and `rule:bump`'s question applies no other function of the definition, so its
    /// function is `shown`. `bigBump` steps where `big(a)` holds, and `big`'s two equations
    /// overlap and disagree for `a` from 6 to 10, a finding of the baseline's critical-pair
    /// check that no name assumes: under the same invariant, `rule:bigBump` is `unchecked`, its
    /// reason names `big`, its evidence is not read (`not-run`), and the command exits 3. The
    /// one evidence run of `ordered` is `rule:bump`'s.
    #[test]
    #[ignore = "kink"]
    fn an_argued_standing_rests_on_every_function_its_connection_evaluates() {
        const BIG_BUMP: &str = "rule:INVARIANT.bigBump";
        let dir = invariant("guard-function");
        edit_k(
            &dir,
            "  rule [idle]:",
            "  syntax Bool ::= big(Int) [function, symbol(big)]\n  rule big(A) => A >Int 10\n  \
             rule big(A) => true requires A >Int 5\n  rule [bigBump]: <k> bump => .K ... </k> <a> \
             A </a> <b> _ => A </b> requires big(A)\n  rule [idle]:",
        );
        argue_on(
            &dir,
            &[ORDERED],
            &[
                (BUMP, "no state has a above b", Some(ORDERED.0)),
                (BIG_BUMP, "no state has a above b", Some(ORDERED.0)),
            ],
        );
        let (document, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let bump = &item(&document, "rules", BUMP)["argument_check"];
        assert_eq!(
            bump["function"],
            json!({"status": "shown", "findings": [], "reason": null}),
            "{bump:#}"
        );
        let big = &item(&document, "rules", BIG_BUMP)["argument_check"];
        assert_eq!(
            (
                &big["standing"],
                &big["function"]["status"],
                &big["evidence"]
            ),
            (
                &json!("unchecked"),
                &json!("not-shown"),
                &json!({"status": "not-run"})
            ),
            "{big:#}"
        );
        assert!(
            !big["function"]["findings"].as_array().unwrap().is_empty(),
            "{big:#}"
        );
        let reason = big["reason"].as_str().unwrap();
        assert!(
            reason.starts_with(
                "the function `big`, which the connection evaluates beside the invariant's \
                 function `ordered`, is not shown to be a function: the baseline's critical-pair \
                 check has a finding no `[spec] assume_joined` name assumes"
            ) && !reason.contains("`ordered` is not shown"),
            "{reason}"
        );
        assert_eq!(document["summary"]["failed_arguments"], json!([]));
        assert_eq!(
            document["summary"]["invariant_runs"],
            json!({"run": 1, "cached": 0})
        );
    }

    /// A function a macro's expansion applies is applied by every program that writes the macro,
    /// so it is an obligation, though the macro has no equation for the reach of a run to follow:
    /// the syntax module's `probe(A)` expands to `write(addr(A), 0)`, and `addr` is applied by no
    /// rule and by the invariant `below-addr`. Its equation stays `unmatched` (no program writes
    /// `probe`), while the invariant's own equation is `invariant`.
    #[test]
    #[ignore = "kink"]
    fn a_function_a_macro_a_program_writes_applies_is_an_obligation() {
        const BELOW_ADDR: (&str, &str, &[&str]) = ("below-addr", "belowAddr", &["a", "b"]);
        let dir = invariant("macro");
        edit_k(
            &dir,
            "               | \"idle\"          [symbol(idle)]\n",
            "               | \"idle\"          [symbol(idle)]\n               | probe(Int)      \
             [macro]\n",
        );
        edit_k(
            &dir,
            "  rule [idle]:",
            "  syntax Int ::= addr(Int) [function, total, symbol(addr)]\n  rule [addrOf]: addr(A) \
             => A +Int 8\n  rule probe(A) => write(addr(A), 0)\n  syntax Bool ::= belowAddr(Int, \
             Int) [function, total, symbol(belowAddr)]\n  rule [below]: belowAddr(A, B) => A \
             <=Int addr(B)\n  rule [idle]:",
        );
        argue_on(
            &dir,
            &[BELOW_ADDR],
            &[(BUMP, "no state has a above b", Some(BELOW_ADDR.0))],
        );
        let (document, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        let status = |label: &str| {
            document["families"]["rules"]["items"]
                .as_array()
                .unwrap()
                .iter()
                .find(|item| {
                    item["label"]
                        .as_str()
                        .is_some_and(|l| l.ends_with(&format!(".{label}")))
                })
                .map(|item| item["status"].clone())
                .unwrap_or_else(|| panic!("no rule {label}: {document:#}"))
        };
        assert_eq!(status("addrOf"), "unmatched", "{document:#}");
        assert_eq!(status("below"), "invariant", "{document:#}");
    }

    /// One program's evidence of an invariant is read from the memo only under the same
    /// invariant and the same rules: the same invariant observed at more rules (another entry
    /// names it), and another invariant (another function of the same cell), each run again. The
    /// invariants are functions of `<k>`, which every rule's left-hand side holds, false of every
    /// state, so each connection holds by the simplification alone, in both profiles.
    #[test]
    #[ignore = "kink"]
    fn the_evidence_memo_misses_on_another_invariant_or_other_rules() {
        let dir = invariant("evidence-memo");
        edit_k(
            &dir,
            "  rule [idle]:",
            "  syntax Bool ::= noK(K) [function, total, symbol(noK)]\n                  | noKToo(K) \
             [function, total, symbol(noKToo)]\n  rule noK(_) => false\n  rule noKToo(_) => \
             false\n  rule [idle]:",
        );
        let no_k: (&str, &str, &[&str]) = ("no-k", "noK", &["k"]);
        let no_k_too: (&str, &str, &[&str]) = ("no-k-too", "noKToo", &["k"]);
        let runs = |document: &Value| document["summary"]["invariant_runs"].clone();
        let bump = (BUMP, "no state is ever reached", Some(no_k.0));
        argue_on(&dir, &[no_k], &[bump]);
        let (first, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(runs(&first), json!({"run": 1, "cached": 0}), "{first:#}");
        let (again, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(runs(&again), json!({"run": 0, "cached": 1}), "{again:#}");
        assert_eq!(evidence_of(&again, BUMP)["cached"], true);

        // Another entry on the invariant: its rules join the ones observed.
        let read = (READZ_ROM_HELD, "no state is ever reached", Some(no_k.0));
        argue_on(&dir, &[no_k], &[bump, read]);
        let (more, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(runs(&more), json!({"run": 1, "cached": 0}), "{more:#}");
        assert_eq!(evidence_of(&more, BUMP)["cached"], false);

        // Another invariant, at the same rules.
        let too = |(item, argument, _): (&'static str, &'static str, Option<&'static str>)| {
            (item, argument, Some(no_k_too.0))
        };
        argue_on(&dir, &[no_k_too], &[too(bump), too(read)]);
        let (other, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(runs(&other), json!({"run": 1, "cached": 0}), "{other:#}");
        assert_eq!(evidence_of(&other, BUMP)["status"], "fails", "{other:#}");
    }

    /// Every argued item says what its argument rests on (`argument_check`): its text alone where
    /// its entry names no invariant (`text`), else the invariant, its connection and its evidence:
    /// under the Z3 profile `connected` (the connection holds, and no run steps `bump`, exit 0),
    /// under the portable one `unchecked` (no solver decides the connection, exit 3).
    /// The settings list the invariants, the summary counts the argued items by
    /// standing, the text states each standing, and the coverage lock gives each argued item's
    /// standing under `[arguments]`: a standing that moves makes `--locked` stale, naming the
    /// item, while the header and the obligations are unchanged.
    #[test]
    #[ignore = "kink"]
    fn each_argued_item_states_its_standing_and_the_lock_records_it() {
        let dir = invariant("standing");
        let lock = dir.join("coverage.lock");
        let path = lock.to_str().unwrap();
        let run = |locked: bool| {
            let mut options = vec!["--lock", path];
            if locked {
                options.push("--locked");
            }
            coverage(&dir, &options, Derived::default())
        };
        argue_on(
            &dir,
            &[ORDERED],
            &[
                (BUMP, "the corpus never bumps", None),
                (BUMP_HELD, "no state has a above b", Some(ORDERED.0)),
            ],
        );
        let standing = if cfg!(feature = "z3") {
            "connected"
        } else {
            "unchecked"
        };
        let (document, status) = run(false);
        let exit = if cfg!(feature = "z3") {
            EXIT_YES
        } else {
            EXIT_UNANSWERED
        };
        assert_eq!(status, exit, "{document:#}");
        assert_eq!(
            item(&document, "rules", BUMP)["argument_check"],
            json!({"standing": "text"})
        );
        assert_eq!(
            item(&document, "requirements", BUMP_HELD)["argument_check"]["standing"],
            standing
        );
        assert_eq!(
            document["settings"]["argued"][1],
            json!({"item": BUMP_HELD, "argument": "no state has a above b",
                   "invariant": "ordered"})
        );
        let summary = &document["summary"];
        assert_eq!(
            summary["argued_by_standing"],
            json!({"text": 1, "connected": u8::from(cfg!(feature = "z3")), "checked_on_runs": 0,
                   "proved": 0, "unchecked": u8::from(!cfg!(feature = "z3"))})
        );
        assert_eq!(summary["failed_arguments"], json!([]));
        let text = text(&document).unwrap();
        assert!(
            text.contains(&format!(
                "argued:\n  {BUMP} [text]: the corpus never bumps\n"
            )),
            "{text}"
        );
        let recorded = fs::read_to_string(&lock).unwrap();
        assert!(
            recorded.contains(&format!(
                "\n[arguments]\n\"{BUMP}\" = \"text\"\n\"{BUMP_HELD}\" = \"{standing}\"\n"
            )),
            "{recorded}"
        );
        assert_eq!(recorded, verdicts(&document).unwrap());

        // The same items argued on their text alone: the requirement's standing moves, and the
        // equation of `ordered`, which only the dropped invariant reached, is an obligation again.
        argue(
            &dir,
            &[
                (BUMP, "the corpus never bumps"),
                (BUMP_HELD, "no state has a above b"),
            ],
        );
        let (stale, status) = run(true);
        assert_eq!(status, EXIT_NO, "{stale:#}");
        let state = &stale["lock"];
        assert_eq!(state["status"], "stale", "{state:#}");
        assert_eq!(
            (
                &state["header"],
                &state["header_changes"],
                &state["open_changes"]
            ),
            (
                &json!(false),
                &json!([]),
                &json!([{"family": "rules", "obligation": ORDERED_EQUATION, "recorded": null,
                         "now": "open"}])
            ),
            "{state:#}"
        );
        assert_eq!(
            state["argument_changes"],
            json!([{"obligation": BUMP_HELD, "recorded": standing, "now": "text"}])
        );
        assert!(
            stale_lines(&stale).contains(&format!(
                "{path}: arguments: {BUMP_HELD}: {standing} -> text"
            )),
            "{:?}",
            stale_lines(&stale)
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
    }

    /// The equations of `outsideRom`, the violation form, which no rule applies.
    const OUTSIDE_ROM_EQUATIONS: [&str; 2] = ["rule:invariant.k:41", "rule:invariant.k:42"];
    /// The memory invariant as a recursive walk over the map's bindings.
    const WALK: (&str, &str, &[&str]) = ("walk", "outsideRomWalk", &["memory", "romEnd"]);
    /// The equation of `inRom`, which the read rules' conditions apply too.
    const IN_ROM_EQUATION: &str = "rule:invariant.k:34";

    /// The sentence of the rules item `id` of `document`.
    fn sentence_of(document: &Value, id: &str) -> SentenceRef {
        let item = item(document, "rules", id);
        SentenceRef {
            module: item["module"].as_str().unwrap().to_owned(),
            index: u32::try_from(item["index"].as_u64().unwrap()).unwrap(),
        }
    }

    /// An equation of a function only the manifest's invariants reach is no obligation of any
    /// family (status `invariant`, with its reason), whatever the programs did: no rule applies
    /// `outsideRom`, so under the invariant `outside-rom` its two equations are no rules item to
    /// cover and the guarded one states no requirement, and a flip that changes only its
    /// condition is not generated, with the reason `invariant`. `inRom`, which the invariant
    /// applies too, is applied by the read rules' conditions, so its equation stays an
    /// obligation, and so does a flip of `readz`. Without the invariant, `outsideRom`'s
    /// equations are obligations again, its guard's requirements open.
    #[test]
    #[ignore = "kink"]
    fn an_equation_only_invariants_reach_is_no_obligation() {
        let dir = invariant("scope");
        with_programs(&dir, &[("clean", "read(8)")]);
        argue_on(
            &dir,
            &[OUTSIDE_ROM],
            &[(
                READZ_ROM_HELD,
                "memory holds no ROM address",
                Some(OUTSIDE_ROM.0),
            )],
        );
        let (plain, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        let flip = |id: &str, at: SentenceRef, path: &str, edits: Vec<EditSpec>| DerivedEntry {
            id: id.to_owned(),
            operator: "flip".to_owned(),
            text: "inRom(E, A)".to_owned(),
            atom: json!({"kind": "boolean", "head": "inRom"}),
            occurrences: vec![Occurrence {
                sentence: at,
                reach: Reach::Operand {
                    path: path.to_owned(),
                },
            }],
            judged: Judged::Admitted { edits },
        };
        let list = DerivedList {
            entries: vec![
                flip(
                    "flip--outsideRom--inRom",
                    sentence_of(&plain, OUTSIDE_ROM_EQUATIONS[0]),
                    "0",
                    Vec::new(),
                ),
                flip(
                    "flip--readz--inRom",
                    sentence(&plain, "readz"),
                    "0.0",
                    vec![edit("readz", "notBool inRom(E, A)", "inRom(E, A)")],
                ),
            ],
            ..DerivedList::default()
        };
        let (document, _) = coverage(&dir, &[], Derived::Flips(&list));
        assert_eq!(document["version"], 19);
        for id in OUTSIDE_ROM_EQUATIONS {
            let equation = item(&document, "rules", id);
            assert_eq!(equation["status"], "invariant", "{equation:#}");
            assert!(
                equation["reason"]
                    .as_str()
                    .is_some_and(|reason| reason.contains("only the manifest's invariants reach")),
                "{equation:#}"
            );
        }
        assert_eq!(item(&document, "rules", IN_ROM_EQUATION)["status"], "fired");
        let rules = &document["families"]["rules"];
        assert_eq!(rules["counts"]["invariant"], 2, "{:#}", rules["counts"]);
        let requirements = document["families"]["requirements"]["items"]
            .as_array()
            .unwrap();
        assert!(
            requirements
                .iter()
                .all(|item| !item["id"].as_str().unwrap().contains("invariant.k:41")),
            "{requirements:#?}"
        );
        let flips = &document["families"]["flips"];
        assert_eq!(
            (
                &flips["not_generated"][0]["id"],
                &flips["not_generated"][0]["reason"]
            ),
            (&json!("flip--outsideRom--inRom"), &json!("invariant")),
            "{flips:#}"
        );
        assert_eq!(
            flips["items"]
                .as_array()
                .unwrap()
                .iter()
                .map(|item| item["id"].clone())
                .collect::<Vec<_>>(),
            [json!("flip--readz--inRom")],
            "{flips:#}"
        );
        let rendered = text(&document).unwrap();
        assert!(rendered.contains(", 2 invariant, "), "{rendered}");

        // Argued on its text alone, no invariant is declared: `outsideRom`'s equations are
        // obligations, and its guard's requirements open.
        argue(&dir, &[(READZ_ROM_HELD, "memory holds no ROM address")]);
        let (unscoped, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        for id in OUTSIDE_ROM_EQUATIONS {
            assert_eq!(item(&unscoped, "rules", id)["status"], "unmatched");
        }
        assert_eq!(unscoped["families"]["rules"]["counts"]["invariant"], 0);
        for outcome in ["held", "refuted"] {
            let id = format!("requirement:{}:{outcome}", &OUTSIDE_ROM_EQUATIONS[0][5..]);
            assert_eq!(item(&unscoped, "requirements", &id)["status"], "open");
        }
    }

    /// An argued standing rests on its invariant being a function: both checks evaluate it with
    /// the backend's choice of matching. `outsideRom`, the violation form, has no finding of the
    /// baseline's critical-pair check (its `false` equation's result reads no binding the map
    /// pattern chose), so `requirement:readzRom:held` is `checked-on-runs` with the function
    /// `shown`. `outsideRomWalk`, the recursive walk, reads the binding it chose, and its two
    /// self-pairs are findings no `[spec] assume_joined` name assumes: `requirement:readz:refuted`,
    /// whose connection holds (by the simplification alone, in both profiles), is `unchecked`
    /// with a reason naming the findings and the canonical form, its evidence is not read
    /// (`not-run`: no state's value could refute or credit it, so the only evidence runs are
    /// `outside-rom`'s, one per program), and the command exits 3. With both findings assumed,
    /// its evidence is read and holds, its standing is the checks' again,
    /// `argument_check.function` records the premise (`assumed`, each finding marked), and the
    /// verdicts rendering's `[arguments]` line, a lock's, names it.
    #[test]
    #[ignore = "kink"]
    fn an_argued_standing_rests_on_its_invariant_being_a_function() {
        let dir = invariant("function");
        with_programs(&dir, &[("clean", "read(8)")]);
        argue_on(
            &dir,
            &[OUTSIDE_ROM, WALK],
            &[
                (
                    READZ_ROM_HELD,
                    "memory holds no ROM address",
                    Some(OUTSIDE_ROM.0),
                ),
                (READZ_REFUTED, "memory holds no ROM address", Some(WALK.0)),
            ],
        );
        let (document, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let guarded = &item(&document, "requirements", READZ_ROM_HELD)["argument_check"];
        assert_eq!(
            (&guarded["standing"], &guarded["function"]),
            (
                &json!("checked-on-runs"),
                &json!({"status": "shown", "findings": [], "reason": null})
            ),
            "{guarded:#}"
        );
        let walk = &item(&document, "requirements", READZ_REFUTED)["argument_check"];
        assert_eq!(
            (
                &walk["standing"],
                &walk["function"]["status"],
                &walk["connection"]["status"],
                &walk["evidence"]["status"]
            ),
            (
                &json!("unchecked"),
                &json!("not-shown"),
                &json!("holds"),
                &json!("not-run")
            ),
            "{walk:#}"
        );
        let names = document["data"]["findings"]
            .as_array()
            .unwrap()
            .iter()
            .map(|finding| finding["name"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        assert_eq!(names.len(), 2, "{:#}", document["data"]);
        let reason = walk["reason"].as_str().unwrap();
        assert!(
            reason.contains("`outsideRomWalk` is not shown to be a function")
                && names.iter().all(|name| reason.contains(name.as_str()))
                && reason.contains("Argued obligations"),
            "{reason}"
        );
        assert_eq!(walk["function"]["findings"].as_array().unwrap().len(), 2);
        assert_eq!(document["summary"]["failed_arguments"], json!([]));
        assert_eq!(
            document["summary"]["invariant_runs"],
            json!({"run": 2, "cached": 0})
        );

        // The findings assumed: the walk is a function by that premise, which the item records.
        let path = dir.join("FLOW.toml");
        let manifest = fs::read_to_string(&path).unwrap();
        let spec = "syntax_module = \"INVARIANT-SYNTAX\"\n";
        assert!(manifest.contains(spec), "{manifest}");
        let assumed = format!(
            "{spec}assume_joined = [{}]\n",
            names
                .iter()
                .map(|name| format!("\"{name}\""))
                .collect::<Vec<_>>()
                .join(", ")
        );
        fs::write(&path, manifest.replacen(spec, &assumed, 1)).unwrap();
        let (premised, _) = coverage(&dir, &["--tier", "1"], Derived::default());
        let walk = &item(&premised, "requirements", READZ_REFUTED)["argument_check"];
        let standing = "checked-on-runs";
        assert_eq!(
            (&walk["standing"], &walk["function"]["status"]),
            (&json!(standing), &json!("assumed")),
            "{walk:#}"
        );
        assert!(
            walk["function"]["findings"]
                .as_array()
                .unwrap()
                .iter()
                .all(|finding| finding["assumed"] == true),
            "{walk:#}"
        );
        // The verdicts rendering, a coverage lock's text.
        let recorded = verdicts(&premised).unwrap();
        assert!(
            recorded.contains(&format!(
                "\"{READZ_REFUTED}\" = \"{standing}, assuming joined {}\"\n",
                names.join(", ")
            )),
            "{recorded}"
        );
        assert!(
            recorded.contains(&format!("\"{READZ_ROM_HELD}\" = \"checked-on-runs\"\n")),
            "{recorded}"
        );
    }

    /// The invariant-shapes fixture's invariants: two bound entries with a pairwise property, a
    /// nested collection, an enum in the guard, a set pattern, the existential dual, two of them
    /// combined by `andBool`, and the recursive walk.
    const MONOTONE: (&str, &str, &[&str]) = ("monotone", "monotone", &["memory"]);
    const OWNED_OUTSIDE: (&str, &str, &[&str]) =
        ("owned-outside", "ownedOutside", &["owners", "romEnd"]);
    const ROM_READ_ONLY: (&str, &str, &[&str]) =
        ("rom-read-only", "romReadOnly", &["perms", "romEnd"]);
    const ROOTS_OUTSIDE: (&str, &str, &[&str]) =
        ("roots-outside", "rootsOutside", &["roots", "romEnd"]);
    const SOME_ROM: (&str, &str, &[&str]) = ("some-rom", "someRom", &["rom", "romEnd"]);
    const MONOTONE_ROOTS: (&str, &str, &[&str]) = (
        "monotone-roots",
        "monotoneRoots",
        &["memory", "roots", "romEnd"],
    );
    const SHAPES_WALK: (&str, &str, &[&str]) = ("walk", "outsideRomWalk", &["memory", "romEnd"]);
    const TOUCH_ROM: &str = "rule:SHAPES.touchRom";

    /// The argued entries of the invariant-shapes fixture, `(family, item, invariant, the rules
    /// that can step where the item's rule matches)`: each shape on the rule its condition makes
    /// hold, the combination on the held requirements of two of them, and the walk on `readRom`.
    const SHAPE_ENTRIES: [(&str, &str, &str, [&str; 2]); 8] = [
        (
            "rules",
            "rule:SHAPES.cmpBad",
            MONOTONE.0,
            ["SHAPES.cmpBad", "SHAPES.cmpOk"],
        ),
        (
            "rules",
            TOUCH_ROM,
            OWNED_OUTSIDE.0,
            ["SHAPES.touchOk", "SHAPES.touchRom"],
        ),
        (
            "rules",
            "rule:SHAPES.storeRom",
            ROM_READ_ONLY.0,
            ["SHAPES.storeOk", "SHAPES.storeRom"],
        ),
        (
            "rules",
            "rule:SHAPES.dropRom",
            ROOTS_OUTSIDE.0,
            ["SHAPES.dropOk", "SHAPES.dropRom"],
        ),
        (
            "rules",
            "rule:SHAPES.unloaded",
            SOME_ROM.0,
            ["SHAPES.loaded", "SHAPES.unloaded"],
        ),
        (
            "requirements",
            "requirement:SHAPES.cmpBad:held",
            MONOTONE_ROOTS.0,
            ["SHAPES.cmpBad", "SHAPES.cmpOk"],
        ),
        (
            "requirements",
            "requirement:SHAPES.dropRom:held",
            MONOTONE_ROOTS.0,
            ["SHAPES.dropOk", "SHAPES.dropRom"],
        ),
        (
            "rules",
            "rule:SHAPES.readRom",
            SHAPES_WALK.0,
            ["SHAPES.readOk", "SHAPES.readRom"],
        ),
    ];

    /// A private copy of the invariant-shapes fixture for one test, its entries argued.
    fn shapes(test: &str) -> PathBuf {
        let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("kink-flow-coverage-argued-{}", std::process::id()))
            .join(test)
            .join("invariant-shapes");
        let _ = fs::remove_dir_all(&dir);
        copy_dir(&flow("invariant-shapes"), &dir);
        let entries = SHAPE_ENTRIES
            .iter()
            .map(|(_, item, invariant, _)| (*item, "the invariant excludes it", Some(*invariant)))
            .collect::<Vec<_>>();
        argue_on(
            &dir,
            &[
                MONOTONE,
                OWNED_OUTSIDE,
                ROM_READ_ONLY,
                ROOTS_OUTSIDE,
                SOME_ROM,
                MONOTONE_ROOTS,
                SHAPES_WALK,
            ],
            &entries,
        );
        dir
    }

    /// The line of `shapes.k` in `dir` that starts with `start` after its indentation.
    fn shapes_line(dir: &Path, start: &str) -> usize {
        let k = fs::read_to_string(dir.join("shapes.k")).unwrap();
        let lines = k
            .lines()
            .enumerate()
            .filter(|(_, line)| line.trim_start().starts_with(start))
            .map(|(at, _)| at + 1)
            .collect::<Vec<_>>();
        assert_eq!(lines.len(), 1, "{start}: {lines:?}");
        lines[0]
    }

    /// The violation form is shown to be a function with no premise in every shape the canonical
    /// form names: two bound entries with a pairwise property (`monotone`), a set pattern nested
    /// in a map's value (`ownedOutside`), a guard that reads a user-declared constructor sort
    /// through a function of its constructors (`romReadOnly`), a set pattern (`rootsOutside`),
    /// the existential dual, `true` where some binding is in the region and `false` otherwise
    /// (`someRom`), and two such functions combined by `andBool` (`monotoneRoots`, argued at two
    /// rules, each excluded by one of its conjuncts). Each argued item's function is `shown` with
    /// no finding, its connection holds by the simplification alone, in both profiles, and its
    /// evidence holds on the one program, which steps every rule its condition refutes, so it is
    /// `checked-on-runs`. The baseline's only findings are the two self-pairs of the recursive
    /// walk, whose right-hand side reads the binding it chose: `rule:readRom`, argued on it, is
    /// `unchecked` with its function `not-shown`, while its connection holds, its evidence is not
    /// read (`not-run`), and the command exits 3.
    #[test]
    #[ignore = "kink"]
    fn each_violation_shape_is_shown_to_be_a_function_with_no_premise() {
        let dir = shapes("function-shapes");
        let (document, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let shown = json!({"status": "shown", "findings": [], "reason": null});
        for (family, id, invariant, rules) in SHAPE_ENTRIES {
            let check = &item(&document, family, id)["argument_check"];
            assert_eq!(check["invariant"], invariant, "{id}: {check:#}");
            let connection = &check["connection"];
            assert_eq!(connection["status"], "holds", "{id}: {check:#}");
            assert!(
                connection["axioms"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|axiom| axiom["answer"] == "connected"),
                "{id}: {check:#}"
            );
            let evidence = &check["evidence"];
            if invariant == SHAPES_WALK.0 {
                assert_eq!(evidence, &json!({"status": "not-run"}), "{id}: {check:#}");
            } else {
                assert_eq!(
                    (
                        &evidence["status"],
                        &evidence["rules"],
                        &evidence["steps"],
                        &evidence["programs"]
                    ),
                    (&json!("holds"), &json!(rules), &json!(1), &json!(["safe"])),
                    "{id}: {check:#}"
                );
            }
            if invariant == SHAPES_WALK.0 {
                assert_eq!(
                    (&check["standing"], &check["function"]["status"]),
                    (&json!("unchecked"), &json!("not-shown")),
                    "{id}: {check:#}"
                );
                assert_eq!(
                    check["function"]["findings"].as_array().unwrap().len(),
                    2,
                    "{check:#}"
                );
                let reason = check["reason"].as_str().unwrap();
                assert!(
                    reason.contains("`outsideRomWalk` is not shown to be a function"),
                    "{reason}"
                );
            } else {
                assert_eq!(
                    (&check["standing"], &check["function"]),
                    (&json!("checked-on-runs"), &shown),
                    "{id}: {check:#}"
                );
                assert_eq!(check["reason"], Value::Null, "{id}: {check:#}");
            }
        }
        // The definition's only findings are the walk's two self-pairs.
        let mut names = document["data"]["findings"]
            .as_array()
            .unwrap()
            .iter()
            .map(|finding| finding["name"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        names.sort();
        let walk = [
            shapes_line(&dir, "rule outsideRomWalk((K:Int |-> _) M, E)"),
            shapes_line(&dir, "rule outsideRomWalk((_ |-> _) M, E)"),
        ]
        .map(|line| format!("shapes.k:{line}:3,shapes.k:{line}:3@root"));
        assert_eq!(names, walk, "{:#}", document["data"]);
        let summary = &document["summary"];
        assert_eq!(
            summary["argued_by_standing"],
            json!({"text": 0, "connected": 0, "checked_on_runs": 7, "proved": 0,
                   "unchecked": 1})
        );
        assert_eq!(summary["failed_arguments"], json!([]));
    }

    /// A set pattern nested in a map's value is matched by the backend's equation matching only
    /// against an inner set without a rest: against `SetItem(P) S`, its match is left to the
    /// collection solver, which solves a nested collection pair only where it may narrow a
    /// subject frame, and equation matching does not (k-rust-backend `matching/collections.rs`,
    /// `solve_term_pair_as_bound`). So where `touchRom` reads an owner's set with its rest, the
    /// `false` equation of `ownedOutside` does not apply at its left-hand side and the connection
    /// is undecided in both profiles, though the function is still `shown` and its evidence holds:
    /// an incompleteness of the simplification, not of the claim that the shape is a function.
    /// The fixture's `touch` rules read the set whole, where the connection holds.
    #[test]
    #[ignore = "kink"]
    fn a_nested_pattern_against_an_open_inner_collection_leaves_the_connection_undecided() {
        let dir = shapes("nested-open");
        let source = dir.join("shapes.k");
        let k = fs::read_to_string(&source).unwrap();
        let closed = "<owners> (O |-> SetItem(P)) _ </owners>";
        assert_eq!(k.matches(closed).count(), 2, "{k}");
        fs::write(
            &source,
            k.replace(closed, "<owners> (O |-> (SetItem(P) _:Set)) _ </owners>"),
        )
        .unwrap();
        let (document, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let check = &item(&document, "rules", TOUCH_ROM)["argument_check"];
        let reason = if cfg!(feature = "z3") {
            "the solver found a model of an approximate translation, which shows no state"
        } else {
            "no solver decides the simplified predicate"
        };
        assert_eq!(
            (
                &check["standing"],
                &check["function"],
                &check["connection"]["status"],
                &check["connection"]["reason"],
                &check["evidence"]["status"]
            ),
            (
                &json!("unchecked"),
                &json!({"status": "shown", "findings": [], "reason": null}),
                &json!("undecided"),
                &json!(reason),
                &json!("holds")
            ),
            "{check:#}"
        );
    }

    /// An invariant the front end cannot resolve refuses the command before any mutant runs, at
    /// stage `coverage`: a function the definition does not hold (`invariant-unresolved`, with
    /// the front end's message), a function whose result is not Bool (`invariant-not-bool`), and
    /// any invariant where the front end resolves none (`invariant-unsupported-front-end`).
    #[test]
    #[ignore = "kink"]
    fn an_invariant_the_front_end_cannot_resolve_is_refused() {
        let dir = invariant("resolution");
        let refusal = |front: FrontEnd<'_>| {
            let command = FlowCommand::parse(
                "coverage",
                CommandFiles::default(),
                &["--tier".into(), "1".into()],
            )
            .unwrap();
            let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
            let (document, status) = dispatch(manifest, command, front).unwrap();
            assert_eq!(status, EXIT_UNASKED, "{document:#}");
            let spec = &document["spec"];
            assert_eq!(spec["stage"], "coverage", "{spec:#}");
            (
                spec["reason"].as_str().unwrap().to_owned(),
                spec["detail"].as_str().unwrap().to_owned(),
            )
        };
        argue_on(
            &dir,
            &[
                ("nothing", "nothing", &["a"]),
                ("lost", "ordered", &["a", "c"]),
            ],
            &[
                (BUMP, "no state has a above b", Some("nothing")),
                (BUMP_HELD, "no state has a above b", Some("lost")),
            ],
        );
        let (reason, detail) = refusal(FrontEnd::default());
        assert_eq!(reason, "invariant-unresolved");
        assert!(
            detail
                .contains("`nothing`: the definition declares no symbol of the K label `nothing`")
                && detail.contains("`lost`: the configuration has no cell `c`"),
            "{detail}"
        );

        argue_on(
            &dir,
            &[("gap", "gap", &["a", "b"])],
            &[(BUMP_HELD, "no state has a above b", Some("gap"))],
        );
        let (reason, detail) = refusal(FrontEnd::default());
        assert_eq!(reason, "invariant-not-bool");
        assert!(detail.contains("`gap`: `gap` returns SortInt"), "{detail}");

        argue_on(
            &dir,
            &[ORDERED],
            &[(BUMP_HELD, "no state has a above b", Some(ORDERED.0))],
        );
        let (reason, detail) = refusal(FrontEnd {
            invariants: None,
            ..FrontEnd::default()
        });
        assert_eq!(reason, "invariant-unsupported-front-end");
        assert!(detail.contains("declares `ordered`"), "{detail}");
    }

    /// An invariant no entry names is refused (`invariant-unused`), and so is an entry that names
    /// one on an item it cannot argue (`argued-invariant-unsupported`): a function equation, a
    /// syntax production and a flip, each named with what it is, while an entry on a rewrite
    /// rule or on a requirement of one passes both, and its invariant is resolved next. Every
    /// refusal is at stage `coverage`.
    #[test]
    #[ignore = "kink"]
    fn invariants_unused_or_on_items_they_cannot_argue_are_refused() {
        let dir = guards("invariant-refusals");
        with_nop(&dir);
        let (baseline, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_YES, "{baseline:#}");
        let list = flips(&baseline, false);
        let refusal = |document: &Value| {
            let spec = &document["spec"];
            assert_eq!(
                (&spec["outcome"], &spec["stage"]),
                (&json!("refused"), &json!("coverage")),
                "{spec:#}"
            );
            (
                spec["reason"].as_str().unwrap().to_owned(),
                spec["detail"].as_str().unwrap().to_owned(),
            )
        };

        argue_on(
            &dir,
            &[NEVER_HALTED, ("spare", "spare", &["k"])],
            &[(
                WAKE,
                "the corpus never halts the machine",
                Some(NEVER_HALTED.0),
            )],
        );
        let (refused, status) = coverage(&dir, &["--tier", "1"], Derived::Flips(&list));
        assert_eq!(status, EXIT_UNASKED, "{refused:#}");
        let (reason, detail) = refusal(&refused);
        assert_eq!(reason, "invariant-unused");
        assert!(
            detail.contains("no [[coverage.argued]] entry names: `spare`"),
            "{detail}"
        );
        assert!(!detail.contains("never-halted"), "{detail}");

        let high_held = baseline["families"]["requirements"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|item| item["rule"] == "rule:GUARDS.high")
            .and_then(|item| item["id"].as_str())
            .unwrap_or_else(|| panic!("no requirement of high: {baseline:#}"))
            .to_owned();
        let on = Some(NEVER_HALTED.0);
        argue_on(
            &dir,
            &[NEVER_HALTED],
            &[
                (WAKE, "the corpus never halts the machine", on),
                (WAKE_HELD, "the corpus never halts the machine", on),
                ("rule:GUARDS.high", "no program stores high", on),
                (&high_held, "no program stores high", on),
                (
                    "syntax:nop",
                    "no program needs a step that does nothing",
                    on,
                ),
                (I, "only a halted machine reads the interrupt flag", on),
            ],
        );
        let (refused, status) = coverage(&dir, &["--tier", "1"], Derived::Flips(&list));
        assert_eq!(status, EXIT_UNASKED, "{refused:#}");
        let (reason, detail) = refusal(&refused);
        assert_eq!(reason, "argued-invariant-unsupported");
        assert!(
            detail.contains(&format!(
                "`rule:GUARDS.high` (equation); `{high_held}` (equation); `syntax:nop` (syntax); \
                 `{I}` (flip)"
            )),
            "{detail}"
        );
        assert!(!detail.contains(&format!("`{WAKE}`")), "{detail}");
        assert!(!detail.contains(&format!("`{WAKE_HELD}`")), "{detail}");

        argue_on(
            &dir,
            &[NEVER_HALTED],
            &[
                (WAKE, "the corpus never halts the machine", on),
                (WAKE_HELD, "the corpus never halts the machine", on),
            ],
        );
        // Every entry is on an item an invariant can argue: the invariant is resolved next,
        // and the guards fixture holds no `neverHalted`.
        let (unresolved, status) = coverage(&dir, &["--tier", "1"], Derived::Flips(&list));
        assert_eq!(status, EXIT_UNASKED, "{unresolved:#}");
        let (reason, detail) = refusal(&unresolved);
        assert_eq!(reason, "invariant-unresolved");
        assert!(
            detail.contains(
                "`never-halted`: the definition declares no symbol of the K label \
                             `neverHalted`"
            ),
            "{detail}"
        );
    }

    /// With every rule's unique-cause requirements, an invariant on a unique-cause requirement is
    /// refused, named as `mcdc`: its obligation is a pair of runs, not a valuation at one
    /// left-hand side. A table only that entry names is named in the same refusal as unused, so
    /// that removing the entry's `invariant` does not just produce the next refusal.
    #[test]
    #[ignore = "kink"]
    fn a_unique_cause_requirement_takes_no_invariant_and_one_refusal_names_the_unused_table() {
        let dir = guards("mcdc-invariant");
        let manifest = dir.join("FLOW.toml");
        let text = fs::read_to_string(&manifest).unwrap();
        fs::write(&manifest, format!("[coverage]\nmcdc = true\n\n{text}")).unwrap();
        let (baseline, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_YES, "{baseline:#}");
        let mcdc = baseline["families"]["requirements"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|item| item["level"] == "mcdc")
            .and_then(|item| item["id"].as_str())
            .unwrap_or_else(|| panic!("{:#}", baseline["families"]["requirements"]))
            .to_owned();
        argue_on(
            &dir,
            &[NEVER_HALTED, ("spare", "spare", &["k"])],
            &[
                (
                    WAKE,
                    "the corpus never halts the machine",
                    Some(NEVER_HALTED.0),
                ),
                (&mcdc, "no pair shows it", Some("spare")),
            ],
        );
        let (refused, status) = coverage(&dir, &["--tier", "1"], Derived::default());
        assert_eq!(status, EXIT_UNASKED, "{refused:#}");
        let spec = &refused["spec"];
        assert_eq!(spec["reason"], "argued-invariant-unsupported", "{spec:#}");
        let detail = spec["detail"].as_str().unwrap();
        assert!(detail.contains(&format!(": `{mcdc}` (mcdc); ")), "{detail}");
        assert!(
            detail.ends_with(
                "; then [[coverage.invariant]] declares an invariant no other [[coverage.argued]] \
                 entry names: `spare`; name it in the `invariant` of the entries whose argument \
                 rests on it, or remove the table"
            ),
            "{detail}"
        );
    }
}
