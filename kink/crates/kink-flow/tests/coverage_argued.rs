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
        assert_eq!(after["version"], 17);
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
        assert!(recorded.contains("\nversion = 21\n"), "{recorded}");
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
    /// ROM region below `romEnd`, as a walk over the map's bindings and as a fold over its keys.
    const ORDERED: (&str, &str, &[&str]) = ("ordered", "ordered", &["a", "b"]);
    const OUTSIDE_ROM: (&str, &str, &[&str]) = ("outside-rom", "outsideRom", &["memory", "romEnd"]);
    const OUTSIDE_ROM_KEYS: (&str, &str, &[&str]) =
        ("outside-rom-keys", "outsideRomKeys", &["memory", "romEnd"]);
    const BUMP: &str = "rule:INVARIANT.bump";
    const BUMP_HELD: &str = "requirement:INVARIANT.bump:held";
    const READZ_REFUTED: &str = "requirement:INVARIANT.readz:refuted";
    const READZ_ROM_HELD: &str = "requirement:INVARIANT.readzRom:held";

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

    /// The same order with its cells swapped, `b <=Int a`, the walk under another function, and a
    /// claim false of every state.
    const REVERSED: (&str, &str, &[&str]) = ("reversed", "ordered", &["b", "a"]);
    const OUTSIDE_ROM_TOO: (&str, &str, &[&str]) =
        ("outside-rom-too", "outsideRomToo", &["memory", "romEnd"]);
    const NEVER: (&str, &str, &[&str]) = ("never", "never", &["a"]);

    /// The cause of a connection the portable profile leaves to a solver it does not have.
    #[cfg(not(feature = "z3"))]
    const NO_SOLVER: &str = "no solver decides the simplified predicate";

    /// An argued item's invariant is checked by its connection, through kink-flow's K front end
    /// (the function by its K label, the cells by their K names, `settings.invariants[].identity`):
    /// - `readzRom`'s `inRom(E, A)` under the walk over `memory`'s bindings: the walk unfolds at
    ///   the binding the rule matches and the simplification alone refutes the question, so the
    ///   connection holds in both profiles. The corpus only idles, so no run steps a rule that can
    ///   step where `readzRom` matches, and the walk holds at the initial state and the end: the
    ///   evidence is vacuous, and the item is `connected`;
    /// - the walk as a fold over `keys_list(memory)` does not unfold there, so `readz`'s refuted
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
        assert_eq!(document["version"], 18);
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
    /// - `read(8)` steps `readz` at a memory with no ROM address, so the walk holds at every state
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

        // A program that stores a ROM address before a read breaks the walk there.
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

        // The same items argued on their text alone: only the requirement's standing moves.
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
            (&json!(false), &json!([]), &json!([])),
            "{state:#}"
        );
        assert_eq!(
            state["argument_changes"],
            json!([{"obligation": BUMP_HELD, "recorded": standing, "now": "text"}])
        );
        assert_eq!(
            stale_lines(&stale),
            [format!(
                "{path}: arguments: {BUMP_HELD}: {standing} -> text"
            )]
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
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
