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
        assert_eq!(after["version"], 15);
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
            json!({"item": WAKE, "argument": argued[0].1})
        );
        // The text names each argued item with its argument.
        let text = text(&after).unwrap();
        assert!(
            text.contains(&format!(
                "argued:\n  {WAKE}: the corpus never halts the machine\n"
            )),
            "{text}"
        );
        assert!(
            text.contains(&format!(
                "  {I}: only a halted machine reads the interrupt flag\n"
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
        assert!(recorded.contains("\nversion = 20\n"), "{recorded}");
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

    /// The invariant the guards fixture's arguments name: no program halts the machine, a
    /// function of the `<k>` cell.
    const NEVER_HALTED: (&str, &str, &[&str]) = ("never-halted", "neverHalted", &["k"]);

    /// Every argued item says what its argument rests on (`argument_check`): its text alone where
    /// its entry names no invariant (`text`), else the invariant, whose checks this build does not
    /// run (`unchecked`, the connection and the evidence `not-run`), so the command has no answer
    /// (exit 3). The settings list the
    /// invariants, the summary counts the argued items by standing and lists no failed argument,
    /// the text states each standing, and the coverage lock gives each argued item's standing
    /// under `[arguments]`: a standing that moves makes `--locked` stale, naming the item, while
    /// the header and the obligations are unchanged.
    #[test]
    #[ignore = "kink"]
    fn each_argued_item_states_its_standing_and_the_lock_records_it() {
        let dir = guards("standing");
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
        argue_on(
            &dir,
            &[NEVER_HALTED],
            &[
                (WAKE, "the corpus never halts the machine", None),
                (WAKE_HELD, "no state is halted", Some(NEVER_HALTED.0)),
            ],
        );
        let (document, status) = run(false);
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        assert_eq!(
            item(&document, "rules", WAKE)["argument_check"],
            json!({"standing": "text"})
        );
        assert_eq!(
            item(&document, "requirements", WAKE_HELD)["argument_check"],
            json!({
                "invariant": "never-halted",
                "standing": "unchecked",
                "connection": {"status": "not-run"},
                "evidence": {"status": "not-run"},
                "proof": null,
            })
        );
        assert_eq!(
            document["settings"]["invariants"],
            json!([{"name": "never-halted", "function": "neverHalted", "cells": ["k"],
                    "identity": null}])
        );
        assert_eq!(
            document["settings"]["argued"][1],
            json!({"item": WAKE_HELD, "argument": "no state is halted",
                   "invariant": "never-halted"})
        );
        let summary = &document["summary"];
        assert_eq!(
            summary["argued_by_standing"],
            json!({"text": 1, "connected": 0, "checked_on_runs": 0, "proved": 0, "unchecked": 1})
        );
        assert_eq!(summary["argued"], 2, "{summary:#}");
        assert_eq!(summary["failed_arguments"], json!([]));
        let text = text(&document).unwrap();
        assert!(
            text.contains(&format!(
                "argued:\n  {WAKE} [text]: the corpus never halts the machine\n"
            )),
            "{text}"
        );
        assert!(
            text.contains(&format!(
                "  {WAKE_HELD} [unchecked, invariant never-halted]: no state is halted\n"
            )),
            "{text}"
        );
        let recorded = fs::read_to_string(&lock).unwrap();
        assert!(
            recorded.contains(&format!(
                "\n[arguments]\n\"{WAKE}\" = \"text\"\n\"{WAKE_HELD}\" = \"unchecked\"\n\n[flips]\nrun = true\n"
            )),
            "{recorded}"
        );
        assert_eq!(recorded, verdicts(&document).unwrap());

        // The same items argued on their text alone: only the requirement's standing moves.
        argue(
            &dir,
            &[
                (WAKE, "the corpus never halts the machine"),
                (WAKE_HELD, "no state is halted"),
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
            json!([{"obligation": WAKE_HELD, "recorded": "unchecked", "now": "text"}])
        );
        assert_eq!(
            stale_lines(&stale),
            [format!("{path}: arguments: {WAKE_HELD}: unchecked -> text")]
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
        assert_eq!(
            stale["summary"]["argued_by_standing"]["text"], 2,
            "{:#}",
            stale["summary"]
        );
    }

    /// An invariant no entry names is refused (`invariant-unused`), and so is an entry that names
    /// one on an item it cannot argue (`argued-invariant-unsupported`): a function equation, a
    /// syntax production and a flip, each named with what it is, while an entry on a rewrite
    /// rule or on a requirement of one is accepted. Both refusals are at stage `coverage`.
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
        let (accepted, status) = coverage(&dir, &["--tier", "1"], Derived::Flips(&list));
        assert_eq!(status, EXIT_UNANSWERED, "{accepted:#}");
        assert_eq!(
            accepted["summary"]["argued_by_standing"]["unchecked"], 2,
            "{:#}",
            accepted["summary"]
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
