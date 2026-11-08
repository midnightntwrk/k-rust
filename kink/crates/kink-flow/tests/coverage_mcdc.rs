//! Unique-cause MC/DC (`[coverage] mcdc`): a selected rule's condition gains one requirement per
//! authored atom, covered by two recorded valuation combinations that differ only in that atom
//! and whose guard outcomes differ; open with the valuation that would make such a pair, or
//! undecided where a record left a combination out; arguable where the operands' coupling makes
//! the pair impossible; and absent, with the document as it was, when nothing is selected. The
//! mcdc fixture's `both` (A andThenBool B) is entered with both operands true and both false,
//! `either` (A orElseBool B) with each operand alone true and both false, and `big`
//! (X >Int 0 andThenBool X >Int 10) with X 20, 5 and -1.

mod flow_support;

use flow_support::{copy_dir, flow};
use kink_flow::{
    CommandFiles, FlowCommand, FlowManifest, FrontEnd, KinkFlowSpelling, ManifestFile,
    cli::{EXIT_UNASKED, EXIT_YES, dispatch},
    coverage::{derive, text},
    manifest::Mcdc,
    verdicts::verdicts,
};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};

/// A private copy of the mcdc fixture for one test, its manifest with `section` before it.
fn fixture(test: &str, section: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-coverage-mcdc-{}", std::process::id()))
        .join(test)
        .join("mcdc");
    let _ = fs::remove_dir_all(&dir);
    copy_dir(&flow("mcdc"), &dir);
    let path = dir.join("FLOW.toml");
    let text = fs::read_to_string(&path).unwrap();
    fs::write(&path, format!("{section}\n{text}")).unwrap();
    dir
}

/// Add a program `id` whose text is `text` to the fixture at `dir`.
fn with_program(dir: &Path, id: &str, text: &str) {
    let path = dir.join("FLOW.toml");
    let mut manifest = fs::read_to_string(&path).unwrap();
    manifest.push_str(&format!(
        "\n[[program]]\nid = \"{id}\"\ntext = \"{text}\"\n"
    ));
    fs::write(&path, manifest).unwrap();
}

/// `coverage --tier 1` on `dir`, derived as the command derives it.
fn coverage(dir: &Path) -> (Value, u8) {
    let options = ["--tier".to_owned(), "1".to_owned()];
    let command = FlowCommand::parse("coverage", CommandFiles::default(), &options).unwrap();
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    dispatch(manifest, command, FrontEnd::default()).expect("the command's thread does not panic")
}

/// The requirements item whose id is `id`.
fn item<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["families"]["requirements"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|item| item["id"] == id)
        .unwrap_or_else(|| panic!("no requirement {id}: {document:#}"))
}

/// The unique-cause requirements of `document`, by id.
fn mcdc_ids(document: &Value) -> Vec<&str> {
    document["families"]["requirements"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|item| item["level"] == "mcdc")
        .map(|item| item["id"].as_str().unwrap())
        .collect()
}

/// The target of `id`.
fn target<'d>(document: &'d Value, id: &str) -> Option<&'d Value> {
    document["targets"]
        .as_array()
        .unwrap()
        .iter()
        .find(|target| target["item"] == id)
}

/// The rule item labelled `MCDC.<label>`.
fn rule_mut<'d>(document: &'d mut Value, label: &str) -> &'d mut Value {
    document["families"]["rules"]["items"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|item| item["label"] == format!("MCDC.{label}"))
        .unwrap_or_else(|| panic!("no rule {label}"))
}

const BOTH_A: &str = "requirement:MCDC.both:A:Bool:mcdc";
const BOTH_B: &str = "requirement:MCDC.both:B:Bool:mcdc";
const EITHER_A: &str = "requirement:MCDC.either:A:Bool:mcdc";
const EITHER_B: &str = "requirement:MCDC.either:B:Bool:mcdc";
const BIG_LOW: &str = "requirement:MCDC.big:X:Int >Int 0:mcdc";
const BIG_HIGH: &str = "requirement:MCDC.big:X:Int >Int 10:mcdc";

fn decode(text: &str) -> Result<ManifestFile, String> {
    let manifest = format!("[spec]\nentry = \"x.k\"\nmain_module = \"X\"\n{text}");
    ManifestFile::decode(&manifest, Path::new(".")).map_err(|e| e.to_string())
}

/// `[coverage] mcdc` is a list of rule names, `true` for every rule, or `false` for none; a
/// name is nonempty and named once.
#[test]
fn mcdc_decodes_names_or_every_rule() {
    let mcdc = |text: &str| decode(text).map(|file| file.coverage.mcdc);
    assert_eq!(mcdc(""), Ok(Mcdc::Rules(Vec::new())));
    assert_eq!(mcdc("[coverage]\nmcdc = true\n"), Ok(Mcdc::All));
    assert_eq!(
        mcdc("[coverage]\nmcdc = false\n"),
        Ok(Mcdc::Rules(Vec::new()))
    );
    assert_eq!(
        mcdc("[coverage]\nmcdc = [\"a\", \"b\"]\n"),
        Ok(Mcdc::Rules(vec!["a".to_owned(), "b".to_owned()]))
    );
    assert!(Mcdc::All.selects("anything") && !Mcdc::default().selects("a"));
    for (text, error) in [
        (
            "[coverage]\nmcdc = \"a\"\n",
            "coverage.mcdc: expected an array of rule names, or true for every rule",
        ),
        (
            "[coverage]\nmcdc = [\"a\", \"a\"]\n",
            "coverage.mcdc: names `a` twice",
        ),
        (
            "[coverage]\nmcdc = [\"\"]\n",
            "coverage.mcdc: entry 0 is not a nonempty string: name a rule",
        ),
    ] {
        assert_eq!(mcdc(text).unwrap_err(), error, "{text}");
    }
}

mod kink_tier {
    use super::*;

    /// An operand with a unique-cause pair among the recorded combinations is covered by the
    /// programs of the pair, which the item shows; `either`'s operands each have one. `both`'s
    /// A has none while the corpus has only (A, B) = (true, true) and (false, false), although
    /// A is reached false: those differ in B too. A program with A false and B true covers it.
    #[test]
    #[ignore = "kink"]
    fn an_operand_is_covered_by_a_unique_cause_pair() {
        let dir = fixture("covered", "[coverage]\nmcdc = true\n");
        let (before, status) = coverage(&dir);
        assert_eq!(status, EXIT_YES, "{before:#}");
        assert_eq!(before["settings"]["mcdc"], true);
        assert_eq!(
            mcdc_ids(&before),
            [BOTH_A, BOTH_B, EITHER_A, EITHER_B, BIG_LOW, BIG_HIGH]
        );
        let either_a = item(&before, EITHER_A);
        assert_eq!(either_a["status"], "covered", "{either_a:#}");
        assert_eq!(
            either_a["covered_by"],
            json!(["two", "one"]),
            "{either_a:#}"
        );
        assert_eq!(
            either_a["pair"],
            json!([
                {"valuation": [{"node": "0.0", "text": "A:Bool", "truth": "true"},
                               {"node": "0.1", "text": "B:Bool", "truth": "false"}],
                 "outcome": "held", "programs": ["two"]},
                {"valuation": [{"node": "0.0", "text": "A:Bool", "truth": "false"},
                               {"node": "0.1", "text": "B:Bool", "truth": "false"}],
                 "outcome": "refuted-false", "programs": ["one"]},
            ]),
            "{either_a:#}"
        );
        assert_eq!(
            item(&before, EITHER_B)["covered_by"],
            json!(["three", "one"])
        );
        assert_eq!(item(&before, BIG_HIGH)["status"], "covered");
        // `both`'s A is reached false (the outcome class is covered) but has no pair.
        assert_eq!(
            item(&before, "requirement:MCDC.both:A:Bool:false")["status"],
            "covered"
        );
        assert_eq!(item(&before, BOTH_A)["status"], "open");
        let level = &before["families"]["requirements"]["mcdc"];
        assert_eq!(
            level["rules"],
            json!(["rule:MCDC.both", "rule:MCDC.either", "rule:MCDC.big"])
        );
        assert_eq!(level["obligations"], 6);
        assert_eq!(level["covered"], 3);

        with_program(&dir, "four", "both(false, true)");
        let (after, status) = coverage(&dir);
        assert_eq!(status, EXIT_YES, "{after:#}");
        let both_a = item(&after, BOTH_A);
        assert_eq!(both_a["status"], "covered", "{both_a:#}");
        assert_eq!(both_a["covered_by"], json!(["one", "four"]), "{both_a:#}");
        assert!(target(&after, BOTH_A).is_none());
        assert_eq!(item(&after, BOTH_B)["status"], "open");
        assert_eq!(after["families"]["requirements"]["mcdc"]["covered"], 4);
    }

    /// An operand no recorded pair covers is open, and its target names the valuation that
    /// would make a pair with a recorded combination: the operand's truth negated, where the
    /// condition then takes the other outcome; a combination whose flip leaves the outcome as it
    /// is makes no pair and is not named. The verdicts rendering lists it open.
    #[test]
    #[ignore = "kink"]
    fn an_operand_missing_its_pair_is_open_with_the_valuation_needed() {
        let dir = fixture("open", "[coverage]\nmcdc = [\"MCDC.both\"]\n");
        let (document, status) = coverage(&dir);
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(mcdc_ids(&document), [BOTH_A, BOTH_B]);
        let both_a = item(&document, BOTH_A);
        assert_eq!(both_a["status"], "open", "{both_a:#}");
        assert_eq!(both_a["covered"], false);
        assert_eq!(both_a["pair"], Value::Null);
        assert_eq!(
            both_a["needed"],
            json!([{
                "valuation": [{"node": "0.0", "text": "A:Bool", "truth": "false"},
                              {"node": "0.1", "text": "B:Bool", "truth": "true"}],
                "outcome": "refuted",
                "against": {
                    "valuation": [{"node": "0.0", "text": "A:Bool", "truth": "true"},
                                  {"node": "0.1", "text": "B:Bool", "truth": "true"}],
                    "outcome": "held", "programs": ["one"]},
            }]),
            "{both_a:#}"
        );
        let open = target(&document, BOTH_A).unwrap();
        assert_eq!(
            open["text"],
            "a case that enters MCDC.both with A:Bool false and B:Bool true, where its \
             condition is false: against one's A:Bool true and B:Bool true, where it holds, \
             A:Bool alone decides it"
        );
        assert_eq!(open["programs"], json!(["one", "two"]));
        assert!(
            target(&document, BOTH_B).unwrap()["text"]
                .as_str()
                .unwrap()
                .contains("with A:Bool true and B:Bool false, where its condition is false"),
            "{document:#}"
        );
        // Only the selected rule keeps its combinations.
        assert!(rule_mut(&mut document.clone(), "both")["guard"]["combinations"].is_object());
        assert!(
            rule_mut(&mut document.clone(), "either")["guard"]
                .get("combinations")
                .is_none()
        );
        let rendering = verdicts(&document).unwrap();
        assert!(
            rendering.contains("\nmcdc = [\"MCDC.both\"]\n"),
            "{rendering}"
        );
        assert!(
            rendering.contains(BOTH_A) && rendering.contains(BOTH_B),
            "{rendering}"
        );
        assert!(!rendering.contains("undecided"), "{rendering}");
        assert!(
            text(&document)
                .unwrap()
                .contains("unique-cause: 0 of 2 covered, 0 undecided"),
            "{}",
            text(&document).unwrap()
        );
    }

    /// Where a program's record of the condition left a combination out, an operand without a
    /// pair is undecided: the pair may be among the combinations left out. It is not covered and
    /// not open, keeps its target, which says why, and the verdicts rendering lists it apart.
    #[test]
    #[ignore = "kink"]
    fn a_truncated_record_makes_an_uncovered_operand_undecided() {
        let dir = fixture("truncated", "[coverage]\nmcdc = [\"MCDC.both\"]\n");
        let (mut document, status) = coverage(&dir);
        assert_eq!(status, EXIT_YES, "{document:#}");
        // A record keeps the least combinations up to its limit; one whose run made more says so.
        // The fixture's runs make a few, so the record of one is marked as one that did.
        rule_mut(&mut document, "both")["guard"]["combinations"]["truncated_by"] = json!(["one"]);
        derive(&mut document, &KinkFlowSpelling);
        for id in [BOTH_A, BOTH_B] {
            let requirement = item(&document, id);
            assert_eq!(requirement["status"], "undecided", "{requirement:#}");
            assert_eq!(requirement["covered"], false);
            assert_eq!(requirement["truncated_by"], json!(["one"]));
            let target = target(&document, id).unwrap();
            assert!(
                target["text"].as_str().unwrap().ends_with(
                    "; undecided: the record of one keeps only part of its combinations of this \
                     condition, so such a pair may be among those left out"
                ),
                "{target:#}"
            );
        }
        let family = &document["families"]["requirements"];
        assert_eq!(family["counts"]["undecided"], 2, "{family:#}");
        assert_eq!(
            family["counts"]["open"].as_u64().unwrap() + 2 + family["covered"].as_u64().unwrap(),
            family["obligations"].as_u64().unwrap()
        );
        let rendering = verdicts(&document).unwrap();
        assert!(
            rendering.contains(&format!("undecided = [\"{BOTH_A}\", \"{BOTH_B}\"]")),
            "{rendering}"
        );
        let open = rendering
            .lines()
            .skip_while(|line| *line != "[requirements]")
            .nth(1)
            .unwrap();
        assert!(!open.contains("mcdc"), "{rendering}");
    }

    /// `X >Int 10` implies `X >Int 0`, so no two valuations differ in `X >Int 0` alone while the
    /// condition changes: its target names the impossible valuation, and the author argues it.
    /// The argued obligation stays counted, is not open and has no target.
    #[test]
    #[ignore = "kink"]
    fn a_coupled_operand_is_argued() {
        let dir = fixture("argued", "[coverage]\nmcdc = [\"MCDC.big\"]\n");
        let (before, status) = coverage(&dir);
        assert_eq!(status, EXIT_YES, "{before:#}");
        assert_eq!(item(&before, BIG_LOW)["status"], "open");
        assert!(
            target(&before, BIG_LOW).unwrap()["text"]
                .as_str()
                .unwrap()
                .contains(
                    "with X:Int >Int 0 false and X:Int >Int 10 true, where its condition is false",
                ),
            "{before:#}"
        );
        let path = dir.join("FLOW.toml");
        let manifest = fs::read_to_string(&path).unwrap();
        fs::write(
            &path,
            manifest.replacen(
                "[coverage]\nmcdc = [\"MCDC.big\"]\n",
                &format!(
                    "[coverage]\nmcdc = [\"MCDC.big\"]\n\n[[coverage.argued]]\nitem = \
                     \"{BIG_LOW}\"\nargument = \"X > 10 implies X > 0, so X > 0 never decides the \
                     condition alone\"\n"
                ),
                1,
            ),
        )
        .unwrap();
        let (after, status) = coverage(&dir);
        assert_eq!(status, EXIT_YES, "{after:#}");
        let argued = item(&after, BIG_LOW);
        assert_eq!(argued["status"], "argued", "{argued:#}");
        assert_eq!(argued["unargued_status"], "open");
        assert!(target(&after, BIG_LOW).is_none());
        let family = &after["families"]["requirements"];
        assert_eq!(
            family["obligations"],
            before["families"]["requirements"]["obligations"]
        );
        assert_eq!(family["argued"], 1);
        assert!(
            verdicts(&after)
                .unwrap()
                .contains(&format!("argued = [\"{BIG_LOW}\"]")),
            "{}",
            verdicts(&after).unwrap()
        );
    }

    /// Without a selection the document is what it was: no guard keeps its combinations, the
    /// requirements family has no unique-cause item, no `mcdc` and no `undecided` count; with
    /// one, the outcome-class requirements and the rules' items are the same, so the level only
    /// adds. A name that selects no rule is refused before anything is reported.
    #[test]
    #[ignore = "kink"]
    fn without_a_selection_the_document_is_unchanged() {
        let off_dir = fixture("off", "");
        let (off, status) = coverage(&off_dir);
        assert_eq!(status, EXIT_YES, "{off:#}");
        assert_eq!(off["settings"]["mcdc"], json!([]));
        let family = &off["families"]["requirements"];
        assert!(family.get("mcdc").is_none(), "{family:#}");
        assert!(family["counts"].get("undecided").is_none(), "{family:#}");
        assert!(mcdc_ids(&off).is_empty());
        for rule in off["families"]["rules"]["items"].as_array().unwrap() {
            assert!(rule["guard"].get("combinations").is_none(), "{rule:#}");
        }

        let on_dir = fixture("on", "[coverage]\nmcdc = true\n");
        let (mut on, status) = coverage(&on_dir);
        assert_eq!(status, EXIT_YES, "{on:#}");
        let outcome_classes = |document: &Value| {
            document["families"]["requirements"]["items"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|item| item["level"] != "mcdc")
                .cloned()
                .collect::<Vec<_>>()
        };
        assert_eq!(outcome_classes(&on), outcome_classes(&off));
        for rule in on["families"]["rules"]["items"].as_array_mut().unwrap() {
            if let Some(guard) = rule.get_mut("guard").and_then(Value::as_object_mut) {
                guard.remove("combinations");
            }
        }
        assert_eq!(on["families"]["rules"], off["families"]["rules"]);

        let stale_dir = fixture(
            "stale",
            "[coverage]\nmcdc = [\"MCDC.both\", \"MCDC.next\"]\n",
        );
        let (stale, status) = coverage(&stale_dir);
        assert_eq!(status, EXIT_UNASKED, "{stale:#}");
        assert_eq!(stale["spec"]["reason"], "mcdc-stale");
        assert!(
            stale["spec"]["detail"]
                .as_str()
                .unwrap()
                .contains("`MCDC.next`"),
            "{stale:#}"
        );
    }
}
