//! `kink-flow coverage`'s rule windows family at a depth above 1: the universe is the windows of
//! the may-follow graph of the authored rewrite rules, a window is covered where a comparable
//! program's run took it, the frontier (an open window whose shorter prefix is covered) has the
//! targets, each with the unified pattern of its last step, and the measure counts every window.
//! A record collected at depth `D` answers every depth up to `D`; a deeper command runs the
//! program again. A universe above `max_obligations` is refused before any program runs.
//!
//! The fixture is written here: every program ends by itself within a few steps, and the
//! manifest's `[budget] time_ms` is far above what such a run takes (R4-WALLCLOCK), so no result
//! depends on a clock.

use kink_flow::{
    cli::{EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, coverage},
    coverage::CoverageOptions,
    query::QueryOptions,
};
use serde_json::{Value, json};
use std::{fs, num::NonZeroU64, path::Path};

/// `start()` takes two rules, `a1` and `a2`, whose paths meet again at `join()` (a diamond, which
/// a state-set run merges); `c1()` is a chain of three rules; `lone()` has one rule. `seq` puts
/// the first instruction of a sequence in front.
const WIN_K: &str = r#"module WIN-SYNTAX
  syntax Instr ::= start() [symbol(start)] | left() [symbol(left)] | right() [symbol(right)]
                 | join() [symbol(join)] | c1() [symbol(c1)] | c2() [symbol(c2)]
                 | c3() [symbol(c3)] | lone() [symbol(lone)]
  syntax Pgm ::= Instr | Instr ";" Pgm [symbol(seq)]
endmodule

module WIN
  imports WIN-SYNTAX
  configuration <k> $PGM:Pgm </k>
  rule [seq]: <k> I:Instr ; P:Pgm => I ~> P ... </k>
  rule [a1]: <k> start() => left() ... </k>
  rule [a2]: <k> start() => right() ... </k>
  rule [l]: <k> left() => join() ... </k>
  rule [r]: <k> right() => join() ... </k>
  rule [j]: <k> join() => .K ... </k>
  rule [c1]: <k> c1() => c2() ... </k>
  rule [c2]: <k> c2() => c3() ... </k>
  rule [c3]: <k> c3() => .K ... </k>
  rule [lone]: <k> lone() => .K ... </k>
endmodule
"#;

fn scratch(name: &str) -> std::path::PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-rule-windows-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// A corpus of the fixture with `programs` (`(id, text)`) and the manifest's `coverage` section
/// text; its manifest's path.
fn corpus(name: &str, coverage: &str, programs: &[(&str, &str)]) -> std::path::PathBuf {
    let dir = scratch(name);
    fs::write(dir.join("win.k"), WIN_K).unwrap();
    // R4-WALLCLOCK: every run ends by itself within a few steps, far below this bound.
    let mut manifest = format!(
        "[spec]\nentry = \"win.k\"\nmain_module = \"WIN\"\nsyntax_module = \
         \"WIN-SYNTAX\"\n\n[budget]\ntime_ms = 600000\n\n{coverage}\n"
    );
    for (id, text) in programs {
        manifest.push_str(&format!(
            "\n[[program]]\nid = \"{id}\"\ntext = \"{text}\"\n"
        ));
    }
    let path = dir.join("FLOW.toml");
    fs::write(&path, manifest).unwrap();
    path
}

/// The derived coverage document of `manifest` under `options`, and its exit status.
fn run(manifest: &Path, options: &CoverageOptions) -> (Value, u8) {
    let (mut document, status) = coverage(manifest, options);
    kink_flow::coverage::derive(&mut document, &kink_flow::cli::KinkFlowSpelling);
    (document, status)
}

/// The derived coverage document of `manifest` at its own depth, which must succeed.
fn document(manifest: &Path) -> Value {
    let (document, status) = run(manifest, &CoverageOptions::default());
    assert_eq!(status, EXIT_YES, "{document:#}");
    document
}

/// The window of `rules` (labels without the module).
fn window_id(rules: &[&str]) -> String {
    format!(
        "window:{}",
        rules
            .iter()
            .map(|rule| format!("WIN.{rule}"))
            .collect::<Vec<_>>()
            .join(",")
    )
}

/// The rule windows item whose id is `id`.
fn window<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["families"]["rule_windows"]["items"]
        .as_array()
        .unwrap_or_else(|| panic!("no rule windows: {document:#}"))
        .iter()
        .find(|item| item["id"] == id)
        .unwrap_or_else(|| panic!("no window {id}: {document:#}"))
}

/// The targets of the rule windows family, by item id.
fn window_targets(document: &Value) -> Vec<&Value> {
    document["targets"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|target| target["family"] == "rule_windows")
        .collect()
}

mod kink_tier {
    use super::*;

    /// At depth 3, the diamond's two paths and the chain are covered window by window, the
    /// diamond's second path although a state-set run merges it into the first at `join()`.
    /// Every edge of the may-follow graph is in the universe, run or not: `j` may be followed by
    /// any rule, since its right-hand side leaves the rest of the computation, so `j` then `c1`
    /// is an open window whose prefix `j` fired, a frontier target whose pattern is the
    /// configuration `j` leaves that `c1` matches; a window starting with `seq`, which no program
    /// fired, is open and no target. The measure counts every window.
    #[test]
    #[ignore = "kink"]
    fn windows_are_covered_where_a_run_took_them_and_the_frontier_is_targeted() {
        let manifest = corpus(
            "diamond",
            "[coverage]\ndepth = 3\n",
            &[("diamond", "start()"), ("chain", "c1()")],
        );
        let document = document(&manifest);
        let family = &document["families"]["rule_windows"];
        assert_eq!(family["depth"], 3, "{family:#}");
        assert_eq!(family["outside_universe"], json!([]), "{family:#}");
        for (rules, program) in [
            (&["a1", "l"][..], "diamond"),
            (&["a2", "r"], "diamond"),
            (&["l", "j"], "diamond"),
            (&["r", "j"], "diamond"),
            (&["a1", "l", "j"], "diamond"),
            (&["a2", "r", "j"], "diamond"),
            (&["c1", "c2"], "chain"),
            (&["c2", "c3"], "chain"),
            (&["c1", "c2", "c3"], "chain"),
        ] {
            let item = window(&document, &window_id(rules));
            assert_eq!(item["status"], "covered", "{item:#}");
            assert_eq!(item["covered_by"], json!([program]), "{item:#}");
        }
        assert_eq!(family["covered"], 9, "{family:#}");
        let obligations = family["items"].as_array().unwrap().len();
        assert_eq!(family["obligations"], obligations);
        assert!(obligations > 9, "{family:#}");
        assert_eq!(family["measure"], json!(9.0 / obligations as f64));
        assert_eq!(
            family["counts"]["by_length"]["3"]["covered"], 3,
            "{family:#}"
        );
        // A step of `a1` is followed only by `l`: `left()` is matched by no other rule.
        let after_a1 = family["items"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|item| {
                item["length"] == 2 && item["id"].as_str().unwrap().starts_with("window:WIN.a1,")
            })
            .map(|item| item["id"].as_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(after_a1, [window_id(&["a1", "l"])], "{family:#}");

        let never = window(&document, &window_id(&["j", "c1"]));
        assert_eq!(never["status"], "open", "{never:#}");
        assert_eq!(never["frontier"], true);
        let seq = window(&document, &window_id(&["seq", "a1"]));
        assert_eq!(
            (&seq["status"], &seq["frontier"]),
            (&json!("open"), &json!(false))
        );
        let targets = window_targets(&document);
        let target = targets
            .iter()
            .find(|target| target["item"] == never["id"])
            .unwrap_or_else(|| panic!("no target for j, c1: {document:#}"));
        assert_eq!(target["programs"], json!(["diamond"]), "{target:#}");
        assert_eq!(target["fuzz"], Value::Null);
        let pattern = target["pattern"]
            .as_str()
            .unwrap_or_else(|| panic!("{target:#}"));
        assert!(pattern.contains("c1"), "{pattern}");
        assert!(
            targets.iter().all(|target| target["item"] != seq["id"]),
            "{document:#}"
        );
        // A longer frontier window names the programs that took its prefix.
        let longer = targets
            .iter()
            .find(|target| target["item"] == window_id(&["l", "j", "c1"]))
            .unwrap_or_else(|| panic!("no target for l, j, c1: {document:#}"));
        assert_eq!(longer["programs"], json!(["diamond"]), "{longer:#}");
        // Every target is on the frontier, and every frontier window has one.
        let frontier = family["items"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|item| item["frontier"] == true)
            .count();
        assert_eq!(targets.len(), frontier);
        assert_eq!(family["counts"]["frontier"], frontier);
        let per = &document["summary"]["per_family"]["rule_windows"];
        assert_eq!(
            per,
            &json!({"obligations": obligations, "covered": 9, "argued": 0,
                    "open": obligations - 9}),
        );

        // The pattern is a `PATTERNS.toml` pattern of the configurations the step of `j` leaves
        // that `c1` matches: a program that takes `j` then `c1` hits it.
        let dir = manifest.parent().unwrap();
        let mut flow = fs::read_to_string(&manifest).unwrap();
        flow.push_str("\n[[program]]\nid = \"both\"\ntext = \"start() ; c1()\"\n");
        fs::write(&manifest, flow).unwrap();
        let patterns = dir.join("PATTERNS.toml");
        fs::write(
            &patterns,
            format!(
                "[[pattern]]\nid = \"j-c1\"\npattern = {}\nprograms = [\"both\"]\n",
                serde_json::to_string(pattern).unwrap()
            ),
        )
        .unwrap();
        let (queried, _) = std::thread::Builder::new()
            .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
            .spawn({
                let (manifest, patterns) = (manifest.clone(), patterns.clone());
                move || kink_flow::cli::query(&manifest, &patterns, &QueryOptions::default())
            })
            .unwrap()
            .join()
            .unwrap();
        let row = queried["rows"]
            .as_array()
            .and_then(|rows| rows.iter().find(|row| row["program"] == "both"))
            .unwrap_or_else(|| panic!("{queried:#}"));
        assert_eq!(row["answer"], "hit", "{queried:#}");
        // And the program covers the window, which leaves the frontier.
        let document = super::document(&manifest);
        let item = window(&document, &window_id(&["j", "c1"]));
        assert_eq!(item["covered_by"], json!(["both"]), "{item:#}");
        assert!(
            window_targets(&document)
                .iter()
                .all(|target| target["item"] != item["id"]),
        );
    }

    /// At depth 1 the document has no rule windows, and its verdicts rendering no
    /// `[rule_windows]`: it is the document it was.
    #[test]
    #[ignore = "kink"]
    fn depth_one_has_no_rule_windows() {
        let manifest = corpus("depth-one", "", &[("diamond", "start()")]);
        let document = document(&manifest);
        assert_eq!(document["settings"]["depth"], 1);
        assert_eq!(document["families"]["rule_windows"], Value::Null);
        assert!(
            document["summary"]["per_family"]
                .get("rule_windows")
                .is_none(),
            "{document:#}"
        );
        let verdicts = kink_flow::verdicts::verdicts(&document).unwrap();
        assert!(!verdicts.contains("rule_windows"), "{verdicts}");
        let text = kink_flow::coverage::text(&document).unwrap();
        assert!(
            text.contains("rule_windows: computed above depth 1 only"),
            "{text}"
        );
    }

    /// A record collected at depth `D` answers every depth up to `D` and no deeper one: a command
    /// of a greater depth runs each program again and replaces its record.
    #[test]
    #[ignore = "kink"]
    fn a_record_answers_every_depth_up_to_its_own() {
        let manifest = corpus(
            "cache",
            "[coverage]\ndepth = 2\n",
            &[("diamond", "start()"), ("chain", "c1()")],
        );
        let at = |depth: Option<u64>| {
            let (document, status) = run(
                &manifest,
                &CoverageOptions {
                    depth: depth.and_then(NonZeroU64::new),
                    ..CoverageOptions::default()
                },
            );
            assert_eq!(status, EXIT_YES, "{document:#}");
            assert_eq!(
                document["result_cache"],
                json!({"enabled": true, "reason": null}),
                "{document:#}"
            );
            document
        };
        let computed = |document: &Value| document["summary"]["computed"].clone();
        let first = at(None);
        assert_eq!(computed(&first), 2);
        let deeper = at(Some(3));
        assert_eq!(computed(&deeper), 2, "{deeper:#}");
        assert_eq!(
            window(&deeper, &window_id(&["a2", "r", "j"]))["covered_by"],
            json!(["diamond"])
        );
        // The records now hold depth 3, which answers 2 and 1.
        let again = at(None);
        assert_eq!(computed(&again), 0, "{again:#}");
        assert_eq!(
            first["families"]["rule_windows"]["items"],
            again["families"]["rule_windows"]["items"]
        );
        let shallow = at(Some(1));
        assert_eq!(computed(&shallow), 0, "{shallow:#}");
        assert_eq!(shallow["families"]["rule_windows"], Value::Null);
        // A record of depth 3 is read for depth 3 too.
        assert_eq!(computed(&at(Some(3))), 0);
    }

    /// A universe above `[coverage] max_obligations` is refused before any program runs, with its
    /// counts by length; at the default bound the same depth runs.
    #[test]
    #[ignore = "kink"]
    fn a_universe_above_max_obligations_is_refused_with_its_counts() {
        let manifest = corpus(
            "bounded",
            "[coverage]\ndepth = 2\nmax_obligations = 5\n",
            &[("diamond", "start()")],
        );
        let (document, status) = run(&manifest, &CoverageOptions::default());
        assert_eq!(status, EXIT_UNASKED, "{document:#}");
        assert_eq!(document["spec"]["stage"], "coverage");
        assert_eq!(document["spec"]["reason"], "max-obligations");
        assert_eq!(document["programs"], json!([]));
        let detail = document["spec"]["detail"].as_str().unwrap();
        assert!(detail.contains("length 2: "), "{detail}");
        assert!(detail.contains("max_obligations = 5"), "{detail}");
        assert!(!manifest.parent().unwrap().join(".kink-flow").exists());
    }

    /// An argued window, and a window containing an argued open rule, argue every window that
    /// contains them: a path that takes the window takes the part.
    #[test]
    #[ignore = "kink"]
    fn a_window_containing_an_argued_part_is_argued_by_it() {
        let j_c1 = window_id(&["j", "c1"]);
        let manifest = corpus(
            "argued",
            &format!(
                "[coverage]\ndepth = 3\n\n[[coverage.argued]]\nitem = \"{j_c1}\"\nargument = \
                 \"no program ends a diamond before a chain\"\n\n[[coverage.argued]]\nitem = \
                 \"rule:WIN.lone\"\nargument = \"no program holds lone\"\n"
            ),
            &[("diamond", "start()"), ("chain", "c1()")],
        );
        let document = document(&manifest);
        let argued = window(&document, &j_c1);
        assert_eq!(argued["status"], "argued", "{argued:#}");
        let extension = window(&document, &window_id(&["j", "c1", "c2"]));
        assert_eq!(
            (&extension["status"], &extension["argued_by"]),
            (&json!("argued"), &json!(j_c1)),
            "{extension:#}"
        );
        let lone = window(&document, &window_id(&["j", "lone"]));
        assert_eq!(lone["argued_by"], "rule:WIN.lone", "{lone:#}");
        assert!(
            window_targets(&document)
                .iter()
                .all(|target| target["item"] != j_c1 && target["item"] != lone["id"]),
            "{document:#}"
        );
        let family = &document["families"]["rule_windows"];
        let argued_items = family["items"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|item| item["status"] == "argued")
            .count();
        assert_eq!(family["counts"]["argued"], argued_items, "{family:#}");
        assert_eq!(
            document["summary"]["per_family"]["rule_windows"]["argued"],
            argued_items
        );
        // The verdicts rendering lists them as argued, not open.
        let verdicts = kink_flow::verdicts::verdicts(&document).unwrap();
        let section = verdicts
            .split("[rule_windows]")
            .nth(1)
            .unwrap_or_else(|| panic!("{verdicts}"));
        let items = |key: &str| {
            let opening = format!("{key} = [");
            section
                .lines()
                .skip_while(|line| *line != opening)
                .skip(1)
                .take_while(|line| *line != "]")
                .collect::<Vec<_>>()
        };
        let quoted = format!("\"{j_c1}\"");
        assert!(
            items("argued").iter().any(|line| line.contains(&quoted)),
            "{verdicts}"
        );
        assert!(
            !items("open").iter().any(|line| line.contains(&quoted)),
            "{verdicts}"
        );
    }

    /// A window argued by a rule whose argument rests on an invariant has the rule's
    /// `argument_check`, unchecked, so the command has no answer (exit 3): here an invariant
    /// false of every state, whose connection holds, which shows nothing while the evidence is
    /// not run. An invariant named on a window itself is refused, the window named as
    /// `rule_windows`, before any invariant is resolved.
    #[test]
    #[ignore = "kink"]
    fn a_window_argued_by_a_rule_has_its_check_and_a_window_takes_no_invariant() {
        let j_c1 = window_id(&["j", "c1"]);
        let invariant =
            "[[coverage.invariant]]\nname = \"i\"\nfunction = \"f\"\ncells = [\"k\"]\n\n";
        let never = "[[coverage.invariant]]\nname = \"i\"\nfunction = \"never\"\ncells = \
                     [\"k\"]\n\n";
        let lone = "[[coverage.argued]]\nitem = \"rule:WIN.lone\"\nargument = \"no program \
                    holds lone\"\ninvariant = \"i\"\n";
        let manifest = corpus(
            "argued-invariant",
            &format!("[coverage]\ndepth = 3\n\n{never}{lone}"),
            &[("diamond", "start()"), ("chain", "c1()")],
        );
        // The fixture with a Bool function of the `<k>` cell false of every state.
        let source = manifest.with_file_name("win.k");
        let k = fs::read_to_string(&source).unwrap();
        let imports = "  imports WIN-SYNTAX\n";
        assert!(k.contains(imports), "{k}");
        fs::write(
            &source,
            k.replacen(
                imports,
                &format!(
                    "{imports}  imports BOOL\n  syntax Bool ::= never(K) [function, total, \
                     symbol(never)]\n  rule never(_) => false\n"
                ),
                1,
            ),
        )
        .unwrap();
        let (document, status) = run(&manifest, &CoverageOptions::default());
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let rule = document["families"]["rules"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|item| item["id"] == "rule:WIN.lone")
            .unwrap();
        assert_eq!(
            (
                &rule["argument_check"]["standing"],
                &rule["argument_check"]["connection"]["status"]
            ),
            (&json!("unchecked"), &json!("holds")),
            "{rule:#}"
        );
        let by = window(&document, &window_id(&["j", "lone"]));
        assert_eq!(
            (&by["argued_by"], &by["argument_check"]),
            (&json!("rule:WIN.lone"), &rule["argument_check"]),
            "{by:#}"
        );

        let manifest = corpus(
            "window-invariant",
            &format!(
                "[coverage]\ndepth = 3\n\n{invariant}[[coverage.argued]]\nitem = \"{j_c1}\"\n\
                 argument = \"no program ends a diamond before a chain\"\ninvariant = \"i\"\n"
            ),
            &[("diamond", "start()"), ("chain", "c1()")],
        );
        let (refused, status) = run(&manifest, &CoverageOptions::default());
        assert_eq!(status, EXIT_UNASKED, "{refused:#}");
        assert_eq!(refused["spec"]["reason"], "argued-invariant-unsupported");
        let detail = refused["spec"]["detail"].as_str().unwrap();
        assert!(
            detail.contains(&format!("`{j_c1}` (rule_windows)")),
            "{detail}"
        );
    }

    /// The rule windows read the scope every family shares: with `c2` marked a claim helper, no
    /// window has it, though the chain's program takes `c1` then `c2`, and its rules item is
    /// `claim-helper`, no obligation, with the program that fired it.
    #[test]
    #[ignore = "kink"]
    fn a_claim_helper_is_no_node_of_the_may_follow_graph() {
        let manifest = corpus(
            "claim-helper",
            "[coverage]\ndepth = 2",
            &[("chain", "c1()")],
        );
        let unmarked = document(&manifest);
        assert_eq!(
            window(&unmarked, &window_id(&["c1", "c2"]))["status"],
            "covered"
        );
        let marked = kink_flow::FlowManifest::read(&manifest)
            .unwrap()
            .with_claim_helpers([("WIN".to_owned(), "c2".to_owned())]);
        let (mut document, ok) =
            kink_flow::coverage::coverage(&marked, &CoverageOptions::default());
        kink_flow::coverage::derive(&mut document, &kink_flow::cli::KinkFlowSpelling);
        assert!(ok, "{document:#}");
        let windows = document["families"]["rule_windows"]["items"]
            .as_array()
            .unwrap();
        assert!(!windows.is_empty(), "{document:#}");
        assert!(
            windows.iter().all(|window| !window["id"]
                .as_str()
                .unwrap()
                .split([':', ','])
                .any(|rule| rule == "WIN.c2")),
            "{document:#}"
        );
        let helper = document["families"]["rules"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|item| item["id"] == "rule:WIN.c2")
            .unwrap_or_else(|| panic!("{document:#}"));
        assert_eq!(
            (
                &helper["status"],
                &helper["obligation"],
                &helper["fired_by"]
            ),
            (&json!("claim-helper"), &json!(false), &json!(["chain"])),
            "{helper:#}"
        );
    }
}
