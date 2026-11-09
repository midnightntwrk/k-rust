//! `kink-flow coverage`'s syntax paths family at a depth above 1: the universe is the paths of
//! the grammar graph of the syntax family's productions, a path is reached where a fired step of
//! a comparable program touched it (it starts at a position the step inspected, built or took as
//! an operand and descends through the touched term), the frontier (an open path whose shorter
//! prefix is reached) has the targets, and the measure counts every path. A collection breaks a
//! path; depth 1 has no family; a universe above `max_obligations` is refused before any program
//! runs; an argued production or prefix argues the paths it starts; a claim helper's step
//! reaches none.
//!
//! The fixture is written here: every program ends by itself within a few steps, and the
//! manifest's `[budget] time_ms` is far above what such a run takes (R4-WALLCLOCK), so no result
//! depends on a clock.

use kink_flow::{
    cli::{EXIT_UNASKED, EXIT_YES, coverage},
    coverage::CoverageOptions,
};
use serde_json::{Value, json};
use std::{fs, path::Path};

/// `exec` runs an operation, `mov` keeps its second register and drops its first, `neg` keeps
/// its register, `wrap` its operation; `run` puts its operation in a builtin list, which `batch`
/// takes apart, so the operation sits below a collection.
const PATH_K: &str = r#"module PATH-SYNTAX
  imports LIST
  syntax Reg ::= a() [symbol(a)] | b() [symbol(b)]
  syntax Op ::= mov(Reg, Reg) [symbol(mov)] | neg(Reg) [symbol(neg)] | wrap(Op) [symbol(wrap)]
  syntax Instr ::= exec(Op) [symbol(exec)] | run(Op) [symbol(run)] | batch(List) [symbol(batch)]
endmodule

module PATH
  imports PATH-SYNTAX
  configuration <k> $PGM:Instr </k>
  rule [exec]: <k> exec(O) => O ... </k>
  rule [mov]: <k> mov(_R1:Reg, R2:Reg) => R2 ... </k>
  rule [neg]: <k> neg(R) => R ... </k>
  rule [wrap]: <k> wrap(O) => O ... </k>
  rule [ra]: <k> a() => .K ... </k>
  rule [rb]: <k> b() => .K ... </k>
  rule [run]: <k> run(O) => batch(ListItem(O)) ... </k>
  rule [batch]: <k> batch(ListItem(O) L) => O ~> batch(L) ... </k>
  rule [done]: <k> batch(.List) => .K ... </k>
endmodule
"#;

fn scratch(name: &str) -> std::path::PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-syntax-paths-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// A corpus of the fixture with `programs` (`(id, text)`) and the manifest's `coverage` section
/// text; its manifest's path.
fn corpus(name: &str, coverage: &str, programs: &[(&str, &str)]) -> std::path::PathBuf {
    let dir = scratch(name);
    fs::write(dir.join("path.k"), PATH_K).unwrap();
    // R4-WALLCLOCK: every run ends by itself within a few steps, far below this bound.
    let mut manifest = format!(
        "[spec]\nentry = \"path.k\"\nmain_module = \"PATH\"\nsyntax_module = \
         \"PATH-SYNTAX\"\n\n[budget]\ntime_ms = 600000\n\n{coverage}\n"
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

/// The syntax paths item whose id is `id`.
fn path<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["families"]["syntax_paths"]["items"]
        .as_array()
        .unwrap_or_else(|| panic!("no syntax paths: {document:#}"))
        .iter()
        .find(|item| item["id"] == id)
        .unwrap_or_else(|| panic!("no path {id}: {document:#}"))
}

/// The targets of the syntax paths family.
fn path_targets(document: &Value) -> Vec<&Value> {
    document["targets"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|target| target["family"] == "syntax_paths")
        .collect()
}

mod kink_tier {
    use super::*;

    /// At depth 2, `exec(mov(a(), b()))` reaches `exec` holding `mov` (the step inspects `exec`
    /// and takes `mov(..)` as its operand) and `mov` holding each register (the operand's root
    /// and its arguments), though `mov`'s own step never reads its first register. `exec`
    /// holding `neg` is open on the frontier, since `exec` is reached: a target naming the path
    /// and the program that reached `exec`. `wrap` holding `mov` is open off the frontier, as
    /// no step touched `wrap`, whose own target comes first. Every edge of the grammar graph is
    /// in the universe, and the measure counts every path. At depth 3 the path from `exec`
    /// through `mov` to a register is reached as well.
    #[test]
    #[ignore = "kink"]
    fn a_path_is_reached_where_a_fired_step_touched_it_and_the_frontier_is_targeted() {
        let manifest = corpus(
            "reached",
            "[coverage]\ndepth = 2\n",
            &[("mov", "exec(mov(a(), b()))")],
        );
        let document = document(&manifest);
        let family = &document["families"]["syntax_paths"];
        assert_eq!(family["depth"], 2, "{family:#}");
        assert_eq!(family["outside_universe"], json!([]), "{family:#}");
        for id in ["path:exec/0/mov", "path:mov/0/a", "path:mov/1/b"] {
            let item = path(&document, id);
            assert_eq!(item["status"], "reached", "{item:#}");
            assert_eq!(item["covered_by"], json!(["mov"]), "{item:#}");
        }
        let open = path(&document, "path:exec/0/neg");
        assert_eq!(
            (&open["status"], &open["frontier"]),
            (&json!("unreached"), &json!(true)),
            "{open:#}"
        );
        let targets = path_targets(&document);
        let target = targets
            .iter()
            .find(|target| target["item"] == "path:exec/0/neg")
            .unwrap_or_else(|| panic!("{document:#}"));
        let text = target["text"].as_str().unwrap();
        assert!(
            text.contains("touches exec holding neg at argument 0"),
            "{text}"
        );
        assert_eq!(target["programs"], json!(["mov"]), "{target:#}");
        let off = path(&document, "path:wrap/0/mov");
        assert_eq!(off["frontier"], false, "{off:#}");
        assert!(targets.iter().all(|target| target["item"] != off["id"]));
        // Two registers at each of `mov`'s arguments and at `neg`'s, three operations at
        // `wrap`'s and `exec`'s and at `run`'s; `batch`'s list holds no production of its own.
        let obligations = family["obligations"].as_u64().unwrap();
        assert_eq!(obligations, 2 * 2 + 2 + 3 * 3, "{family:#}");
        assert_eq!(
            family["counts"]["by_length"]["2"]["obligations"],
            obligations
        );
        assert_eq!(family["covered"], 3, "{family:#}");
        assert_eq!(
            document["summary"]["per_family"]["syntax_paths"]["obligations"],
            obligations
        );
        let verdicts = kink_flow::verdicts::verdicts(&document).unwrap();
        assert!(verdicts.contains("[coverage.syntax_paths]"), "{verdicts}");
        let text = kink_flow::coverage::text(&document).unwrap();
        assert!(text.contains("syntax_paths: 3 of 15 reached"), "{text}");

        let deeper = corpus(
            "deeper",
            "[coverage]\ndepth = 3\n",
            &[("mov", "exec(mov(a(), b()))")],
        );
        let deeper = super::document(&deeper);
        for id in ["path:exec/0/mov/0/a", "path:exec/0/mov/1/b"] {
            assert_eq!(path(&deeper, id)["status"], "reached", "{deeper:#}");
        }
        // The paths of length 2 are those of depth 2.
        assert_eq!(
            deeper["families"]["syntax_paths"]["counts"]["by_length"]["2"],
            json!({"obligations": 15, "covered": 3})
        );
    }

    /// `run(neg(a()))` builds `batch(ListItem(neg(a())))`: the list breaks every path through
    /// `batch`, so the grammar graph has no edge from `batch` and the runs record none through
    /// it, while `neg` holding `a` is reached, its root a value `batch`'s step reads from the
    /// list.
    #[test]
    #[ignore = "kink"]
    fn a_collection_breaks_a_path() {
        let manifest = corpus(
            "collection",
            "[coverage]\ndepth = 2\n",
            &[("batch", "run(neg(a()))")],
        );
        let document = document(&manifest);
        let family = &document["families"]["syntax_paths"];
        assert!(
            family["items"]
                .as_array()
                .unwrap()
                .iter()
                .all(|item| item["symbols"][0] != "Lblbatch"),
            "{family:#}"
        );
        assert_eq!(family["outside_universe"], json!([]), "{family:#}");
        for id in ["path:run/0/neg", "path:neg/0/a"] {
            assert_eq!(
                path(&document, id)["covered_by"],
                json!(["batch"]),
                "{document:#}"
            );
        }
    }

    /// At depth 1 the document has no syntax paths, and its verdicts rendering no
    /// `[syntax_paths]`: the syntax family is what it was.
    #[test]
    #[ignore = "kink"]
    fn depth_one_has_no_syntax_paths() {
        let manifest = corpus("depth-one", "", &[("mov", "exec(mov(a(), b()))")]);
        let document = document(&manifest);
        assert_eq!(document["settings"]["depth"], 1);
        assert_eq!(document["families"]["syntax_paths"], Value::Null);
        assert!(
            document["summary"]["per_family"]
                .get("syntax_paths")
                .is_none(),
            "{document:#}"
        );
        let verdicts = kink_flow::verdicts::verdicts(&document).unwrap();
        assert!(!verdicts.contains("syntax_paths"), "{verdicts}");
        let text = kink_flow::coverage::text(&document).unwrap();
        assert!(
            text.contains("syntax_paths: computed above depth 1 only"),
            "{text}"
        );
        let reached = document["families"]["syntax"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|item| item["status"] == "reached")
            .filter_map(|item| item["id"].as_str())
            .collect::<Vec<_>>();
        // `a` lies below `mov` in `exec`'s operand and is `mov`'s unread register: no step
        // touched it, though at depth 2 the path from `mov` to it is reached.
        assert_eq!(
            reached,
            ["syntax:b", "syntax:mov", "syntax:exec"],
            "{document:#}"
        );
    }

    /// A universe above `[coverage] max_obligations` is refused before any program runs, with
    /// the syntax paths family's counts by length and the grammar graph's size.
    #[test]
    #[ignore = "kink"]
    fn a_universe_above_max_obligations_is_refused_with_its_counts() {
        let manifest = corpus(
            "bounded",
            "[coverage]\ndepth = 2\nmax_obligations = 14\n",
            &[("mov", "exec(mov(a(), b()))")],
        );
        let (document, status) = run(&manifest, &CoverageOptions::default());
        assert_eq!(status, EXIT_UNASKED, "{document:#}");
        assert_eq!(document["spec"]["stage"], "coverage");
        assert_eq!(document["spec"]["reason"], "max-obligations");
        assert_eq!(document["programs"], json!([]));
        let detail = document["spec"]["detail"].as_str().unwrap();
        assert!(
            detail.contains("the syntax paths family has 15 obligations (length 2: 15"),
            "{detail}"
        );
        assert!(detail.contains("max_obligations = 14"), "{detail}");
        assert!(!manifest.parent().unwrap().join(".kink-flow").exists());
    }

    /// An argued production argues every path it starts, and an argued path every path it is a
    /// prefix of; neither has a target. A path whose later production is argued is not argued
    /// by it: that production lies below a touched position without being touched.
    #[test]
    #[ignore = "kink"]
    fn a_path_starting_with_an_argued_part_is_argued_by_it() {
        let manifest = corpus(
            "argued",
            "[coverage]\ndepth = 3\n\n[[coverage.argued]]\nitem = \"syntax:wrap\"\nargument = \
             \"no program wraps\"\n\n[[coverage.argued]]\nitem = \"path:exec/0/neg\"\nargument \
             = \"no program executes a negation\"\n",
            &[("mov", "exec(mov(a(), b()))")],
        );
        let document = document(&manifest);
        let wrapped = path(&document, "path:wrap/0/mov");
        assert_eq!(
            (&wrapped["status"], &wrapped["argued_by"]),
            (&json!("argued"), &json!("syntax:wrap")),
            "{wrapped:#}"
        );
        let extension = path(&document, "path:exec/0/neg/0/a");
        assert_eq!(extension["argued_by"], "path:exec/0/neg", "{extension:#}");
        let below = path(&document, "path:exec/0/wrap");
        assert_eq!(below["status"], "unreached", "{below:#}");
        assert!(
            path_targets(&document)
                .iter()
                .any(|target| target["item"] == "path:exec/0/wrap"),
            "{document:#}"
        );
        let family = &document["families"]["syntax_paths"];
        let argued = family["items"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|item| item["status"] == "argued")
            .count();
        assert_eq!(family["counts"]["argued"], argued, "{family:#}");
        assert_eq!(
            document["summary"]["per_family"]["syntax_paths"]["argued"],
            argued
        );
    }

    /// An invariant named on a syntax path is refused, the path named as `syntax_paths`.
    #[test]
    #[ignore = "kink"]
    fn a_syntax_path_takes_no_invariant() {
        let manifest = corpus(
            "path-invariant",
            "[coverage]\ndepth = 3\n\n[[coverage.invariant]]\nname = \"i\"\nfunction = \"f\"\n\
             cells = [\"k\"]\n\n[[coverage.argued]]\nitem = \"path:exec/0/neg\"\nargument = \
             \"no program executes a negation\"\ninvariant = \"i\"\n",
            &[("mov", "exec(mov(a(), b()))")],
        );
        let (refused, status) = run(&manifest, &CoverageOptions::default());
        assert_eq!(status, EXIT_UNASKED, "{refused:#}");
        assert_eq!(refused["spec"]["reason"], "argued-invariant-unsupported");
        let detail = refused["spec"]["detail"].as_str().unwrap();
        assert!(
            detail.contains("`path:exec/0/neg` (syntax_paths)"),
            "{detail}"
        );
    }

    /// The syntax paths read the scope every family shares: with `exec` marked a claim helper,
    /// its fired instance reaches no path, so `exec` holding `mov`, which only that step
    /// touched, is unreached and off the frontier (`exec` itself is unreached), while `mov`
    /// holding `b`, which `mov`'s own step touched, is still reached.
    #[test]
    #[ignore = "kink"]
    fn a_claim_helper_reaches_no_path() {
        let manifest = corpus(
            "claim-helper",
            "[coverage]\ndepth = 2\n",
            &[("mov", "exec(mov(a(), b()))")],
        );
        let marked = kink_flow::FlowManifest::read(&manifest)
            .unwrap()
            .with_claim_helpers([("PATH".to_owned(), "exec".to_owned())]);
        let (mut document, ok) =
            kink_flow::coverage::coverage(&marked, &CoverageOptions::default());
        kink_flow::coverage::derive(&mut document, &kink_flow::cli::KinkFlowSpelling);
        assert!(ok, "{document:#}");
        let helper = document["families"]["rules"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|item| item["id"] == "rule:PATH.exec")
            .unwrap_or_else(|| panic!("{document:#}"));
        assert_eq!(helper["status"], "claim-helper", "{helper:#}");
        let held = path(&document, "path:exec/0/mov");
        assert_eq!(
            (&held["status"], &held["covered_by"], &held["frontier"]),
            (&json!("unreached"), &json!([]), &json!(false)),
            "{held:#}"
        );
        assert_eq!(
            path(&document, "path:mov/1/b")["covered_by"],
            json!(["mov"]),
            "{document:#}"
        );
    }
}
