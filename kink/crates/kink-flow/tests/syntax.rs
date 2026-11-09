//! `kink-flow coverage`'s syntax family at depth 1: a production of an authored sort is reached
//! when a fired instance of a sentence touched it, as the left-hand side's inspected
//! production, as the head of an operand the sentence reads, or as the right-hand side's built
//! production; a production only carried in a state, or bound and never read, is not, and an
//! unreached one is a target naming the rules that inspect it. Of an axiom with several
//! alternatives, what the alternative a fired instance took inspects is reached, not what the
//! others inspect.
//!
//! The fixtures are written here: every program ends by itself within a few steps, and the
//! manifest's `[budget] time_ms` is far above what such a run takes (R4-WALLCLOCK), so no result
//! depends on a clock.

use kink_flow::{
    cli::{EXIT_YES, coverage},
    coverage::CoverageOptions,
};
use serde_json::{Value, json};
use std::{fs, path::Path};

const SYN_K: &str = r#"module SYN-SYNTAX
  imports INT-SYNTAX
  syntax Val ::= num(Int) [symbol(num)]
  syntax Flag ::= "none" [symbol(none)] | flag() [symbol(flag)]
  syntax Note ::= note(Int) [symbol(note)]
  syntax Instr ::= push(Val) [symbol(push)] | mark() [symbol(mark)] | pop() [symbol(pop)]
  syntax Pgm ::= Instr | Instr ";" Pgm [symbol(seq)]
endmodule

module SYN
  imports SYN-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k> <acc> .K </acc> <flag> none </flag> <log> note(0) </log>
  rule [seq]: <k> I:Instr ; P:Pgm => I ~> P ... </k>
  rule [push]: <k> push(V) => .K ... </k> <acc> _ => V </acc>
  rule [mark]: <k> mark() => .K ... </k> <flag> _ => flag() </flag>
  rule [pop]: <k> pop() => .K ... </k> <acc> _ => .K </acc>
endmodule
"#;

/// A rule whose left-hand side is a disjunction: k-rust loads one rule per disjunct, under one
/// id.
const ALT_K: &str = r#"module ALT-SYNTAX
  syntax Instr ::= alpha() [symbol(alpha)] | beta() [symbol(beta)]
  syntax Pgm ::= Instr | Instr ";" Pgm [symbol(seq)]
endmodule

module ALT
  imports ALT-SYNTAX
  configuration <k> $PGM:Pgm </k>
  rule [seq]: <k> I:Instr ; P:Pgm => I ~> P ... </k>
  rule [either]: <k> (alpha() #Or beta()) => .K ... </k>
endmodule
"#;

fn scratch(name: &str) -> std::path::PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-syntax-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// The coverage document of the fixture with `programs`, each `(id, text)`.
fn document(name: &str, programs: &[(&str, &str)]) -> Value {
    document_of(name, ("syn.k", SYN_K, "SYN"), programs)
}

/// The coverage document of the specification `(file, text, main module)`, whose syntax module
/// is the main module's name with `-SYNTAX`, with `programs`, each `(id, text)`.
fn document_of(
    name: &str,
    (file, text, main): (&str, &str, &str),
    programs: &[(&str, &str)],
) -> Value {
    let dir = scratch(name);
    fs::write(dir.join(file), text).unwrap();
    // R4-WALLCLOCK: every run ends by itself within a few steps, far below this bound.
    let mut manifest = format!(
        "[spec]\nentry = \"{file}\"\nmain_module = \"{main}\"\nsyntax_module = \
         \"{main}-SYNTAX\"\n\n[budget]\ntime_ms = 600000\n"
    );
    for (id, text) in programs {
        manifest.push_str(&format!(
            "\n[[program]]\nid = \"{id}\"\ntext = \"{text}\"\n"
        ));
    }
    fs::write(dir.join("FLOW.toml"), manifest).unwrap();
    let (mut document, status) = coverage(&dir.join("FLOW.toml"), &CoverageOptions::default());
    assert_eq!(status, EXIT_YES, "{document:#}");
    kink_flow::coverage::derive(&mut document, &kink_flow::cli::KinkFlowSpelling);
    document
}

/// The syntax item of the production whose symbol is `symbol`.
fn production<'d>(document: &'d Value, symbol: &str) -> &'d Value {
    document["families"]["syntax"]["items"]
        .as_array()
        .unwrap_or_else(|| panic!("no syntax items: {document:#}"))
        .iter()
        .find(|item| item["symbol"] == symbol)
        .unwrap_or_else(|| panic!("no production {symbol}: {document:#}"))
}

/// `(inspected_by, operand_of, built_by)` of a syntax item.
fn touches(item: &Value) -> (Value, Value, Value) {
    (
        item["inspected_by"].clone(),
        item["operand_of"].clone(),
        item["built_by"].clone(),
    )
}

mod kink_tier {
    use super::*;

    /// One program, `push(num(1)) ; mark()`, touches each production one way or several:
    /// - `push` is inspected by the rule `push`, and is the head of the operand `I` of `seq`;
    /// - `num` is inspected and built by no rule, and is reached only as the head of the operand
    ///   `V` that `push` takes (through its injection into `K`) and puts in `<acc>`;
    /// - `flag` is reached only as what `mark` builds;
    /// - `none` is in `<flag>` until `mark` overwrites it (`<flag> _ => flag() </flag>`): `mark`
    ///   binds it and never reads it, so the step carried it and dropped it, and `none` is
    ///   unreached, with a target, though no rule inspects or builds it;
    /// - `note` sits in the `<log>` cell from the initial state to the end: every rule carries the
    ///   cell in a variable whose head is the cell's own, so `note` is unreached, and no rule
    ///   inspects or builds it;
    /// - `pop` is unreached, and its target names the rule that inspects it.
    ///
    /// The universe is the constructors of the sorts the specification declares, with no function,
    /// cell or library production.
    #[test]
    #[ignore = "kink"]
    fn a_production_is_reached_where_a_fired_instance_touched_it() {
        let document = document("touched", &[("p", "push(num(1)) ; mark()")]);
        let program = || json!(["p"]);
        let none = || json!([]);
        assert_eq!(
            touches(production(&document, "Lblpush")),
            (program(), program(), none()),
            "{document:#}"
        );
        assert_eq!(
            touches(production(&document, "Lblnum")),
            (none(), program(), none())
        );
        assert_eq!(
            touches(production(&document, "Lblflag")),
            (none(), none(), program())
        );
        for symbol in ["Lblpush", "Lblnum", "Lblflag", "Lblmark", "Lblseq"] {
            let item = production(&document, symbol);
            assert_eq!(item["status"], "reached", "{symbol}: {item:#}");
            assert_eq!(item["covered"], true, "{symbol}");
            assert_eq!(item["reached_by"], program(), "{symbol}");
        }
        let none_item = production(&document, "Lblnone");
        assert_eq!(none_item["status"], "unreached", "{none_item:#}");
        assert_eq!(touches(none_item), (none(), none(), none()));
        assert_eq!(none_item["inspecting_rules"], none());
        assert_eq!(none_item["building_rules"], none());
        let note = production(&document, "Lblnote");
        assert_eq!(note["status"], "unreached", "{note:#}");
        assert_eq!(touches(note), (none(), none(), none()));
        assert_eq!(note["inspecting_rules"], none());
        assert_eq!(note["building_rules"], none());
        let pop = production(&document, "Lblpop");
        assert_eq!(pop["status"], "unreached", "{pop:#}");
        assert_eq!(pop["inspecting_rules"], json!(["rule:SYN.pop"]));
        assert_eq!(pop["sort"], "Instr");
        let symbols = document["families"]["syntax"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .map(|item| item["symbol"].as_str().unwrap().to_owned())
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            symbols,
            [
                "Lblflag", "Lblmark", "Lblnone", "Lblnote", "Lblnum", "Lblpop", "Lblpush", "Lblseq"
            ]
            .map(str::to_owned)
            .into_iter()
            .collect()
        );
        let syntax = &document["families"]["syntax"];
        assert_eq!(syntax["obligations"], 8, "{syntax:#}");
        assert_eq!(syntax["covered"], 5);
        assert_eq!(
            syntax["counts"]["productions"],
            json!({"obligations": 8, "covered": 5, "argued": 0})
        );
        assert_eq!(
            syntax["counts"]["field_values"],
            json!({"obligations": 0, "covered": 0, "argued": 0})
        );
        // An unreached production is a target, in item order, naming the rules that inspect it.
        let targets = document["targets"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|target| target["family"] == "syntax")
            .collect::<Vec<_>>();
        let pop_id = pop["id"].as_str().unwrap();
        let note_id = note["id"].as_str().unwrap();
        let none_id = none_item["id"].as_str().unwrap();
        assert_eq!(
            targets
                .iter()
                .map(|target| target["item"].as_str().unwrap())
                .collect::<Vec<_>>(),
            [none_id, note_id, pop_id],
            "{document:#}"
        );
        assert_eq!(targets[0]["rules"], none());
        let none_text = targets[0]["text"].as_str().unwrap();
        assert!(
            none_text.contains("only a step that takes it as an operand reaches it"),
            "{none_text}"
        );
        let pop_target = targets[2];
        assert_eq!(pop_target["rules"], json!(["rule:SYN.pop"]));
        let text = pop_target["text"].as_str().unwrap();
        assert!(text.contains("rule:SYN.pop inspect it"), "{text}");
        assert_eq!(document["summary"]["per_family"]["syntax"]["open"], 3);
        // The verdicts rendering lists the open productions.
        let verdicts = kink_flow::verdicts::verdicts(&document).unwrap();
        assert!(
            verdicts.contains(&format!(
                "[coverage.syntax]\nopen = [\n  \"{none_id}\",\n  \"{note_id}\",\n  \"{pop_id}\",\n]\n"
            )),
            "{verdicts}"
        );
    }

    /// A program that touches nothing new reaches nothing new: adding `push(num(2))` beside the
    /// first program leaves every status and the open list as they were, and the second program is
    /// listed where it touched.
    #[test]
    #[ignore = "kink"]
    fn a_program_that_touches_nothing_new_moves_no_status() {
        let one = document("one", &[("p", "push(num(1)) ; mark()")]);
        let two = document(
            "two",
            &[("p", "push(num(1)) ; mark()"), ("q", "push(num(2))")],
        );
        let statuses = |document: &Value| {
            document["families"]["syntax"]["items"]
                .as_array()
                .unwrap()
                .iter()
                .map(|item| (item["id"].clone(), item["status"].clone()))
                .collect::<Vec<_>>()
        };
        assert_eq!(statuses(&one), statuses(&two));
        assert_eq!(
            production(&two, "Lblnum")["operand_of"],
            json!(["p", "q"]),
            "{two:#}"
        );
    }

    /// `either`'s left-hand side is `alpha() #Or beta()`, loaded as one rule per disjunct under
    /// one id. A program that runs `alpha()` fires the disjunct that inspects `alpha`: `alpha` is
    /// reached, inspected by `either`, and `beta`, which only the other disjunct inspects, is
    /// unreached, its target naming `either`, though the sentence `either` fired.
    #[test]
    #[ignore = "kink"]
    fn only_the_alternative_a_fired_instance_took_is_reached() {
        let document = document_of("alternative", ("alt.k", ALT_K, "ALT"), &[("l", "alpha()")]);
        let rules = document["families"]["rules"]["items"].as_array().unwrap();
        let either = rules
            .iter()
            .find(|rule| rule["id"] == "rule:ALT.either")
            .unwrap_or_else(|| panic!("no rule either: {document:#}"));
        assert_eq!(either["status"], "fired", "{either:#}");
        let alpha = production(&document, "Lblalpha");
        assert_eq!(alpha["status"], "reached", "{alpha:#}");
        assert_eq!(alpha["inspected_by"], json!(["l"]));
        let beta = production(&document, "Lblbeta");
        assert_eq!(beta["status"], "unreached", "{beta:#}");
        assert_eq!(touches(beta), (json!([]), json!([]), json!([])));
        assert_eq!(beta["inspecting_rules"], json!(["rule:ALT.either"]));
    }

    /// A front end's selection names each binder once. One binder under one axiom name with two
    /// caps is refused by the manifest (`syntax.binders`); under the axiom's label and its
    /// `UNIQUE_ID` (read from a run that selected it by label, whose record names the binder by
    /// its `UNIQUE_ID`) the specification is refused when the definition is loaded (stage
    /// `syntax`, reason `binder-selected-twice`), before any program runs.
    #[test]
    #[ignore = "kink"]
    fn a_binder_selected_twice_is_refused_before_any_run() {
        use kink_flow::manifest::{FlowManifest, SyntaxSelection};
        use std::collections::BTreeSet;
        let dir = scratch("twice");
        fs::write(dir.join("syn.k"), SYN_K).unwrap();
        fs::write(
            dir.join("FLOW.toml"),
            "[spec]\nentry = \"syn.k\"\nmain_module = \"SYN\"\nsyntax_module = \
             \"SYN-SYNTAX\"\n\n[budget]\ntime_ms = 600000\n\n[[program]]\nid = \"p\"\ntext = \
             \"push(num(1))\"\n",
        )
        .unwrap();
        let selection = |binders: &[(&str, usize)]| SyntaxSelection {
            sorts: ["Val", "Flag", "Note", "Instr", "Pgm"]
                .map(str::to_owned)
                .into_iter()
                .collect(),
            binders: binders
                .iter()
                .map(|(axiom, cap)| ((*axiom).to_owned(), "VarV".to_owned(), *cap))
                .collect::<BTreeSet<_>>(),
        };
        let manifest = || FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
        let refused = manifest()
            .with_syntax(selection(&[("SYN.push", 4), ("SYN.push", 8)]))
            .expect_err("one binder with two caps is refused");
        assert_eq!(refused.key, "syntax.binders", "{refused:?}");
        let by_label = manifest()
            .with_syntax(selection(&[("SYN.push", 4)]))
            .expect("one selection of a binder is accepted");
        let (document, _) = kink_flow::coverage::coverage(&by_label, &CoverageOptions::default());
        let binders = document["families"]["syntax"]["binders"]
            .as_array()
            .unwrap_or_else(|| panic!("no binders: {document:#}"));
        assert_eq!(binders.len(), 1, "{document:#}");
        let unique_id = binders[0]["axiom"].as_str().unwrap().to_owned();
        assert_ne!(unique_id, "SYN.push");
        let twice = manifest()
            .with_syntax(selection(&[("SYN.push", 4), (&unique_id, 4)]))
            .expect("the manifest cannot tell a label from a UNIQUE_ID");
        let (document, _) = kink_flow::coverage::coverage(&twice, &CoverageOptions::default());
        assert_eq!(document["spec"]["stage"], "syntax", "{document:#}");
        assert_eq!(document["spec"]["reason"], "binder-selected-twice");
        assert_eq!(document["programs"], json!([]));
    }
}
