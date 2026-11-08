//! `kink-flow coverage`'s syntax family at depth 1: a production of an authored sort is reached
//! when a fired instance of a sentence touched it, as the left-hand side's inspected
//! production, as the head of an operand, or as the right-hand side's built production; a
//! production only carried in a state is not, and an unreached one is a target naming the rules
//! that inspect it.
//!
//! The fixture is written here: every program ends by itself, far inside the default budget's
//! depth, so no result depends on a clock.

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
    let dir = scratch(name);
    fs::write(dir.join("syn.k"), SYN_K).unwrap();
    let mut manifest = "[spec]\nentry = \"syn.k\"\nmain_module = \"SYN\"\nsyntax_module = \
                        \"SYN-SYNTAX\"\n"
        .to_owned();
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
    ///   `V` that `push` takes (through its injection into `K`);
    /// - `flag` is reached only as what `mark` builds;
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
        assert_eq!(syntax["covered"], 6);
        assert_eq!(
            syntax["counts"]["productions"],
            json!({"obligations": 8, "covered": 6})
        );
        assert_eq!(
            syntax["counts"]["field_values"],
            json!({"obligations": 0, "covered": 0})
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
        assert_eq!(
            targets
                .iter()
                .map(|target| target["item"].as_str().unwrap())
                .collect::<Vec<_>>(),
            [note_id, pop_id],
            "{document:#}"
        );
        let pop_target = targets[1];
        assert_eq!(pop_target["rules"], json!(["rule:SYN.pop"]));
        let text = pop_target["text"].as_str().unwrap();
        assert!(text.contains("rule:SYN.pop inspect it"), "{text}");
        assert_eq!(document["summary"]["per_family"]["syntax"]["open"], 2);
        // The verdicts rendering lists the open productions.
        let verdicts = kink_flow::verdicts::verdicts(&document).unwrap();
        assert!(
            verdicts.contains(&format!("[syntax]\nopen = [\"{note_id}\", \"{pop_id}\"]")),
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
}
