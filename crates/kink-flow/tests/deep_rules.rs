//! Re-pin L1-3-fix-1 (review L1-3-1): a mutation of a rule 60, 200 or 1500 terms deep is
//! decoded and judged as at depth 50. Re-pin L1-3-fix-2 (review L1-3-2 D1): the judgement does
//! not depend on the calling thread's stack, and a rule too deep for kink's document limit is
//! refused by that limit's name while every other row stands. The specification's rule `[big]` rewrites to a Peano
//! numeral DEPTH levels deep; the list mutates `[add]` (killed) and `[big]`'s guard (survived:
//! the one program never reaches `[big]`). Before the fix, kink-patch's codec read k-rust's KAST
//! JSON with serde_json's recursion limit of 128, so every depth past about 55 refused `[big]`'s
//! mutation as `invalid-mutation` (`patch-rejected`). Each depth runs cold and then warm with the
//! default compile workers, on a 256 MiB thread as the command does.

use kink_flow::{
    FlowManifest, MutationList,
    search::{ProgramOrder, RunOptions, run},
};
use serde_json::Value;
use std::{fs, path::PathBuf};

const FLOW: &str = "[spec]\nentry = \"deep.k\"\nmain_module = \"DEEP\"\nsyntax_module = \
                    \"DEEP-SYNTAX\"\n\n[[program]]\nid = \"add\"\nfile = \"programs/add.deep\"\n";

const MUTATIONS: &str = "[[mutation]]\nid = \"add-becomes-sub\"\n  [[mutation.edit]]\n  rule = \
                         \"add\"\n  find = \"I1 +Int I2\"\n  replace = \"I1 -Int I2\"\n\n\
                         [[mutation]]\nid = \"big-guard\"\n  [[mutation.edit]]\n  rule = \
                         \"big\"\n  find = \"I >Int 100\"\n  replace = \"I >Int 200\"\n";

fn specification(depth: usize) -> String {
    format!(
        "module DEEP-SYNTAX\n  imports INT-SYNTAX\n  syntax Exp ::= Int\n               | \"go\" \
         \"(\" Int \")\"\n               > left:\n                 Exp \"+\" Exp [strict, \
         symbol(add)]\nendmodule\n\nmodule DEEP\n  imports DEEP-SYNTAX\n  imports INT\n  \
         configuration <k> $PGM:Exp </k>\n  syntax KResult ::= Int\n  syntax Peano ::= \"z\" | \
         s(Peano)\n  syntax Exp ::= deep(Peano)\n  rule [add]: I1:Int + I2:Int => I1 +Int I2\n  \
         rule [big]: go(I:Int) => deep({}z{}) requires I >Int 100\nendmodule\n",
        "s(".repeat(depth),
        ")".repeat(depth)
    )
}

fn fixture(depth: usize) -> PathBuf {
    fixture_with(&depth.to_string(), depth, MUTATIONS)
}

fn fixture_with(name: &str, depth: usize, mutations: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-deep-rules-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("programs")).unwrap();
    fs::write(dir.join("FLOW.toml"), FLOW).unwrap();
    fs::write(dir.join("MUTATIONS.toml"), mutations).unwrap();
    fs::write(dir.join("deep.k"), specification(depth)).unwrap();
    fs::write(dir.join("programs/add.deep"), "1 + 2\n").unwrap();
    dir
}

/// Each row's judgement: everything but the fields that name the definition (the mutation's
/// identity and digest, and the edited rules' text) or time the run.
fn judged(document: &Value) -> Vec<Value> {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            let mut row = row.as_object().unwrap().clone();
            for key in ["identity", "digest", "rules", "call_wall_ms"] {
                row.remove(key);
            }
            for executed in row
                .get_mut("executed")
                .and_then(Value::as_array_mut)
                .into_iter()
                .flatten()
            {
                let executed = executed.as_object_mut().unwrap();
                executed.remove("wall_ms");
                executed.remove("baseline_ms");
            }
            Value::Object(row)
        })
        .collect()
}

/// The cold and the warm run's rows.
fn search(depth: usize) -> [Vec<Value>; 2] {
    search_in(&fixture(depth), depth)
}

fn search_in(dir: &std::path::Path, depth: usize) -> [Vec<Value>; 2] {
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let mutations = MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
    let options = RunOptions {
        only: Vec::new(),
        cache: None,
        order: ProgramOrder::Corpus,
        compile_workers: None,
    };
    [(); 2].map(|()| {
        let (document, ok) = run(&manifest, &mutations, &options);
        assert!(ok, "depth {depth}: {document}");
        judged(&document)
    })
}

#[test]
fn deep_rules_are_judged_as_at_depth_50() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let shallow = search(50);
            let statuses = |rows: &[Value]| {
                rows.iter()
                    .map(|row| format!("{}={}", row["id"], row["status"]))
                    .collect::<Vec<_>>()
            };
            assert_eq!(
                statuses(&shallow[0]),
                [
                    "\"add-becomes-sub\"=\"killed\"",
                    "\"big-guard\"=\"survived\""
                ]
            );
            assert_eq!(statuses(&shallow[1]), statuses(&shallow[0]));
            for depth in [60, 200, 1500] {
                assert_eq!(search(depth), shallow, "depth {depth} against depth 50");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Re-pin L1-3-fix-2 (review L1-3-2 D1): on a 16 MiB thread, a mutation of a rule 10,000 terms
/// deep is judged as at depth 50, as on kink-flow's 256 MiB thread. Typing the edited rule
/// (about 2 KiB of stack per level) and encoding its patch (about 3.9 KiB per level
/// unoptimized) ran on the calling thread before the fix and overflowed this one, aborting the
/// process; both now run on a stack sized from the rule's depth.
#[test]
fn deep_rules_are_judged_alike_on_a_thread_too_small_for_them() {
    std::thread::Builder::new()
        .stack_size(16 << 20)
        .spawn(|| assert_eq!(search(10_000), search(50), "depth 10000 on 16 MiB"))
        .unwrap()
        .join()
        .unwrap();
}

/// Re-pin L1-3-fix-2 (review L1-3-2 D1): a replacement text whose rule is too deep for kink
/// (its patch's document would nest past kink-patch `MAX_JSON_DEPTH`: half as many term levels,
/// 64,000 in this unoptimized build and 300,000 in an optimized one) makes that mutation
/// `invalid-mutation` with the reason `edited-rule-too-deep`, which names kink's limit, and the
/// other mutation of the list is still killed. Before, such a rule reached k-rust's unguarded
/// typing on the calling thread and the process aborted, losing every row (300,000 levels on a
/// 256 MiB thread in release); main 5a7f1f9 called it `patch-rejected`.
#[test]
fn a_rule_too_deep_for_kink_is_refused_by_name_and_the_other_rows_stand() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let depth = kink_patch::MAX_JSON_DEPTH / 2;
            let mutations = format!(
                "[[mutation]]\nid = \"add-becomes-sub\"\n  [[mutation.edit]]\n  rule = \"add\"\n  \
                 find = \"I1 +Int I2\"\n  replace = \"I1 -Int I2\"\n\n[[mutation]]\nid = \
                 \"big-deep\"\n  [[mutation.edit]]\n  rule = \"big\"\n  find = \"deep(z)\"\n  \
                 replace = \"deep({}z{})\"\n",
                "s(".repeat(depth),
                ")".repeat(depth)
            );
            let dir = fixture_with("too-deep", 0, &mutations);
            for rows in search_in(&dir, depth) {
                let row = |id: &str| {
                    rows.iter()
                        .find(|row| row["id"] == id)
                        .unwrap_or_else(|| panic!("no row {id}"))
                        .clone()
                };
                assert_eq!(row("add-becomes-sub")["status"], "killed");
                let deep = row("big-deep");
                assert_eq!(deep["status"], "invalid-mutation", "{deep}");
                assert_eq!(deep["reason"], "edited-rule-too-deep", "{deep}");
                let detail = deep["detail"].as_str().unwrap();
                assert!(detail.contains("MAX_JSON_DEPTH"), "{detail}");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
