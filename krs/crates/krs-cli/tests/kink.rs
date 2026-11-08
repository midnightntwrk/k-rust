//! `krs kink <verb>`: the corpus loop over a KRS package, with kink-flow as its engine.
//!
//! The main fixture is a copy of the introduction's story package (`docs-site/story/plus`) with
//! its corpus, `kink/FLOW.toml` and the story's four cases: the tool must report what the
//! story's pages claim, each rule named by its Rust item and position, and kill the story's
//! three edits written as K patches anchored by `plus_zero` and `plus_succ`. A small counter
//! definition, which has rewrite rules, gives `fuzz --matched` and a query witness rules to name;
//! `fixtures/inputs` gives a case of typed inputs, and `fixtures/inferred-main` and
//! `fixtures/bytes-main` program files bound to a main parameter that is not `$PGM`. A
//! definition of guarded transitions, a nondet group, a branching function, a division in a
//! condition and a claim helper gives the front end's own mutation checks something to refuse,
//! each checked against `krs check` of a Rust source that emits the mutant. The
//! configuration-cells gate's cell group gives a mutation of a rule a library writes for its group,
//! judged in each of the two definitions that hold the group, and its harts a corpus narrowed to a
//! cell inside the instances of a Map collection.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;
use std::sync::{Arc, Mutex, Weak};

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value, json};

const STORY: &str = include_str!("../../../../docs-site/story/plus/src/lib.rs");
/// The story's corpus (`docs-site/story/plus/kink`), the one the introduction's pages show:
/// its manifest and four cases (story.toml `[[test]]`). The expectations below are what the
/// pages show for these programs, which the docs-site derives from its recorded outputs: the
/// coverage from `krs kink coverage` (story-kink-coverage), and the tests that catch each edit from
/// `krs kink run --full` (story-kink-run).
const STORY_FLOW: &str = include_str!("../../../../docs-site/story/plus/kink/FLOW.toml");
const STORY_CASES: [(&str, &str); 4] = [
    (
        "t1",
        include_str!("../../../../docs-site/story/plus/kink/cases/t1.nat"),
    ),
    (
        "t2",
        include_str!("../../../../docs-site/story/plus/kink/cases/t2.nat"),
    ),
    (
        "t3",
        include_str!("../../../../docs-site/story/plus/kink/cases/t3.nat"),
    ),
    (
        "t4",
        include_str!("../../../../docs-site/story/plus/kink/cases/t4.nat"),
    ),
];
const INPUTS: &str = include_str!("fixtures/inputs/src/lib.rs");
const INFERRED_MAIN: &str = include_str!("fixtures/inferred-main/src/lib.rs");
const BYTES_MAIN: &str = include_str!("fixtures/bytes-main/src/lib.rs");

/// A definition with rewrite rules: `count(n)` steps down to `count(0)`, which stops.
const COUNTER: &str = r#"use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("count({value})")] Count { value: Int },
    #[k::syntax("done")] Done(),
}

#[k::rule]
#[k::requires(int::gt(value, 0))]
fn step(k::term![ExpSyntax::Count { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Count(int::sub(value, 1))
}

#[k::rule]
#[k::requires(int::le(value, 0))]
fn stop(k::term![ExpSyntax::Count { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Done()
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}
"#;

/// A story-shaped machine for guard outcomes: four complementary boundary rules over the
/// `halted`, `irq` and `ime` cells, of which no case reaches the halted ones (the corpus never
/// halts); a write whose function splits the address range, of which no case reaches the high
/// half; a rule whose condition divides and reads the `mem` map, and an equation that divides
/// (definedness tests); a rule that looks up a computed key (a lookup guard), and one whose
/// condition reads the looked-up value; and a decode function over `k::bits!` templates, one
/// with a condition of its own, one without, and one no case matches.
const GUARDED: &str = r#"use k::builtin::{map, Bool, Int, KSequence, Map};
use k::{KResult, Term};

k::sorts! {
    Cmd;
}

#[k::constructors(sort = Cmd, result = KResult)]
#[k::precedence((Raise, Boundary, Write, Scale, Fetch, Peek, Ratio, Decode) > (Seq))]
pub enum CmdSyntax {
    #[k::syntax("{first} ; {rest}")]
    Seq { first: Cmd, rest: Cmd },
    #[k::syntax("raise")]
    Raise(),
    #[k::syntax("boundary")]
    Boundary(),
    #[k::syntax("write {addr} {value}")]
    Write { addr: Int, value: Int },
    #[k::syntax("scale {a}")]
    Scale { a: Int },
    #[k::syntax("fetch {a}")]
    Fetch { a: Int },
    #[k::syntax("peek {a}")]
    Peek { a: Int },
    #[k::syntax("ratio {a}")]
    Ratio { a: Int },
    #[k::syntax("decode {op}")]
    Decode { op: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub halted: Bool,
    #[k::cell]
    pub irq: Bool,
    #[k::cell]
    pub ime: Bool,
    #[k::cell]
    pub mem: Map,
    #[k::cell]
    pub idx: Map,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Cmd) -> Self {
        Self {
            k: k::k![pgm],
            halted: false,
            irq: false,
            ime: true,
            mem: map![1 -> 5, 2 -> 2],
            idx: map![1 -> 1, 2 -> 2],
            acc: 0,
        }
    }
}

k::rules! {
    for Machine;
    use CmdSyntax::*;

    seq: { k: [Seq(first, rest), ..] } => { k: [first, rest, ..] };
    raise: { k: [Raise(), ..], irq: _ } => { k: [..], irq: true };
    #[k::requires(!halted && irq && ime)]
    boundary_dispatch: { k: [Boundary(), ..], halted: halted, irq: irq, ime: ime, acc: _ } => { k: [..], acc: 1 };
    #[k::requires(!halted && !irq)]
    boundary_run: { k: [Boundary(), ..], halted: halted, irq: irq, acc: _ } => { k: [..], acc: 2 };
    #[k::requires(halted && irq)]
    boundary_wake: { k: [Boundary(), ..], halted: halted, irq: irq, acc: _ } => { k: [..], acc: 3 };
    #[k::requires(halted && !irq)]
    boundary_halted: { k: [Boundary(), ..], halted: halted, irq: irq, acc: _ } => { k: [..], acc: 4 };
    write: { k: [Write(addr, value), ..], mem: m } => { k: [..], mem: crate::WriteByte(m, addr, value) };
    #[k::requires(100 / a > 1 && m[a] > 0)]
    scale: { k: [Scale(a), ..], mem: m, acc: _ } => { k: [..], acc: 1 };
    fetch: { k: [Fetch(a), ..], idx: ix, mem: { ix[a] -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
    #[k::requires(v > 3)]
    peek: { k: [Peek(a), ..], idx: ix, mem: { ix[a] -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
    ratio: { k: [Ratio(a), ..], acc: _ } => { k: [..], acc: crate::Quotient(a) };
    decode: { k: [Decode(op), ..], acc: _ } => { k: [..], acc: crate::DecodeOp(op) };
}

#[k::function(total, internal)]
pub fn WriteByte(mem: Term<Map>, addr: Term<Int>, value: Term<Int>) -> Term<Map> {
    if addr < 32768 { map::update(mem, addr, value) } else { mem }
}

#[k::function(total, internal)]
pub fn Quotient(a: Term<Int>) -> Term<Int>;

#[k::requires(100 / a > 1)]
#[k::equation]
fn quotient_big(k::term![Quotient(a)]: Term<Int>) -> Term<Int> {
    1
}

#[k::equation(owise)]
fn quotient_other(k::term![Quotient(a)]: Term<Int>) -> Term<Int> {
    0
}

#[k::function(total, internal)]
pub fn DecodeOp(op: Term<Int>) -> Term<Int>;

k::equations! {
    for DecodeOp;
    #[k::requires(r != 6)]
    decode_ld_r_r: k::bits!("01 rrr sss") => r;
    decode_alu: k::bits!("10 aaa bbb") => a;
    decode_xor: k::bits!("11 aaa bbb") => b;
    #[k::equation(owise)]
    decode_other: n => 0;
}
"#;

fn guarded() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, || {
        let mut files = vec![("src/lib.rs".to_owned(), GUARDED.as_bytes().to_vec())];
        let cases = [
            ("irq", "raise ; boundary"),
            ("idle", "boundary"),
            ("low", "write 5 7"),
            ("scale", "scale 1"),
            ("scale-zero", "scale 0"),
            ("fetch", "fetch 1"),
            ("ratio", "ratio 50"),
            ("ratio-zero", "ratio 0"),
            ("peek", "peek 1"),
            ("peek-low", "peek 2"),
            ("peek-missing", "peek 3"),
            ("load", "decode 65"),
            ("load-six", "decode 112"),
            ("alu", "decode 130"),
            ("other", "decode 7"),
        ];
        let mut flow = "[spec]\nkrs = { definition = \"main\" }\n".to_owned();
        for (id, program) in cases {
            flow += &[
                "\n[[program]]\nid = \"",
                id,
                "\"\nfile = \"cases/",
                id,
                ".g\"\n",
            ]
            .concat();
            files.push((
                format!("kink/cases/{id}.g"),
                format!("{program}\n").into_bytes(),
            ));
            if UNENTERED.contains(&id) {
                files.push((
                    format!("corpora/unentered/cases/{id}.g"),
                    format!("{program}\n").into_bytes(),
                ));
            }
        }
        files.push(("kink/FLOW.toml".to_owned(), flow.into_bytes()));
        // A corpus that never fetches, peeks or decodes: no case enters those conditions.
        let mut flow = "[spec]\nkrs = { definition = \"main\" }\n".to_owned();
        for id in UNENTERED {
            flow += &[
                "\n[[program]]\nid = \"",
                id,
                "\"\nfile = \"cases/",
                id,
                ".g\"\n",
            ]
            .concat();
        }
        files.push(("corpora/unentered/FLOW.toml".to_owned(), flow.into_bytes()));
        project_of("krs-cli-kink-guarded", "GUARDED", &files)
    })
}

/// The cases of [`GUARDED`]'s corpus `corpora/unentered`, which no `fetch`, `peek` or `decode`
/// is among.
const UNENTERED: [&str; 6] = ["irq", "idle", "low", "scale", "scale-zero", "ratio"];

/// The guard row of the equation or rule whose `krs.item` is `item`.
fn guard_of<'d>(document: &'d Value, item: &str) -> &'d Value {
    &rule(document, item)["guard"]
}

/// The authored operand of `guard` whose Rust text is `text`.
fn authored<'d>(guard: &'d Value, text: &str) -> &'d Value {
    guard["krs"]["authored"]
        .as_array()
        .unwrap()
        .iter()
        .find(|operand| operand["text"] == text)
        .unwrap_or_else(|| panic!("no authored operand {text:?}: {guard:#}"))
}

/// FB-33's four lines on a story-shaped machine whose corpus never halts:
/// 1. `boundary_wake` and `boundary_halted` are never held and `WriteByte`'s low branch is never
///    refuted;
/// 2. `boundary_dispatch`'s operand `halted` is never true (so `!halted` never decides it), in
///    the row and in the verdicts rendering;
/// 3. equations are reported, and the tests KRS inserted (the division's definedness test, the
///    computed key's lookup guard) are listed apart under the constructs they serve, a
///    `k::bits!` template under `templates`;
/// 4. every guard node is named by its KRS item and Rust text and position, no status reads
///    `covered`, and the rules matched and never fired read `matched`;
///
/// a guard's `held_by`, `refuted_by` and `never` at the KRS level read the author's conjuncts
/// alone: a template that did not match and an inserted test that was `false` refute nothing,
/// and a condition with no authored conjunct (a template's or a lookup guard's alone) has no
/// guard gap; and a decode template no case matches reads `unmatched` at the KRS level, although
/// every decoded program matches its bare K left-hand side.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One assertion per acceptance line of FB-33."
)]
fn coverage_reports_each_guards_outcomes_per_operand() {
    let project = guarded();
    let output = project.kink("coverage", &[]);
    assert_status(&output, 0);
    let document = json(&output);
    assert_eq!(document["krs"]["version"], 6, "{:#}", document["krs"]);
    // krs's front end gives coverage its condition flips: the family ran, and the flip of `irq`
    // across the halted machine's two transitions, which test `halted` first, is unreached on a
    // corpus that never halts, with no mutant run.
    let flips = &document["families"]["flips"];
    assert_eq!(flips["run"], true, "{flips:#}");
    let irq = flips["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|flip| {
            flip["text"] == "irq"
                && strings(&json!(
                    flip["sentences"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|sentence| sentence["rule"].clone())
                        .collect::<Vec<_>>()
                )) == ["rule:crate::boundary_halted", "rule:crate::boundary_wake"]
        })
        .unwrap_or_else(|| panic!("{flips:#}"));
    assert_eq!(irq["status"], "unreached", "{irq:#}");
    assert_eq!(irq["live_runs"], 0, "{irq:#}");
    assert!(
        document["krs"].get("unmatched_guards").is_none(),
        "{:#}",
        document["krs"]
    );
    // 1.
    for item in ["crate::boundary_wake", "crate::boundary_halted"] {
        let row = rule(&document, item);
        assert_eq!(row["status"], "matched", "{item}: {row:#}");
        assert_eq!(row["guard"]["held_by"], json!([]), "{item}: {row:#}");
        assert_eq!(strings(&row["guard"]["krs"]["never"]), ["held"], "{item}");
        assert!(row["krs"]["line"].as_u64().is_some(), "{item}: {row:#}");
    }
    let low = document["families"]["rules"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| {
            row["krs"]["kind"] == "equation" && row["krs"]["source_item"] == "WriteByte, branch 1"
        })
        .collect::<Vec<_>>();
    let [low] = low.as_slice() else {
        panic!("one low branch: {low:#?}");
    };
    assert_eq!(low["guard"]["held_by"], json!(["low"]), "{low:#}");
    assert_eq!(low["guard"]["refuted_by"], json!([]), "{low:#}");
    assert_eq!(strings(&low["guard"]["krs"]["never"]), ["refuted"]);
    // 2.
    let dispatch = guard_of(&document, "crate::boundary_dispatch");
    let halted = authored(dispatch, "halted");
    assert_eq!(halted["true_by"], json!([]), "{dispatch:#}");
    assert_eq!(strings(&halted["never"]), ["true"]);
    assert_eq!(strings(&halted["false_by"]), ["irq", "idle"]);
    // The negation restates its operand: no operand of its own.
    let negation = dispatch["operands"]
        .as_array()
        .unwrap()
        .iter()
        .find(|node| node["kind"] == "negation")
        .unwrap();
    assert!(negation.get("never").is_none(), "{negation:#}");
    assert_eq!(negation["krs"]["text"], "!");
    assert_eq!(
        rule(&document, "crate::boundary_dispatch")["status"],
        "fired"
    );
    // 3.
    let scale = guard_of(&document, "crate::scale");
    assert_eq!(
        scale["krs"]["authored"]
            .as_array()
            .unwrap()
            .iter()
            .map(|operand| operand["text"].as_str().unwrap())
            .collect::<Vec<_>>(),
        ["100 / a > 1", "m[a] > 0"],
        "{scale:#}"
    );
    let anchors = |guard: &Value| {
        guard["krs"]["generated"]
            .as_array()
            .unwrap()
            .iter()
            .map(|test| {
                (
                    test["origin"].as_str().unwrap().to_owned(),
                    test["anchor"]["text"].as_str().unwrap().to_owned(),
                )
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        anchors(scale),
        [
            ("definedness_test".to_owned(), "/".to_owned()),
            ("definedness_test".to_owned(), "[a]".to_owned()),
            ("definedness_test".to_owned(), "[a]".to_owned()),
        ]
    );
    let division = &scale["krs"]["generated"][0];
    assert_eq!(division["false_by"], json!(["scale-zero"]), "{scale:#}");
    assert_eq!(authored(scale, "100 / a > 1")["true_by"], json!(["scale"]));
    // A zero divisor fails the division's test, which refutes nothing the author wrote.
    assert_eq!(scale["refuted_by"], json!(["scale-zero"]), "{scale:#}");
    assert_eq!(scale["krs"]["held_by"], json!(["scale"]), "{scale:#}");
    assert_eq!(scale["krs"]["refuted_by"], json!([]), "{scale:#}");
    assert_eq!(strings(&scale["krs"]["never"]), ["refuted"]);
    // A lookup guard alone is no condition of the author's: no guard gap.
    let fetch = guard_of(&document, "crate::fetch");
    assert_eq!(fetch["krs"]["authored"], json!([]), "{fetch:#}");
    assert!(
        anchors(fetch)
            .iter()
            .any(|(origin, _)| origin == "lookup_guard"),
        "{fetch:#}"
    );
    assert_eq!(fetch["krs"]["held_by"], Value::Null, "{fetch:#}");
    assert_eq!(fetch["krs"]["refuted_by"], Value::Null, "{fetch:#}");
    assert_eq!(fetch["krs"]["never"], json!([]), "{fetch:#}");
    // A lookup guard and an authored conjunct: the missing key is the guard's, not a refutation.
    let peek = guard_of(&document, "crate::peek");
    assert!(
        strings(&peek["refuted_by"]).contains(&"peek-missing"),
        "{peek:#}"
    );
    assert!(
        peek["krs"]["generated"]
            .as_array()
            .unwrap()
            .iter()
            .any(|test| strings(&test["false_by"]).contains(&"peek-missing")),
        "{peek:#}"
    );
    assert_eq!(
        authored(peek, "v > 3")["false_by"],
        json!(["peek-low"]),
        "{peek:#}"
    );
    assert_eq!(peek["krs"]["held_by"], json!(["peek"]), "{peek:#}");
    assert_eq!(peek["krs"]["refuted_by"], json!(["peek-low"]), "{peek:#}");
    assert_eq!(peek["krs"]["never"], json!([]), "{peek:#}");
    let quotient = guard_of(&document, "crate::quotient_big");
    assert_eq!(
        rule(&document, "crate::quotient_big")["krs"]["kind"],
        "equation"
    );
    assert_eq!(
        anchors(quotient),
        [("definedness_test".to_owned(), "/".to_owned())]
    );
    assert_eq!(
        authored(quotient, "100 / a > 1")["true_by"],
        json!(["ratio"])
    );
    let load = guard_of(&document, "crate::decode_ld_r_r");
    let templates = &load["krs"]["templates"];
    assert_eq!(
        templates["conjuncts"].as_array().unwrap().len(),
        3,
        "{load:#}"
    );
    assert_eq!(templates["binders"][0]["text"], "\"01 rrr sss\"");
    assert_eq!(
        templates["matched_by"],
        json!(["load", "load-six"]),
        "{load:#}"
    );
    assert_eq!(templates["not_matched_by"], json!(["other"]), "{load:#}");
    // A template and an authored conjunct: the template's misses are no refutations.
    assert_eq!(
        authored(load, "r != 6")["false_by"],
        json!(["load-six"]),
        "{load:#}"
    );
    assert_eq!(load["refuted_by"], json!(["load-six", "other"]), "{load:#}");
    assert_eq!(load["krs"]["held_by"], json!(["load"]), "{load:#}");
    assert_eq!(load["krs"]["refuted_by"], json!(["load-six"]), "{load:#}");
    assert_eq!(load["krs"]["never"], json!([]), "{load:#}");
    // 4.
    for row in document["families"]["rules"]["items"].as_array().unwrap() {
        if let Some(guard) = row.get("guard").filter(|guard| guard["krs"].is_object()) {
            assert!(row["krs"]["item"].is_string(), "{row:#}");
            for operand in guard["krs"]["authored"].as_array().unwrap() {
                assert!(operand["text"].is_string(), "{row:#}");
                assert!(operand["line"].as_u64().is_some(), "{row:#}");
                assert_eq!(operand["file"], "src/lib.rs", "{row:#}");
            }
        }
    }
    assert_eq!(
        authored(dispatch, "halted")["line"],
        line_of(GUARDED, "#[k::requires(!halted && irq && ime)]")
    );
    assert_eq!(rule(&document, "crate::boundary_wake")["status"], "matched");
    // A template alone is no condition of the author's: no guard gap.
    let alu = rule(&document, "crate::decode_alu");
    assert_eq!(alu["krs"]["status"], "fired", "{alu:#}");
    assert_eq!(
        alu["guard"]["refuted_by"],
        json!(["load", "load-six", "other"]),
        "{alu:#}"
    );
    assert_eq!(alu["guard"]["krs"]["authored"], json!([]), "{alu:#}");
    assert_eq!(alu["guard"]["krs"]["held_by"], Value::Null, "{alu:#}");
    assert_eq!(alu["guard"]["krs"]["refuted_by"], Value::Null, "{alu:#}");
    assert_eq!(alu["guard"]["krs"]["never"], json!([]), "{alu:#}");
    // A template no case matches.
    let xor = rule(&document, "crate::decode_xor");
    assert_eq!(xor["status"], "matched", "{xor:#}");
    assert_eq!(xor["krs"]["status"], "unmatched", "{xor:#}");
    assert_eq!(xor["krs"]["matched_by"], json!([]), "{xor:#}");
    assert_eq!(xor["guard"]["krs"]["authored"], json!([]), "{xor:#}");
    assert_eq!(
        xor["guard"]["krs"]["templates"]["matched_by"],
        json!([]),
        "{xor:#}"
    );
    assert_eq!(
        rule(&document, "crate::decode_ld_r_r")["krs"]["matched_by"],
        json!(["load", "load-six"])
    );
    // Every guard is grouped, also one whose condition has no node (an `else` branch's).
    let guards = document["families"]["rules"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|row| row.get("guard"))
        .collect::<Vec<_>>();
    assert!(
        guards.iter().all(|guard| guard["krs"].is_object()),
        "{guards:#?}"
    );
    // The families name every item by KRS item and Rust text: a rule by its item, a requirement
    // by its item and its authored operand's source text; the tests KRS inserted and the
    // templates are no requirements, and a condition with no authored conjunct states none.
    assert_eq!(
        rule(&document, "crate::boundary_wake")["id"],
        "rule:crate::boundary_wake"
    );
    let ids = requirement_ids(&document);
    for id in [
        "requirement:crate::boundary_wake:held",
        "requirement:crate::boundary_dispatch:halted:true",
        "requirement:crate::boundary_dispatch:halted:false",
        "requirement:crate::scale:100 / a > 1:true",
        "requirement:crate::scale:m[a] > 0:false",
        "requirement:crate::decode_ld_r_r:refuted",
    ] {
        assert!(ids.contains(&id.to_owned()), "{id}: {ids:#?}");
    }
    // A condition's outcome that is an operand's reached truth is one obligation, the root's:
    // `decode_ld_r_r`'s one authored conjunct `r != 6` is its condition, so its truths are the
    // condition's `held` and `refuted`; `scale` holds where its last conjunct `m[a] > 0` is
    // reached true.
    let refuted = requirement_of(&document, "requirement:crate::decode_ld_r_r:refuted");
    assert_eq!(
        (&refuted["text"], &refuted["node_truth"]),
        (&json!("r != 6"), &json!("false")),
        "{refuted:#}"
    );
    for id in [
        "requirement:crate::decode_ld_r_r:r != 6:false",
        "requirement:crate::decode_ld_r_r:r != 6:true",
        "requirement:crate::scale:m[a] > 0:true",
    ] {
        assert!(!ids.contains(&id.to_owned()), "{id}: {ids:#?}");
    }
    let held = requirement_of(&document, "requirement:crate::scale:held");
    assert_eq!(
        (&held["text"], &held["node_truth"], &held["covered_by"]),
        (&json!("m[a] > 0"), &json!("true"), &json!(["scale"])),
        "{held:#}"
    );
    for id in &ids {
        assert!(
            !id.contains("=/=Int") && !id.contains("bitRangeInt"),
            "{id}: {ids:#?}"
        );
        for item in ["crate::fetch:", "crate::decode_alu:", "crate::decode_xor:"] {
            assert!(!id.contains(item), "{id}");
        }
    }
    let requirement = requirement_of(
        &document,
        "requirement:crate::boundary_dispatch:halted:true",
    );
    assert_eq!(requirement["status"], "open", "{requirement:#}");
    assert_eq!(requirement["file"], "src/lib.rs");
    let requirement = requirement_of(&document, "requirement:crate::scale:100 / a > 1:true");
    assert_eq!(
        requirement["covered_by"],
        json!(["scale"]),
        "{requirement:#}"
    );
    // A target per open obligation, named by KRS item and Rust text, at its Rust position.
    let targets = document["targets"].as_array().unwrap();
    assert_eq!(document["summary"]["open"], json!(targets.len()));
    let wake = targets
        .iter()
        .find(|target| target["item"] == "rule:crate::boundary_wake")
        .unwrap_or_else(|| panic!("{targets:#?}"));
    assert!(
        wake["text"]
            .as_str()
            .unwrap()
            .starts_with("a case where crate::boundary_wake is entered and its condition holds"),
        "{wake:#}"
    );
    assert_eq!(wake["file"], "src/lib.rs");
    assert_eq!(
        wake["line"],
        rule(&document, "crate::boundary_wake")["krs"]["line"]
    );
    let halted_true = targets
        .iter()
        .find(|target| target["item"] == "requirement:crate::boundary_dispatch:halted:true")
        .unwrap_or_else(|| panic!("{targets:#?}"));
    assert_eq!(
        halted_true["text"],
        "a case that enters crate::boundary_dispatch with halted true"
    );
    let rules = &document["families"]["rules"];
    assert_eq!(
        rules["obligations"],
        json!(
            rules["counts"]["fired"].as_u64().unwrap()
                + rules["counts"]["matched"].as_u64().unwrap()
                + rules["counts"]["unmatched"].as_u64().unwrap()
        )
    );

    let verdicts = project.kink("coverage", &["--output", "verdicts"]);
    assert_status(&verdicts, 0);
    let verdicts = stdout(&verdicts);
    assert!(verdicts.contains("krs_annotation = 6"), "{verdicts}");
    assert!(
        verdicts.contains("\"rule:crate::boundary_wake\""),
        "{verdicts}"
    );
    assert!(
        verdicts.contains("\"requirement:crate::boundary_dispatch:halted:true\""),
        "{verdicts}"
    );
    // Neither the inserted tests nor a template's conjuncts are requirements, and no case is
    // listed: the rendering moves only when a gap opens or closes.
    assert!(!verdicts.contains("=/=Int 0"), "{verdicts}");
    assert!(!verdicts.contains("bitRangeInt"), "{verdicts}");
    assert!(!verdicts.contains("[[case]]"), "{verdicts}");
    assert!(
        !verdicts.contains("requirement:crate::fetch:"),
        "{verdicts}"
    );

    let text = project.kink("coverage", &["--output", "text"]);
    assert_status(&text, 0);
    let text = stdout(&text);
    assert!(
        text.contains("  requirement:crate::boundary_dispatch:halted:true (src/lib.rs:"),
        "{text}"
    );
}

/// The ids of a coverage document's requirements.
fn requirement_ids(document: &Value) -> Vec<String> {
    document["families"]["requirements"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .map(|item| item["id"].as_str().unwrap().to_owned())
        .collect()
}

/// The requirement of a coverage document whose id is `id`.
fn requirement_of<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["families"]["requirements"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|item| item["id"] == id)
        .unwrap_or_else(|| panic!("no requirement {id}"))
}

/// Which conjuncts of a condition are the author's is a fact of the definition, not of the cases
/// that reached it: over a corpus that never fetches, peeks or decodes, every guard is grouped,
/// the sentences with no authored conjunct (`fetch`'s lookup guard, the `decode_alu` and
/// `decode_xor` templates) have `held_by` and `refuted_by` `null` and state no requirement, and
/// those with one (`peek`'s `v > 3` behind its lookup guard, `decode_ld_r_r`'s `r != 6` behind
/// its template) were never held and never refuted: the nodes come from the definition's
/// skeleton, so their requirements are all open.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One corpus: every guard's grouping and the requirements it states."
)]
fn coverage_groups_the_guards_no_case_entered() {
    let project = guarded();
    let output = project.kink("coverage", &["--corpus", "corpora/unentered"]);
    assert_status(&output, 0);
    let document = json(&output);
    assert!(
        document["krs"].get("unmatched_guards").is_none(),
        "{:#}",
        document["krs"]
    );
    for item in [
        "crate::fetch",
        "crate::decode_alu",
        "crate::decode_xor",
        "crate::peek",
        "crate::decode_ld_r_r",
    ] {
        let guard = guard_of(&document, item);
        // The nodes come from the definition's skeleton of the condition, so a guard no case
        // entered shows them, with no outcome.
        assert!(
            !guard["operands"].as_array().unwrap().is_empty(),
            "{item}: {guard:#}"
        );
        assert_eq!(
            strings(&guard["never"]),
            ["held", "refuted"],
            "{item}: {guard:#}"
        );
        for operand in guard["krs"]["authored"].as_array().unwrap() {
            assert_eq!(operand["true_by"], json!([]), "{item}: {guard:#}");
            assert_eq!(operand["false_by"], json!([]), "{item}: {guard:#}");
        }
    }
    for item in ["crate::fetch", "crate::decode_alu", "crate::decode_xor"] {
        let guard = guard_of(&document, item);
        assert_eq!(guard["krs"]["authored"], json!([]), "{item}: {guard:#}");
    }
    let authored_texts = |item: &str| {
        guard_of(&document, item)["krs"]["authored"]
            .as_array()
            .unwrap()
            .iter()
            .map(|operand| operand["text"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>()
    };
    assert_eq!(authored_texts("crate::peek"), ["v > 3"]);
    assert_eq!(authored_texts("crate::decode_ld_r_r"), ["r != 6"]);
    // So the requirements are a function of the definition: every one of an unentered guard is
    // open, and a condition with no authored conjunct states none.
    let ids = requirement_ids(&document);
    for id in [
        "requirement:crate::peek:held",
        "requirement:crate::peek:refuted",
        "requirement:crate::decode_ld_r_r:held",
        "requirement:crate::decode_ld_r_r:refuted",
    ] {
        assert!(ids.contains(&id.to_owned()), "{id}: {ids:#?}");
        assert_eq!(requirement_of(&document, id)["status"], "open");
    }
    // `peek`'s one authored conjunct `v > 3` is its condition: two obligations, not four.
    assert_eq!(
        ids.iter()
            .filter(|id| id.starts_with("requirement:crate::peek:"))
            .collect::<Vec<_>>(),
        [
            "requirement:crate::peek:held",
            "requirement:crate::peek:refuted"
        ]
    );
    assert!(
        !ids.iter()
            .any(|id| id.starts_with("requirement:crate::fetch:"))
    );
    for item in ["crate::fetch", "crate::decode_alu", "crate::decode_xor"] {
        let guard = guard_of(&document, item);
        assert_eq!(guard["krs"]["held_by"], Value::Null, "{item}: {guard:#}");
        assert_eq!(guard["krs"]["refuted_by"], Value::Null, "{item}: {guard:#}");
        assert_eq!(guard["krs"]["never"], json!([]), "{item}: {guard:#}");
    }
    for item in ["crate::peek", "crate::decode_ld_r_r"] {
        let guard = guard_of(&document, item);
        assert_eq!(guard["krs"]["held_by"], json!([]), "{item}: {guard:#}");
        assert_eq!(guard["krs"]["refuted_by"], json!([]), "{item}: {guard:#}");
        assert_eq!(
            strings(&guard["krs"]["never"]),
            ["held", "refuted"],
            "{item}: {guard:#}"
        );
    }
    let templates = &guard_of(&document, "crate::decode_ld_r_r")["krs"]["templates"];
    assert_eq!(
        templates["binders"][0]["text"], "\"01 rrr sss\"",
        "{templates:#}"
    );
    assert_eq!(templates["matched_by"], json!([]), "{templates:#}");
    assert_eq!(templates["not_matched_by"], json!([]), "{templates:#}");
    assert_eq!(
        guard_of(&document, "crate::fetch")["krs"]["templates"],
        Value::Null
    );
    // No case decodes, so no case matched a template.
    for item in [
        "crate::decode_ld_r_r",
        "crate::decode_alu",
        "crate::decode_xor",
    ] {
        let row = rule(&document, item);
        assert_eq!(row["krs"]["status"], "unmatched", "{item}: {row:#}");
        assert_eq!(row["krs"]["matched_by"], json!([]), "{item}: {row:#}");
    }
    // Every guard is grouped.
    let guards = document["families"]["rules"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|row| row.get("guard"))
        .collect::<Vec<_>>();
    assert!(
        guards.iter().all(|guard| guard["krs"].is_object()),
        "{guards:#?}"
    );
    let reported = guards
        .iter()
        .filter(|guard| !guard["krs"]["held_by"].is_null())
        .count();
    assert_eq!(reported + 3, guards.len(), "{guards:#?}");
}

/// A definition that never ends on its own: `tick(n)` steps to `tick(n + 1)` forever, so a run's
/// end is where a stop puts it.
const TICKER: &str = r#"use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("tick({value})")] Tick { value: Int },
}

#[k::rule]
fn tick(k::term![ExpSyntax::Tick { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Tick(int::add(value, 1))
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}
"#;

/// A corpus of [`TICKER`] whose runs stop at `stop` (a `[stop]` table), with the one case
/// `tick(0)`.
fn ticker_flow(stop: &str) -> Vec<u8> {
    format!(
        "[spec]\nkrs = {{ definition = \"main\" }}\n\n{stop}\n[[program]]\nid = \"t0\"\nfile = \"cases/t0.tick\"\n"
    )
    .into_bytes()
}

fn ticker() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, || {
        let mut files = vec![("src/lib.rs".to_owned(), TICKER.as_bytes().to_vec())];
        for (corpus, stop) in [
            ("kink", "[stop]\nafter = [\"crate::tick\"]\ncount = 3\n"),
            ("corpora/before", "[stop]\nbefore = [\"crate::tick\"]\n"),
            ("corpora/unknown", "[stop]\nafter = [\"crate::nothing\"]\n"),
        ] {
            files.push((format!("{corpus}/FLOW.toml"), ticker_flow(stop)));
            files.push((format!("{corpus}/cases/t0.tick"), b"tick(0)\n".to_vec()));
        }
        project_of("krs-cli-kink-ticker", "TICKER", &files)
    })
}

/// A library crate `lang` of a language that never ends on its own: `step` turns `tick(n)` into
/// `tock(n)`, and the context `tick_value` evaluates a `tick`'s value first, so K writes a heat
/// and a cool rule for that one item.
const CONSOLE_LANG: &str = r#"use k::builtin::{Int, int};
use k::{KItem, KResult, Term};

k::sorts! {
    Op: KItem;
    #[k::bracket("(", ")")]
    Exp;
    Value: Exp + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Op, result = KResult)]
#[rustfmt::skip]
pub enum Step {
    #[k::syntax("tick({value})")] Tick { value: Exp },
    #[k::syntax("tock({value})")] Tock { value: Int },
}

#[k::constructors(sort = Exp, result = KResult)]
#[k::precedence(left (Add))]
pub enum Arith {
    #[k::syntax("{lhs} + {rhs}")]
    Add { lhs: Exp, rhs: Exp },
}

k::rules! {
    for Exp;
    use Arith::*;
    add: Add { lhs, rhs } => int::add(lhs, rhs) where lhs: Int, rhs: Int;
}

k::rules! {
    for Op;
    use Step::*;
    step: Tick { value } => Tock { value } where value: Int;
}

#[k::context(hole = h)]
fn tick_value(k::term![Step::Tick(h)]: Term<Op>) {}
"#;

/// A console over [`CONSOLE_LANG`]: its configuration rule `frame` counts a frame at each `tock`
/// and starts the next `tick`, so a run of `tick(0)` takes `step`, `frame`, the heat rule, `add`
/// and the cool rule in turn, forever.
const CONSOLE: &str = r"use k::builtin::{Int, KSequence};

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub frames: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: lang::Op) -> Self {
        Self { k: k::k![pgm], frames: 0 }
    }
}

k::rules! {
    for Machine;
    frame: { k: [lang::Step::Tock { value }, ..], frames } => { k: [lang::Step::Tick { value: lang::Arith::Add { lhs: value, rhs: 1 } }, ..], frames: frames + 1 };
}
";

/// The console package, which depends on its language crate `lang` (`--dependency
/// lang-core:main`), with a corpus that stops after the console's own `frame` (`kink`) and one
/// that stops at the language crate's items (`corpora/lang`). The language package is
/// `lang-core`, whose `[lib]` section names its library `lang`, so a name that spells a
/// dependency's item by its package name (`lang_core::step`) rather than its library's crate
/// name is told apart.
fn console() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, || {
        let mut files = vec![
            ("src/lib.rs".to_owned(), CONSOLE.as_bytes().to_vec()),
            (
                "lang/src/lib.rs".to_owned(),
                CONSOLE_LANG.as_bytes().to_vec(),
            ),
        ];
        for (corpus, stop) in [
            ("kink", "[stop]\nafter = [\"crate::frame\"]\ncount = 2\n"),
            (
                "corpora/lang",
                "[stop]\nafter = [\"lang::step\", \"lang::tick_value\"]\n",
            ),
        ] {
            files.push((
                format!("{corpus}/FLOW.toml"),
                format!(
                    "[spec]\nkrs = {{ definition = \"main\" }}\n\n{stop}\n[[program]]\nid = \"t0\"\nfile = \"cases/t0.op\"\n"
                )
                .into_bytes(),
            ));
            files.push((format!("{corpus}/cases/t0.op"), b"tick(0)\n".to_vec()));
        }
        let project = project_of("krs-cli-kink-console", "CONSOLE", &files);
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        let package = |name: &str, library: &str, namespace: &str, dependencies: &str| {
            format!(
                "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n{library}\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n"
            )
        };
        project.write(
            "lang/Cargo.toml",
            package("lang-core", "\n[lib]\nname = \"lang\"\n", "LANG", ""),
        );
        project.write(
            "Cargo.toml",
            format!(
                "{}\n[workspace]\n",
                package(
                    "krs-cli-kink-console",
                    "",
                    "CONSOLE",
                    "lang-core = { path = \"lang\" }\n"
                )
            ),
        );
        project
    })
}

/// The story's three edits (`docs-site/story/plus/kink/mutations/plus.toml`), the K patches the
/// introduction's mutation scenes make, each anchored by its Rust item and with the
/// misunderstanding the scenes quote.
const STORY_MUTATIONS: &str =
    include_str!("../../../../docs-site/story/plus/kink/mutations/plus.toml");

/// A package in a fresh directory, shared by the tests that overlap in this process: its
/// manifest path keys the collector's directory, so the tests that share it build it once, and
/// they run `krs` on it one at a time.
struct Project {
    package: &'static str,
    directory: TempDir,
    _target: SharedFixtureTarget,
    target: PathBuf,
    turn: Mutex<()>,
}

impl Project {
    fn new(package: &'static str, namespace: &str, files: &[(&str, &[u8])]) -> Self {
        let target = shared_fixture_target();
        let directory = temp_dir();
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        let project = Self {
            package,
            directory,
            target: target.path().to_path_buf(),
            _target: target,
            turn: Mutex::new(()),
        };
        project.write(
            "Cargo.toml",
            format!(
                "[package]\nname = \"{package}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
            ),
        );
        for (path, contents) in files {
            project.write(path, contents);
        }
        project
    }

    fn shared(slot: &'static Mutex<Weak<Self>>, build: impl FnOnce() -> Self) -> Arc<Self> {
        let mut slot = slot
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(project) = slot.upgrade() {
            return project;
        }
        let project = Arc::new(build());
        *slot = Arc::downgrade(&project);
        project
    }

    fn path(&self) -> &Path {
        self.directory.path()
    }

    fn write(&self, relative: &str, contents: impl AsRef<[u8]>) {
        let path = self.path().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn read(&self, relative: &str) -> String {
        fs::read_to_string(self.path().join(relative)).unwrap()
    }

    /// `krs ARGUMENTS` with this package selected, from the package directory.
    fn krs(&self, arguments: &[&str]) -> Output {
        let _turn = self
            .turn
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut process = krs_command!();
        fixture_build_env(&mut process, &self.target);
        process.current_dir(self.path()).args(arguments).args([
            "--package",
            self.package,
            "--definition",
            "main",
        ]);
        process.output().unwrap()
    }

    /// `krs kink VERB ARGUMENTS`.
    fn kink(&self, verb: &str, arguments: &[&str]) -> Output {
        let mut all = vec!["kink", verb];
        all.extend_from_slice(arguments);
        self.krs(&all)
    }
}

/// The story package with its corpus, the files of `story_files`.
fn story_files() -> Vec<(String, Vec<u8>)> {
    let mut files = vec![
        ("src/lib.rs".to_owned(), STORY.as_bytes().to_vec()),
        ("kink/FLOW.toml".to_owned(), STORY_FLOW.as_bytes().to_vec()),
    ];
    for (id, text) in STORY_CASES {
        files.push((format!("kink/cases/{id}.nat"), text.as_bytes().to_vec()));
    }
    files
}

fn project_of(package: &'static str, namespace: &str, files: &[(String, Vec<u8>)]) -> Project {
    let files = files
        .iter()
        .map(|(path, bytes)| (path.as_str(), bytes.as_slice()))
        .collect::<Vec<_>>();
    Project::new(package, namespace, &files)
}

/// The story package shared by the tests that read it and edit only its corpus.
fn story() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, || project_of("story-plus", "NAT", &story_files()))
}

fn counter() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, || {
        project_of(
            "krs-cli-kink-counter",
            "COUNTER",
            &[
                ("src/lib.rs".to_owned(), COUNTER.as_bytes().to_vec()),
                (
                    "kink/FLOW.toml".to_owned(),
                    b"[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\nid = \"c3\"\nfile = \"cases/c3.cnt\"\n"
                        .to_vec(),
                ),
                ("kink/cases/c3.cnt".to_owned(), b"count(3)\n".to_vec()),
            ],
        )
    })
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn json(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
            stdout(output),
            stderr(output)
        )
    })
}

#[track_caller]
fn assert_status(output: &Output, code: i32) {
    assert_eq!(
        output.status.code(),
        Some(code),
        "stdout:\n{}\nstderr:\n{}",
        stdout(output),
        stderr(output)
    );
}

/// The 1-based line of the first line of `source` that contains `text`.
fn line_of(source: &str, text: &str) -> u64 {
    let index = source
        .lines()
        .position(|line| line.contains(text))
        .unwrap_or_else(|| panic!("{text:?} is not in the source"));
    u64::try_from(index).unwrap() + 1
}

/// The rule of a results document whose `krs.item` is `item`.
fn rule<'d>(document: &'d Value, item: &str) -> &'d Value {
    document["families"]["rules"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .find(|rule| rule["krs"]["item"] == item)
        .unwrap_or_else(|| {
            panic!(
                "no rule names {item}: {:#}",
                document["families"]["rules"]["items"]
            )
        })
}

fn strings(value: &Value) -> Vec<&str> {
    value
        .as_array()
        .unwrap_or_else(|| panic!("{value} is no array"))
        .iter()
        .map(|item| item.as_str().unwrap())
        .collect()
}

/// `coverage` reports each case's class and the rules it fires, each rule named by its Rust item
/// and position: the story's own coverage table.
#[test]
fn coverage_names_each_rule_by_its_rust_item_and_position() {
    let project = story();
    let output = project.kink("coverage", &[]);
    assert_status(&output, 0);
    let document = json(&output);
    assert_eq!(document["schema"], "kink-flow-coverage");
    assert!(
        matches!(
            document["definition"]["status"].as_str(),
            Some("written" | "unchanged")
        ),
        "{:#}",
        document["definition"]
    );
    assert_eq!(document["definition"]["path"], "kink/definition.k");
    for (item, function) in [
        ("crate::plus_zero", "fn plus_zero("),
        ("crate::plus_succ", "fn plus_succ("),
    ] {
        let krs = &rule(&document, item)["krs"];
        // The `// KRS` line names the item as the source writes it.
        assert_eq!(
            krs["source_item"],
            item.strip_prefix("crate::").unwrap(),
            "{krs:#}"
        );
        assert_eq!(krs["file"], "src/lib.rs", "{krs:#}");
        assert_eq!(krs["package"], "story-plus", "{krs:#}");
        assert_eq!(krs["kind"], "equation", "{krs:#}");
        assert_eq!(krs["claim_helper"], false, "{krs:#}");
        assert_eq!(krs["line"], line_of(STORY, function), "{krs:#}");
        assert!(krs["column"].as_u64().is_some(), "{krs:#}");
    }
    assert_eq!(
        strings(&rule(&document, "crate::plus_zero")["fired_by"]),
        ["t1", "t2", "t3", "t4"]
    );
    assert_eq!(
        strings(&rule(&document, "crate::plus_succ")["fired_by"]),
        ["t3", "t4"]
    );
    for program in document["programs"].as_array().unwrap() {
        assert_eq!(program["class"], "comparable", "{program:#}");
    }
    assert_eq!(
        document["krs"],
        serde_json::json!({"version": 6}),
        "every rule is named, by version 6 of the annotation"
    );
    // The story's two equations fire and have no condition, and they inspect both constructors
    // of `Nat` (`plus_succ` also builds `s`): nothing is open.
    assert_eq!(
        rule(&document, "crate::plus_zero")["id"],
        "rule:crate::plus_zero"
    );
    assert_eq!(
        document["summary"]["per_family"],
        json!({"rules": {"obligations": 2, "covered": 2, "argued": 0, "open": 0},
               "requirements": {"obligations": 0, "covered": 0, "argued": 0, "open": 0},
               "syntax": {"obligations": 2, "covered": 2, "argued": 0, "open": 0}})
    );
    assert_eq!(document["targets"], json!([]));
    // The story's equations have no guard and no `k::bits!` argument, so krs derives no condition
    // flip, and the flips family says why.
    assert_eq!(
        document["families"]["flips"],
        json!({"tier": 2, "run": false, "obligations": null, "items": [],
               "reason": "no sentence of the definition has a guard or a k::bits! argument, so \
                          no sentences are kept apart by a condition a flip could negate"})
    );

    // The verdicts rendering, as the docs-site's recorded `story-kink-coverage`: nothing open.
    let output = project.kink("coverage", &["--output", "verdicts"]);
    assert_status(&output, 0);
    let verdicts = stdout(&output);
    // Its header says which annotation version spells the names.
    assert!(
        verdicts.lines().any(|line| line == "krs_annotation = 6"),
        "{verdicts}"
    );
    assert!(
        verdicts.ends_with(
            "\n[rules]\nopen = []\n\n[requirements]\nopen = []\n\n[syntax]\nopen = []\n\n[flips]\nrun = false\n"
        ),
        "{verdicts}"
    );

    coverage_and_stops_name_rules_as_the_document_does(&project, &document);
}

/// `krs run --coverage` names each rule of the story's results `document` by the string the
/// document names it by, and a stop reads that string as the same item.
fn coverage_and_stops_name_rules_as_the_document_does(project: &Project, document: &Value) {
    let output = project.krs(&["run", "kink/cases/t3.nat", "--coverage", "--output", "json"]);
    assert_status(&output, 0);
    let run = json(&output);
    for label in ["nat--plus_zero", "nat--plus_succ"] {
        let covered = run["run"]["coverage"]["rules"]
            .as_array()
            .unwrap()
            .iter()
            .find(|rule| rule["label"] == label)
            .unwrap_or_else(|| panic!("{label} is not covered: {run:#}"));
        let named = document["families"]["rules"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|rule| rule["label"] == label)
            .unwrap_or_else(|| panic!("{label} is not named: {document:#}"));
        assert_eq!(
            covered["item"], named["krs"]["item"],
            "{covered:#}\n{named:#}"
        );
    }
    // The story's rules are equations, which take no step, so the stop names the item it read.
    let output = project.krs(&[
        "run",
        "kink/cases/t3.nat",
        "--stop-before",
        "crate::plus_succ",
    ]);
    assert!(
        stderr(&output).contains("KRS item `crate::plus_succ`: each of its sentences is"),
        "{}",
        stderr(&output)
    );
}

/// `run` kills the story's three edits, written as K patches anchored by the Rust items, and a
/// full run finds exactly the killers the story's pages show (the docs-site takes them from its
/// recorded full run, story-kink-run).
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One story: its three patches, their kills and their pinned Rust locations."
)]
fn run_kills_the_story_edits() {
    let project = story();
    project.write("kink/mutations/plus.toml", STORY_MUTATIONS);
    // A lock of this test's own: the default `kink/verdicts.lock` of the shared project would be
    // read by every other test that runs its corpus.
    let lock = ["--lock", "target/locks/story-edits.lock"];
    let ran = project.kink("run", &[&["--full"][..], &lock[..]].concat());
    assert_status(&ran, 0);
    let document = json(&ran);
    let rows = document["mutations"].as_array().unwrap();
    let verdicts = rows
        .iter()
        .map(|row| {
            (
                row["id"].as_str().unwrap(),
                row["status"].as_str().unwrap(),
                strings(&row["killed_by"]),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        verdicts,
        [
            ("plus/a", "killed", vec!["t2", "t3", "t4"]),
            ("plus/b", "killed", vec!["t3", "t4"]),
            ("plus/c", "killed", vec!["t4"]),
        ],
        "{document:#}"
    );
    // A kill's evidence is krs-exec's comparison of the two ends, in the format of every KRS
    // difference: the cell by Rust field path and both values as their canonical documents.
    // plus/a's killer t2, `plus(zero, s(zero))`, ends in `s(zero)` and its mutant in `zero`.
    let killer = rows[0]["executed"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["program"] == "t2")
        .unwrap_or_else(|| panic!("{:#}", rows[0]));
    let difference = &killer["difference"];
    let shown = |document: Value| {
        serde_json::json!({
            "rendering": "document",
            "document": document,
            "truncated": false,
            "offset": 0,
        })
    };
    assert_eq!(difference["format"], "krs-difference/3", "{difference:#}");
    assert_eq!(difference["at"], "cell", "{difference:#}");
    assert_eq!(difference["cell"], "k", "{difference:#}");
    assert_eq!(difference["path"], "k[0]", "{difference:#}");
    assert_eq!(difference["outside"], "mutant", "{difference:#}");
    assert_eq!(
        difference["compared"],
        serde_json::json!(["k"]),
        "{difference:#}"
    );
    for (side, name, value) in [
        (
            "left",
            "baseline",
            serde_json::json!({"Succ": {"n": "Zero"}}),
        ),
        ("right", "mutant", serde_json::json!({"Zero": []})),
    ] {
        let side = &difference[side];
        assert_eq!(side["name"], name, "{difference:#}");
        // kink compares ends by configuration alone: the evidence states no class.
        assert_eq!(side.get("class"), None, "{difference:#}");
        assert_eq!(side["value"], shown(value), "{difference:#}");
    }
    // `report` prints the stored run document byte for byte as `run` printed it, named by the
    // emission the run judged and with the run's `definition` object, and builds nothing.
    let timings = project.path().join("report-timings.json");
    let output = project.kink("report", &["--timings", timings.to_str().unwrap()]);
    assert_status(&output, 0);
    assert_eq!(stdout(&output), stdout(&ran));
    assert_eq!(json(&output), document);
    let built = |timings: &Path| {
        let timings: Value = serde_json::from_str(&fs::read_to_string(timings).unwrap()).unwrap();
        let ids = timings["spans"]
            .as_array()
            .unwrap()
            .iter()
            .map(|span| span["id"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        assert!(ids.iter().any(|id| id == "kink.report"), "{ids:?}");
        ids.into_iter()
            .filter(|id| {
                [
                    "collector.build",
                    "collector.run",
                    "semantic.",
                    "spec_stage.",
                    "protocol.",
                    "definition.",
                    "emit_k.",
                    "kink.definition",
                ]
                .iter()
                .any(|built| id.starts_with(built))
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(built(&timings), Vec::<String>::new());
    // `report --output verdicts` prints what `run --output verdicts` printed.
    let rendered = project.kink(
        "run",
        &[&["--full", "--output", "verdicts"][..], &lock[..]].concat(),
    );
    assert_status(&rendered, 0);
    assert!(
        stdout(&rendered).contains("killer = \"t2\"\nkilled_by = [\"t2\", \"t3\", \"t4\"]\n"),
        "{}",
        stdout(&rendered)
    );
    let output = project.kink(
        "report",
        &[
            "--output",
            "verdicts",
            "--timings",
            timings.to_str().unwrap(),
        ],
    );
    assert_status(&output, 0);
    assert_eq!(stdout(&output), stdout(&rendered));
    assert_eq!(built(&timings), Vec::<String>::new());
    // A missing or unreadable stored report: the reason on stderr, nothing rendered.
    let empty = project.path().join("target/empty-kink-cache");
    fs::create_dir_all(&empty).unwrap();
    let cache = empty.to_str().unwrap();
    let output = project.kink("report", &["--cache", cache, "--output", "verdicts"]);
    assert_status(&output, 2);
    assert_eq!(stdout(&output), "");
    assert!(
        stderr(&output).contains("missing run report") && stderr(&output).contains("no run report"),
        "{}",
        stderr(&output)
    );
    // Under `--output json` the reason is the refusal document, as every kink-flow refusal is.
    let output = project.kink("report", &["--cache", cache]);
    assert_status(&output, 2);
    assert_eq!(json(&output)["outcome"], "missing");
    fs::write(empty.join("report.json"), "{").unwrap();
    let output = project.kink("report", &["--cache", cache, "--output", "verdicts"]);
    assert_status(&output, 2);
    assert_eq!(stdout(&output), "");
    assert!(
        stderr(&output).contains("unreadable run report") && stderr(&output).contains("not JSON"),
        "{}",
        stderr(&output)
    );
    // `check` resolves the layout's mutations, runs nothing, and names each edited rule by its
    // item (a run row lists its edited rules only for a mutation that is not killed).
    let output = project.kink("check", &[]);
    assert_status(&output, 0);
    let check = json(&output);
    assert_eq!(check["schema"], "kink-flow-check");
    let named = check["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            let rules = row["rules"].as_array().unwrap();
            assert_eq!(rules.len(), 1, "{row:#}");
            (
                row["id"].as_str().unwrap(),
                rules[0]["krs"]["item"].as_str().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        named,
        [
            ("plus/a", "crate::plus_zero"),
            ("plus/b", "crate::plus_succ"),
            ("plus/c", "crate::plus_succ")
        ],
        "{check:#}"
    );
    // The story's edits are each the emission of a Rust edit KRS admits: no finding, and each
    // edit named by the Rust bytes it changes.
    for row in check["mutations"].as_array().unwrap() {
        assert_eq!(row["outcome"], "ok", "{row:#}");
        assert_eq!(row["refusals"], serde_json::json!([]), "{row:#}");
        assert_eq!(row["warnings"], serde_json::json!([]), "{row:#}");
    }
    // The Rust each patch stands for is the whole construct its K edit replaces: the `n` that
    // plus_zero returns, the `NatSyntax::Succ(..)` call plus/b unwraps, and the `Plus(m, n)` call
    // plus/c replaces by `n`, each in the body of its function, the line after its signature.
    for (row, (label, item, function, text)) in check["mutations"].as_array().unwrap().iter().zip([
        ("nat--plus_zero", "crate::plus_zero", "fn plus_zero(", "n"),
        (
            "nat--plus_succ",
            "crate::plus_succ",
            "fn plus_succ(",
            "NatSyntax::Succ(Plus(m, n))",
        ),
        (
            "nat--plus_succ",
            "crate::plus_succ",
            "fn plus_succ(",
            "Plus(m, n)",
        ),
    ]) {
        let edits = row["krs"]["edits"].as_array().unwrap();
        assert_eq!(edits.len(), 1, "{row:#}");
        let edit = &edits[0];
        assert_eq!(edit["label"], label, "{edit:#}");
        assert_eq!(edit["item"], item, "{edit:#}");
        assert_eq!(edit["judged"], "authored", "{edit:#}");
        let rust = edit["rust"].as_array().unwrap();
        assert_eq!(rust.len(), 1, "{edit:#}");
        let line = line_of(STORY, function) + 1;
        let column = STORY
            .lines()
            .nth(usize::try_from(line).unwrap() - 1)
            .unwrap()
            .find(text)
            .unwrap()
            + 1;
        assert_eq!(rust[0]["file"], "src/lib.rs", "{edit:#}");
        assert_eq!(rust[0]["text"], text, "{edit:#}");
        assert_eq!(rust[0]["line"].as_u64(), Some(line), "{edit:#}");
        assert_eq!(rust[0]["end_line"].as_u64(), Some(line), "{edit:#}");
        assert_eq!(
            rust[0]["column"].as_u64(),
            Some(u64::try_from(column).unwrap()),
            "{edit:#}"
        );
        assert_eq!(
            rust[0]["end_column"].as_u64(),
            Some(u64::try_from(column + text.len()).unwrap()),
            "{edit:#}"
        );
    }
}

/// A definition with cells kink's slot leaves out: an unobservable cell, and an unobservable
/// cell inside a group beside an observable one. `run(n)` steps to `done(n + 1)` by the rule
/// `finish`.
const LEFT_OUT: &str = r#"use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("run({value})")] Run { value: Int },
    #[k::syntax("done({value})")] Done { value: Int },
}

#[k::rule]
fn finish(k::term![Cmd::Run { value }]: Term<Exp>) -> Term<Exp> {
    Cmd::Done(int::add(value, 1))
}

#[k::cell]
pub struct Regs {
    #[k::cell]
    pub a: Int,
    #[k::cell(unobservable)]
    pub w: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell(nested)]
    pub regs: Regs,
    #[k::cell(unobservable)]
    pub scratch: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self {
            k: k::k![pgm],
            regs: Regs { a: 0, w: 0 },
            scratch: 0,
        }
    }
}
"#;

/// A kill's evidence compares the cells kink's slot compared and no other: by default every cell
/// but the unobservable ones (`scratch`, and `regs.w` inside the group `regs`), and under
/// `[result] cells = ["k"]` only `k` (the group `regs` is then left out whole). Each end is read
/// with the cells left out not stated, so the evidence is the KRS comparison's, with no note.
#[test]
fn a_kills_evidence_compares_the_cells_the_slot_compares() {
    let mut files = vec![("src/lib.rs".to_owned(), LEFT_OUT.as_bytes().to_vec())];
    for (corpus, result) in [
        ("kink", ""),
        ("corpora/narrow", "[result]\ncells = [\"k\"]\n\n"),
    ] {
        files.push((
            format!("{corpus}/FLOW.toml"),
            format!(
                "[spec]\nkrs = {{ definition = \"main\" }}\n\n{result}[[program]]\nid = \"t1\"\nfile = \"cases/t1.exp\"\n"
            )
            .into_bytes(),
        ));
        files.push((format!("{corpus}/cases/t1.exp"), b"run(1)\n".to_vec()));
        files.push((
            format!("{corpus}/mutations/finish.toml"),
            b"[[mutation]]\nid = \"twice\"\nmisunderstanding = \"adds two\"\n\n  [[mutation.edit]]\n  rule = \"finish\"\n  find = \"+Int 1\"\n  replace = \"+Int 2\"\n"
                .to_vec(),
        ));
    }
    let project = project_of("krs-cli-kink-left-out", "LEFTOUT", &files);
    for (corpus, compared, not_compared) in [
        ("kink", vec!["k", "regs.a"], vec!["regs.w", "scratch"]),
        (
            "corpora/narrow",
            vec!["k"],
            vec!["regs.a", "regs.w", "scratch"],
        ),
    ] {
        let output = project.kink("run", &["--corpus", corpus]);
        let run = json(&output);
        let row = &run["mutations"][0];
        assert_eq!(row["status"], "killed", "{run:#}");
        let difference = &row["executed"][0]["difference"];
        assert_eq!(difference["format"], "krs-difference/3", "{difference:#}");
        assert_eq!(difference.get("note"), None, "{difference:#}");
        assert_eq!(difference["path"], "k[0].Done.value", "{difference:#}");
        assert_eq!(
            difference["compared"],
            serde_json::json!(compared),
            "{difference:#}"
        );
        assert_eq!(
            difference["not_compared"],
            serde_json::json!(not_compared),
            "{difference:#}"
        );
        assert_eq!(
            difference["also_differ"],
            serde_json::json!([]),
            "{difference:#}"
        );
        assert_eq!(difference["left"]["value"]["document"], 2, "{difference:#}");
        assert_eq!(
            difference["right"]["value"]["document"], 3,
            "{difference:#}"
        );
        // The kill's slot sides, read from the run, are unchanged by the format.
        assert_eq!(
            row["executed"][0]["slots"]["cells"]["sides"]["baseline"]["final_configurations"], 1,
            "{row:#}"
        );
    }
}

/// `[result] cells` names a cell by its Rust path, as every krs surface does, or by its K name
/// where no cell has that name as its path: kink compares the cells it reads as, and every
/// document's `result` gains them by path (`result.krs`) with the reading of each entry. A name
/// that is neither is refused at stage `result` with each path and its K cell; an unobservable
/// cell named by path is refused by kink-flow, by K name, with the path told. A run with
/// `--progress` reports on stderr and prints the same document on stdout.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One corpus package states every reading of `[result] cells` side by side."
)]
fn result_cells_are_named_by_rust_path() {
    let mut files = vec![("src/lib.rs".to_owned(), LEFT_OUT.as_bytes().to_vec())];
    for (corpus, cells) in [
        ("kink", r#"["k", "regs.a"]"#),
        ("corpora/k-name", r#"["a"]"#),
        ("corpora/unknown", r#"["regs.b"]"#),
        ("corpora/hidden", r#"["k", "regs.w"]"#),
        ("corpora/repeated", r#"["regs.a", "a"]"#),
    ] {
        files.push((
            format!("{corpus}/FLOW.toml"),
            format!(
                "[spec]\nkrs = {{ definition = \"main\" }}\n\n[result]\ncells = {cells}\n\n[[program]]\nid = \"t1\"\nfile = \"cases/t1.exp\"\n"
            )
            .into_bytes(),
        ));
        files.push((format!("{corpus}/cases/t1.exp"), b"run(1)\n".to_vec()));
        files.push((
            format!("{corpus}/mutations/finish.toml"),
            b"[[mutation]]\nid = \"twice\"\nmisunderstanding = \"adds two\"\n\n  [[mutation.edit]]\n  rule = \"finish\"\n  find = \"+Int 1\"\n  replace = \"+Int 2\"\n"
                .to_vec(),
        ));
    }
    let project = project_of("krs-cli-kink-result-paths", "RESULTPATHS", &files);

    let output = project.kink("run", &["--full", "--progress"]);
    assert_status(&output, 0);
    let run = json(&output);
    assert_eq!(run["mutations"][0]["status"], "killed", "{run:#}");
    assert_eq!(
        run["result"],
        serde_json::json!({
            "slots": ["exit-stop", "cells"],
            "compared": ["k", "a"],
            "not_compared": ["w", "scratch"],
            "unobservable": ["w", "scratch"],
            "krs": {
                "compared": ["k", "regs.a"],
                "not_compared": ["regs.w", "scratch"],
                "unobservable": ["regs.w", "scratch"],
                "cells": {"k": "k", "regs.a": "a"},
            },
        }),
        "{run:#}"
    );
    let difference = &run["mutations"][0]["executed"][0]["difference"];
    assert_eq!(
        difference["compared"],
        serde_json::json!(["k", "regs.a"]),
        "{difference:#}"
    );
    // Each phase of a cold run is announced as it starts or as its row is decided, in order.
    let progress = stderr(&output);
    let phases = [
        "krs kink: run: building the package and emitting its K\n",
        "krs kink: run: binding the corpus to the emitted K\n",
        "krs kink: run: checking the list's 1 mutation against the lowering\n",
        "krs kink: run: 1 mutation on 1 program, after the baseline results\n",
        "krs kink: run: admitting the specification (its load, compile and checks)\n",
        "krs kink: run: preparing the baseline runner\n",
        "krs kink: run: baseline of program 1 of 1, `t1`: comparable\n",
        "krs kink: run: resolving the list's 1 mutation\n",
        "krs kink: run: mutation 1 of 1, `finish/twice`: killed\n",
    ];
    let mut rest = progress.as_str();
    for phase in phases {
        let at = rest
            .find(phase)
            .unwrap_or_else(|| panic!("no {phase:?} in order in {progress}"));
        rest = &rest[at + phase.len()..];
    }
    // Without `--progress` (stderr is no terminal here) the run reports nothing on stderr.
    let quiet = project.kink("run", &["--full"]);
    assert_status(&quiet, 0);
    assert!(
        !stderr(&quiet).contains("krs kink: run:"),
        "{}",
        stderr(&quiet)
    );

    let output = project.kink("check", &["--corpus", "corpora/k-name"]);
    assert_status(&output, 0);
    let check = json(&output);
    assert_eq!(
        check["result"]["compared"],
        serde_json::json!(["a"]),
        "{check:#}"
    );
    assert_eq!(
        check["result"]["krs"]["compared"],
        serde_json::json!(["regs.a"]),
        "{check:#}"
    );
    assert_eq!(
        check["result"]["krs"]["cells"],
        serde_json::json!({"a": "a"}),
        "{check:#}"
    );

    let output = project.kink("check", &["--corpus", "corpora/unknown"]);
    assert_status(&output, 2);
    let refused = json(&output);
    assert_eq!(refused["spec"]["stage"], "result", "{refused:#}");
    assert_eq!(
        refused["spec"]["reason"], "result-cell-unknown",
        "{refused:#}"
    );
    assert_eq!(
        refused["spec"]["detail"],
        "[result] cells names `regs.b`, which is neither the Rust path nor the K name of a cell \
         of the configuration; name a cell by its Rust path (its K cell in brackets): k (<k>), \
         regs (<regs>), regs.a (<a>), regs.w (<w>), scratch (<scratch>)",
        "{refused:#}"
    );

    // Two spellings of one cell name it twice: the cell is known, the entry repeats it.
    let output = project.kink("check", &["--corpus", "corpora/repeated"]);
    assert_status(&output, 2);
    let refused = json(&output);
    assert_eq!(refused["spec"]["stage"], "result", "{refused:#}");
    assert_eq!(
        refused["spec"]["reason"], "result-cell-repeated",
        "{refused:#}"
    );
    assert_eq!(
        refused["spec"]["detail"],
        "[result] cells names the cell `regs.a` (<a>) twice, as `regs.a` and as `a`; name it once",
        "{refused:#}"
    );

    let output = project.kink("check", &["--corpus", "corpora/hidden"]);
    assert_status(&output, 2);
    let refused = json(&output);
    assert_eq!(refused["spec"]["stage"], "result", "{refused:#}");
    assert_eq!(
        refused["spec"]["reason"], "result-cell-unobservable",
        "{refused:#}"
    );
    let detail = refused["spec"]["detail"].as_str().unwrap_or_default();
    assert!(
        detail
            .starts_with("[result] cells names <w>, which the specification declares unobservable")
            && detail.ends_with(" (as [result] cells writes them: `regs.w` is <w>)"),
        "{refused:#}"
    );
}

/// A kill's evidence names cells, constructors and fields by the Definition IR's Rust names, and
/// a field's name never reaches the emitted K. Renaming the field of `Cmd::Done`, the ends'
/// constructor, under the same syntax leaves the K, and so the execution digest, unchanged, yet
/// the evidence names the new field: the renderer's identity keeps the stored kill (tier 1 is on
/// in both profiles) from serving the old name. An edit that only moves text leaves
/// both the K and the identity unchanged, so the stored kill serves it.
#[test]
fn a_kills_evidence_follows_a_renamed_field_that_the_k_does_not_carry() {
    let corpus = |files: &mut Vec<(String, Vec<u8>)>| {
        files.push((
            "kink/FLOW.toml".to_owned(),
            b"[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\nid = \"t1\"\nfile = \"cases/t1.exp\"\n"
                .to_vec(),
        ));
        files.push(("kink/cases/t1.exp".to_owned(), b"run(1)\n".to_vec()));
        files.push((
            "kink/mutations/finish.toml".to_owned(),
            b"[[mutation]]\nid = \"twice\"\nmisunderstanding = \"adds two\"\n\n  [[mutation.edit]]\n  rule = \"finish\"\n  find = \"+Int 1\"\n  replace = \"+Int 2\"\n"
                .to_vec(),
        ));
    };
    let mut files = vec![("src/lib.rs".to_owned(), LEFT_OUT.as_bytes().to_vec())];
    corpus(&mut files);
    let project = project_of("krs-cli-kink-renamed", "RENAMED", &files);
    let run = |project: &Project| {
        let output = project.kink("run", &[]);
        let run = json(&output);
        let row = run["mutations"][0].clone();
        assert_eq!(row["status"], "killed", "{run:#}");
        let difference = row["executed"][0]["difference"].clone();
        assert_eq!(difference["format"], "krs-difference/3", "{difference:#}");
        (row["killer_source"].clone(), difference["path"].clone())
    };
    let (_, path) = run(&project);
    assert_eq!(path, "k[0].Done.value");
    // Only moved text: the K and the Definition IR up to positions are unchanged.
    let moved = format!("// moved\n\n{LEFT_OUT}");
    project.write("src/lib.rs", &moved);
    let (source, path) = run(&project);
    assert_eq!(path, "k[0].Done.value");
    assert_eq!(source, "outcome-cache");
    let renamed = LEFT_OUT.replace(
        "#[k::syntax(\"done({value})\")] Done { value: Int }",
        "#[k::syntax(\"done({total})\")] Done { total: Int }",
    );
    assert_ne!(renamed, LEFT_OUT);
    project.write("src/lib.rs", &renamed);
    let (source, path) = run(&project);
    assert_eq!(path, "k[0].Done.total");
    assert_ne!(source, "outcome-cache");
}

/// After an edit of the specification, the command builds the edited package once and runs
/// every patch whose anchored text the edit left unchanged, with no build of its own; a patch
/// whose anchored text changed is reported stale, naming the KRS item and the Rust position of
/// the rule its anchor names, and runs nothing.
#[test]
fn an_edit_of_the_specification_leaves_patches_running_or_stale() {
    // plus_succ is restated: `s(m) + n` is `m + s(n)`. The K it emits no longer holds the text
    // plus/b and plus/c replace; plus/a's anchor, plus_zero, is unchanged.
    let edited = STORY.replace("NatSyntax::Succ(Plus(m, n))", "Plus(m, NatSyntax::Succ(n))");
    assert_ne!(edited, STORY);
    let mut files = story_files();
    files[0].1 = edited.as_bytes().to_vec();
    files.push((
        "kink/mutations/plus.toml".to_owned(),
        STORY_MUTATIONS.as_bytes().to_vec(),
    ));
    let project = project_of("story-plus-respec", "NAT", &files);
    let timings = project.path().join("timings.json");
    let output = project.kink("run", &["--full", "--timings", timings.to_str().unwrap()]);
    // A mutation that does not resolve makes the run fail, after every other mutation ran.
    assert_status(&output, 2);
    let document = json(&output);
    assert_eq!(document["definition"]["status"], "written", "{document:#}");
    let rows = document["mutations"].as_array().unwrap();
    let statuses = rows
        .iter()
        .map(|row| (row["id"].as_str().unwrap(), row["status"].as_str().unwrap()))
        .collect::<Vec<_>>();
    assert_eq!(
        statuses,
        [
            ("plus/a", "killed"),
            ("plus/b", "invalid-mutation"),
            ("plus/c", "invalid-mutation"),
        ],
        "{document:#}"
    );
    for row in &rows[1..] {
        assert_eq!(row["reason"], "find-not-found", "{row:#}");
        assert_eq!(row["edit"], 0, "{row:#}");
        let anchor = &row["anchor"];
        assert_eq!(anchor["label"], "nat--plus_succ", "{row:#}");
        assert_eq!(anchor["krs"]["item"], "crate::plus_succ", "{row:#}");
        assert_eq!(anchor["krs"]["file"], "src/lib.rs", "{row:#}");
        assert_eq!(
            anchor["krs"]["line"],
            line_of(&edited, "fn plus_succ("),
            "{row:#}"
        );
    }
    // The command's one krs build is the edited package's own; the patches run on its K.
    let timings: Value = serde_json::from_str(&fs::read_to_string(&timings).unwrap()).unwrap();
    let runs = timings["spans"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|span| span["id"] == "collector.run")
        .count();
    assert_eq!(runs, 1, "{timings:#}");

    // `check` refuses the stale patches with the same rule, and resolves the other.
    let output = project.kink("check", &[]);
    assert_status(&output, 2);
    let check = json(&output);
    let outcomes = check["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row["outcome"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(outcomes, ["ok", "refused", "refused"], "{check:#}");
    for row in &check["mutations"].as_array().unwrap()[1..] {
        let refusal = &row["refusals"][0];
        assert_eq!(refusal["reason"], "find-not-found", "{row:#}");
        assert_eq!(
            refusal["rule"]["krs"]["item"], "crate::plus_succ",
            "{row:#}"
        );
        assert_eq!(
            refusal["rule"]["krs"]["line"],
            line_of(&edited, "fn plus_succ("),
            "{row:#}"
        );
    }
}

/// `query` and `fuzz` run through the front end and print kink-flow's documents, with the
/// rules they name named by their Rust items.
#[test]
fn query_and_fuzz_name_rules_by_their_items() {
    let project = counter();
    project.write(
        "kink/PATTERNS.toml",
        "[[pattern]]\nid = \"done\"\npattern = \"<k> done </k>\"\nprograms = [\"c3\"]\n",
    );
    let output = project.kink("query", &[]);
    assert_status(&output, 0);
    let document = json(&output);
    assert_eq!(document["schema"], "kink-flow-query", "{document:#}");
    let row = &document["rows"][0];
    assert_eq!(row["answer"], "hit", "{document:#}");
    let steps = row["witness"]["krs_rules"]
        .as_array()
        .unwrap_or_else(|| panic!("the witness names its steps: {row:#}"))
        .iter()
        .map(|step| step["item"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        steps,
        ["crate::step", "crate::step", "crate::step", "crate::stop"],
        "{row:#}"
    );
    // `--patterns PATH` names another list than the layout's PATTERNS.toml.
    project.write(
        "kink/other-patterns.toml",
        "[[pattern]]\nid = \"elsewhere\"\npattern = \"<k> done </k>\"\nprograms = [\"c3\"]\n",
    );
    let output = project.kink("query", &["--patterns", "kink/other-patterns.toml"]);
    assert_status(&output, 0);
    let document = json(&output);
    let rows = document["rows"].as_array().unwrap();
    assert_eq!(rows.len(), 1, "{document:#}");
    assert_eq!(rows[0]["pattern"], "elsewhere", "{document:#}");

    project.write(
        "kink/TEMPLATES.toml",
        "[[template]]\nid = \"count\"\nprogram = \"c3\"\n\n  [[template.hole]]\n  name = \"N\"\n  \
         sort = \"Int\"\n  find = \"3\"\n  literal = \"3\"\n  range = { min = 0, max = 4 }\n",
    );
    let output = project.kink(
        "fuzz",
        &["--template", "count", "--matched", "stop", "--cases", "4"],
    );
    let document = json(&output);
    assert_eq!(document["schema"], "kink-flow-fuzz", "{document:#}");
    assert_eq!(
        document["job"]["rule"]["krs"]["item"], "crate::stop",
        "the rule job's target is named by its item: {document:#}"
    );
    assert_status(&output, 3);
    // `--templates PATH` names another list than the layout's TEMPLATES.toml, which has no
    // template `elsewhere`: the job runs, as the one above, instead of being refused.
    project.write(
        "kink/other-templates.toml",
        "[[template]]\nid = \"elsewhere\"\nprogram = \"c3\"\n\n  [[template.hole]]\n  name = \"N\"\n  \
         sort = \"Int\"\n  find = \"3\"\n  literal = \"3\"\n  range = { min = 0, max = 4 }\n",
    );
    let output = project.kink(
        "fuzz",
        &[
            "--templates",
            "kink/other-templates.toml",
            "--template",
            "elsewhere",
            "--matched",
            "stop",
            "--cases",
            "4",
        ],
    );
    let document = json(&output);
    assert_eq!(document["schema"], "kink-flow-fuzz", "{document:#}");
    assert_eq!(
        document["job"]["rule"]["krs"]["item"], "crate::stop",
        "{document:#}"
    );
    assert_status(&output, 3);
}

/// `emit --check` is the gate: it fails when `kink/definition.k` differs from the emission,
/// writes nothing and names the command that writes it; `--locked` refuses a stale file; without
/// it a command writes the file and says so.
#[test]
fn a_stale_definition_is_written_or_refused() {
    let project = project_of("story-plus-edit", "NAT", &story_files());
    let check = project.kink("emit", &["--check"]);
    assert_status(&check, 2);
    let document = json(&check);
    assert_eq!(document["definition"]["status"], "stale");
    // The refusal names the next step, as `--locked`'s does.
    assert!(
        document["refusal"].as_str().unwrap().contains(
            "(emit --check); run `krs kink emit --package story-plus-edit --definition main`"
        ),
        "{document:#}"
    );
    assert!(!project.path().join("kink/definition.k").exists());
    // A usage error kink-flow's parser finds carries the front end's prefix, as its own do,
    // then the verb's usage line and where its options are: not the whole help.
    let bogus = project.kink("check", &["--bogus"]);
    assert_status(&bogus, 2);
    let lines = stderr(&bogus)
        .lines()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    assert_eq!(lines.len(), 3, "{lines:#?}");
    assert!(lines[0].starts_with("krs kink: "), "{lines:#?}");
    assert!(lines[1].starts_with("usage: krs kink check "), "{lines:#?}");
    assert!(
        lines[2].starts_with("`krs kink check --help` lists its options"),
        "{lines:#?}"
    );
    // A tier coverage does not have is a usage error that names the tiers it has.
    let tier_three = project.kink("coverage", &["--tier", "3"]);
    assert_status(&tier_three, 2);
    assert!(
        stderr(&tier_three).starts_with("krs kink: --tier \"3\": expected 1 or 2"),
        "{}",
        stderr(&tier_three)
    );

    let emit = project.kink("emit", &[]);
    assert_status(&emit, 0);
    assert_eq!(json(&emit)["definition"]["status"], "written");
    assert_status(&project.kink("emit", &["--check"]), 0);
    let emitted = project.read("kink/definition.k");

    // Renaming plus_zero's variable changes the K.
    let edited = STORY
        .replace("Plus(NatSyntax::Zero(), n)", "Plus(NatSyntax::Zero(), rhs)")
        .replace("    n\n}", "    rhs\n}");
    assert_ne!(edited, STORY);
    project.write("src/lib.rs", &edited);
    let check = project.kink("emit", &["--check"]);
    assert_status(&check, 2);
    assert_eq!(json(&check)["definition"]["status"], "stale");
    assert_eq!(project.read("kink/definition.k"), emitted);

    let locked = project.kink("coverage", &["--tier", "1", "--locked"]);
    assert_status(&locked, 2);
    let document = json(&locked);
    assert_eq!(document["spec"]["stage"], "definition", "{document:#}");
    assert_eq!(
        document["spec"]["reason"], "definition-stale",
        "{document:#}"
    );
    assert!(
        document["spec"]["detail"]
            .as_str()
            .unwrap()
            .contains("krs kink emit --package story-plus-edit --definition main"),
        "{document:#}"
    );
    assert_eq!(project.read("kink/definition.k"), emitted);

    let results = project.kink("coverage", &[]);
    assert_status(&results, 0);
    let document = json(&results);
    assert_eq!(document["definition"]["status"], "written", "{document:#}");
    assert_ne!(project.read("kink/definition.k"), emitted);
    assert_status(&project.kink("emit", &["--check"]), 0);
    let again = project.kink("coverage", &["--locked"]);
    assert_status(&again, 0);
    assert_eq!(json(&again)["definition"]["status"], "unchanged");
}

/// A FLOW.toml is a K corpus or a KRS one; the krs front end refuses a K corpus naming
/// kink-flow, and a KRS corpus of another facet naming both, before it builds anything.
#[test]
fn the_front_end_refuses_another_front_ends_corpus() {
    let project = story();
    project.write(
        "corpora/k/FLOW.toml",
        "[spec]\nentry = \"plus.k\"\nmain_module = \"NAT\"\n",
    );
    let output = project.kink("check", &["--corpus", "corpora/k"]);
    assert_status(&output, 2);
    let document = json(&output);
    assert_eq!(document["spec"]["stage"], "manifest", "{document:#}");
    let detail = document["spec"]["detail"].as_str().unwrap();
    assert!(
        detail.starts_with("spec.entry: a K corpus") && detail.contains("kink-flow"),
        "{detail}"
    );

    project.write(
        "corpora/other/FLOW.toml",
        "[spec]\nkrs = { definition = \"other\" }\n",
    );
    let output = project.kink("coverage", &["--corpus", "corpora/other"]);
    assert_status(&output, 2);
    let document = json(&output);
    let detail = document["spec"]["detail"].as_str().unwrap();
    assert!(
        detail.starts_with("spec.krs.definition:")
            && detail.contains("`other`")
            && detail.contains("`main`"),
        "{detail}"
    );

    // A package krs refuses while selecting it is answered by krs's diagnostics and the verb's
    // document, refused at stage krs-build: with the corpus's layout (coverage), and without it
    // (query, whose PATTERNS.toml the corpus lacks).
    for (verb, schema) in [
        ("coverage", "kink-flow-coverage"),
        ("query", "kink-flow-query"),
    ] {
        let output = {
            let _turn = project
                .turn
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let mut process = krs_command!();
            fixture_build_env(&mut process, &project.target);
            process
                .current_dir(project.path())
                .args(["kink", verb, "--package", "nope", "--definition", "main"])
                .output()
                .unwrap()
        };
        assert_status(&output, 2);
        assert!(
            stderr(&output).contains("missing-package"),
            "{}",
            stderr(&output)
        );
        let document = json(&output);
        assert_eq!(document["schema"], schema, "{document:#}");
        assert_eq!(document["spec"]["stage"], "krs-build", "{document:#}");
        assert_eq!(document["spec"]["reason"], "krs-refused", "{document:#}");
    }
}

/// The K kink judges is the K `krs emit-k` writes: the in-process emission, `kink/definition.k`
/// and `emit-k`'s `definition.k` are the same bytes, and the rule table names the story's two
/// equations.
#[test]
fn the_emitted_definition_is_the_one_emit_k_writes() {
    let project = story();
    let output = project.krs(&["emit-k", "--output", "target/krs-k"]);
    assert_status(&output, 0);
    let emit_k = project.read("target/krs-k/definition.k");
    let emit = project.kink("emit", &[]);
    assert_status(&emit, 0);
    assert_eq!(project.read("kink/definition.k"), emit_k);

    let request = krs_cli::CommandRequest {
        command: krs_cli::Command::Check {
            backend: None,
            partition: false,
        },
        manifest_path: project.path().join("Cargo.toml"),
        root: krs_cli::FacetSelector {
            package: krs_cli::PackageSelector::Name("story-plus".into()),
            definition: "main".into(),
        },
        dependencies: Vec::new(),
        cfg: Vec::new(),
        registration: krs_cli::RegistrationMode::Inventory,
        no_reuse: true,
        message_format: krs_cli::MessageFormat::Human,
        profile: None,
    };
    let emitted = {
        let _turn = project
            .turn
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let collected = krs_cli::collect_descriptors(&request, Some(&project.target)).unwrap();
        collected.emit_k(collected.bundle.clone()).unwrap()
    };
    assert_eq!(emitted.definition, emit_k);
    let mut items = emitted
        .rules
        .iter()
        .map(|rule| {
            (
                rule.module.as_str(),
                rule.label.as_str(),
                rule.item.as_deref(),
                rule.source_item.as_deref(),
                rule.file.as_deref(),
            )
        })
        .collect::<Vec<_>>();
    items.sort_unstable();
    assert_eq!(
        items,
        [
            (
                "NAT",
                "nat--plus_succ",
                Some("crate::plus_succ"),
                Some("plus_succ"),
                Some("src/lib.rs")
            ),
            (
                "NAT",
                "nat--plus_zero",
                Some("crate::plus_zero"),
                Some("plus_zero"),
                Some("src/lib.rs")
            ),
        ]
    );
    // Each rule is labelled as its K sentence is, under the `// KRS` line that names its item.
    for rule in &emitted.rules {
        let comment = format!(
            "// KRS story-plus/src/lib.rs: {}\n",
            rule.source_item.as_deref().unwrap()
        );
        let sentence = format!("[label({})]", rule.label);
        let at = emit_k.find(&comment).unwrap();
        assert!(emit_k[at..].lines().nth(1).unwrap().ends_with(&sentence));
    }
}

/// A case of typed inputs, a map from a data file and bytes from a binary file, is read by
/// KRS's encoding, admitted and reported; the case's digest follows what the files denote, so
/// reformatting the data file reuses its result and changing a value computes it again.
#[test]
fn a_case_of_typed_inputs_is_read_by_the_krs_encoding() {
    let project = project_of(
        "krs-cli-kink-inputs",
        "ORG-KRS-CLI-KINK-INPUTS",
        &[
            ("src/lib.rs".to_owned(), INPUTS.as_bytes().to_vec()),
            (
                "kink/FLOW.toml".to_owned(),
                b"[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\ncases = \"cases/*.toml\"\n"
                    .to_vec(),
            ),
            (
                "kink/cases/boot.toml".to_owned(),
                br#"[inputs]
memory = { "$data-file" = "data/memory.toml" }
rom = { "$file" = "data/boot.bin" }
pc = 256
entry = { Load = { addr = 2, len = 3 } }
"#
                .to_vec(),
            ),
            (
                "kink/cases/data/memory.toml".to_owned(),
                b"\"0x0100\" = 0\n\"0x0101\" = 195\n".to_vec(),
            ),
            (
                "kink/cases/data/boot.bin".to_owned(),
                (0..=255_u8).collect::<Vec<_>>(),
            ),
        ],
    );
    let program = |output: &Output| {
        assert_status(output, 0);
        let document = json(output);
        let program = document["programs"][0].clone();
        assert_eq!(program["id"], "cases/boot.toml", "{document:#}");
        assert_eq!(program["class"], "comparable", "{document:#}");
        program
    };
    let first_output = project.kink("coverage", &[]);
    // The result cache is on in both profiles (kink-flow `result_store`).
    let cache_on = json(&first_output)["result_cache"]["enabled"] == true;
    assert!(cache_on, "{}", json(&first_output));
    let first = program(&first_output);
    // The same map, written otherwise.
    project.write(
        "kink/cases/data/memory.toml",
        "\"257\" = 195\n\"256\" = 0\n",
    );
    let reformatted = program(&project.kink("coverage", &[]));
    assert_eq!(reformatted["digest"], first["digest"]);
    assert_eq!(reformatted["cached"], cache_on, "{reformatted:#}");
    // Another map.
    project.write(
        "kink/cases/data/memory.toml",
        "\"0x0100\" = 1\n\"0x0101\" = 195\n",
    );
    let changed = program(&project.kink("coverage", &[]));
    assert_ne!(changed["digest"], first["digest"]);
    assert_eq!(changed["cached"], false, "{changed:#}");
}

/// The definition the front end's mutation checks judge (its module doc says what it holds).
const CHECKED: &str = include_str!("fixtures/kink-checks/src/lib.rs");

/// The corpus of [`CHECKED`]: one program for each of three heads.
const CHECKED_FLOW: &str = "[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\nid = \"s5\"\nfile = \"cases/s5.exp\"\n\n[[program]]\nid = \"o3\"\nfile = \"cases/o3.exp\"\n\n[[program]]\nid = \"h2\"\nfile = \"cases/h2.exp\"\n";

fn checked_files(library: &str) -> Vec<(String, Vec<u8>)> {
    vec![
        ("src/lib.rs".to_owned(), library.as_bytes().to_vec()),
        (
            "kink/FLOW.toml".to_owned(),
            CHECKED_FLOW.as_bytes().to_vec(),
        ),
        ("kink/cases/s5.exp".to_owned(), b"step(5)\n".to_vec()),
        ("kink/cases/o3.exp".to_owned(), b"other(3)\n".to_vec()),
        ("kink/cases/h2.exp".to_owned(), b"half(2)\n".to_vec()),
    ]
}

fn checked() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, || {
        project_of("krs-cli-kink-checked", "CHECKS", &checked_files(CHECKED))
    })
}

/// One mutation of one edit: `rule`'s `find` becomes `replace`.
fn mutation(id: &str, rule: &str, find: &str, replace: &str) -> String {
    format!(
        "[[mutation]]\nid = \"{id}\"\nmisunderstanding = \"{id}\"\n\n  [[mutation.edit]]\n  rule = \"{rule}\"\n  find = {}\n  replace = {}\n\n",
        serde_json::to_string(find).unwrap(),
        serde_json::to_string(replace).unwrap()
    )
}

/// The mutations the checks judge, by what they show.
fn checked_mutations() -> String {
    [
        // Two transitions at one priority that now apply to one configuration.
        mutation("overlap", "step_nonneg", "Value:Int >=Int 0", "Value:Int >=Int -1"),
        // An if/else condition edited in its own branch only, then in every branch it renders.
        mutation("branch-one", "clamp_1", "Value:Int <Int 0", "Value:Int <Int 5"),
        format!(
            "{}  [[mutation.edit]]\n  rule = \"clamp_2\"\n  find = \"Value:Int <Int 0\"\n  replace = \"Value:Int <Int 5\"\n\n  [[mutation.edit]]\n  rule = \"clamp_3\"\n  find = \"Value:Int <Int 0\"\n  replace = \"Value:Int <Int 5\"\n\n",
            mutation("branch-all", "clamp_1", "Value:Int <Int 0", "Value:Int <Int 5")
        ),
        // The nondet group: an edit that keeps the overlap, one that leaves a member stale, one
        // that makes it overlap a rule outside the group, and a deletion leaving one member.
        mutation("toss-keeps", "toss_heads", "done ( 1 )", "done ( 2 )"),
        mutation("toss-stale", "toss_heads", "toss ( Value:Int )", "go ( Value:Int )"),
        mutation("toss-other", "toss_heads", "toss ( Value:Int )", "other ( Value:Int )"),
        "[[mutation]]\nid = \"toss-single\"\nmisunderstanding = \"no tails\"\n\n  [[mutation.edit]]\n  rule = \"toss_tails\"\n  delete = true\n\n".to_owned(),
        // The definedness test of a division: removed alone, kept for an edited divisor, and
        // edited with it.
        mutation("test-only", "half", "(Value:Int =/=Int 0) andThenBool ", ""),
        mutation("divisor", "half", "10 /Int Value:Int", "10 /Int (Value:Int +Int 1)"),
        format!(
            "{}  [[mutation.edit]]\n  rule = \"half\"\n  find = \"(Value:Int =/=Int 0)\"\n  replace = \"((Value:Int +Int 1) =/=Int 0)\"\n\n",
            mutation("divisor-both", "half", "10 /Int Value:Int", "10 /Int (Value:Int +Int 1)")
        ),
        // Layout only, and a renaming at every occurrence: neither changes what the rule says.
        mutation("layout", "other", "done ( Value:Int )", "done (  Value:Int )"),
        mutation(
            "renamed",
            "other",
            "other ( Value:Int ) => done ( Value:Int )",
            "other ( V:Int ) => done ( V:Int )",
        ),
        // A label only: kink's own refusal, which the front end never sees.
        mutation(
            "label",
            "other",
            "label(checks--other)",
            "label(checks--other-renamed)",
        ),
        // An equation of a function only the claim applies.
        mutation("helper", "expected", "+Int 1", "+Int 2"),
        // A priority that orders two overlapping rules, removed: never judged with the
        // specification's priority.
        mutation("priority", "pick_first", "priority(40), ", ""),
    ]
    .concat()
}

/// The row of the mutation `id` of a check or run document.
fn row<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("no row {id}: {document:#}"))
}

/// The reasons of a check row's refusals, then of its warnings.
fn reasons(row: &Value) -> (Vec<&str>, Vec<&str>) {
    let of = |key: &str| {
        row[key]
            .as_array()
            .unwrap_or_else(|| panic!("{key} of {row:#}"))
            .iter()
            .map(|finding| finding["reason"].as_str().unwrap())
            .collect::<Vec<_>>()
    };
    (of("refusals"), of("warnings"))
}

/// `check` refuses, with KRS's own code and next step, each mutation whose Rust source KRS
/// refuses, and each edit KRS's emission does not follow; it accepts the rest, warns of a claim
/// helper and an edited construct left in its other renderings, and names each edit's Rust.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One check document, read for each kind of refusal it shows."
)]
fn check_refuses_what_krs_refuses_of_the_mutations_source() {
    let project = checked();
    // `check` reads the stored results, which the other tests of this shared project write as
    // they run: the corpus's results come first, so its warnings do not depend on their order.
    assert_status(&project.kink("coverage", &[]), 0);
    // Each test of this shared project reads a list of its own.
    project.write("kink/check-mutations.toml", checked_mutations());
    let output = project.kink("check", &["--mutations", "kink/check-mutations.toml"]);
    assert_status(&output, 2);
    let document = json(&output);
    // With the corpus's results stored, `check` also warns of the edited rules no case applies
    // (`unapplied-rule`: no case clamps a negative value) or reaches (`unmatched-rule`: no case
    // tosses, and none reaches the claim's helper or the priority rule).
    let expected: [(&str, &[&str], &[&str]); 15] = [
        ("overlap", &["krs::analysis::overlapping-rule-heads"], &[]),
        (
            "branch-one",
            &["krs::analysis::overlapping-match-arms"],
            &["unapplied-rule", "partial-rendering"],
        ),
        ("branch-all", &[], &["unapplied-rule", "unapplied-rule"]),
        ("toss-keeps", &[], &["unmatched-rule"]),
        (
            "toss-stale",
            &["krs::analysis::nondet-group"],
            &["unmatched-rule"],
        ),
        (
            "toss-other",
            &["krs::analysis::overlapping-rule-heads"],
            &["unmatched-rule"],
        ),
        (
            "toss-single",
            &["krs::analysis::nondet-group"],
            &["unmatched-rule"],
        ),
        ("test-only", &["generated-only"], &[]),
        ("divisor", &["derived-mismatch"], &[]),
        ("divisor-both", &[], &[]),
        // kink-flow's own refusal: the texts are equal up to formatting.
        ("layout", &["no-change"], &[]),
        ("renamed", &["no-change"], &[]),
        ("label", &["label-changed"], &[]),
        ("helper", &[], &["unmatched-rule", "claim-helper"]),
        ("priority", &["not-judged"], &["unmatched-rule"]),
    ];
    for (id, refusals, warnings) in expected {
        let row = row(&document, id);
        assert_eq!(
            reasons(row),
            (refusals.to_vec(), warnings.to_vec()),
            "{id}: {row:#}"
        );
        assert_eq!(
            row["outcome"],
            if refusals.is_empty() { "ok" } else { "refused" },
            "{row:#}"
        );
    }
    // A mutation that does not resolve gets no KRS judgement: no finding and no `krs` value.
    assert_eq!(row(&document, "label")["krs"], Value::Null, "{document:#}");
    // The claim helper's function is named as a stop reads its item, and as its source names it.
    let helper = &row(&document, "helper")["warnings"][1];
    assert!(
        helper["detail"]
            .as_str()
            .unwrap()
            .starts_with("`checks--expected` is an equation of `crate::expected` (`Expected`),"),
        "{helper:#}"
    );
    // The overlap names both rules and says no Rust edit of the edited construct avoids it.
    let overlap = &row(&document, "overlap")["refusals"][0];
    let detail = overlap["detail"].as_str().unwrap();
    for named in [
        "`checks--step_neg` (crate::step_neg",
        "`checks--step_nonneg` (crate::step_nonneg",
    ] {
        assert!(detail.contains(named), "{detail}");
    }
    assert!(
        detail.contains("no Rust edit of these constructs avoids the refusal by itself"),
        "{detail}"
    );
    // The overlap leaves no rendering unchanged, so its next step names no siblings.
    let next = overlap["next"].as_str().unwrap();
    assert!(
        next.starts_with("KRS accepts these rules only if they cannot apply"),
        "{overlap:#}"
    );
    assert!(next.contains("a correlated edit"), "{overlap:#}");
    assert!(!next.contains("siblings"), "{overlap:#}");
    // The edited branch condition is rendered, negated, in the later branches: they are the
    // siblings, the one KRS names first.
    let branch = row(&document, "branch-one");
    let siblings = branch["krs"]["siblings"]
        .as_array()
        .unwrap()
        .iter()
        .map(|sibling| {
            (
                sibling["label"].as_str().unwrap(),
                sibling["named_by_krs"].as_bool().unwrap(),
                sibling["changed"].as_bool().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        siblings,
        [
            ("checks--clamp_3", true, false),
            ("checks--clamp_2", false, false)
        ],
        "{branch:#}"
    );
    // The detail lists the unchanged siblings, and the next step names them.
    let next = branch["refusals"][0]["next"].as_str().unwrap();
    assert!(next.contains("siblings"), "{branch:#}");
    // The generated-only refusal names the authored construct and its Rust.
    let generated = &row(&document, "test-only")["refusals"][0];
    let detail = generated["detail"].as_str().unwrap();
    assert!(
        detail.contains("a definedness test KRS inserts"),
        "{detail}"
    );
    let division = line_of(CHECKED, "10 / value");
    assert!(
        detail.contains(&format!("`10 /Int Value:Int` at src/lib.rs:{division}:")),
        "{detail}"
    );
    // The derived mismatch shows the test KRS derives.
    let derived = row(&document, "divisor")["refusals"][0]["detail"]
        .as_str()
        .unwrap()
        .to_owned();
    assert!(derived.contains("(Value:Int +Int 1) =/=Int 0"), "{derived}");
    // Each edit's Rust: the guard's literal, the deleted rule's item.
    let edit = &row(&document, "overlap")["krs"]["edits"][0];
    assert_eq!(edit["judged"], "authored", "{edit:#}");
    assert_eq!(edit["item"], "crate::step_nonneg", "{edit:#}");
    assert_eq!(edit["rust"][0]["text"], "0", "{edit:#}");
    assert_eq!(
        edit["rust"][0]["line"].as_u64(),
        Some(line_of(CHECKED, "int::ge(value, 0)")),
        "{edit:#}"
    );
    let edit = &row(&document, "toss-single")["krs"]["edits"][0];
    assert_eq!(edit["judged"], "deleted", "{edit:#}");
    assert_eq!(
        edit["rust"][0]["line"].as_u64(),
        Some(line_of(CHECKED, "fn toss_tails")),
        "{edit:#}"
    );
    assert_eq!(
        row(&document, "test-only")["krs"]["edits"][0]["judged"],
        "inserted"
    );
}

/// `run` gives each mutation the front end refuses its first refusal, runs nothing for it, runs
/// the rest, and exits non-zero.
#[test]
fn run_refuses_what_check_refuses() {
    // A lock of this test's own, outside the shared corpus.
    const LOCK: [&str; 2] = ["--lock", "target/locks/run-refuses.lock"];
    let project = checked();
    // `run` reads the layout's list; the check test of this shared project reads another.
    project.write(
        "kink/MUTATIONS.toml",
        [
            mutation(
                "overlap",
                "step_nonneg",
                "Value:Int >=Int 0",
                "Value:Int >=Int -1",
            ),
            mutation("toss-keeps", "toss_heads", "done ( 1 )", "done ( 2 )"),
            mutation("test-only", "half", "(Value:Int =/=Int 0) andThenBool ", ""),
            mutation(
                "layout",
                "other",
                "done ( Value:Int )",
                "done (  Value:Int )",
            ),
        ]
        .concat(),
    );
    let refused = [
        ("overlap", "krs::analysis::overlapping-rule-heads"),
        ("test-only", "generated-only"),
        ("layout", "no-change"),
    ];
    let output = project.kink(
        "run",
        &[&["--full", "--cache", "kink/run-cache"][..], &LOCK].concat(),
    );
    assert_status(&output, 2);
    let document = json(&output);
    for (id, reason) in refused {
        let row = row(&document, id);
        assert_eq!(row["status"], "invalid-mutation", "{row:#}");
        assert_eq!(row["reason"], reason, "{row:#}");
    }
    // A refused mutation ran nothing, so it has no tier-1 record and no hint; the mutation
    // that ran has its records (tier 1 is on in both profiles).
    let cached = cached_mutations(&project.path().join("kink/run-cache"));
    for (id, _) in refused {
        assert!(
            !cached.contains(id),
            "{id} has a record or a hint: {cached:?}"
        );
    }
    assert!(cached.contains("toss-keeps"), "{cached:?}");
    let refused = row(&document, "overlap");
    assert!(
        refused["action"]
            .as_str()
            .unwrap()
            .contains("KRS accepts these rules only if they cannot apply"),
        "{refused:#}"
    );
    assert_ne!(
        row(&document, "toss-keeps")["status"],
        "invalid-mutation",
        "{document:#}"
    );
    // `--only` judges the mutations it runs, and refuses them as the whole list does.
    let only = ["--only", "overlap", "--cache", "kink/only-cache"];
    let output = project.kink("run", &[&only[..], &LOCK].concat());
    assert_status(&output, 2);
    let document = json(&output);
    let rows = document["mutations"].as_array().unwrap();
    assert_eq!(rows.len(), 1, "{document:#}");
    assert_eq!(rows[0]["status"], "invalid-mutation", "{document:#}");
    assert_eq!(
        rows[0]["reason"], "krs::analysis::overlapping-rule-heads",
        "{document:#}"
    );
    // `--mutations PATH` names another list than the layout's: only its mutation is judged.
    project.write(
        "kink/run-other.toml",
        mutation(
            "elsewhere",
            "step_nonneg",
            "Value:Int >=Int 0",
            "Value:Int >=Int -1",
        ),
    );
    let output = project.kink(
        "run",
        &[
            "--mutations",
            "kink/run-other.toml",
            "--cache",
            "kink/other-cache",
        ],
    );
    assert_status(&output, 2);
    let document = json(&output);
    let rows = document["mutations"].as_array().unwrap();
    assert_eq!(rows.len(), 1, "{document:#}");
    assert_eq!(rows[0]["id"], "elsewhere", "{document:#}");
    assert_eq!(rows[0]["status"], "invalid-mutation", "{document:#}");
}

/// Every file under `directory`, none when it does not exist.
fn walk_files(directory: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let mut directories = vec![directory.to_path_buf()];
    while let Some(directory) = directories.pop() {
        let Ok(entries) = fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                directories.push(path);
            } else {
                files.push(path);
            }
        }
    }
    files
}

/// The mutation ids the cache at `cache` holds an outcome file or a hint for.
fn cached_mutations(cache: &Path) -> std::collections::BTreeSet<String> {
    let mut ids = std::collections::BTreeSet::new();
    let mut directories = vec![cache.join("outcomes")];
    while let Some(directory) = directories.pop() {
        let Ok(entries) = fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                directories.push(path);
            } else if let Ok(text) = fs::read_to_string(&path)
                && let Ok(record) = serde_json::from_str::<Value>(&text)
                && let Some(id) = record["mutation_id"].as_str()
            {
                ids.insert(id.to_owned());
            }
        }
    }
    if let Ok(text) = fs::read_to_string(cache.join("hints.json")) {
        let hints: Value = serde_json::from_str(&text).unwrap();
        for hint in hints["hints"]
            .as_object()
            .into_iter()
            .flat_map(|map| map.values())
        {
            if let Some(id) = hint["mutation_id"].as_str() {
                ids.insert(id.to_owned());
            }
        }
    }
    ids
}

/// A `fuzz` kill job of a mutation the front end refuses is refused before any case, with the
/// front end's reason and next step.
#[test]
fn a_fuzz_kill_job_of_a_refused_mutation_runs_nothing() {
    let project = checked();
    project.write(
        "kink/fuzz-mutations.toml",
        [
            mutation(
                "overlap",
                "step_nonneg",
                "Value:Int >=Int 0",
                "Value:Int >=Int -1",
            ),
            mutation("toss-keeps", "toss_heads", "done ( 1 )", "done ( 2 )"),
        ]
        .concat(),
    );
    project.write(
        "kink/TEMPLATES.toml",
        "[[template]]\nid = \"step\"\nprogram = \"s5\"\n\n  [[template.hole]]\n  name = \"N\"\n  \
         sort = \"Int\"\n  find = \"5\"\n  literal = \"5\"\n  range = { min = 0, max = 9 }\n",
    );
    let output = project.kink(
        "fuzz",
        &[
            "--template",
            "step",
            "--kill",
            "overlap",
            "--mutations",
            "kink/fuzz-mutations.toml",
        ],
    );
    let document = json(&output);
    let job = &document["job"];
    assert_eq!(job["outcome"], "refused", "{document:#}");
    assert_eq!(job["status"], "invalid-mutation", "{document:#}");
    assert_eq!(
        job["reason"], "krs::analysis::overlapping-rule-heads",
        "{document:#}"
    );
    assert!(
        document["action"]
            .as_str()
            .unwrap()
            .contains("KRS accepts these rules only if they cannot apply"),
        "{document:#}"
    );
    assert_status(&output, 2);
}

/// The verdict of `krs check` on a Rust source that emits each refused mutant is the front
/// end's: the same code, or `overlapping-equations` where the front end says
/// `overlapping-match-arms`, since the source writing one branch's guard alone is three
/// equations; and on a source that emits an accepted mutant, none.
#[test]
fn a_refused_mutants_rust_source_is_refused_by_krs_check() {
    let sources = [
        (
            "overlap",
            CHECKED.replace("int::ge(value, 0)", "int::ge(value, -1)"),
            Some("krs::analysis::overlapping-rule-heads"),
        ),
        (
            "toss-stale",
            CHECKED.replace(
                "fn toss_heads(k::term![ExpSyntax::Toss { value }]",
                "fn toss_heads(k::term![ExpSyntax::Go { value }]",
            ),
            Some("krs::analysis::nondet-group"),
        ),
        (
            "toss-other",
            CHECKED.replace(
                "fn toss_heads(k::term![ExpSyntax::Toss { value }]",
                "fn toss_heads(k::term![ExpSyntax::Other { value }]",
            ),
            Some("krs::analysis::overlapping-rule-heads"),
        ),
        (
            "toss-single",
            CHECKED.replace(
                "#[k::rule(nondet = toss)]\nfn toss_tails(k::term![ExpSyntax::Toss { value }]: Term<Exp>) -> Term<Exp> {\n    ExpSyntax::Done(0)\n}\n",
                "",
            ),
            Some("krs::analysis::nondet-group"),
        ),
        (
            "branch-one",
            CHECKED.replace(
                "#[k::function(total, internal)]\npub fn Clamp(value: Term<Int>) -> Term<Int> {\n    if value < 0 { 0 } else if value > 255 { 255 } else { value }\n}",
                "#[k::function(total, sort = Int, syntax = \"clamp({value})\")]\npub struct Clamp {\n    pub value: Term<Int>,\n}\n\n#[k::requires(value < 5)]\n#[k::equation]\nfn clamp_1(k::term![Clamp(value)]: Term<Int>) -> Term<Int> {\n    0\n}\n\n#[k::requires(!(value < 0) && value > 255)]\n#[k::equation]\nfn clamp_2(k::term![Clamp(value)]: Term<Int>) -> Term<Int> {\n    255\n}\n\n#[k::requires(!(value < 0) && !(value > 255))]\n#[k::equation]\nfn clamp_3(k::term![Clamp(value)]: Term<Int>) -> Term<Int> {\n    value\n}",
            ),
            Some("krs::analysis::overlapping-equations"),
        ),
        (
            "branch-all",
            CHECKED.replace("if value < 0 {", "if value < 5 {"),
            None,
        ),
    ];
    for (id, source, code) in sources {
        assert_ne!(source, CHECKED, "{id}: the source is edited");
        let project = project_of(
            "krs-cli-kink-checked-source",
            "CHECKS",
            &checked_files(&source),
        );
        let output = project.krs(&["check"]);
        let stderr = stderr(&output);
        match code {
            Some(code) => {
                assert!(!output.status.success(), "{id}: {stderr}");
                assert!(stderr.contains(&format!("[{code}]")), "{id}: {stderr}");
            }
            None => assert!(output.status.success(), "{id}: {stderr}"),
        }
    }
}

/// A claim helper is no program's coverage: `coverage` gives the equation of `Expected`, which
/// only the claim applies, the status `claim-helper` (summary `claim_helper`), not `uncovered`,
/// so the uncovered rules are the ones a case can reach.
#[test]
fn coverage_gives_a_claim_helper_its_own_status() {
    let project = checked();
    let output = project.kink("coverage", &[]);
    assert_status(&output, 0);
    let document = json(&output);
    let rules = document["families"]["rules"]["items"].as_array().unwrap();
    let helpers = rules
        .iter()
        .filter(|rule| rule["krs"]["claim_helper"] == true)
        .map(|rule| {
            (
                rule["krs"]["item"].as_str().unwrap(),
                rule["krs"]["source_item"].as_str().unwrap(),
                rule["status"].as_str().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    // The function's one equation is the item `expected`, as `krs run --coverage` names it; the
    // `// KRS` line names the function.
    assert_eq!(
        helpers,
        [("crate::expected", "Expected", "claim-helper")],
        "{document:#}"
    );
    for rule in rules {
        if rule["status"] == "claim-helper" {
            assert_eq!(rule["krs"]["claim_helper"], true, "{rule:#}");
            assert_eq!(rule["matched_by"], serde_json::json!([]), "{rule:#}");
        }
    }
    let count = |status: &str| rules.iter().filter(|rule| rule["status"] == status).count();
    let counts = &document["families"]["rules"]["counts"];
    assert_eq!(counts["claim_helper"], 1, "{counts:#}");
    assert_eq!(counts["unmatched"], count("unmatched"));
    assert_eq!(document["version"], 5);
}

/// A false `total` claim of a KRS function, observed by a run, is a specification diagnostic
/// whose rules are named by their Rust items: `Div` is declared total and divides by its
/// argument, and on `sib(0)` the nondet group's `sib_div` applies it at 0 beside `sib_done`
/// (the sibling keeps the run's leaf clean, so only k-rust's list holds the record).
#[test]
fn a_contradicted_total_claim_names_its_rust_items() {
    const LIBRARY: &str = r#"use k::builtin::{Int, KSequence};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum ExpSyntax {
    #[k::syntax("sib({value})")] Sib { value: Int },
    #[k::syntax("val({value})")] Val { value: Int },
    #[k::syntax("done")] Done(),
}

#[k::function(total, internal)]
pub fn Div(value: Term<Int>) -> Term<Int> {
    10 / value
}

#[k::rule(nondet = sib)]
fn sib_div(k::term![ExpSyntax::Sib { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Val(Div(value))
}

#[k::rule(nondet = sib)]
fn sib_done(k::term![ExpSyntax::Sib { value }]: Term<Exp>) -> Term<Exp> {
    ExpSyntax::Done()
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
        Self { k: k::k![pgm] }
    }
}
"#;
    let project = project_of(
        "krs-cli-kink-total",
        "TOTAL",
        &[
            ("src/lib.rs".to_owned(), LIBRARY.as_bytes().to_vec()),
            (
                "kink/FLOW.toml".to_owned(),
                b"[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\nid = \"sib-0\"\nfile = \"cases/sib0.exp\"\n"
                    .to_vec(),
            ),
            ("kink/cases/sib0.exp".to_owned(), b"sib(0)\n".to_vec()),
        ],
    );
    let output = project.kink("coverage", &[]);
    assert_status(&output, 3);
    let document = json(&output);
    let program = &document["programs"][0];
    assert_eq!(program["class"], "unknown", "{program:#}");
    let [record] = program["specification_diagnostics"]
        .as_array()
        .unwrap()
        .as_slice()
    else {
        panic!("one record: {program:#}")
    };
    assert_eq!(record["claim"], "total", "{record:#}");
    assert_eq!(record["krs_rule"]["item"], "crate::div", "{record:#}");
    assert_eq!(record["krs_rule"]["source_item"], "Div", "{record:#}");
    assert_eq!(record["krs_rule"]["file"], "src/lib.rs", "{record:#}");
    // The equation's authored source starts at the function or in its body.
    let line = record["krs_rule"]["line"].as_u64().unwrap();
    let function = line_of(LIBRARY, "pub fn Div(");
    assert!((function..=function + 1).contains(&line), "{record:#}");
    assert_eq!(
        record["krs_observing_rule"]["item"], "crate::sib_div",
        "{record:#}"
    );
    assert_eq!(document["krs"], serde_json::json!({"version": 6}));
}

/// A program file binds the main parameter as `krs run FILE` does: on a definition whose main
/// parameter is a `Bytes` (`$ROM`), each file a `files` pattern matches is one program, the
/// file's bytes, with the entry's typed inputs for the other parameter, so a corpus of ROMs
/// needs no case document per ROM. A file whose bytes are UTF-8 text is bytes too. The bound
/// value is the file's bytes, which `query` shows by a hit of the pattern of that literal, and
/// `krs run` of the file binds the same. The program digest is a function of the file's bytes
/// and the inputs, not of the file's name: a copy of a ROM under another name has its digest.
/// Inline text has no reading as bytes, and is refused, pointing at `$hex`.
#[test]
fn a_program_file_binds_a_bytes_main_parameter() {
    let project = project_of(
        "krs-cli-kink-bytes-main",
        "ORG-KRS-CLI-KINK-BYTES-MAIN",
        &[
            ("src/lib.rs".to_owned(), BYTES_MAIN.as_bytes().to_vec()),
            (
                "kink/FLOW.toml".to_owned(),
                b"[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\nfiles = \"roms/*.bin\"\ninputs = { pc = 256 }\n\n[[program]]\nid = \"inline\"\ntext = \"ab\"\ninputs = { pc = 256 }\n"
                    .to_vec(),
            ),
            (
                "kink/PATTERNS.toml".to_owned(),
                br#"[[pattern]]
id = "text-rom"
pattern = '<rom> b"ab" </rom> <pc> 256 </pc>'
programs = ["roms/u.bin"]

[[pattern]]
id = "binary-rom"
pattern = '<rom> b"\xff\x00" </rom> <pc> 256 </pc>'
programs = ["roms/b.bin"]
"#
                .to_vec(),
            ),
            ("kink/roms/a.bin".to_owned(), (0..=255_u8).collect()),
            ("kink/roms/b.bin".to_owned(), vec![0xff, 0x00]),
            ("kink/roms/c.bin".to_owned(), (0..=255_u8).collect()),
            ("kink/roms/u.bin".to_owned(), b"ab".to_vec()),
        ],
    );
    let output = project.kink("coverage", &[]);
    assert_status(&output, 2);
    let document = json(&output);
    let programs = document["programs"].as_array().unwrap();
    let program = |id: &str| {
        programs
            .iter()
            .find(|program| program["id"] == id)
            .unwrap_or_else(|| panic!("no program {id}: {document:#}"))
    };
    for id in ["roms/a.bin", "roms/b.bin", "roms/c.bin", "roms/u.bin"] {
        assert_eq!(program(id)["class"], "comparable", "{document:#}");
    }
    assert_eq!(
        program("roms/a.bin")["digest"],
        program("roms/c.bin")["digest"]
    );
    assert_ne!(
        program("roms/a.bin")["digest"],
        program("roms/b.bin")["digest"]
    );
    let inline = program("inline");
    assert_eq!(inline["class"], "refused", "{document:#}");
    assert_eq!(
        inline["cause"],
        "inputs/input-value: the program text: the main parameter `rom` ($ROM: Bytes) takes a \
         file's bytes, and inline text has no reading as bytes; give the program as a file, or \
         bind its bytes under `inputs` instead: `rom = { \"$hex\" = \"..\" }`",
        "{document:#}"
    );

    let output = project.kink("query", &[]);
    let document = json(&output);
    let rows = document["rows"]
        .as_array()
        .unwrap_or_else(|| panic!("the query has rows: {document:#}"))
        .iter()
        .map(|row| {
            (
                row["pattern"].as_str().unwrap(),
                row["program"].as_str().unwrap(),
                row["answer"].as_str().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        rows,
        [
            ("text-rom", "roms/u.bin", "hit"),
            ("binary-rom", "roms/b.bin", "hit")
        ],
        "{document:#}"
    );

    let run = project.krs(&[
        "run",
        "kink/roms/u.bin",
        "--input",
        "pc=256",
        "--depth",
        "0",
    ]);
    assert_status(&run, 0);
    assert!(
        stdout(&run).contains("  <rom>\n    b\"ab\"\n  </rom>\n"),
        "{}",
        stdout(&run)
    );
}

/// On a definition with no main parameter and no `$PGM`, a program file is stray, as `krs run
/// FILE` refuses it, and the refusal is kink's own (`stray-program`), with no native compile.
#[test]
fn a_program_file_is_stray_without_a_main_parameter() {
    let project = project_of(
        "krs-cli-kink-stray-program",
        "ORG-KRS-CLI-KINK-STRAY-PROGRAM",
        &[
            ("src/lib.rs".to_owned(), INPUTS.as_bytes().to_vec()),
            (
                "kink/FLOW.toml".to_owned(),
                b"[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\nid = \"x\"\nfile = \"cases/x.txt\"\n"
                    .to_vec(),
            ),
            ("kink/cases/x.txt".to_owned(), b"go\n".to_vec()),
        ],
    );
    let output = project.kink("coverage", &[]);
    assert_status(&output, 2);
    let document = json(&output);
    assert_eq!(document["programs"][0]["class"], "refused", "{document:#}");
    assert!(
        document["programs"][0]["cause"]
            .as_str()
            .is_some_and(|cause| cause.starts_with("inputs/stray-program: ")),
        "{document:#}"
    );
}

/// A program file binds a main parameter that reads text whatever its K name: on a definition
/// whose main parameter is `$ENTRY`, the file is `entry`'s text, not a stray `$PGM` program.
#[test]
fn a_program_file_binds_a_text_main_parameter_not_named_pgm() {
    let project = project_of(
        "krs-cli-kink-inferred-main",
        "ORG-KRS-CLI-KINK-INFERRED-MAIN",
        &[
            ("src/lib.rs".to_owned(), INFERRED_MAIN.as_bytes().to_vec()),
            (
                "kink/FLOW.toml".to_owned(),
                b"[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\nid = \"go\"\nfile = \"cases/go.txt\"\n"
                    .to_vec(),
            ),
            ("kink/cases/go.txt".to_owned(), b"go\n".to_vec()),
        ],
    );
    let output = project.kink("coverage", &[]);
    assert_status(&output, 0);
    let document = json(&output);
    assert_eq!(document["programs"][0]["id"], "go", "{document:#}");
    assert_eq!(
        document["programs"][0]["class"], "comparable",
        "{document:#}"
    );
}

/// The configuration-cells gate's cell group: `group-core` declares the group `Core` and the
/// rules typed by it, and no configuration; `group-small` (`Small { core, mem }`) and
/// `group-board` (`Board { core, timer, mem }`) each hold the group and resolve its bus items.
const GROUP_CORE: &str =
    include_str!("../../../tests/configuration-cells/packages/group-core/src/lib.rs");
const GROUP_SMALL: &str =
    include_str!("../../../tests/configuration-cells/packages/group-small/src/lib.rs");
const GROUP_BOARD: &str =
    include_str!("../../../tests/configuration-cells/packages/group-board/src/lib.rs");

/// The group's package, which every definition below composes.
const GROUP_CORE_PACKAGE: &str = "krs-configuration-cells-group-core";

/// One corpus for both definitions: a program that never reads the bus, and one that stores and
/// loads back through it.
const GROUP_FLOW: &str = "[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\nid = \"count\"\nfile = \"cases/count.prog\"\n\n[[program]]\nid = \"store-load\"\nfile = \"cases/store-load.prog\"\n";

/// One edit of the group's `reply` rule, anchored by its module-qualified label, which is the
/// same in every definition that holds the group: the library's module is its namespace.
const GROUP_MUTATIONS: &str = r#"[[mutation]]
id = "reply-adds"
misunderstanding = "adds the value a load reads to the accumulator instead of loading it"

  [[mutation.edit]]
  rule = "KRS-GROUP-CORE.reply"
  find = "_ => Value:Int"
  replace = "Acc:Int => Acc:Int +Int Value:Int"
"#;

/// Writes into `directory` a workspace of the gate's three group packages, each of the two
/// definitions with the corpus and the mutation list above.
fn group_workspace(directory: &Path) {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
    let write = |relative: &str, contents: &str| {
        let path = directory.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    };
    for (name, source) in [
        ("core", GROUP_CORE),
        ("small", GROUP_SMALL),
        ("board", GROUP_BOARD),
    ] {
        let dependency = if name == "core" {
            String::new()
        } else {
            format!(
                "group-core = {{ package = \"{GROUP_CORE_PACKAGE}\", path = \"../group-core\" }}\n"
            )
        };
        write(&format!("group-{name}/src/lib.rs"), source);
        write(
            &format!("group-{name}/Cargo.toml"),
            &format!(
                "[package]\nname = \"krs-configuration-cells-group-{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n{dependency}\n[package.metadata.krs]\nk-namespace = \"KRS-GROUP-{}\"\n\n[package.metadata.krs.definitions.main]\n",
                name.to_ascii_uppercase()
            ),
        );
        if name != "core" {
            write(&format!("group-{name}/kink/FLOW.toml"), GROUP_FLOW);
            write(
                &format!("group-{name}/kink/cases/count.prog"),
                "inc ; inc ; done\n",
            );
            write(
                &format!("group-{name}/kink/cases/store-load.prog"),
                "inc ; inc ; store ( 7 ) ; inc ; load ( 7 ) ; done\n",
            );
            write(
                &format!("group-{name}/kink/mutations/core.toml"),
                GROUP_MUTATIONS,
            );
        }
    }
    write(
        "Cargo.toml",
        "[workspace]\nmembers = [\"group-core\", \"group-small\", \"group-board\"]\nresolver = \"3\"\n",
    );
}

/// `krs kink VERB ARGUMENTS` on the definition of `group-<name>`, composed with the group's.
fn group_kink(
    target: &Path,
    workspace: &Path,
    name: &str,
    verb: &str,
    arguments: &[&str],
) -> Output {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    process
        .current_dir(workspace.join(format!("group-{name}")))
        .args(["kink", verb])
        .args(arguments)
        .args([
            "--package",
            &format!("krs-configuration-cells-group-{name}"),
            "--definition",
            "main",
            "--dependency",
            &format!("{GROUP_CORE_PACKAGE}:main"),
        ]);
    process.output().unwrap()
}

/// A mutation of a rule the library writes for its cell group is one mutation of each definition
/// that holds the group: the anchor `KRS-GROUP-CORE.reply` names the same sentence in `small`
/// and in `board`, `check` names it by the library's Rust item and position, in the library's
/// package, in both, and `run` kills it in both by the one program that loads through the bus,
/// whatever cells each definition holds beside the group.
#[test]
fn a_mutation_of_a_group_rule_is_judged_in_every_definition_that_holds_the_group() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    group_workspace(temporary.path());
    let mut named = Vec::new();
    for name in ["small", "board"] {
        let output = group_kink(target.path(), temporary.path(), name, "check", &[]);
        assert_status(&output, 0);
        let check = json(&output);
        let rows = check["mutations"].as_array().unwrap();
        assert_eq!(rows.len(), 1, "{name}: {check:#}");
        let row = &rows[0];
        assert_eq!(row["id"], "core/reply-adds", "{name}: {row:#}");
        assert_eq!(row["outcome"], "ok", "{name}: {row:#}");
        assert_eq!(row["refusals"], serde_json::json!([]), "{name}: {row:#}");
        assert_eq!(row["warnings"], serde_json::json!([]), "{name}: {row:#}");
        let rules = row["rules"].as_array().unwrap();
        assert_eq!(rules.len(), 1, "{name}: {row:#}");
        let rule = &rules[0];
        assert_eq!(rule["label"], "KRS-GROUP-CORE.reply", "{name}: {rule:#}");
        assert_eq!(rule["module"], "KRS-GROUP-CORE", "{name}: {rule:#}");
        assert_eq!(
            rule["krs"],
            serde_json::json!({
                // The library's item, by its crate name, as a stop names it.
                "item": "krs_configuration_cells_group_core::reply",
                "source_item": "reply",
                "package": GROUP_CORE_PACKAGE,
                "file": "src/lib.rs",
                "line": line_of(GROUP_CORE, "    reply: {"),
                "column": 5,
                "kind": "rule",
                "claim_helper": false,
            }),
            "{name}: {rule:#}"
        );
        // The Rust the edit stands for is the library's `acc` entry. An edit's Rust lies in the
        // item of the rule that lists the edit (`rules[].edits`), so its file is relative to that
        // rule's package (`rules[].krs.package`): here the library's, not the selected
        // definition's.
        let edits = row["krs"]["edits"].as_array().unwrap();
        assert_eq!(edits.len(), 1, "{name}: {row:#}");
        let holder = rules
            .iter()
            .filter(|rule| {
                rule["edits"]
                    .as_array()
                    .unwrap()
                    .contains(&edits[0]["edit"])
            })
            .collect::<Vec<_>>();
        assert_eq!(holder, [rule], "{name}: {row:#}");
        let rust = edits[0]["rust"].as_array().unwrap();
        assert_eq!(rust.len(), 1, "{name}: {row:#}");
        assert_eq!(
            (&rule["krs"]["package"], &rust[0]["file"]),
            (
                &serde_json::json!(GROUP_CORE_PACKAGE),
                &serde_json::json!("src/lib.rs")
            ),
            "{name}: {row:#}"
        );
        assert_eq!(rust[0]["text"], "acc", "{name}: {row:#}");
        assert_eq!(
            rust[0]["line"].as_u64(),
            Some(line_of(GROUP_CORE, "        acc: _,")),
            "{name}: {row:#}"
        );
        named.push((
            rule["before"].clone(),
            rule["after"].clone(),
            row["krs"].clone(),
        ));
    }
    // The emitted rule, its edit and their Rust are the same in both definitions.
    assert_eq!(named[0], named[1]);

    for name in ["small", "board"] {
        let output = group_kink(target.path(), temporary.path(), name, "run", &["--full"]);
        assert_status(&output, 0);
        let document = json(&output);
        let verdicts = document["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| {
                (
                    row["id"].as_str().unwrap(),
                    row["status"].as_str().unwrap(),
                    strings(&row["killed_by"]),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            verdicts,
            [("core/reply-adds", "killed", vec!["store-load"])],
            "{name}: {document:#}"
        );
    }
}

/// The configuration-cells gate's harts: `group-harts/hart` declares the group `Hart` and its rules,
/// `group-harts/smp` holds harts as the instances of a Map collection keyed by `id`, and
/// `group-harts/nested` holds them as the instances of a Map collection inside each instance of
/// a Map collection of clusters keyed by `cid`.
const GROUP_HARTS_HART: &str =
    include_str!("../../../tests/configuration-cells/packages/group-harts/hart/src/lib.rs");
const GROUP_HARTS_SMP: &str =
    include_str!("../../../tests/configuration-cells/packages/group-harts/smp/src/lib.rs");
const GROUP_HARTS_NESTED: &str =
    include_str!("../../../tests/configuration-cells/packages/group-harts/nested/src/lib.rs");

/// The harts' library package, which `smp` composes.
const GROUP_HARTS_HART_PACKAGE: &str = "krs-configuration-cells-group-harts-hart";

/// One edit of `smp`'s `write`, which answers a hart's bus write in the shared memory.
const GROUP_HARTS_MUTATIONS: &str = r#"[[mutation]]
id = "write-off"
misunderstanding = "a write stores one more than the value written"

  [[mutation.edit]]
  rule = "KRS-GROUP-HARTS-SMP.write"
  find = "Addr:Int <- Value:Int"
  replace = "Addr:Int <- Value:Int +Int 1"
"#;

/// Writes into `workspace` the harts packages, `hart` holding `hart`, and the package `holder`
/// (its name and its source) that composes it, with its corpus `kink`, narrowed to `pc`, and its
/// corpus `corpora/all`, which compares every cell; each corpus runs `program` (its id and its
/// text) and lists `mutations`.
fn harts_workspace(
    workspace: &Path,
    hart: &str,
    holder: (&str, &str),
    program: (&str, &str),
    mutations: &str,
) {
    let (holder, holder_source) = holder;
    let (id, text) = program;
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
    let write = |relative: &str, contents: &str| {
        let path = workspace.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    };
    for (name, source, dependency) in [
        ("hart", hart, String::new()),
        (
            holder,
            holder_source,
            format!("hart = {{ package = \"{GROUP_HARTS_HART_PACKAGE}\", path = \"../hart\" }}\n"),
        ),
    ] {
        write(&format!("{name}/src/lib.rs"), source);
        write(
            &format!("{name}/Cargo.toml"),
            &format!(
                "[package]\nname = \"krs-configuration-cells-group-harts-{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n{dependency}\n[package.metadata.krs]\nk-namespace = \"KRS-GROUP-{}\"\n\n[package.metadata.krs.definitions.main]\n",
                if name == "hart" {
                    "HART".to_owned()
                } else {
                    format!("HARTS-{}", name.to_uppercase())
                }
            ),
        );
    }
    let corpora = [
        ("kink", "[result]\ncells = [\"pc\"]\n\n"),
        ("corpora/all", ""),
    ];
    for (corpus, result) in corpora {
        write(
            &format!("{holder}/{corpus}/FLOW.toml"),
            &format!(
                "[spec]\nkrs = {{ definition = \"main\" }}\n\n{result}[[program]]\nid = \"{id}\"\nfile = \"cases/{id}.prog\"\n"
            ),
        );
        write(&format!("{holder}/{corpus}/cases/{id}.prog"), text);
        write(
            &format!("{holder}/{corpus}/mutations/harts.toml"),
            mutations,
        );
    }
    write(
        "Cargo.toml",
        &format!("[workspace]\nmembers = [\"hart\", \"{holder}\"]\nresolver = \"3\"\n"),
    );
}

/// A corpus narrowed to a cell inside the instances of a Map collection compares it in each
/// instance, by its key. In `smp` the program stores hart 0's id at address 0 and loads it back
/// onto the hart's computation cell, so `write-off` changes the memory and that cell. Narrowed to
/// `["pc"]`, the corpus compares each hart's `pc` and its key `id`, leaves every other cell out
/// (in each hart too) and the mutation survives; the corpus that compares every cell kills it.
#[test]
fn a_corpus_narrowed_to_cells_of_a_maps_instances_compares_them_by_key() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let workspace = temporary.path();
    harts_workspace(
        workspace,
        GROUP_HARTS_HART,
        ("smp", GROUP_HARTS_SMP),
        ("store-load", "store ( 0 ) ; load ( 0 )\n"),
        GROUP_HARTS_MUTATIONS,
    );
    let run = |corpus: &str| harts_kink_run(target.path(), workspace, "smp", corpus, 0);
    let verdicts = |run: &Value| {
        run["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| {
                (
                    row["id"].as_str().unwrap().to_owned(),
                    row["status"].as_str().unwrap().to_owned(),
                )
            })
            .collect::<Vec<_>>()
    };

    let narrowed = run("kink");
    assert_eq!(
        narrowed["result"],
        serde_json::json!({
            "slots": ["exit-stop", "cells"],
            "compared": ["id", "pc"],
            "not_compared": ["k", "regs", "reservation", "jobs", "mem", "nextId"],
            "unobservable": [],
            // The same cells by Rust path; `pc` is a K name, which no cell has as its path.
            "krs": {
                "compared": ["harts.hart.id", "harts.hart.pc"],
                "not_compared": [
                    "harts.hart.k",
                    "harts.hart.regs",
                    "harts.hart.reservation",
                    "harts.hart.jobs",
                    "mem",
                    "next_id",
                ],
                "unobservable": [],
                "cells": {"pc": "pc"},
            },
        }),
        "{narrowed:#}"
    );
    assert_eq!(
        verdicts(&narrowed),
        [("harts/write-off".to_owned(), "survived".to_owned())],
        "{narrowed:#}"
    );
    let row = &narrowed["mutations"][0]["executed"][0];
    assert_eq!(row["slots"]["cells"]["outcome"], "agree", "{row:#}");

    let all = run("corpora/all");
    assert_eq!(
        all["result"]["slots"],
        serde_json::json!(["exit-stop", "whole-term"])
    );
    assert_eq!(
        verdicts(&all),
        [("harts/write-off".to_owned(), "killed".to_owned())],
        "{all:#}"
    );
    let difference = &all["mutations"][0]["executed"][0]["difference"];
    assert_eq!(difference["format"], "krs-difference/3", "{difference:#}");
    // The first difference is the loaded value, in hart 0's computation cell, named by key.
    assert_eq!(difference["cell"], "harts.hart[0].k", "{difference:#}");
    assert_eq!(difference["left"]["value"]["document"], 0, "{difference:#}");
    assert_eq!(
        difference["right"]["value"]["document"], 1,
        "{difference:#}"
    );
    assert_eq!(
        difference["also_differ"],
        serde_json::json!(["mem"]),
        "{difference:#}"
    );
}

/// `inc` of [`GROUP_HARTS_HART`] as a `#[k::rule]` fn over `k::cells! { .. }: Hart`, which
/// `krs expand` prints for the readable rule.
const HART_CELLS_INC: &str = r#"
#[k::rule(label = "inc")]
pub fn inc(
    pc: Int,
    k::cells! {
        k: k::configuration::KCell(Op::Inc(), tail @ ..),
        pc: k::configuration::Cell(pc),
        state @ ..
    }: Hart,
) -> Hart {
    k::cells! {
        k: k::configuration::KCell(..tail),
        pc: k::configuration::Cell(int::add(pc, 1)),
        ..state
    }
}
"#;

/// Edits of `hart`'s rules for `Hart`, which `smp` holds as the instances of a Map collection:
/// one of `inc`'s result, one that adds a cell outside the hart to `inc`, and one that writes
/// the key `tick` matches.
const GROUP_HARTS_RULE_MUTATIONS: &str = r#"[[mutation]]
id = "inc-two"
misunderstanding = "an instruction counts two"

  [[mutation.edit]]
  rule = "KRS-GROUP-HART.inc"
  find = "Pc:Int +Int 1"
  replace = "Pc:Int +Int 2"

[[mutation]]
id = "inc-next-id"
misunderstanding = "counting an instruction also takes the next hart id"

  [[mutation.edit]]
  rule = "KRS-GROUP-HART.inc"
  find = "</hart>"
  replace = "</hart>\n    <nextId> N:Int => N:Int +Int 1 </nextId>"

[[mutation]]
id = "tick-rekeys"
misunderstanding = "a tick moves hart 0 to the key 1"

  [[mutation.edit]]
  rule = "KRS-GROUP-HART.tick"
  find = "<id> 0 </id>"
  replace = "<id> 0 => 1 </id>"
"#;

/// Runs `krs kink run --full` on the corpus `corpus` of the package `holder` in the harts
/// workspace `workspace`, which exits with `status`.
fn harts_kink_run(
    target: &Path,
    workspace: &Path,
    holder: &str,
    corpus: &str,
    status: i32,
) -> Value {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    process
        .current_dir(workspace.join(holder))
        .args(["kink", "run", "--full", "--corpus", corpus])
        .args([
            "--package",
            &format!("krs-configuration-cells-group-harts-{holder}"),
            "--definition",
            "main",
            "--dependency",
            &format!("{GROUP_HARTS_HART_PACKAGE}:main"),
        ]);
    let output = process.output().unwrap();
    assert_status(&output, status);
    json(&output)
}

/// An edit of a rule for `Hart`, whose cells lie in an instance of `smp`'s Map collection, is
/// judged: the rule mentions the hart's own cells inside the instance's cell, which is its
/// footprint, not a change of it. So `inc-two` runs, and the corpus narrowed to `pc` kills it
/// through hart 0's `pc`, its difference naming the cell by key with the other cells of the
/// hart unstated. An edit that changes the footprint stays refused: `inc-next-id` adds a cell
/// outside the hart, and `tick-rekeys` writes the key of the instance `tick` matched, which is
/// another instance's identity, as KRS refuses the Rust source that writes it. The readable rule
/// and its `cells!` print, whose K binds the computation's tail, judge alike.
#[test]
fn an_edit_of_a_rule_for_a_maps_instance_is_judged_by_its_footprint() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let readable_inc = "    /// Count one instruction.\n    inc: {\n        k: [Inc(), ..],\n        pc,\n    } => {\n        k: [..],\n        pc: int::add(pc, 1),\n    };\n\n";
    assert!(GROUP_HARTS_HART.contains(readable_inc));
    let cells = format!(
        "{}{HART_CELLS_INC}",
        GROUP_HARTS_HART.replace(readable_inc, "")
    );
    let mut spellings = Vec::new();
    for (spelling, hart) in [("readable", GROUP_HARTS_HART), ("cells", cells.as_str())] {
        let workspace = temporary.path().join(spelling);
        harts_workspace(
            &workspace,
            hart,
            ("smp", GROUP_HARTS_SMP),
            ("count", "inc ; inc\n"),
            GROUP_HARTS_RULE_MUTATIONS,
        );
        // The refused mutations are invalid, which the run's status reports.
        let run = harts_kink_run(target.path(), &workspace, "smp", "kink", 2);
        let rows = run["mutations"].as_array().unwrap();
        let verdicts = rows
            .iter()
            .map(|row| {
                (
                    row["id"].as_str().unwrap(),
                    row["status"].as_str().unwrap(),
                    row["reason"].as_str(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            verdicts,
            [
                ("harts/inc-two", "killed", None),
                ("harts/inc-next-id", "invalid-mutation", Some("not-judged")),
                (
                    "harts/tick-rekeys",
                    "invalid-mutation",
                    Some("krs::analysis::map-collection-key")
                ),
            ],
            "{spelling}: {run:#}"
        );
        let difference = &rows[0]["executed"][0]["difference"];
        assert_eq!(
            difference["format"], "krs-difference/3",
            "{spelling}: {difference:#}"
        );
        assert_eq!(
            difference["cell"], "harts.hart[0].pc",
            "{spelling}: {difference:#}"
        );
        assert_eq!(
            difference["left"]["value"]["document"], 2,
            "{spelling}: {difference:#}"
        );
        assert_eq!(
            difference["right"]["value"]["document"], 4,
            "{spelling}: {difference:#}"
        );
        assert_eq!(
            difference["also_differ"],
            serde_json::json!([]),
            "{spelling}: {difference:#}"
        );
        let detail = rows[1]["detail"].as_str().unwrap();
        assert!(
            detail.ends_with("the edit changes the cells the rule mentions; it is not judged"),
            "{spelling}: {detail}"
        );
        let definition = fs::read_to_string(workspace.join("smp/kink/definition.k")).unwrap();
        let start = definition.find("rule [inc]:").unwrap();
        let end = start + definition[start..].find("</hart>").unwrap() + "</hart>".len();
        spellings.push(definition[start..end].to_owned());
    }
    expect_test::expect![[r#"
        [
            "rule [inc]:\n    <hart>\n        <k> inc => .K ... </k>\n        <pc> Pc:Int => Pc:Int +Int 1 </pc>\n        ...\n    </hart>",
            "rule [inc]:\n    <hart>\n        <k> inc ~> Tail:K => .K ~> Tail:K </k>\n        <pc> Pc:Int => Pc:Int +Int 1 </pc>\n        ...\n    </hart>",
        ]
    "#]]
    .assert_debug_eq(&spellings);
}

/// An edit of `nested`'s `leap`, a rule for `Hart` whose harts lie in the instances of a Map
/// collection inside each cluster, and which passes `pcPlus` the keys of its hart and cluster.
const GROUP_HARTS_NESTED_MUTATIONS: &str = r#"[[mutation]]
id = "leap-long"
misunderstanding = "a leap goes one past its distance"

  [[mutation.edit]]
  rule = "KRS-GROUP-HARTS-NESTED.leap"
  find = "pcPlus ( N:Int )"
  replace = "pcPlus ( N:Int +Int 1 )"
"#;

/// An edit of a rule about one hart of one cluster is judged beside the key cells KRS adds to it
/// and the key arguments it passes: `leap` names the cluster's key `<cid>` around the hart's cell
/// and the hart's key `<id>` in it, and passes both to `pcPlus`, which KRS writes so that the
/// function reads the program counter of the hart the rule is about. KRS derives them again for
/// the edited rule, so `leap-long` runs, and the corpus narrowed to `pc` kills it through that
/// hart's `pc`, named by both keys.
#[test]
fn an_edit_of_a_rule_for_a_nested_instance_is_judged_beside_the_keys_krs_adds() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let workspace = temporary.path();
    harts_workspace(
        workspace,
        GROUP_HARTS_HART,
        ("nested", GROUP_HARTS_NESTED),
        ("leap", "leap ( 3 )\n"),
        GROUP_HARTS_NESTED_MUTATIONS,
    );
    let run = harts_kink_run(target.path(), workspace, "nested", "kink", 0);
    let row = &run["mutations"][0];
    assert_eq!(row["id"], "harts/leap-long", "{run:#}");
    assert_eq!(row["status"], "killed", "{run:#}");
    let difference = &row["executed"][0]["difference"];
    assert_eq!(difference["format"], "krs-difference/3", "{difference:#}");
    assert_eq!(
        difference["cell"], "clusters.cluster[0].harts.hart[0].pc",
        "{difference:#}"
    );
    assert_eq!(difference["left"]["value"]["document"], 3, "{difference:#}");
    assert_eq!(
        difference["right"]["value"]["document"], 4,
        "{difference:#}"
    );
}

/// A corpus of a definition that never ends on its own names its stop by KRS item, as `krs run
/// --stop-after` does: the front end hands kink-flow the rule's K label, every document names the
/// stop with the labels each name selects, the run ends at its third stop, and a mutation is
/// judged relative to the stop. A name that selects no rewrite rule refuses the corpus.
#[test]
fn a_stop_named_by_krs_item_ends_the_runs_of_a_definition_that_never_stops() {
    let project = ticker();
    let output = project.kink("coverage", &[]);
    assert_status(&output, 0);
    let document = json(&output);
    let stop = &document["stop"];
    let labels = strings(&stop["after"]);
    // A term rule's label is its `label(..)` attribute, which K keeps as written.
    assert_eq!(labels, ["ticker--tick"], "{stop:#}");
    assert_eq!(stop["before"], serde_json::json!([]), "{stop:#}");
    assert_eq!(stop["count"], 3, "{stop:#}");
    assert_eq!(
        stop["krs"]["items"]["crate::tick"],
        serde_json::json!(labels),
        "{stop:#}"
    );
    let program = &document["programs"][0];
    assert_eq!(program["class"], "comparable", "{program:#}");
    let end = &program["ends"][0];
    assert_eq!(end["halt"], "stop", "{program:#}");
    let head = end["head"]["text"].as_str().unwrap();
    assert!(head.contains('3') && !head.contains('4'), "{program:#}");

    // A mutation of the stopped rule's right-hand side, after its label: killed relative to the
    // stop, which reaches its third tick on the mutant too.
    let definition = project.read("kink/definition.k");
    let rule = definition
        .lines()
        .find(|line| line.contains("label(ticker--tick)"))
        .unwrap_or_else(|| panic!("no rule ticker--tick:\n{definition}"));
    let find = "+Int 1";
    assert!(rule.contains(find), "{rule}");
    project.write(
        "kink/mutations/tick.toml",
        format!(
            "[[mutation]]\nid = \"twice\"\nmisunderstanding = \"a tick adds two\"\n\n  [[mutation.edit]]\n  rule = \"tick\"\n  find = {find:?}\n  replace = \"+Int 2\"\n"
        ),
    );
    let output = project.kink("run", &["--lock", "target/locks/ticker-stop.lock"]);
    let run = json(&output);
    assert_eq!(
        run["stop"]["krs"]["items"]["crate::tick"],
        serde_json::json!(labels)
    );
    let row = &run["mutations"][0];
    assert_eq!(row["status"], "killed", "{run:#}\n{definition}");

    // Stopped before `tick` with the count 1, the run never takes its step: `check` warns that
    // an edit of only its right-hand side changes no end.
    let output = project.kink(
        "check",
        &[
            "--corpus",
            "corpora/before",
            "--mutations",
            "kink/mutations/tick.toml",
        ],
    );
    let check = json(&output);
    assert_eq!(
        check["stop"]["krs"]["items"]["crate::tick"],
        serde_json::json!(labels)
    );
    let warnings = check["mutations"][0]["warnings"]
        .as_array()
        .unwrap_or_else(|| panic!("{check:#}"))
        .iter()
        .map(|warning| warning["reason"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert!(warnings.contains(&"stop-hides-edit"), "{check:#}");

    // An item that wrote no rule selects nothing: the corpus is refused before kink-flow runs.
    let output = project.kink("coverage", &["--corpus", "corpora/unknown"]);
    assert_status(&output, 2);
    let refused = json(&output);
    assert_eq!(refused["spec"]["stage"], "stop", "{refused:#}");
    assert_eq!(refused["spec"]["reason"], "stop-unresolved", "{refused:#}");
    let detail = refused["spec"]["detail"].as_str().unwrap();
    assert!(detail.contains("after `crate::nothing`"), "{detail}");
}

/// A free-running counter: `tick` adds 1 to `n` and ticks again, so a run never ends on its own,
/// and `Third` holds where `n` is a multiple of 3: a stop condition of the one cell `n`.
const STOPWATCH: &str = r##"use k::builtin::{Bool, Int, KSequence};
use k::{KItem, Term};

k::sorts! {
    Op: KItem;
}

#[k::constructors(sort = Op, result = k::KResult)]
pub enum Step {
    #[k::syntax("#tick")]
    Tick,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub n: Int,
}

impl Machine {
    #[k::init]
    pub fn init(start: Int) -> Self {
        Self {
            k: k::k![Step::Tick],
            n: start,
        }
    }
}

k::rules! {
    for Machine;

    tick: { k: [Step::Tick, ..], n } => { k: [Step::Tick, ..], n: n + 1 };
}

/// Whether `n` is a multiple of 3.
#[k::function(total, internal)]
pub fn Third(n: Term<Int>) -> Term<Bool> {
    n % 3 == 0
}
"##;

/// The package of [`STOPWATCH`].
const STOPWATCH_PACKAGE: &str = "krs-cli-kink-stopwatch";

/// The observer of [`STOPWATCH`], a second package of its workspace that depends on it.
const STOPWATCH_OBSERVER_PACKAGE: &str = "krs-cli-kink-stopwatch-observe";

/// The observer's source: two conditions of `n` that no definition imports, one total and one
/// partial.
const STOPWATCH_OBSERVER: &str = r"//! An observer of the stopwatch, imported by no definition.

use k::Term;
use k::builtin::{Bool, Int};

/// Whether `n` is a multiple of 5.
#[k::function(total, internal)]
pub fn Fifth(n: Term<Int>) -> Term<Bool> {
    n % 5 == 0
}

/// A condition with no value from 2 on: partial, defined by its equation alone.
#[k::function(partial, internal)]
#[k::requires(n < 2)]
pub fn Small(n: Term<Int>) -> Term<Bool> {
    n >= 5
}
";

/// [`STOPWATCH`] and its observer, with corpora that stop after `tick` where `Third` holds of
/// `n` (`kink`), name a function the definition does not hold (`corpora/unknown`), stop before
/// `tick` where `Third` holds, from 0, where the first arrival is a stop (`corpora/hidden`), and
/// from 1, where the run takes `tick`'s step at the arrivals at 1 and 2 (`corpora/taken`), and
/// stop after `tick` where the observer's `Fifth` holds (`corpora/observed`) or where its partial
/// `Small` does, which has no value at the second arrival (`corpora/partial`).
fn stopwatch() -> Arc<Project> {
    static PROJECT: Mutex<Weak<Project>> = Mutex::new(Weak::new());
    Project::shared(&PROJECT, || {
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        let manifest = |name: &str, namespace: &str, dependencies: &str, workspace: &str| {
            format!(
                "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n{workspace}"
            )
            .into_bytes()
        };
        let mut files = vec![
            (
                "Cargo.toml".to_owned(),
                manifest(
                    STOPWATCH_PACKAGE,
                    "STOPWATCH",
                    "",
                    "\n[workspace]\nmembers = [\"observe\"]\nresolver = \"3\"\n",
                ),
            ),
            ("src/lib.rs".to_owned(), STOPWATCH.as_bytes().to_vec()),
            (
                "observe/Cargo.toml".to_owned(),
                manifest(
                    STOPWATCH_OBSERVER_PACKAGE,
                    "STOPWATCH-OBSERVE",
                    &format!(
                        "stopwatch = {{ package = \"{STOPWATCH_PACKAGE}\", path = \"..\" }}\n"
                    ),
                    "",
                ),
            ),
            (
                "observe/src/lib.rs".to_owned(),
                STOPWATCH_OBSERVER.as_bytes().to_vec(),
            ),
        ];
        let observer = format!(", observer = \"{STOPWATCH_OBSERVER_PACKAGE}:main\"");
        for (corpus, side, function, observer, start) in [
            ("kink", "after", "Third", "", 0),
            ("corpora/unknown", "after", "Nothing", "", 0),
            ("corpora/hidden", "before", "Third", "", 0),
            ("corpora/taken", "before", "Third", "", 1),
            ("corpora/observed", "after", "Fifth", observer.as_str(), 0),
            ("corpora/partial", "after", "Small", observer.as_str(), 0),
        ] {
            files.push((
                format!("{corpus}/FLOW.toml"),
                format!(
                    "[spec]\nkrs = {{ definition = \"main\" }}\n\n[stop]\n{side} = [\"crate::tick\"]\nwhen = {{ function = \"{function}\", cells = [\"n\"]{observer} }}\n\n[[program]]\ncases = \"cases/*.toml\"\n"
                )
                .into_bytes(),
            ));
            files.push((
                format!("{corpus}/cases/start.toml"),
                format!("[inputs]\nstart = {start}\n").into_bytes(),
            ));
        }
        files.push((
            "kink/mutations/tick.toml".to_owned(),
            b"[[mutation]]\nid = \"twice\"\nmisunderstanding = \"a tick adds two\"\n\n  [[mutation.edit]]\n  rule = \"tick\"\n  find = \"+Int 1\"\n  replace = \"+Int 2\"\n"
                .to_vec(),
        ));
        project_of(STOPWATCH_PACKAGE, "STOPWATCH", &files)
    })
}

/// A stop condition (`[stop] when`) named with KRS's spellings, as `krs run --stop-when` names
/// one: the front end resolves the function in the observer (here the definition itself) and
/// the cell by Rust path, and every document names the condition, by the identity it resolved
/// (`stop.when`: the observer's Definition IR digest, the function's path and the cells) and as
/// the corpus wrote it (`stop.krs.when`). The run of `start = 0` ends after the tick that
/// reaches 3, the first arrival where `Third` holds; a tick that adds two reaches 2, 4 and then
/// 6, so the condition's state moves and the mutation is killed relative to the condition. A
/// function the definition does not hold refuses the corpus at stage `stop` before anything runs.
#[test]
fn a_stop_condition_names_where_the_runs_of_a_corpus_end() {
    let project = stopwatch();
    let output = project.kink("coverage", &[]);
    assert_status(&output, 0);
    let document = json(&output);
    let stop = &document["stop"];
    assert_eq!(stop["when"]["cells"], serde_json::json!(["n"]), "{stop:#}");
    assert!(
        stop["when"]["function"]
            .as_str()
            .is_some_and(|path| path.ends_with("Third")),
        "{stop:#}"
    );
    assert_eq!(
        stop["when"]["observer"]["definition"],
        serde_json::Value::Null,
        "{stop:#}"
    );
    assert!(
        stop["when"]["observer"]["definition_ir"].is_string(),
        "{stop:#}"
    );
    assert_eq!(
        stop["krs"]["when"],
        serde_json::json!({"function": "Third", "cells": ["n"], "observer": null}),
        "{stop:#}"
    );
    let program = &document["programs"][0];
    assert_eq!(program["class"], "comparable", "{program:#}");
    assert_eq!(program["ends"][0]["halt"], "stop", "{program:#}");

    let output = project.kink("run", &[]);
    let run = json(&output);
    assert_eq!(run["stop"]["when"], stop["when"], "{run:#}");
    let row = &run["mutations"][0];
    assert_eq!(row["status"], "killed", "{run:#}");
    // The baseline stops at 3, the mutant at 6: the first counts where the condition holds.
    let difference = &row["executed"][0]["difference"];
    assert_eq!(difference["path"], "n", "{difference:#}");
    assert_eq!(difference["left"]["value"]["document"], 3, "{difference:#}");
    assert_eq!(
        difference["right"]["value"]["document"], 6,
        "{difference:#}"
    );

    let output = project.kink("coverage", &["--corpus", "corpora/unknown"]);
    assert_status(&output, 2);
    let refused = json(&output);
    assert_eq!(refused["spec"]["stage"], "stop", "{refused:#}");
    assert_eq!(
        refused["spec"]["reason"], "stop-condition-unresolved",
        "{refused:#}"
    );
    let detail = refused["spec"]["detail"].as_str().unwrap();
    assert!(detail.contains("`Nothing`"), "{detail}");

    // Stopped before `tick` under the condition, the count alone does not say whether the step
    // is taken: from 0 the first arrival is a stop and no case takes the step, so `check` warns
    // that an edit of only its right-hand side changes no end; from 1 the run takes the step at
    // the arrivals where the condition fails, and it does not.
    for (corpus, hidden) in [("corpora/hidden", true), ("corpora/taken", false)] {
        assert_status(&project.kink("coverage", &["--corpus", corpus]), 0);
        let output = project.kink(
            "check",
            &[
                "--corpus",
                corpus,
                "--mutations",
                "kink/mutations/tick.toml",
            ],
        );
        let check = json(&output);
        assert_eq!(check["coverage"]["decides"], true, "{corpus}: {check:#}");
        let warnings = check["mutations"][0]["warnings"]
            .as_array()
            .unwrap_or_else(|| panic!("{check:#}"))
            .iter()
            .map(|warning| warning["reason"].as_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            warnings.contains(&"stop-hides-edit"),
            hidden,
            "{corpus}: {check:#}"
        );
    }
}

/// A stop condition evaluated in a named observer (`observer = "PACKAGE:DEFINITION"`): the
/// front end decodes each run's cells with the definition's declarations and evaluates the
/// observer's function, which the definition does not hold, on them; the identity names the
/// observer as written and its own Definition IR digest, not the definition's. The run of
/// `start = 0` ends after the tick that reaches 5, the first arrival where `Fifth` holds; a tick
/// that adds two reaches 10 first, so the mutation is killed.
#[test]
fn a_stop_condition_is_evaluated_in_its_named_observer() {
    let project = stopwatch();
    let observer = format!("{STOPWATCH_OBSERVER_PACKAGE}:main");
    let output = project.kink("coverage", &["--corpus", "corpora/observed"]);
    assert_status(&output, 0);
    let document = json(&output);
    let when = &document["stop"]["when"];
    assert_eq!(
        when["observer"]["definition"],
        observer.as_str(),
        "{when:#}"
    );
    assert!(
        when["function"]
            .as_str()
            .is_some_and(|path| path.ends_with("Fifth")),
        "{when:#}"
    );
    assert_eq!(
        document["stop"]["krs"]["when"],
        serde_json::json!({"function": "Fifth", "cells": ["n"], "observer": observer}),
        "{document:#}"
    );
    // The observer's digest, not the definition's, which a condition the definition itself
    // evaluates names.
    let baseline = json(&project.kink("coverage", &[]));
    let digest = &when["observer"]["definition_ir"];
    assert!(digest.is_string(), "{when:#}");
    assert_ne!(
        *digest, baseline["stop"]["when"]["observer"]["definition_ir"],
        "{when:#}"
    );
    let program = &document["programs"][0];
    assert_eq!(program["class"], "comparable", "{program:#}");

    let output = project.kink(
        "run",
        &[
            "--corpus",
            "corpora/observed",
            "--mutations",
            "kink/mutations/tick.toml",
        ],
    );
    let run = json(&output);
    let row = &run["mutations"][0];
    assert_eq!(row["status"], "killed", "{run:#}");
    let difference = &row["executed"][0]["difference"];
    assert_eq!(difference["left"]["value"]["document"], 5, "{difference:#}");
    assert_eq!(
        difference["right"]["value"]["document"], 10,
        "{difference:#}"
    );
}

/// A condition with no value at an arrival of the baseline's run (`Small` of 2) leaves the run
/// no evidence: the program is not judged, class `unknown` with the cause `stop-condition`, which
/// names the condition's refusal, and its result is not cached, so the next command runs it
/// again.
#[test]
fn a_baseline_run_whose_condition_has_no_value_is_not_judged_and_not_cached() {
    let project = stopwatch();
    for _ in 0..2 {
        let output = project.kink("coverage", &["--corpus", "corpora/partial"]);
        let document = json(&output);
        let program = &document["programs"][0];
        assert_eq!(program["class"], "unknown", "{program:#}");
        assert_eq!(program["cached"], false, "{program:#}");
        let cause = program["cause"].as_str().unwrap_or_default();
        assert!(cause.starts_with("stop-condition: "), "{program:#}");
        assert!(cause.contains("`Small` has no value"), "{program:#}");
        let not_cached = program["not_cached"].as_str().unwrap_or_default();
        assert!(not_cached.contains("stop condition"), "{program:#}");
    }
    let records = project.path().join("corpora/partial/.kink-flow/results");
    let written = walk_files(&records);
    assert!(written.is_empty(), "{written:?}");
}

/// A stop names a configuration rule of the root package, an item of a dependency crate and an
/// item K lowers to several rewrite rules exactly as `krs run --stop-after` names them: the front
/// end maps each to the K labels of the rules it selects, which the K kink-flow loads has, and
/// the run of the console ends at its second frame.
#[test]
fn a_stop_names_configuration_rules_and_a_dependencys_items_as_krs_run_does() {
    let project = console();
    let dependency = ["--dependency", "lang-core:main"];
    let output = project.kink("coverage", &dependency);
    assert_status(&output, 0);
    let document = json(&output);
    let stop = &document["stop"];
    // A configuration rule's label is written `rule [frame]:`, which K qualifies by the module.
    assert_eq!(strings(&stop["after"]), ["CONSOLE.frame"], "{stop:#}");
    assert_eq!(
        stop["krs"]["items"],
        serde_json::json!({"crate::frame": ["CONSOLE.frame"]}),
        "{stop:#}"
    );
    let program = &document["programs"][0];
    assert_eq!(program["class"], "comparable", "{program:#}");
    let end = &program["ends"][0];
    assert_eq!(end["halt"], "stop", "{program:#}");
    // After the second frame: the next tick's value is `1 + 1`, not yet evaluated.
    let head = end["head"]["text"].as_str().unwrap();
    assert!(head.contains("tick") && head.contains('+'), "{program:#}");

    let mut arguments = vec!["--corpus", "corpora/lang"];
    arguments.extend(dependency);
    let output = project.kink("check", &arguments);
    assert_status(&output, 0);
    let check = json(&output);
    let items = &check["stop"]["krs"]["items"];
    // A dependency's item by its crate name, and the context's heat and cool rules by its one
    // name.
    assert_eq!(
        items["lang::step"],
        serde_json::json!(["LANG.step"]),
        "{items:#}"
    );
    let context = strings(&items["lang::tick_value"]);
    assert_eq!(context.len(), 2, "{items:#}");
    assert!(
        context.iter().all(|label| label.starts_with("LANG.")),
        "{items:#}"
    );
    let mut labels = context.clone();
    labels.push("LANG.step");
    labels.sort_unstable();
    assert_eq!(strings(&check["stop"]["after"]), labels, "{check:#}");

    // A rule a document names is named as the stop names it: a dependency's item by its
    // library's crate name, the console's by `crate::`. `krs run --coverage` names the rules the run took by the
    // same strings.
    let items = document["families"]["rules"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|rule| rule["krs"]["item"].as_str())
        .collect::<std::collections::BTreeSet<_>>();
    for item in ["crate::frame", "lang::step", "lang::add"] {
        assert!(items.contains(item), "{item} in {items:?}");
    }
    // The language crate's items are named by its library's crate name, never by its package
    // name.
    assert!(
        !items.iter().any(|item| item.starts_with("lang_core::")),
        "{items:?}"
    );
    let output = project.krs(&[
        "run",
        "kink/cases/t0.op",
        "--dependency",
        "lang-core:main",
        "--stop-after",
        "crate::frame",
        "--stop-count",
        "2",
        "--coverage",
        "--output",
        "json",
    ]);
    assert_status(&output, 0);
    let run = json(&output);
    let covered = run["run"]["coverage"]["rules"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|rule| rule["committed"] == true)
        .filter_map(|rule| rule["item"].as_str())
        .collect::<std::collections::BTreeSet<_>>();
    for item in [
        "crate::frame",
        "lang::step",
        "lang::tick_value",
        "lang::add",
    ] {
        assert!(covered.contains(item), "{item} in {covered:?}");
    }
    // The context's heat and cool rules are K's, generated from the context sentence, which a
    // document lists as no rule; every other rule the run took is named by the same string.
    let covered = covered
        .into_iter()
        .filter(|item| *item != "lang::tick_value")
        .collect::<std::collections::BTreeSet<_>>();
    assert!(covered.is_subset(&items), "{covered:?} named in {items:?}");
}

/// The case documents of [`LEFT_OUT`]'s expectation corpora: `run(1)` ends in `done(2)` and
/// `run(2)` in `done(3)`, each `stuck` without a stop and stopped after `finish` with one.
fn expectation_files() -> Vec<(String, Vec<u8>)> {
    let flow = |stop: &str| {
        format!("[spec]\nkrs = {{ definition = \"main\" }}\n\n{stop}[[program]]\ncases = \"cases/*.toml\"\n")
            .into_bytes()
    };
    let mutation = b"[[mutation]]\nid = \"twice\"\nmisunderstanding = \"adds two\"\n\n  [[mutation.edit]]\n  rule = \"finish\"\n  find = \"+Int 1\"\n  replace = \"+Int 2\"\n";
    vec![
        ("src/lib.rs".to_owned(), LEFT_OUT.as_bytes().to_vec()),
        ("kink/FLOW.toml".to_owned(), flow("")),
        ("kink/mutations/finish.toml".to_owned(), mutation.to_vec()),
        (
            "kink/cases/runs.toml".to_owned(),
            br#"[[case]]
name = "met"
inputs = { pgm = { Run = { value = 1 } } }
expect = { halt = "stuck", cells = { k = { "$seq" = [{ Done = { value = 2 } }] }, regs = { a = 0 } } }

[[case]]
name = "unmet"
inputs = { pgm = { Run = { value = 2 } } }
expect = { halt = "stuck", compare = ["k"], cells = { k = { "$seq" = [{ Done = { value = 4 } }] } } }

[[case]]
"$data-file" = "data/more.json"
"#
            .to_vec(),
        ),
        (
            "kink/cases/data/more.json".to_owned(),
            br#"[{"name": "stopped", "inputs": {"pgm": {"Run": {"value": 3}}},
  "expect": {"halt": "stopped", "rule": "crate::finish", "compare": ["k"],
             "cells": {"k": {"$seq": [{"Done": {"value": 4}}]}}}}]"#
                .to_vec(),
        ),
        (
            "corpora/stopped/FLOW.toml".to_owned(),
            flow("[stop]\nafter = [\"crate::finish\"]\n\n"),
        ),
        (
            "corpora/stopped/cases/runs.toml".to_owned(),
            br#"[[case]]
name = "stopped"
inputs = { pgm = { Run = { value = 1 } } }
expect = { halt = "stopped", rule = "crate::finish", compare = ["k"], cells = { k = { "$seq" = [{ Done = { value = 2 } }] } } }

[[case]]
name = "undefined"
inputs = { pgm = { Run = { value = 2 } } }
expect = { halt = "undefined" }

[[case]]
name = "differs"
inputs = { pgm = { Run = { value = 3 } } }
expect = { halt = "stuck", compare = ["k"], cells = { k = { "$seq" = [{ Done = { value = 5 } }] } } }
"#
            .to_vec(),
        ),
        ("corpora/bad/FLOW.toml".to_owned(), flow("")),
        (
            "corpora/bad/cases/runs.toml".to_owned(),
            br#"[[case]]
name = "nope"
inputs = { pgm = { Run = { value = 1 } } }
expect = { halt = "stuck", cells = { nope = 1 } }

[[case]]
name = "depth"
inputs = { pgm = { Run = { value = 1 } } }
expect = { halt = "depth-bound", compare = ["k"], cells = { k = { "$seq" = [{ Done = { value = 2 } }] } } }
"#
            .to_vec(),
        ),
    ]
}

/// Each program row's id and its expectation's verdict.
fn verdicts(document: &Value) -> Vec<(String, Option<String>)> {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            (
                row["id"].as_str().unwrap().to_owned(),
                row["expectation"]["verdict"].as_str().map(str::to_owned),
            )
        })
        .collect()
}

/// The program row of `id`.
fn program_row(document: &Value, id: &str) -> Value {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == id)
        .unwrap()
        .clone()
}

/// A case document's named cases are programs `<path>#<name>`, and each case's expectation is
/// checked against its baseline run by KRS's comparison of ends and reported in its row: `met`,
/// `unmet` with the first difference by Rust field path (`expected` against `baseline`), or
/// `inconclusive` with why (an end stopped where the corpus has no stop). A baseline that misses
/// its own expectation is reported, and the case kept: it still kills the mutation, whose kill
/// is a difference from the baseline. Under `[stop]` the halt of a stuck end or of one stopped at
/// a stop rule is not observed: ends that agree on the compared cells are inconclusive, ends that
/// differ on them unmet, and the row says the halt was not compared; an expectation of a halt no
/// end of the truncated system has is unmet at the class, with the baseline's class left
/// unstated. `check` reports each expectation from the case's current result record, and refuses
/// a case whose expectation is no expectation of the definition.
#[test]
fn a_case_expectation_is_reported_and_its_case_kept() {
    let project = project_of(
        "krs-cli-kink-expectations",
        "EXPECTATIONS",
        &expectation_files(),
    );
    let output = project.kink("coverage", &[]);
    assert_status(&output, 1);
    let results = json(&output);
    let expected = [
        ("cases/runs.toml#met", "met"),
        ("cases/runs.toml#unmet", "unmet"),
        ("cases/runs.toml#stopped", "inconclusive"),
    ]
    .map(|(id, verdict)| (id.to_owned(), Some(verdict.to_owned())));
    assert_eq!(verdicts(&results), expected, "{results:#}");
    for id in ["cases/runs.toml#met", "cases/runs.toml#unmet"] {
        assert_eq!(
            program_row(&results, id)["class"],
            "comparable",
            "{results:#}"
        );
    }
    let met = program_row(&results, "cases/runs.toml#met")["expectation"].clone();
    assert_eq!(met["detail"], Value::Null, "{met:#}");
    assert_eq!(met["difference"], Value::Null, "{met:#}");
    let unmet = program_row(&results, "cases/runs.toml#unmet")["expectation"].clone();
    let difference = &unmet["difference"];
    assert_eq!(difference["format"], "krs-difference/3", "{unmet:#}");
    assert_eq!(difference["path"], "k[0].Done.value", "{unmet:#}");
    assert_eq!(difference["left"]["name"], "expected", "{unmet:#}");
    assert_eq!(difference["left"]["value"]["document"], 4, "{unmet:#}");
    assert_eq!(difference["right"]["name"], "baseline", "{unmet:#}");
    assert_eq!(difference["right"]["value"]["document"], 3, "{unmet:#}");
    assert_eq!(difference["right"]["class"]["halt"], "stuck", "{unmet:#}");
    let stopped = program_row(&results, "cases/runs.toml#stopped")["expectation"].clone();
    assert_eq!(
        stopped["detail"],
        "the expectation's end is stopped at `crate::finish`, and the corpus declares no [stop]: \
         kink runs every program as the corpus says",
        "{stopped:#}"
    );

    // The unmet case is kept: it kills the mutation as every other case does.
    let output = project.kink("run", &["--full"]);
    let run = json(&output);
    assert_eq!(run["mutations"][0]["status"], "killed", "{run:#}");
    assert_eq!(
        strings(&run["mutations"][0]["killed_by"]),
        [
            "cases/runs.toml#met",
            "cases/runs.toml#unmet",
            "cases/runs.toml#stopped"
        ],
        "{run:#}"
    );
    assert_eq!(verdicts(&run), expected, "{run:#}");

    // `check` runs nothing: it reads each case's current result record.
    let output = project.kink("check", &[]);
    assert_status(&output, 0);
    let check = json(&output);
    assert_eq!(check["version"], 13, "{check:#}");
    assert_eq!(results["result_cache"]["enabled"], true, "{results:#}");
    assert_eq!(verdicts(&check), expected, "{check:#}");

    expectations_under_a_stop(&project);
    a_refused_expectation(&project);
}

/// [`a_case_expectation_is_reported_and_its_case_kept`] under `[stop]`: the halt of a stuck end or
/// of one stopped at a stop rule is not observed, so ends that agree on the compared cells are
/// inconclusive and ends that differ on them unmet, and a halt no end of the truncated system has
/// differs at the class.
fn expectations_under_a_stop(project: &Project) {
    let output = project.kink("coverage", &["--corpus", "corpora/stopped"]);
    assert_status(&output, 1);
    let results = json(&output);
    assert_eq!(
        verdicts(&results),
        [
            ("cases/runs.toml#stopped", "inconclusive"),
            ("cases/runs.toml#undefined", "unmet"),
            ("cases/runs.toml#differs", "unmet"),
        ]
        .map(|(id, verdict)| (id.to_owned(), Some(verdict.to_owned()))),
        "{results:#}"
    );
    let detail = |id: &str| {
        program_row(&results, id)["expectation"]["detail"]
            .as_str()
            .unwrap()
            .to_owned()
    };
    let stopped = detail("cases/runs.toml#stopped");
    assert!(
        stopped.starts_with(
            "every end agrees with the expectation on the compared cells, but its halt is not \
             observed: under [stop] an end kink keeps is stuck or stopped at a rule of the stop, \
             and the ends do not say which"
        ),
        "{results:#}"
    );
    assert!(
        detail("cases/runs.toml#undefined").starts_with("the halt is compared: under [stop]"),
        "{results:#}"
    );
    assert!(
        detail("cases/runs.toml#differs").starts_with("the halt is not compared: under [stop]"),
        "{results:#}"
    );
    let undefined = program_row(&results, "cases/runs.toml#undefined")["expectation"].clone();
    assert_eq!(undefined["difference"]["at"], "class", "{undefined:#}");
    assert_eq!(
        undefined["difference"]["left"]["class"]["halt"], "undefined",
        "{undefined:#}"
    );
    assert_eq!(
        undefined["difference"]["right"].get("class"),
        None,
        "{undefined:#}"
    );
    let differs = program_row(&results, "cases/runs.toml#differs")["expectation"].clone();
    assert_eq!(
        differs["difference"]["path"], "k[0].Done.value",
        "{differs:#}"
    );
    assert_eq!(
        differs["difference"]["left"]["value"]["document"], 5,
        "{differs:#}"
    );
    assert_eq!(
        differs["difference"]["right"]["value"]["document"], 4,
        "{differs:#}"
    );
    assert_eq!(
        differs["difference"]["right"].get("class"),
        None,
        "{differs:#}"
    );
}

/// A definition whose cell `a` holds the input `a`, whose view `Positive` identifies the
/// positive `Int`s and whose view `OnlyZero` has a value at `0` only; `run(n)` steps to
/// `done(n + 1)`.
const VIEWED: &str = r#"use k::builtin::{Int, KSequence, int};
use k::{KItem, Term};

k::sorts! {
    Exp: KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("run({value})")] Run { value: Int },
    #[k::syntax("done({value})")] Done { value: Int },
}

#[k::rule]
fn finish(k::term![Cmd::Run { value }]: Term<Exp>) -> Term<Exp> {
    Cmd::Done(int::add(value, 1))
}

/// Whether an `Int` is positive, as `1` or `0`: a view that identifies different values.
#[k::function(total, internal)]
pub fn Positive(n: Term<Int>) -> Term<Int> {
    if n > 0 { 1 } else { 0 }
}

/// `1` at `0`, and no value elsewhere: a view defined at one value only.
#[k::function(partial, internal)]
#[k::requires(n.eq::<Int>(0))]
pub fn OnlyZero(n: Term<Int>) -> Term<Int> {
    1
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub a: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp, a: Int) -> Self {
        Self { k: k::k![pgm], a }
    }
}
"#;

/// The package of [`VIEWED`].
const VIEWED_PACKAGE: &str = "krs-cli-kink-views";

/// The observer of [`VIEWED`], a second package of its workspace that depends on it.
const VIEWED_OBSERVER_PACKAGE: &str = "krs-cli-kink-views-observe";

/// The observer's source: a view no semantics imports.
const VIEWED_OBSERVER: &str = r"//! An observer of the viewed definition, imported by no definition.

use k::Term;
use k::builtin::Int;

/// Whether an `Int` is below ten, as `1` or `0`.
#[k::function(total, internal)]
pub fn BelowTen(n: Term<Int>) -> Term<Int> {
    if n < 10 { 1 } else { 0 }
}
";

/// The files of [`VIEWED`]'s workspace and corpora: `kink/` holds expectations met and unmet
/// only through a view of the definition, one met only through the observer's, one met through
/// neither, since it names no view, one whose view has no value at the baseline's end, and one
/// of an end stopped at a rule, which the corpus has no `[stop]` to observe, decided before any
/// view is evaluated; `corpora/observer` names an
/// observer no package of the workspace is, `corpora/view` a view that is no function of the
/// definition, and `corpora/partial` a view without a value at the expected end.
fn viewed_files() -> Vec<(String, Vec<u8>)> {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
    let manifest = |name: &str, namespace: &str, dependencies: &str, workspace: &str| {
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n{workspace}"
        )
        .into_bytes()
    };
    let flow =
        b"[spec]\nkrs = { definition = \"main\" }\n\n[[program]]\ncases = \"cases/*.toml\"\n";
    let case = |name: &str, a: i64, expect: &str| {
        format!(
            "[[case]]\nname = \"{name}\"\ninputs = {{ pgm = {{ Run = {{ value = 1 }} }}, a = {a} }}\nexpect = {{ halt = \"stuck\", compare = [\"a\"], cells = {{ a = {expect} }}\n"
        )
    };
    let cases = [
        case("met", 1, "5 }, views = { a = \"Positive\" }"),
        case("unmet", -1, "5 }, views = { a = \"Positive\" }"),
        case(
            "observed",
            3,
            &format!("7 }}, views = {{ a = \"BelowTen\" }}, observer = \"{VIEWED_OBSERVER_PACKAGE}:main\""),
        ),
        case("unviewed", 1, "5 }"),
        case("partial", 1, "0 }, views = { a = \"OnlyZero\" }"),
        case("stopped", 1, "5 }, views = { a = \"Positive\" }").replace(
            "halt = \"stuck\"",
            "halt = \"stopped\", rule = \"crate::finish\"",
        ),
    ]
    .join("\n");
    vec![
        (
            "Cargo.toml".to_owned(),
            manifest(
                VIEWED_PACKAGE,
                "VIEWS",
                "",
                "\n[workspace]\nmembers = [\"observe\"]\nresolver = \"3\"\n",
            ),
        ),
        ("src/lib.rs".to_owned(), VIEWED.as_bytes().to_vec()),
        (
            "observe/Cargo.toml".to_owned(),
            manifest(
                VIEWED_OBSERVER_PACKAGE,
                "VIEWS-OBSERVE",
                &format!("viewed = {{ package = \"{VIEWED_PACKAGE}\", path = \"..\" }}\n"),
                "",
            ),
        ),
        (
            "observe/src/lib.rs".to_owned(),
            VIEWED_OBSERVER.as_bytes().to_vec(),
        ),
        ("kink/FLOW.toml".to_owned(), flow.to_vec()),
        ("kink/cases/views.toml".to_owned(), cases.into_bytes()),
        ("corpora/observer/FLOW.toml".to_owned(), flow.to_vec()),
        (
            "corpora/observer/cases/views.toml".to_owned(),
            case(
                "nowhere",
                1,
                "5 }, views = { a = \"Positive\" }, observer = \"no-such-package:main\"",
            )
            .into_bytes(),
        ),
        ("corpora/view/FLOW.toml".to_owned(), flow.to_vec()),
        (
            "corpora/view/cases/views.toml".to_owned(),
            case("nothing", 1, "5 }, views = { a = \"NoSuchView\" }").into_bytes(),
        ),
        ("corpora/partial/FLOW.toml".to_owned(), flow.to_vec()),
        (
            "corpora/partial/cases/views.toml".to_owned(),
            case("undefined", 0, "5 }, views = { a = \"OnlyZero\" }").into_bytes(),
        ),
    ]
}

/// The verdict word `krs run --case` gives `case` of `file` (relative to the package), from its
/// exit status: 0 met, 1 unmet, 3 inconclusive; and its stderr.
fn run_case_verdict(project: &Project, file: &str, case: &str) -> (Option<&'static str>, String) {
    let output = project.krs(&["run", "--case", file, "--case-name", case]);
    let verdict = match output.status.code() {
        Some(0) => Some("met"),
        Some(1) => Some("unmet"),
        Some(3) => Some("inconclusive"),
        _ => None,
    };
    (verdict, stderr(&output))
}

/// A case's expectation is checked with its views applied, as `krs run --case` checks it: a
/// view of the definition makes an expectation met or unmet that the cell's value alone would
/// not, a view of the observer the expectation names is evaluated there, and each verdict is the
/// one `krs run --case` gives and names the views it applied. A view without a value at the
/// baseline's end, which `krs run --case` refuses, makes the expectation inconclusive with that
/// refusal as its detail, and a verdict decided before any view is evaluated names none. A case
/// whose observer cannot be prepared, whose view names no function, or whose view has no value
/// at the expected end is refused, as `krs run --case` refuses it, with the same reason.
#[test]
fn a_case_expectation_is_checked_through_its_views_as_krs_run_checks_it() {
    let project = project_of("krs-cli-kink-views", "VIEWS", &viewed_files());
    let output = project.kink("coverage", &[]);
    assert_status(&output, 1);
    let results = json(&output);
    let expected = [
        ("met", "met"),
        ("unmet", "unmet"),
        ("observed", "met"),
        ("unviewed", "unmet"),
        ("partial", "inconclusive"),
        ("stopped", "inconclusive"),
    ];
    assert_eq!(
        verdicts(&results),
        expected
            .map(|(name, verdict)| (format!("cases/views.toml#{name}"), Some(verdict.to_owned()))),
        "{results:#}"
    );
    let [compared @ .., _, _] = expected;
    for (name, verdict) in compared {
        let (run, stderr) = run_case_verdict(&project, "kink/cases/views.toml", name);
        assert_eq!(run, Some(verdict), "krs run --case of `{name}`:\n{stderr}");
    }
    let row = |name: &str| program_row(&results, &format!("cases/views.toml#{name}"));
    assert_eq!(
        row("met")["expectation"]["detail"],
        "views: `a` = `Positive`",
        "{results:#}"
    );
    assert_eq!(
        row("observed")["expectation"]["detail"],
        format!("views: `a` = `BelowTen`, in `{VIEWED_OBSERVER_PACKAGE}:main`"),
        "{results:#}"
    );
    assert_eq!(row("unviewed")["expectation"]["detail"], Value::Null);
    // `OnlyZero` has a value at the expected `0` and none at the baseline's `1`: `krs run --case`
    // refuses the case, and kink, which admitted it, cannot check it.
    let partial = row("partial")["expectation"]["detail"]
        .as_str()
        .unwrap()
        .to_owned();
    assert!(
        partial.starts_with("the expectation cannot be checked: a view refuses the case")
            && partial.contains(
                "the view `OnlyZero` of the cell `a`: it has no value at the baseline end's `a`"
            ),
        "{results:#}"
    );
    let output = project.krs(&[
        "run",
        "--case",
        "kink/cases/views.toml",
        "--case-name",
        "partial",
    ]);
    assert_status(&output, 2);
    let refusal = stderr(&output);
    assert!(
        refusal.contains(
            "the view `OnlyZero` of the cell `a`: it has no value at the actual end's `a`"
        ),
        "{refusal}"
    );
    // An end stopped at a rule, under a corpus with no `[stop]`, is decided before any view is
    // evaluated: the detail names none.
    let stopped = row("stopped")["expectation"]["detail"]
        .as_str()
        .unwrap()
        .to_owned();
    assert!(
        stopped.starts_with(
            "the expectation's end is stopped at `crate::finish`, and the corpus declares no [stop]"
        ) && !stopped.contains("views"),
        "{results:#}"
    );
    let unmet = row("unmet")["expectation"].clone();
    let difference = &unmet["difference"];
    assert_eq!(difference["path"], "a", "{unmet:#}");
    assert_eq!(
        difference["views"],
        serde_json::json!({"a": "Positive"}),
        "{unmet:#}"
    );

    // `check` runs nothing: the stored results give the same verdicts.
    let output = project.kink("check", &[]);
    assert_status(&output, 0);
    let check = json(&output);
    assert_eq!(verdicts(&check), verdicts(&results), "{check:#}");

    viewed_refusals(&project);
}

/// [`a_case_expectation_is_checked_through_its_views_as_krs_run_checks_it`]: an observer that is
/// no package of the workspace, a view that is no function, and a view without a value at the
/// expected end refuse the case at admission under `krs kink`, and `krs run --case` refuses it
/// with the same reason.
fn viewed_refusals(project: &Project) {
    for (corpus, name, named) in [
        ("observer", "nowhere", "no-such-package"),
        ("view", "nothing", "NoSuchView"),
        ("partial", "undefined", "OnlyZero"),
    ] {
        let output = project.kink("check", &["--corpus", &format!("corpora/{corpus}")]);
        assert_status(&output, 2);
        let check = json(&output);
        let program = &check["programs"][0];
        assert_eq!(program["outcome"], "refused", "{check:#}");
        assert_eq!(program["reason"], "expectation-value", "{check:#}");
        let detail = program["detail"].as_str().unwrap();
        assert!(detail.contains(named), "{check:#}");
        let output = project.krs(&[
            "run",
            "--case",
            &format!("corpora/{corpus}/cases/views.toml"),
            "--case-name",
            name,
        ]);
        assert_status(&output, 2);
        let refusal = stderr(&output);
        assert!(refusal.contains(named), "{refusal}");
        if corpus != "observer" {
            // The same refusal of the view, after the position both name.
            let (_, reason) = detail.split_once("`expect.views`: ").unwrap();
            assert!(refusal.contains(reason), "{reason}\n{refusal}");
        }
    }
}

/// [`a_case_expectation_is_reported_and_its_case_kept`]: an expectation that is no expectation of
/// the definition refuses its case, an expectation of a `depth-bound` end among them, as
/// `krs run --case` refuses it, although no case's run has a depth bound under kink.
fn a_refused_expectation(project: &Project) {
    let output = project.kink("check", &["--corpus", "corpora/bad"]);
    assert_status(&output, 2);
    let check = json(&output);
    let programs = check["programs"].as_array().unwrap();
    assert_eq!(programs.len(), 2, "{check:#}");
    for (program, id, detail) in [
        (&programs[0], "cases/runs.toml#nope", "nope"),
        (
            &programs[1],
            "cases/runs.toml#depth",
            "`expect.halt`: an expected end is never `depth-bound`",
        ),
    ] {
        assert_eq!(program["id"], id, "{check:#}");
        assert_eq!(program["outcome"], "refused", "{check:#}");
        assert_eq!(program["reason"], "expectation-value", "{check:#}");
        assert!(
            program["detail"].as_str().unwrap().contains(detail),
            "{check:#}"
        );
        assert_eq!(
            program["expectation"]["verdict"], "inconclusive",
            "{check:#}"
        );
    }
}

/// A mutation that replaces an equation by an instance of itself only weakens the specification:
/// the reviewer's `plus_succ` narrowed to a nonzero second argument, with the same result on
/// every input it still covers, is `unkillable` with reason `weakening` and runs nothing: kink
/// reads each variable's sort from the loaded rule (KRS writes it, `N:Nat`), which is what lets
/// it read the narrowing as an instance. A `requires isNat ( N:Nat )` holds of every `Nat`, so it
/// narrows nothing: the mutant is the specification, `equivalent` with reason
/// `valid-condition`. `fuzz --kill` refuses both before any case, exit 2, with the row's status
/// and action: no case can change a fact of the axioms.
#[test]
fn a_narrowed_equation_of_the_story_is_unkillable() {
    let project = project_of("story-plus-narrow", "NAT", &story_files());
    project.write(
        "kink/narrowing.toml",
        "[[mutation]]\nid = \"needs-nonzero\"\nmisunderstanding = \"adds only to a nonzero number\"\n\n  \
         [[mutation.edit]]\n  rule = \"plus_succ\"\n  \
         find = \"plus ( s ( M:Nat ) , N:Nat ) => s ( plus ( M:Nat , N:Nat ) )\"\n  \
         replace = \"plus ( s ( M:Nat ) , s ( N:Nat ) ) => s ( plus ( M:Nat , s ( N:Nat ) ) )\"\n",
    );
    let output = project.kink("run", &["--mutations", "kink/narrowing.toml"]);
    assert_status(&output, 0);
    let document = json(&output);
    let rows = document["mutations"].as_array().unwrap();
    assert_eq!(rows.len(), 1, "{document:#}");
    let row = &rows[0];
    assert_eq!(row["id"], "needs-nonzero", "{row:#}");
    assert_eq!(row["status"], "unkillable", "{row:#}");
    assert_eq!(row["reason"], "weakening", "{row:#}");
    assert_eq!(row["executed"], serde_json::json!([]), "{row:#}");
    let weakening = row["weakening"].as_array().unwrap();
    assert_eq!(weakening.len(), 1, "{row:#}");
    assert_eq!(weakening[0]["label"], "nat--plus_succ", "{row:#}");
    assert_eq!(weakening[0]["head"], "plus", "{row:#}");
    assert_eq!(weakening[0]["kind"], "narrowed", "{row:#}");

    project.write(
        "kink/always.toml",
        mutation(
            "always-nat",
            "plus_succ",
            "s ( plus ( M:Nat , N:Nat ) )",
            "s ( plus ( M:Nat , N:Nat ) ) requires isNat ( N:Nat )",
        ),
    );
    let output = project.kink("run", &["--mutations", "kink/always.toml"]);
    assert_status(&output, 0);
    let document = json(&output);
    let row = &document["mutations"][0];
    assert_eq!(row["status"], "equivalent", "{row:#}");
    assert_eq!(row["reason"], "valid-condition", "{row:#}");
    assert_eq!(row["weakening"][0]["kind"], "valid-condition", "{row:#}");
    assert_eq!(row["executed"], serde_json::json!([]), "{row:#}");

    project.write(
        "kink/narrowing-templates.toml",
        "[[template]]\nid = \"t4-second\"\nprogram = \"t4\"\n\n  [[template.hole]]\n  name = \"B\"\n  \
         sort = \"Nat\"\n  find = \", s(zero))\"\n  literal = \"s(zero)\"\n  allow-refused-sort = true\n",
    );
    for (list, id, status) in [
        ("kink/narrowing.toml", "needs-nonzero", "unkillable"),
        ("kink/always.toml", "always-nat", "equivalent"),
    ] {
        let output = project.kink(
            "fuzz",
            &[
                "--mutations",
                list,
                "--templates",
                "kink/narrowing-templates.toml",
                "--template",
                "t4-second",
                "--kill",
                id,
            ],
        );
        assert_status(&output, 2);
        let document = json(&output);
        assert_eq!(document["stopped"], "refused", "{document:#}");
        assert_eq!(
            document["job"]["refusal"]["stage"], "mutation",
            "{document:#}"
        );
        assert_eq!(document["job"]["refusal"]["reason"], status, "{document:#}");
        assert_eq!(document["job"]["status"], status, "{document:#}");
        assert!(
            document["action"]
                .as_str()
                .unwrap()
                .contains("no search can kill this mutation (`krs kink run "),
            "{document:#}"
        );
    }
}

/// A status is a property of the loaded axiom: kink reads each variable's sort from the rule as
/// loaded, written or inferred, so the story's `plus_succ` narrowing written without sorts,
/// which loads to the mutant of the sorted narrowing (one digest, one identity), is `unkillable`
/// as that one is.
#[test]
fn a_narrowing_written_without_sorts_gets_the_sorted_narrowings_status() {
    let project = story();
    let cache = project.path().join("target/sorts-kink-cache");
    let cache = cache.to_str().unwrap();
    let plus_succ = "plus ( s ( M:Nat ) , N:Nat ) => s ( plus ( M:Nat , N:Nat ) )";
    project.write(
        "kink/sorts-mutations.toml",
        [
            mutation(
                "guide-pattern",
                "plus_succ",
                plus_succ,
                "plus ( s ( M:Nat ) , s ( N:Nat ) ) => s ( plus ( M:Nat , s ( N:Nat ) ) )",
            ),
            mutation(
                "unsorted",
                "plus_succ",
                plus_succ,
                "plus ( s ( M ) , s ( N ) ) => s ( plus ( M , s ( N ) ) )",
            ),
        ]
        .concat(),
    );
    let ran = project.kink(
        "run",
        &["--mutations", "kink/sorts-mutations.toml", "--cache", cache],
    );
    assert_status(&ran, 0);
    let document = json(&ran);
    let rows = document["mutations"].as_array().unwrap();
    let row = |id: &str| {
        rows.iter()
            .find(|row| row["id"] == id)
            .unwrap_or_else(|| panic!("no row {id}: {document:#}"))
    };
    let (sorted, unsorted) = (row("guide-pattern"), row("unsorted"));
    assert_eq!(sorted["digest"], unsorted["digest"], "{document:#}");
    assert_eq!(sorted["identity"], unsorted["identity"], "{document:#}");
    for narrowed in [sorted, unsorted] {
        assert_eq!(narrowed["status"], "unkillable", "{narrowed:#}");
        assert_eq!(narrowed["reason"], "weakening", "{narrowed:#}");
        assert_eq!(narrowed["executed"], serde_json::json!([]), "{narrowed:#}");
        assert_eq!(narrowed["weakening"], sorted["weakening"], "{narrowed:#}");
        assert_eq!(
            narrowed["weakening"][0]["label"], "nat--plus_succ",
            "{narrowed:#}"
        );
        assert_eq!(narrowed["weakening"][0]["kind"], "narrowed", "{narrowed:#}");
    }
    assert_eq!(rows.len(), 2, "{document:#}");
}

/// A case witnesses a mutation when its baseline run reaches a sentence the mutant changes,
/// whatever the mutant then does. `no-decrease` edits only `plus_succ`'s result, into one that
/// reuses its left-hand side's `s(M)` (which k-rust's compiler writes as an alias of the
/// left-hand side), and its mutant recurses without end: its witnesses are the cases that apply
/// `plus_succ`, `t3` and `t4`, never `t1` or `t2`, which apply only `plus_zero`, and it stays
/// `unknown` with the reason `stack-stop`. `shifted` edits `plus_succ`'s pattern: an equation
/// whose pattern changes can match terms no baseline run tried, so every case witnesses it
/// (`witnesses_global`), and `fuzz --kill` says so. Its mutant also narrows `plus_succ` through
/// a result the syntactic narrowing test does not read as an instance, so on `t4`,
/// `plus(s(s(zero)), s(zero))`, it ends stuck on `plus(s(zero), zero)`, which no equation of the
/// mutant reduces: the cause names that application and the mutation's reason is
/// `open-application`, still `unknown`, on a warm cache as on a cold one.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One run of two mutations and the fuzz job that reads it."
)]
fn witnesses_follow_coverage_and_an_open_application_names_the_unknown() {
    let project = story();
    let cache = project.path().join("target/witnesses-kink-cache");
    let cache = cache.to_str().unwrap();
    project.write(
        "kink/witnesses-mutations.toml",
        [
            mutation(
                "no-decrease",
                "plus_succ",
                "s ( plus ( M:Nat , N:Nat ) )",
                "s ( plus ( s ( M:Nat ) , N:Nat ) )",
            ),
            mutation(
                "shifted",
                "plus_succ",
                "plus ( s ( M:Nat ) , N:Nat ) => s ( plus ( M:Nat , N:Nat ) )",
                "plus ( s ( M:Nat ) , s ( N:Nat ) ) => s ( s ( plus ( M:Nat , N:Nat ) ) )",
            ),
        ]
        .concat(),
    );
    // `no-decrease` stops at the native stack's bound, a bound on work: the clock never decides
    // a run of the tests (R4-WALLCLOCK), so this copy of the story's corpus gives its runs a time
    // far above it.
    project.write(
        "corpora/witnesses/FLOW.toml",
        format!(
            "{STORY_FLOW}\n[budget]\n# the clock never decides a run of the tests (R4-WALLCLOCK)\ntime_ms = 600000\n"
        ),
    );
    for (id, text) in STORY_CASES {
        project.write(&format!("corpora/witnesses/cases/{id}.nat"), text);
    }
    let mutations = [
        "--corpus",
        "corpora/witnesses",
        "--mutations",
        "kink/witnesses-mutations.toml",
    ];
    let mut arguments = mutations.to_vec();
    arguments.extend(["--cache", cache]);
    let ran = project.kink("run", &arguments);
    assert_status(&ran, 3);
    let document = json(&ran);
    let rows = document["mutations"].as_array().unwrap();
    let row = |id: &str| {
        rows.iter()
            .find(|row| row["id"] == id)
            .unwrap_or_else(|| panic!("no row {id}: {document:#}"))
    };
    let no_decrease = row("no-decrease");
    assert_eq!(no_decrease["status"], "unknown", "{no_decrease:#}");
    assert_eq!(no_decrease["reason"], "stack-stop", "{no_decrease:#}");
    assert_eq!(
        strings(&no_decrease["witnesses"]),
        ["t3", "t4"],
        "{no_decrease:#}"
    );
    assert_eq!(no_decrease["witnesses_global"], false, "{no_decrease:#}");
    assert!(
        no_decrease["action"]
            .as_str()
            .unwrap()
            .contains("write the misunderstanding as a mutant that ends, or drop the mutation"),
        "{no_decrease:#}"
    );
    let shifted = row("shifted");
    assert_eq!(shifted["status"], "unknown", "{shifted:#}");
    assert_eq!(
        strings(&shifted["witnesses"]),
        ["t1", "t2", "t3", "t4"],
        "{shifted:#}"
    );
    assert_eq!(shifted["witnesses_global"], true, "{shifted:#}");
    assert_eq!(shifted["reason"], "open-application", "{shifted:#}");
    assert!(
        shifted["action"]
            .as_str()
            .unwrap()
            .contains("write the misunderstanding as a replacement"),
        "{shifted:#}"
    );
    let t4 = shifted["executed"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["program"] == "t4")
        .unwrap_or_else(|| panic!("t4 ran: {shifted:#}"));
    assert_eq!(t4["outcome"], "unknown", "{t4:#}");
    assert!(
        t4["cause"].as_str().unwrap().starts_with(
            "its stuck leaf at depth 0 holds `plus ( s(zero) , zero )`, an application of the \
             function `plus`, whose equations the mutation edits, that no equation of the mutant \
             reduces: the mutant leaves its value open there; "
        ) && t4["cause"].as_str().unwrap().ends_with(
            "the mutant's run: k-rust returned 1 leaf (stuck 1), the deepest at depth 0"
        ),
        "{t4:#}"
    );

    // The same inputs on the warm cache: t4's unknown comes from the outcome cache, whose record
    // keeps whether the program is undecided by an open application, so the reason and the
    // action are the cold run's.
    let again = project.kink("run", &arguments);
    assert_status(&again, 3);
    let again = json(&again);
    let warm = again["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == "shifted")
        .unwrap_or_else(|| panic!("no row shifted: {again:#}"));
    let cached = warm["executed"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["program"] == "t4")
        .unwrap_or_else(|| panic!("t4 listed: {warm:#}"));
    assert_eq!(cached["cached"], true, "{cached:#}");
    assert_eq!(cached["outcome"], "unknown", "{cached:#}");
    assert_eq!(cached["cause"], t4["cause"], "{cached:#}");
    assert_eq!(warm["reason"], "open-application", "{warm:#}");
    assert_eq!(warm["action"], shifted["action"], "{warm:#}");

    project.write(
        "kink/witnesses-templates.toml",
        "[[template]]\nid = \"t1-first\"\nprogram = \"t1\"\n\n  [[template.hole]]\n  name = \"M\"\n  \
         sort = \"Nat\"\n  find = \"(zero,\"\n  literal = \"zero\"\n  allow-refused-sort = true\n",
    );
    let mut arguments = mutations.to_vec();
    arguments.extend([
        "--cache",
        cache,
        "--templates",
        "kink/witnesses-templates.toml",
        "--template",
        "t1-first",
        "--kill",
        "shifted",
        "--cases",
        "2",
    ]);
    let output = project.kink("fuzz", &arguments);
    let document = json(&output);
    assert_eq!(document["schema"], "kink-flow-fuzz", "{document:#}");
    let last = &document["template"]["last_run"]["mutation"];
    assert_eq!(last["witnesses_global"], true, "{document:#}");
    let kinds = document["warnings"]
        .as_array()
        .unwrap()
        .iter()
        .map(|warning| warning["kind"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert!(kinds.contains(&"global-witnesses"), "{document:#}");
    assert!(!kinds.contains(&"template-not-a-witness"), "{document:#}");
}

/// The guide's corpus (`docs-site/story/plus/guide`): the introduction's cases and the case `t5`
/// that kills a survivor, with its two mutation lists, one of them holding the survivor `swap`.
const GUIDE_FILES: [(&str, &str); 8] = [
    (
        "guide/FLOW.toml",
        include_str!("../../../../docs-site/story/plus/guide/FLOW.toml"),
    ),
    (
        "guide/cases/t1.nat",
        include_str!("../../../../docs-site/story/plus/guide/cases/t1.nat"),
    ),
    (
        "guide/cases/t2.nat",
        include_str!("../../../../docs-site/story/plus/guide/cases/t2.nat"),
    ),
    (
        "guide/cases/t3.nat",
        include_str!("../../../../docs-site/story/plus/guide/cases/t3.nat"),
    ),
    (
        "guide/cases/t4.nat",
        include_str!("../../../../docs-site/story/plus/guide/cases/t4.nat"),
    ),
    (
        "guide/cases/t5.nat",
        include_str!("../../../../docs-site/story/plus/guide/cases/t5.nat"),
    ),
    (
        "guide/mutations/correlated.toml",
        include_str!("../../../../docs-site/story/plus/guide/mutations/correlated.toml"),
    ),
    (
        "guide/mutations/survivors.toml",
        include_str!("../../../../docs-site/story/plus/guide/mutations/survivors.toml"),
    ),
];

/// A private copy of the story package with its corpus, the story's three edits as the corpus's
/// own list, and the guide's corpus: the default lock is written into it, so no other test reads
/// it.
fn locked_story(package: &'static str) -> Project {
    let mut files = story_files();
    files.push((
        "kink/mutations/plus.toml".to_owned(),
        STORY_MUTATIONS.as_bytes().to_vec(),
    ));
    for (path, text) in GUIDE_FILES {
        files.push((path.to_owned(), text.as_bytes().to_vec()));
    }
    project_of(package, "NAT", &files)
}

/// The lock of the story's three edits naming `killers` (`plus/a`, `plus/b`, `plus/c`), in the
/// bytes `krs kink run` writes: the run's verdicts rendering without `killed_by`, under the Z3
/// profile krs links, whose header names the Z3 build (k-rust's `z3_build`).
fn story_lock(killers: [&str; 3]) -> String {
    use std::fmt::Write as _;
    let build = k_rust::backend::z3_build().expect("krs links Z3");
    let mut text = format!(
        "schema = \"kink-flow-verdicts\"\nversion = 12\ndocument = \"run\"\nprofile = \"z3\"\n\
         z3_version = \"{}\"\n",
        build.version
    );
    if let Some(digest) = &build.library_sha256 {
        let _ = writeln!(text, "z3_library_sha256 = \"{digest}\"");
    }
    text.push_str("\n[spec]\noutcome = \"admitted\"\n");
    for (id, killer) in ["plus/a", "plus/b", "plus/c"].into_iter().zip(killers) {
        let _ = write!(
            text,
            "\n[[mutation]]\nid = \"{id}\"\nstatus = \"killed\"\nkiller = \"{killer}\"\n"
        );
    }
    text
}

/// The programs of each call of the row `id` of a run document.
fn row_calls(document: &Value, id: &str) -> Vec<Vec<String>> {
    let row = document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("no row {id}: {document:#}"));
    row["calls"]
        .as_array()
        .unwrap()
        .iter()
        .map(|call| {
            strings(&call["programs"])
                .into_iter()
                .map(str::to_owned)
                .collect()
        })
        .collect()
}

/// `(id, status)` of every row of a run document.
fn row_statuses(document: &Value) -> Vec<(String, String)> {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            (
                row["id"].as_str().unwrap().to_owned(),
                row["status"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

/// FB-32 acceptance 4 on the corpus `corpus` (`[]` for `kink/`) in its current state: the
/// statuses of a first-kill run equal a `--full` run's, and the lock a `--full` run would write is
/// the first-kill run's (`--locked` finds it unchanged). Both runs leave the lock as it was.
fn assert_full_agrees(project: &Project, corpus: &[&str]) -> Value {
    let lock = corpus.get(1).map_or_else(
        || "kink/verdicts.lock".to_owned(),
        |dir| format!("{dir}/verdicts.lock"),
    );
    let before = project.read(&lock);
    let mut first_args = corpus.to_vec();
    first_args.push("--locked");
    let first = project.kink("run", &first_args);
    assert_status(&first, 0);
    let mut full_args = first_args.clone();
    full_args.push("--full");
    let full = project.kink("run", &full_args);
    assert_status(&full, 0);
    assert_eq!(
        json(&full)["lock"]["status"],
        "unchanged",
        "{:#}",
        json(&full)
    );
    assert_eq!(row_statuses(&json(&first)), row_statuses(&json(&full)));
    assert_eq!(project.read(&lock), before);
    json(&full)
}

/// FB-32 acceptance 1: a fresh checkout with a committed lock and no cache runs each killed
/// mutation's recorded killer alone (here `t4`, a valid killer that is not the search's first for
/// `plus/a` and `plus/b`), keeps it, and leaves the lock byte for byte; `run --output verdicts`
/// prints the lock's bytes, and a second run makes no call.
#[test]
fn a_recorded_killer_runs_alone_from_a_fresh_checkout() {
    let project = locked_story("story-plus-lock-fresh");
    let lock = story_lock(["t4", "t4", "t4"]);
    project.write("kink/verdicts.lock", &lock);
    // A checkout commits definition.k beside the lock.
    assert_status(&project.kink("emit", &[]), 0);
    assert!(!project.path().join("kink/.kink-flow").exists());
    let ran = project.kink("run", &["--locked"]);
    assert_status(&ran, 0);
    let document = json(&ran);
    assert_eq!(
        document["profile"], "z3",
        "the lock's header names krs's profile"
    );
    for row in document["mutations"].as_array().unwrap() {
        let id = row["id"].as_str().unwrap();
        assert_eq!(row_calls(&document, id), [["t4"]], "{id}");
        assert_eq!(
            (&row["killer"], &row["killer_source"], &row["killer_change"]),
            (&Value::from("t4"), &Value::from("record"), &Value::Null),
            "{id}"
        );
    }
    assert_eq!(document["lock"]["status"], "unchanged", "{document:#}");
    assert_eq!(document["lock"]["path"], "kink/verdicts.lock");
    assert_eq!(project.read("kink/verdicts.lock"), lock);
    let rendered = project.kink("run", &["--output", "verdicts", "--locked"]);
    assert_status(&rendered, 0);
    assert_eq!(stdout(&rendered), lock);
    let again = project.kink("run", &[]);
    assert_status(&again, 0);
    let again = json(&again);
    for id in ["plus/a", "plus/b", "plus/c"] {
        assert!(row_calls(&again, id).is_empty(), "{id}: {again:#}");
    }
    assert_eq!(project.read("kink/verdicts.lock"), lock);
    assert_full_agrees(&project, &[]);
}

/// FB-32 acceptance 2: on the guide's corpus, which holds the survivor `swap`, a killing case
/// prepended to `FLOW.toml` moves no killer: the lock is unchanged, no killed row runs the new
/// case, and the survivor runs only it. From a fresh cache each killed row runs its recorded
/// killer alone.
#[test]
fn prepending_a_killing_case_moves_no_killer() {
    let project = locked_story("story-plus-lock-prepend");
    let guide = ["--corpus", "guide"];
    let created = project.kink("run", &guide);
    assert_status(&created, 0);
    assert_eq!(json(&created)["lock"]["status"], "created");
    let lock = project.read("guide/verdicts.lock");
    let killers = json(&created)["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| row["status"] == "killed")
        .map(|row| {
            (
                row["id"].as_str().unwrap().to_owned(),
                row["killer"].as_str().unwrap().to_owned(),
            )
        })
        .collect::<Vec<_>>();
    assert!(
        killers.iter().any(|(id, _)| id == "survivors/one"),
        "{killers:?}"
    );
    // t0, `plus(s(zero), s(s(zero)))`, kills `survivors/one`, whose recorded killer is t5, and
    // comes first in the search's order.
    project.write("guide/cases/t0.nat", "plus(s(zero), s(s(zero)))\n");
    let flow = project.read("guide/FLOW.toml");
    project.write(
        "guide/FLOW.toml",
        flow.replacen(
            "[[program]]\nid = \"t1\"",
            "[[program]]\nid = \"t0\"\nfile = \"cases/t0.nat\"\n\n[[program]]\nid = \"t1\"",
            1,
        ),
    );
    let warm = project.kink("run", &guide);
    assert_status(&warm, 0);
    let warm = json(&warm);
    assert_eq!(warm["lock"]["status"], "unchanged", "{warm:#}");
    assert_eq!(project.read("guide/verdicts.lock"), lock);
    for (id, killer) in &killers {
        assert!(row_calls(&warm, id).is_empty(), "{id}: {warm:#}");
        let row = warm["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["id"] == id.as_str())
            .unwrap();
        assert_eq!(row["killer"], killer.as_str(), "{id}");
    }
    assert_eq!(row_calls(&warm, "survivors/swap"), [["t0"]]);
    // From a fresh cache, with the same lock.
    fs::remove_dir_all(project.path().join("guide/.kink-flow")).unwrap();
    let cold = project.kink("run", &guide);
    assert_status(&cold, 0);
    let cold = json(&cold);
    for (id, killer) in &killers {
        assert_eq!(row_calls(&cold, id), [[killer.clone()]], "{id}: {cold:#}");
    }
    assert_eq!(project.read("guide/verdicts.lock"), lock);
    // The premise: t0 kills `survivors/one`, so the unchanged lock is the record's choice and not
    // a corpus in which the prepended case kills nothing.
    let full = assert_full_agrees(&project, &guide);
    let one = full["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == "survivors/one")
        .unwrap();
    assert!(strings(&one["killed_by"]).contains(&"t0"), "{one:#}");
}

/// FB-32 acceptance 3: a recorded killer that leaves the corpus (a) or no longer kills (b) is
/// replaced by the first killer in the search's order, which is the first member of `--full`'s
/// `killed_by` that witnesses the edit; `plus/c`, which only t4 killed, survives. `run --locked`
/// names exactly the moved rows and exits 1; `run` rewrites the lock, and its diff is those rows.
#[test]
fn a_killer_that_stops_killing_or_leaves_is_replaced() {
    let story_flow = STORY_FLOW.to_owned();
    for (package, how) in [
        ("story-plus-lock-left", "not-in-corpus"),
        ("story-plus-lock-agrees", "no-longer-kills"),
    ] {
        let project = locked_story(package);
        project.write("kink/verdicts.lock", story_lock(["t4", "t4", "t4"]));
        match how {
            "not-in-corpus" => project.write(
                "kink/FLOW.toml",
                story_flow.replacen(
                    "\n[[program]]\nid = \"t4\"\nfile = \"cases/t4.nat\"\n",
                    "",
                    1,
                ),
            ),
            _ => project.write(
                "kink/cases/t4.nat",
                include_str!("../../../../docs-site/story/plus/kink/cases/t1.nat"),
            ),
        }
        assert_status(&project.kink("emit", &[]), 0);
        let full = project.kink("run", &["--full", "--mutations", "kink/mutations"]);
        assert_status(&full, 0);
        let full = json(&full);
        let first_witness = |id: &str| {
            let row = full["mutations"]
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["id"] == id)
                .unwrap();
            let witnesses = row["witnesses"].as_array().unwrap();
            row["killed_by"]
                .as_array()
                .unwrap()
                .iter()
                .find(|program| witnesses.contains(program))
                .cloned()
                .unwrap()
        };
        let stale = project.kink("run", &["--locked"]);
        assert_status(&stale, 1);
        let stale = json(&stale);
        assert_eq!(stale["lock"]["status"], "stale", "{package}");
        let changed = stale["lock"]["changes"]
            .as_array()
            .unwrap()
            .iter()
            .map(|change| change["mutation"].as_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(changed, ["plus/a", "plus/b", "plus/c"], "{package}");
        let ran = project.kink("run", &[]);
        assert_status(&ran, 0);
        let ran = json(&ran);
        assert_eq!(ran["lock"]["status"], "written", "{package}");
        for (id, killer) in [("plus/a", "t2"), ("plus/b", "t3")] {
            let row = ran["mutations"]
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["id"] == id)
                .unwrap();
            assert_eq!(row["killer"], killer, "{package} {id}");
            assert_eq!(row["killer"], first_witness(id), "{package} {id}");
            assert_eq!(row["killer_change"], how, "{package} {id}");
        }
        let survived = &ran["mutations"][2];
        assert_eq!(
            (&survived["id"], &survived["status"]),
            (&Value::from("plus/c"), &Value::from("survived")),
            "{package}"
        );
        let written = project.read("kink/verdicts.lock");
        assert_eq!(
            written,
            story_lock(["t2", "t3", "t4"]).replace(
                "id = \"plus/c\"\nstatus = \"killed\"\nkiller = \"t4\"\n",
                "id = \"plus/c\"\nstatus = \"survived\"\n"
            ),
            "{package}"
        );
        assert_full_agrees(&project, &[]);
    }
}

/// The front end's lock: `--locked` with no lock file is a finding (exit 1) and creates nothing;
/// a run of another list (`--mutations`) uses no lock and writes none beside either corpus.
#[test]
fn locked_without_a_lock_is_a_finding_and_mutations_use_no_lock() {
    let project = locked_story("story-plus-lock-absent");
    assert_status(&project.kink("emit", &[]), 0);
    let locked = project.kink("run", &["--locked"]);
    assert_status(&locked, 1);
    assert_eq!(json(&locked)["lock"]["status"], "stale");
    assert!(
        stderr(&locked).contains("kink/verdicts.lock: the header differs"),
        "{}",
        stderr(&locked)
    );
    assert!(!project.path().join("kink/verdicts.lock").exists());
    let other = project.kink("run", &["--mutations", "guide/mutations"]);
    assert_status(&other, 0);
    assert_eq!(json(&other)["lock"], Value::Null);
    for corpus in ["kink", "guide"] {
        assert!(
            !project.path().join(corpus).join("verdicts.lock").exists(),
            "{corpus}"
        );
    }
}
