//! `cases`: test cases for a generated project from programs. Parsing and the expected results
//! come from krust: krust parses each program (`krun --depth 0`, with `--io off`, the
//! program's standard input buffered into `$STDIN`), and krust's own execution gives the
//! expected result: `krun` (one schedule, `--strategy any`) for a `run` case, `krun
//! --search-final --strategy all` (every final configuration) for a `search` case.
//!
//! `--case NAME=PROGRAM[@STDIN][!search[:BOUND]]`. With a bound, krust stops after BOUND
//! solutions and the Lean side checks that each is among its final configurations.

use crate::convert::Conv;
use crate::ir::{self, Def, P};
use crate::model::Model;
use crate::rules;
use std::path::PathBuf;
use std::process::{Command, Stdio};

struct Case {
    name: String,
    program: PathBuf,
    stdin: Option<PathBuf>,
    search: bool,
    bound: Option<usize>,
}

fn parse_case(s: &str) -> Case {
    let (name, rest) = s
        .split_once('=')
        .expect("--case NAME=PROGRAM[@STDIN][!search[:BOUND]]");
    let (rest, mode) = match rest.split_once('!') {
        Some((a, b)) => (a, Some(b)),
        None => (rest, None),
    };
    let (program, stdin) = match rest.split_once('@') {
        Some((p, i)) => (PathBuf::from(p), Some(PathBuf::from(i))),
        None => (PathBuf::from(rest), None),
    };
    let (search, bound) = match mode {
        None => (false, None),
        Some(m) => {
            let (kind, b) = m
                .split_once(':')
                .map(|(k, b)| (k, Some(b.parse().unwrap())))
                .unwrap_or((m, None));
            assert_eq!(kind, "search", "unknown case mode {kind}");
            (true, b)
        }
    };
    Case {
        name: name.to_string(),
        program,
        stdin,
        search,
        bound,
    }
}

fn krun(
    krust: &str,
    definition: &str,
    sort: &str,
    c: &Case,
    extra: &[&str],
) -> Result<String, String> {
    let mut cmd = Command::new(krust);
    cmd.args([
        "krun",
        "--definition",
        definition,
        "--sort",
        sort,
        "--io",
        "off",
    ])
    .args(extra)
    .arg(&c.program);
    let stdin = match &c.stdin {
        Some(p) => Stdio::from(std::fs::File::open(p).map_err(|e| e.to_string())?),
        None => Stdio::null(),
    };
    let out = cmd.stdin(stdin).output().map_err(|e| e.to_string())?;
    if !out.status.success() {
        return Err(String::from_utf8_lossy(&out.stderr).to_string());
    }
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}

/// The top-cell terms of a krust result (a configuration, or `\or` of search solutions).
fn configs(p: &P, top_sym: &str, out: &mut Vec<P>) {
    match p {
        P::App(f, _, _) if f == top_sym => out.push(p.clone()),
        P::App(_, _, args) | P::And(_, args) | P::Or(_, args) => {
            args.iter().for_each(|a| configs(a, top_sym, out))
        }
        P::Equals(_, _, a, b) | P::In(_, _, a, b) => {
            configs(a, top_sym, out);
            configs(b, top_sym, out);
        }
        _ => {}
    }
}

pub fn run(def: &Def, rest: &[String], ns: &str) {
    let mut krust = String::new();
    let mut definition = String::new();
    let mut sort = "Stmt".to_string();
    let mut out = PathBuf::new();
    let mut cases = Vec::new();
    let mut config_vars: Vec<String> = Vec::new();
    let mut it = rest.iter();
    while let Some(x) = it.next() {
        match x.as_str() {
            "--krust" => krust = it.next().unwrap().clone(),
            "--definition" => definition = it.next().unwrap().clone(),
            "--sort" => sort = it.next().unwrap().clone(),
            "--lean-out" => out = it.next().unwrap().into(),
            "--case" => cases.push(parse_case(it.next().unwrap())),
            // a configuration variable passed to every krun call (`-c NAME=VALUE`)
            "--config-var" => config_vars.extend(["-c".to_string(), it.next().unwrap().clone()]),
            other => panic!("unknown cases argument {other}"),
        }
    }
    let m = Model::build(def).unwrap();
    let conv = Conv::new(&m, def);
    let top = rules::top_sort(def).unwrap();
    // the top cell's constructor symbol
    let top_sym = m
        .sort(&top)
        .own
        .first()
        .cloned()
        .expect("top cell constructor");
    let mut defs = Vec::new();
    let mut items = Vec::new();
    // the generated initial configuration (`init.rs`) against krust's
    let init_t = crate::init::of(def);
    let value = |p: &ir::P, sort: &str| conv.value(p, sort).ok().map(|l| l.render_arg());
    let mut checks: Vec<String> = Vec::new();
    for (ci, c) in cases.iter().enumerate() {
        let mut d0: Vec<&str> = config_vars.iter().map(|s| s.as_str()).collect();
        d0.extend(["--depth", "0"]);
        let init = krun(&krust, &definition, &sort, c, &d0)
            .unwrap_or_else(|e| panic!("{}: krust: {e}", c.name));
        let ip = ir::pat(&k_rust_kore::kore::parser::parse_pattern(&init).unwrap());
        let iv = conv
            .value(&ip, &top)
            .unwrap_or_else(|e| panic!("{}: {e}", c.name));
        defs.push(format!("def init{ci} : {top} :=\n  {}\n", iv.render()));
        if let Some(t) = &init_t {
            checks.push(crate::init::check(
                t,
                def,
                &format!("init{ci}"),
                &ip,
                &value,
            ));
        }
        let mut extra: Vec<String> = config_vars.clone();
        if c.search {
            extra.extend([
                "--search-final".to_string(),
                "--strategy".into(),
                "all".into(),
            ]);
            if let Some(b) = c.bound {
                extra.extend(["--search-bound".to_string(), b.to_string()]);
            }
        }
        let extra_ref: Vec<&str> = extra.iter().map(|s| s.as_str()).collect();
        let res = krun(&krust, &definition, &sort, c, &extra_ref)
            .unwrap_or_else(|e| panic!("{}: krust: {e}", c.name));
        let rp = ir::pat(&k_rust_kore::kore::parser::parse_pattern(&res).unwrap());
        let mut finals = Vec::new();
        configs(&rp, &top_sym, &mut finals);
        let mut names = Vec::new();
        for (j, f) in finals.iter().enumerate() {
            let v = conv
                .value(f, &top)
                .unwrap_or_else(|e| panic!("{}: {e}", c.name));
            defs.push(format!(
                "def expected{ci}_{j} : {top} :=\n  {}\n",
                v.render()
            ));
            names.push(format!("expected{ci}_{j}"));
        }
        let mode = match (c.search, c.bound) {
            (false, _) => ".run".to_string(),
            (true, None) => ".search none".to_string(),
            (true, Some(b)) => format!(".search (some {b})"),
        };
        items.push(format!(
            "  {{ name := {}, init := init{ci}, mode := {mode}, expected := [{}] }}",
            crate::names::string_lit(&c.name),
            names.join(", ")
        ));
        eprintln!("case {}: {} krust result(s)", c.name, finals.len());
    }
    let (init_import, init_doc) = if init_t.is_some() {
        (
            format!("import {ns}.Init\n"),
            "\nEach initial configuration is the generated `init` at some values of the configuration variables\n(`init…_is_init`).",
        )
    } else {
        (String::new(), "")
    };
    let checks = if checks.is_empty() {
        String::new()
    } else {
        format!("\n{}", checks.join(""))
    };
    let text = format!(
        "import {ns}\n{init_import}\n/-! Generated by `k2lean cases` (do not edit): initial configurations from krust\n\
`krun --depth 0 --io off`; expected results from krust `krun --io off` (one schedule) or\n\
`krun --io off --search-final --strategy all` (every final configuration).{init_doc} -/\n\n\
set_option maxRecDepth 100000\n\nnamespace {ns}Test\n\nopen {ns} KPrelude\n\n\
inductive Mode where\n  | run\n  /-- every final configuration; with a bound, krust's first solutions only -/\n  | search (bound : Option Nat)\n\n\
structure Case where\n  name : String\n  init : {top}\n  mode : Mode\n  expected : List {top}\n\n{}\n\
def cases : List Case := [\n{}]\n{checks}\nend {ns}Test\n",
        defs.join("\n"),
        items.join(",\n")
    );
    std::fs::write(&out, text).unwrap();
}

/// The `lake test` driver for case files: runs and breadth-first searches over `successors`.
pub fn test_main(ns: &str, top: &str) -> String {
    format!(
        r#"import {ns}Test.Cases
import {ns}Test.Axioms
import Std.Data.TreeSet

/-! Generated by k2lean; do not edit. `lake test`: every case through the generated semantics.
A `run` case follows `step` (the first defined rule and match, as krust `--strategy any`); a
`search` case explores `successors` breadth first, without duplicates, and collects the
configurations without successors. Each final configuration is printed (`FINAL name: …`) for
the acceptance script. -/

namespace {ns}Test

open {ns} KPrelude

def runFuel : Nat := 100000000
def maxStates : Nat := 2000000

def statusStr : Status → String
  | .final => "final"
  | .stuck => "stuck"
  | .undefined r => s!"undefined step (rule {{r}})"
  | .outOfFuel => "out of fuel"

/-- Breadth-first search, one level per unit of fuel: (final configurations, states visited,
complete?). -/
def bfs (enough : List {top} → Bool) : Nat → List {top} → Std.TreeSet {top} cmp_{top} → List {top} → Nat → List {top} × Nat × Bool
  | _, [], _, finals, n => (finals.reverse, n, true)
  | 0, _, _, finals, n => (finals.reverse, n, false)
  | fuel + 1, frontier, seen, finals, n =>
    if n > maxStates || enough finals then (finals.reverse, n, false) else
    let (next, seen, finals, n) := frontier.foldl (fun (acc : List {top} × Std.TreeSet {top} cmp_{top} × List {top} × Nat) c =>
      let (next, seen, finals, n) := acc
      let ss := {ns}.successors c
      -- a leaf where a rule applies but every result is undefined (`⊥`) has no successor and
      -- is not a final configuration (krust reports it as an undefined step)
      let finals := if ss.isEmpty && step c == .stuck then c :: finals else finals
      let (next, seen) := ss.foldl (fun (p : List {top} × Std.TreeSet {top} cmp_{top}) s =>
        if p.2.contains s then p else (s :: p.1, p.2.insert s)) (next, seen)
      (next, seen, finals, n + 1)) ([], seen, finals, n)
    bfs enough fuel next.reverse seen finals n

def testMain : IO UInt32 := do
  let mut failed := 0
  for c in cases do
    match c.mode with
    | .run =>
      let t0 ← IO.monoNanosNow
      let r := run runFuel c.init
      let t1 ← IO.monoNanosNow
      IO.println s!"FINAL {{c.name}}: {{toK_{top} r.config}}"
      -- no krust result: krust found the step undefined (a rule applied with a `⊥` result)
      let ok := if c.expected.isEmpty then (match r.status with | .undefined _ => true | _ => false)
        else (r.status == .stuck) && c.expected.any (· == r.config)
      if !ok then failed := failed + 1
      IO.println s!"{{if ok then "PASS" else "FAIL"}} {{c.name}} (run): {{r.steps}} steps, {{statusStr r.status}}, equal to krust: {{c.expected.any (· == r.config)}}, {{(t1 - t0) / 1000000}} ms"
    | .search bound =>
      let t0 ← IO.monoNanosNow
      -- with a bound (krust stopped after that many solutions) the search stops once krust's
      -- solutions are all found
      let enough := fun (fs : List {top}) => bound.isSome && c.expected.all fun e => fs.any (· == e)
      let (finals, n, complete) := bfs enough maxStates [c.init] (Std.TreeSet.empty.insert c.init) [] 0
      let t1 ← IO.monoNanosNow
      for f in finals do
        IO.println s!"FINAL {{c.name}}: {{toK_{top} f}}"
      let found := c.expected.all fun e => finals.any (· == e)
      let same := found && (bound.isSome || finals.all fun f => c.expected.any (· == f))
      let ok := same && (complete || bound.isSome)
      if !ok then failed := failed + 1
      IO.println s!"{{if ok then "PASS" else "FAIL"}} {{c.name}} (search): {{n}} states, {{finals.length}} final, krust {{c.expected.length}}, krust's among ours: {{found}}, same set: {{same}}, complete: {{complete}}, {{(t1 - t0) / 1000000}} ms"
  if failed == 0 then IO.println "PASS" else IO.println s!"FAIL ({{failed}})"
  return if failed == 0 then 0 else 1

end {ns}Test

def main : IO UInt32 := {ns}Test.testMain
"#
    )
}
