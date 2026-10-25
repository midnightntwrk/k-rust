//! Golden test data (directories of cases, read-only; `k2lean/tests/goldens/`) as Lean test cases
//! for a generated project.
//!
//! The program text of each case is parsed by krust, whose `krun --depth 0` gives the initial
//! configuration as KORE; the expected final configuration is the KAST JSON recorded with K's LLVM
//! backend, which the generated tests compare with the Lean semantics' result.

use crate::convert::Conv;
use crate::ir::{self, Def};
use crate::model::Model;
use crate::rules;
use serde_json::Value;
use std::path::PathBuf;
use std::process::{Command, Stdio};

/// One recorded state of a trace: (depth, rendered Lean value, pattern).
type State = (usize, String, ir::P);

struct Opts {
    krust: String,
    definition: String,
    sort: String,
    goldens: Vec<PathBuf>,
    out: PathBuf,
    scratch: PathBuf,
    depths: Vec<(String, usize, usize)>,
    interpreter: Option<String>,
}

fn opts(rest: &[String]) -> Opts {
    let mut o = Opts {
        krust: String::new(),
        definition: String::new(),
        sort: "Stmt".into(),
        goldens: vec![],
        out: PathBuf::new(),
        scratch: std::env::temp_dir().join("k2lean-goldens"),
        depths: vec![],
        interpreter: None,
    };
    let mut it = rest.iter();
    while let Some(x) = it.next() {
        match x.as_str() {
            "--krust" => o.krust = it.next().unwrap().clone(),
            "--definition" => o.definition = it.next().unwrap().clone(),
            "--sort" => o.sort = it.next().unwrap().clone(),
            "--goldens" => o.goldens.push(it.next().unwrap().into()),
            "--lean-out" => o.out = it.next().unwrap().into(),
            "--scratch" => o.scratch = it.next().unwrap().into(),
            // K's LLVM backend `interpreter` of the same definition, kompiled by K: traces also
            // record its configuration after 0..N steps, from the same initial configuration
            "--interpreter" => o.interpreter = Some(it.next().unwrap().clone()),
            // `--depths NAME:N`: also record krust's configuration after 0..N steps of case NAME
            // `--depths NAME:N[:STRIDE]`: the configurations after 0, STRIDE, 2·STRIDE, … ≤ N steps
            "--depths" => {
                let v = it.next().unwrap();
                let parts: Vec<&str> = v.split(':').collect();
                let stride = parts.get(2).map(|x| x.parse().unwrap()).unwrap_or(1);
                o.depths
                    .push((parts[0].to_string(), parts[1].parse().unwrap(), stride));
            }
            other => panic!("unknown goldens argument {other}"),
        }
    }
    o
}

/// `env` is `VAR=VALUE` configuration-variable assignments separated by `;` (may be empty).
fn krun(o: &Opts, file: &PathBuf, env: &str, depth: usize) -> Result<String, String> {
    let mut cmd = Command::new(&o.krust);
    cmd.args([
        "krun",
        "--definition",
        &o.definition,
        "--depth",
        &depth.to_string(),
        "--sort",
        &o.sort,
    ]);
    for a in env.split(';').filter(|a| !a.is_empty()) {
        cmd.arg(format!("-c{a}"));
    }
    let out = cmd
        .arg(file)
        .stdin(Stdio::null())
        .output()
        .map_err(|e| e.to_string())?;
    if !out.status.success() {
        return Err(String::from_utf8_lossy(&out.stderr).to_string());
    }
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}

pub fn run(def: &Def, rest: &[String], ns: &str) {
    let o = opts(rest);
    let m = Model::build(def).unwrap();
    let conv = Conv::new(&m, def);
    let top = rules::top_sort(def).unwrap();
    std::fs::create_dir_all(&o.scratch).unwrap();
    let mut files: Vec<PathBuf> = Vec::new();
    for g in &o.goldens {
        let mut v: Vec<PathBuf> = std::fs::read_dir(g)
            .unwrap()
            .map(|e| e.unwrap().path())
            .collect();
        v.sort();
        files.extend(
            v.into_iter()
                .filter(|p| p.extension().is_some_and(|e| e == "json")),
        );
    }
    let mut cases = Vec::new();
    let mut traces = Vec::new();
    let mut state_defs: Vec<String> = Vec::new();
    let mut init_defs: Vec<String> = Vec::new();
    // the generated initial configuration (`init.rs`) against krust's: each initial configuration
    // krust builds is `init` at some values of the configuration variables
    let init_t = crate::init::of(def);
    let value = |p: &ir::P, sort: &str| conv.value(p, sort).ok().map(|l| l.render_arg());
    let check = |d: &str, actual: &ir::P| {
        init_t
            .as_ref()
            .map(|t| crate::init::check(t, def, d, actual, &value))
    };
    let mut init_checks: Vec<String> = Vec::new();
    let mut trace_checks: Vec<String> = Vec::new();
    for f in &files {
        let d: Value = serde_json::from_str(&std::fs::read_to_string(f).unwrap()).unwrap();
        let name = d["name"].as_str().unwrap().to_string();
        let group = f
            .parent()
            .unwrap()
            .file_name()
            .unwrap()
            .to_string_lossy()
            .to_string();
        let src = d["source"].as_str().unwrap();
        let env = format!("ENV={}", d["env"].as_str().unwrap());
        let env = env.as_str();
        let pf = o.scratch.join(format!("{name}.imp"));
        std::fs::write(&pf, src).unwrap();
        let init_kore = krun(&o, &pf, env, 0).unwrap_or_else(|e| panic!("{name}: krust: {e}"));
        let init_p = ir::pat(&k_rust_kore::kore::parser::parse_pattern(&init_kore).unwrap());
        let init = conv
            .value(&init_p, &top)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        let term = &d["krun"]["term"];
        let expected = if term.is_null() {
            let msg = d["krun"]["stderr"]
                .as_str()
                .unwrap_or("")
                .lines()
                .last()
                .unwrap_or("")
                .trim()
                .to_string();
            format!(".failure {}", crate::names::string_lit(&msg))
        } else {
            let p = conv
                .kast(term, &top)
                .unwrap_or_else(|e| panic!("{name}: {e}"));
            format!(
                ".config ({})",
                conv.value(&p, &top)
                    .unwrap_or_else(|e| panic!("{name}: {e}"))
                    .render()
            )
        };
        let gname = format!("goldenInit{}", cases.len());
        init_defs.push(format!("def {gname} : {top} :=\n  {}\n", init.render()));
        cases.push(format!(
            "  {{ name := {}, group := {}, init := {gname}, expected := {} }}",
            crate::names::string_lit(&name),
            crate::names::string_lit(&group),
            expected
        ));
        if let Some(c) = check(&gname, &init_p) {
            init_checks.push(c);
        }
        if let Some((_, k, stride)) = o.depths.iter().find(|(n, _, _)| *n == name) {
            let depths: Vec<usize> = (0..=*k).step_by(*stride).collect();
            let mut engines: Vec<(&str, Vec<State>)> = Vec::new();
            let mut states = Vec::new();
            for &depth in &depths {
                let s = krun(&o, &pf, env, depth).unwrap();
                let p = ir::pat(&k_rust_kore::kore::parser::parse_pattern(&s).unwrap());
                states.push((depth, conv.value(&p, &top).unwrap().render(), p));
            }
            engines.push(("krust", states));
            if let Some(interp) = &o.interpreter {
                let init_file = o.scratch.join(format!("{name}.init.kore"));
                std::fs::write(&init_file, &init_kore).unwrap();
                let mut states = Vec::new();
                for &depth in &depths {
                    let out_file = o.scratch.join(format!("{name}.llvm.{depth}.kore"));
                    // the interpreter appends to an existing output file
                    let _ = std::fs::remove_file(&out_file);
                    let st = Command::new(interp)
                        .arg(&init_file)
                        .arg(depth.to_string())
                        .arg(&out_file)
                        .stdin(Stdio::null())
                        .status()
                        .unwrap();
                    assert!(st.success(), "{name}: interpreter failed at depth {depth}");
                    let s = std::fs::read_to_string(&out_file).unwrap();
                    let p = ir::pat(&k_rust_kore::kore::parser::parse_pattern(&s).unwrap());
                    states.push((depth, conv.value(&p, &top).unwrap().render(), p));
                }
                engines.push(("K LLVM backend", states));
            }
            for (engine, states) in engines {
                let mut items = Vec::new();
                for (depth, st, kore) in states {
                    let dname = format!("state{}", state_defs.len());
                    if depth == 0
                        && let Some(c) = check(&dname, &kore)
                    {
                        trace_checks.push(c);
                    }
                    state_defs.push(format!("def {dname} : {top} :=\n  {st}\n"));
                    items.push(format!("({depth}, {dname})"));
                }
                traces.push(format!(
                    "  ({}, {}, [{}])",
                    crate::names::string_lit(&name),
                    crate::names::string_lit(engine),
                    items.join(", ")
                ));
            }
        }
    }
    let (init_import, init_doc) = if init_t.is_some() {
        (
            format!("import {ns}.Init\n"),
            "\n\nEach initial configuration is the generated `init` at some values of the configuration variables\n(`…_is_init`).",
        )
    } else {
        (String::new(), "")
    };
    let checks_text = |v: &[String]| {
        if v.is_empty() {
            String::new()
        } else {
            format!("\n{}", v.join(""))
        }
    };
    let traces_text = format!(
        "import {ns}\n{init_import}\n/-! Generated by `k2lean goldens` (do not edit): configurations after a number of steps,\n\
recorded with krust `krun --depth N` and K's LLVM backend `interpreter … N`, for step-by-step comparison.{init_doc} -/\n\n\
set_option maxRecDepth 100000\n\nnamespace {ns}Test\n\nopen {ns} KPrelude\n\n{}\n\
/-- (case, engine, [(steps, configuration)]) -/\ndef traces : List (String × String × List (Nat × {top})) := [\n{}]\n{}\nend {ns}Test\n",
        state_defs.join("\n"),
        traces.join(",\n"),
        checks_text(&trace_checks)
    );
    let traces_path = o.out.with_file_name("Traces.lean");
    std::fs::write(&traces_path, traces_text).unwrap();
    let text = format!(
        "import {ns}\n{init_import}\n/-! Generated by `k2lean goldens` from the golden cases (do not edit).\n\
Initial configurations: krust `krun --depth 0` on each case's program text.\n\
Expected: the final configuration K recorded (KAST JSON), or K's failure message.{init_doc} -/\n\n\
set_option maxRecDepth 100000\n\nnamespace {ns}Test\n\nopen {ns} KPrelude\n\n\
inductive Expected where\n  | config (c : {top})\n  | failure (message : String)\n\n\
structure Golden where\n  name : String\n  group : String\n  init : {top}\n  expected : Expected\n\n\
{}\n\
def goldens : List Golden := [\n{}]\n{}\nend {ns}Test\n",
        init_defs.join("\n"),
        cases.join(",\n"),
        checks_text(&init_checks)
    );
    std::fs::write(&o.out, text).unwrap();
    eprintln!("{} cases, {} traces", cases.len(), traces.len());
}

/// `configs --program NAME=FILE[@ENV] …`: named initial configurations for the run executable.
pub fn configs(def: &Def, rest: &[String], ns: &str) {
    let mut progs = Vec::new();
    let mut other = Vec::new();
    let mut it = rest.iter();
    while let Some(x) = it.next() {
        if x == "--program" {
            progs.push(it.next().unwrap().clone());
        } else {
            other.push(x.clone());
        }
    }
    let o = opts(&other);
    let m = Model::build(def).unwrap();
    let conv = Conv::new(&m, def);
    let top = rules::top_sort(def).unwrap();
    let mut items = Vec::new();
    let mut defs = Vec::new();
    for p in progs {
        let (name, spec) = p.split_once('=').unwrap();
        // NAME=FILE[@VAR=VALUE;…]
        let (file, env) = spec.split_once('@').unwrap_or((spec, ""));
        let k = krun(&o, &PathBuf::from(file), env, 0).unwrap_or_else(|e| panic!("{name}: {e}"));
        let pp = ir::pat(&k_rust_kore::kore::parser::parse_pattern(&k).unwrap());
        let v = conv.value(&pp, &top).unwrap();
        let dname: String = format!(
            "prog_{}",
            name.chars()
                .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
                .collect::<String>()
        );
        defs.push(format!("def {dname} : {top} :=\n  {}\n", v.render()));
        items.push(format!("  ({}, {dname})", crate::names::string_lit(name)));
    }
    let text = format!(
        "import {ns}.Rules\n\n/-! Generated by `k2lean configs` (do not edit): initial configurations from krust `krun --depth 0`. -/\n\n\
namespace {ns}Bench\n\nopen {ns}\n\n{}\ndef programs : List (String × {top}) := [\n{}]\n\nend {ns}Bench\n",
        defs.join("\n"),
        items.join(",\n")
    );
    std::fs::write(&o.out, text).unwrap();
}
