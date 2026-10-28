//! `k2lean new-invariant`: the skeleton of a kind 2 invariant (a predicate written in Lean over a
//! generated library's configurations; `k2lean/docs/invariants.md`, part 3), and stubs for the rule cases
//! that `k2l_preserve` did not close.
//!
//! The project it writes is a Lake package that requires the generated library and the prelude,
//! with three hand-written modules:
//! - `NAME/Invariant.lean`: the predicate `Invariant` (a placeholder `True` to replace) and the
//!   definitions and lemmas it is made of;
//! - `NAME/Cases.lean`: the namespace `NAME.hand`, one theorem `NAME.hand.r : Step.Case.r P` per
//!   rule `r` whose case needs a hand proof, each in its own marked section; then
//!   `NAME.preserved : Preserved Step Invariant` by `k2l_preserve … hand NAME.hand`, which takes
//!   the hand cases by name and closes the other rules' cases with its closers;
//! - `NAME/Run.lean`: `init_holds` (the predicate at the generated `init`) and the corollaries
//!   `star` and `stepsN` (every configuration reachable from `init`), under the axiom guard.
//!
//! Nothing in it is regenerated: every file is the user's once written, and the command never
//! overwrites one. A hand case is stated by reference to the generated `Step.Case.r`, so after
//! a K edit and a regeneration of the library the same files state the new cases; `k2lean diff`
//! says which hand cases to revisit.
//!
//! `--from-log BUILD.log` reads the `k2l_preserve` lines of a build of the project and, for each
//! rule left open that has no hand case yet, inserts a stub into `Cases.lean` above its marker
//! line: the statement, the introduction of the rule's variables and side conditions under their
//! generated names, and `done`, which fails with the goal still to prove (no `sorry`).

use crate::casediff::{self, Case};
use std::path::{Component, Path, PathBuf};

const MARKER: &str = "-- k2lean new-invariant --from-log: new hand cases go above this line";

struct Lib {
    dir: PathBuf,
    ns: String,
    top: String,
    cases: Vec<Case>,
    /// `init`'s parameters, `(name, sort)`, when the library has `Init.lean`.
    init: Option<Vec<(String, String)>>,
    prelude: Option<PathBuf>,
}

fn read(p: &Path) -> Result<String, String> {
    std::fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()))
}

fn load_lib(dir: &Path) -> Result<Lib, String> {
    let lake = read(&dir.join("lakefile.lean"))?;
    let ns = lake
        .lines()
        .find_map(|l| l.strip_prefix("package "))
        .map(|l| {
            l.trim_end_matches(" where")
                .trim()
                .trim_start_matches('«')
                .trim_end_matches('»')
                .to_string()
        })
        .ok_or_else(|| format!("{}: no `package`", dir.display()))?;
    let prelude = lake
        .lines()
        .find_map(|l| l.strip_prefix("require k2lean from \""))
        .map(|l| dir.join(l.trim_end_matches('"')));
    let g = casediff::load(dir)?;
    if g.ns != ns {
        return Err(format!(
            "{}: the package is {ns} but Preserves.lean is in namespace {}",
            dir.display(),
            g.ns
        ));
    }
    let top = g
        .cases
        .first()
        .map(|c| c.top.clone())
        .ok_or_else(|| format!("{}: no rules", dir.display()))?;
    let init = match std::fs::read_to_string(dir.join(&ns).join("Init.lean")) {
        Ok(t) => {
            let l = t
                .lines()
                .find(|l| l.starts_with("def init"))
                .ok_or("Init.lean: no `def init`")?;
            let toks = casediff::tokens(l);
            let mut ps = Vec::new();
            let mut i = 2;
            while toks.get(i).map(|t| t.as_str()) == Some("(") {
                let close = toks[i..]
                    .iter()
                    .position(|t| t == ")")
                    .map(|k| i + k)
                    .ok_or("Init.lean: unbalanced")?;
                ps.push((toks[i + 1].clone(), toks[i + 3..close].join(" ")));
                i = close + 1;
            }
            Some(ps)
        }
        Err(_) => None,
    };
    Ok(Lib {
        dir: dir.to_path_buf(),
        ns,
        top,
        cases: g.cases,
        init,
        prelude,
    })
}

/// `to` relative to the directory `from` (both made absolute).
fn relative(from: &Path, to: &Path) -> PathBuf {
    let a = std::fs::canonicalize(from).unwrap_or_else(|_| from.to_path_buf());
    let b = std::fs::canonicalize(to).unwrap_or_else(|_| to.to_path_buf());
    let ac: Vec<Component> = a.components().collect();
    let bc: Vec<Component> = b.components().collect();
    let common = ac.iter().zip(&bc).take_while(|(x, y)| x == y).count();
    let mut out = PathBuf::new();
    for _ in common..ac.len() {
        out.push("..");
    }
    for c in &bc[common..] {
        out.push(c.as_os_str());
    }
    out
}

fn quote_rel(p: &Path) -> String {
    let s = p.to_string_lossy().to_string();
    if s.is_empty() { ".".into() } else { s }
}

/// Lean keywords that a generated variable name could collide with.
fn binder(n: &str) -> String {
    const KW: &[&str] = &[
        "at", "by", "do", "fun", "from", "have", "if", "in", "let", "match", "then", "else",
        "with", "show", "where", "end", "this", "λ", "Type", "Prop", "Sort",
    ];
    if KW.contains(&n) {
        format!("«{n}»")
    } else {
        n.to_string()
    }
}

fn display(n: &str) -> &str {
    n.trim_start_matches('«').trim_end_matches('»')
}

pub struct Skeleton {
    pub files: Vec<(PathBuf, String)>,
}

fn skeleton(
    lib: &Lib,
    name: &str,
    lib_rel: &Path,
    prelude_rel: &Path,
    toolchain: &str,
) -> Skeleton {
    let ns = &lib.ns;
    let top = format!("{ns}.{}", lib.top);
    let n_rules = lib.cases.len();
    let mut files = Vec::new();
    files.push((PathBuf::from("lean-toolchain"), toolchain.to_string()));
    files.push((
        PathBuf::from("lakefile.lean"),
        format!(
            "import Lake\nopen Lake DSL\n\n/-- A kind 2 invariant of `{ns}`: a predicate written in Lean, proved to be kept by every rule\n(skeleton written by `k2lean new-invariant`; every file is hand-written from here on). -/\npackage «{name}» where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n\nrequire k2lean from \"{}\"\nrequire «{ns}» from \"{}\"\n\n@[default_target]\nlean_lib {name}\n",
            quote_rel(prelude_rel),
            quote_rel(lib_rel)
        ),
    ));
    files.push((
        PathBuf::from(format!("{name}.lean")),
        format!("import {name}.Invariant\nimport {name}.Cases\nimport {name}.Run\n"),
    ));
    files.push((
        PathBuf::from(format!("{name}/Invariant.lean")),
        format!(
            "import {ns}.Rules\n\n/-!\n# The invariant (kind 2 layout: `Invariant.lean`)\n\nHAND-WRITTEN, stable under edits of the K rules. `Invariant` is a predicate on the configurations\nof `{ns}`. Replace the placeholder `True` by the property that every run should keep, and put\nhere the definitions it is made of and the lemmas that say how it computes: they are the\nunfolding set of `k2l_preserve` in `Cases.lean`.\n\nOnly inductive invariants are proved rule by rule: when a rule's case is false at a\nconfiguration that satisfies `Invariant` but is not reachable, strengthen `Invariant`.\n`Preserved` says nothing about a step whose result is undefined, since it has no successor.\n-/\n\nnamespace {name}\n\nopen KPrelude\n\n/-- The invariant (placeholder: replace `True`). -/\ndef Invariant : {top} → Prop := fun _ => True\n\nend {name}\n"
        ),
    ));
    files.push((
        PathBuf::from(format!("{name}/Cases.lean")),
        format!(
            "import {name}.Invariant\nimport {ns}.Preserves\nimport KPrelude.InvTactic\nimport KPrelude.InvColl\n\n/-!\n# Every rule of `{ns}` keeps `Invariant` (kind 2 layout: `Cases.lean`)\n\nHAND-WRITTEN. `preserved` applies the generated `{ns}.Step.preserves_of` ({n_rules} rules) through\n`k2l_preserve … hand {name}.hand`: the case of rule `r` is the theorem `{name}.hand.r` below when it\nexists, and the tactic's closers prove it otherwise. A build logs\n`k2l_preserve: N of M rules closed; hand: [...]; open: [...]`; each rule in `open` is an\n`unsolved goals` error tagged by the rule, showing its goal `P lhs → P rhs` with the rule's\nvariables and side conditions in context. Give the closers more lemmas\n(`k2l_preserve [l₁, …] split [f, …] hand …`), or prove the case by hand below:\n`k2lean new-invariant --lib … --out … --from-log BUILD.log` adds a stub per open rule.\n\nA hand case is stated as the generated `{ns}.Step.Case.r Invariant`, by reference, so an edit of\nrule `r` changes what its hand case must prove and nothing else here; `k2lean diff OLD NEW --hand\nTHIS_PROJECT` lists the hand cases to revisit after a regeneration.\n-/\n\nnamespace {name}\n\nopen KPrelude\n\nnamespace hand\n\n{MARKER}\nend hand\n\n/-- Every rule of `{ns}` keeps `Invariant`. -/\ntheorem preserved : Preserved {ns}.Step Invariant := by\n  k2l_preserve hand {name}.hand\n\nend {name}\n"
        ),
    ));
    let run = match &lib.init {
        Some(ps) => {
            let params: Vec<String> = ps
                .iter()
                .map(|(n, s)| format!("({} : {ns}.{s})", binder(n)))
                .collect();
            let implicit: Vec<String> = ps
                .iter()
                .map(|(n, s)| format!("{{{} : {ns}.{s}}}", binder(n)))
                .collect();
            let args: Vec<String> = ps.iter().map(|(n, _)| binder(n)).collect();
            let vars = ps
                .iter()
                .map(|(n, _)| format!("`{n}`"))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "import {name}.Cases\nimport {ns}.Init\nimport KPrelude.InvSteps\nimport KPrelude.Tactic\n\n/-!\n# Every run keeps `Invariant` (kind 2 layout: `Run.lean`)\n\nHAND-WRITTEN, stable under edits of the K rules (it depends on the configuration declaration\nonly, through the generated `{ns}.init`). `init_holds` is `Invariant` at the initial configuration\nfor the configuration variables {vars}; add the hypotheses on them that it needs (krust accepts any\nvalue of their sorts). `star` and `stepsN` extend it to every configuration reachable from there.\n-/\n\nnamespace {name}\n\nopen KPrelude\n\n/-- The initial configuration satisfies `Invariant`. -/\ntheorem init_holds {} : Invariant ({ns}.init {}) :=\n  trivial\n\n/-- Every configuration reachable from the initial configuration satisfies `Invariant`. -/\ntheorem star {} {{c : {top}}} (h : Star {ns}.Step ({ns}.init {}) c) : Invariant c :=\n  preserved.star h (init_holds {})\n\n/-- Every configuration reached in `n` steps from the initial configuration satisfies `Invariant`. -/\ntheorem stepsN {} {{n : Nat}} {{c : {top}}} (h : StepsN {ns}.Step n ({ns}.init {}) c) : Invariant c :=\n  preserved.stepsN h (init_holds {})\n\n#k2l_assert_axioms preserved init_holds star stepsN\n\nend {name}\n",
                params.join(" "),
                args.join(" "),
                implicit.join(" "),
                args.join(" "),
                args.join(" "),
                implicit.join(" "),
                args.join(" "),
                args.join(" "),
            )
        }
        None => format!(
            "import {name}.Cases\nimport KPrelude.InvSteps\nimport KPrelude.Tactic\n\n/-!\n# Every run keeps `Invariant` (kind 2 layout: `Run.lean`)\n\nHAND-WRITTEN. `{ns}` has no generated `init` (the generator's note says why), so the corollaries\nstart from any configuration that satisfies `Invariant`.\n-/\n\nnamespace {name}\n\nopen KPrelude\n\ntheorem star {{c₀ c : {top}}} (h₀ : Invariant c₀) (h : Star {ns}.Step c₀ c) : Invariant c :=\n  preserved.star h h₀\n\ntheorem stepsN {{c₀ c : {top}}} {{n : Nat}} (h₀ : Invariant c₀) (h : StepsN {ns}.Step n c₀ c) : Invariant c :=\n  preserved.stepsN h h₀\n\n#k2l_assert_axioms preserved star stepsN\n\nend {name}\n"
        ),
    };
    files.push((PathBuf::from(format!("{name}/Run.lean")), run));
    Skeleton { files }
}

/// The rules that a build log's `k2l_preserve` lines leave open.
pub fn open_rules(log: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for l in log.lines() {
        let Some(k) = l.find("k2l_preserve: ") else {
            continue;
        };
        let l = &l[k..];
        let names: Vec<String> = if let Some(o) = l.find("; open: [") {
            let body = &l[o + "; open: [".len()..];
            let body = body.strip_suffix(']').unwrap_or(body);
            split_names(body)
        } else if let Some(r) = l.strip_prefix("k2l_preserve: rule ") {
            r.find(" not closed")
                .map(|e| vec![r[..e].to_string()])
                .unwrap_or_default()
        } else {
            vec![]
        };
        for n in names {
            if !out.contains(&n) {
                out.push(n);
            }
        }
    }
    out
}

/// The names of a printed Lean list body (`«…»` names may hold `,` and spaces).
fn split_names(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut quoted = false;
    for ch in s.chars() {
        match ch {
            '«' => {
                quoted = true;
                cur.push(ch)
            }
            '»' => {
                quoted = false;
                cur.push(ch)
            }
            ',' if !quoted => {
                if !cur.trim().is_empty() {
                    out.push(cur.trim().to_string());
                }
                cur.clear();
            }
            _ => cur.push(ch),
        }
    }
    if !cur.trim().is_empty() {
        out.push(cur.trim().to_string());
    }
    out
}

/// A stub for the hand case of rule `c`.
pub fn stub(ns: &str, c: &Case, params: &str, pred: &str) -> String {
    let intro: Vec<String> = c
        .vars
        .iter()
        .chain(&c.hyps)
        .map(|(n, _)| binder(n))
        .collect();
    let loc = c
        .loc
        .as_deref()
        .map(|l| format!(" ({l})"))
        .unwrap_or_default();
    let params = if params.is_empty() {
        String::new()
    } else {
        format!(" {params}")
    };
    let intro_line = if intro.is_empty() {
        String::new()
    } else {
        format!("  intro {}\n", intro.join(" "))
    };
    format!(
        "/-! ## HAND CASE `{}`{loc}\n\n`k2l_preserve` does not close this rule's case. Its statement is `{ns}.Step.Case.{}` in\n`{ns}/Preserves.lean`; after the introductions the goal is `P lhs → P rhs`, with the rule's\nvariables and side conditions in context. -/\n\ntheorem {}{params} : {ns}.Step.Case.{} ({pred}) := by\n{intro_line}  intro h\n  done\n\n",
        display(&c.name),
        c.name,
        c.name,
        c.name
    )
}

fn fail(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::exit(2)
}

pub fn main(args: &[String]) {
    let usage = "usage: k2lean new-invariant --lib GENERATED_DIR --out PROJECT_DIR [--name NAME] [--prelude PRELUDE_DIR]\n                            [--from-log BUILD.log [--params '(G : T)'] [--pred 'P G']]";
    let mut lib = None;
    let mut out = None;
    let mut name = None;
    let mut prelude = None;
    let mut log = None;
    let mut params = String::new();
    let mut pred = "Invariant".to_string();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut val = || it.next().cloned().unwrap_or_else(|| fail(usage));
        match a.as_str() {
            "--lib" => lib = Some(PathBuf::from(val())),
            "--out" => out = Some(PathBuf::from(val())),
            "--name" => name = Some(val()),
            "--prelude" => prelude = Some(PathBuf::from(val())),
            "--from-log" => log = Some(PathBuf::from(val())),
            "--params" => params = val(),
            "--pred" => pred = val(),
            _ => fail(usage),
        }
    }
    let (Some(lib), Some(out)) = (lib, out) else {
        fail(usage)
    };
    let l = load_lib(&lib).unwrap_or_else(|e| fail(&e));
    let name = name.unwrap_or_else(|| {
        out.file_name()
            .map(|n| n.to_string_lossy().to_string())
            .unwrap_or_else(|| fail(usage))
    });
    if !name.chars().next().is_some_and(|c| c.is_ascii_uppercase())
        || !name.chars().all(|c| c.is_ascii_alphanumeric())
    {
        fail(&format!(
            "--name {name}: use a capitalized alphanumeric Lean module name"
        ));
    }
    std::fs::create_dir_all(&out).unwrap_or_else(|e| fail(&format!("{}: {e}", out.display())));
    let prelude = prelude
        .or(l.prelude.clone())
        .unwrap_or_else(|| fail("no --prelude, and the library's lakefile names none"));
    let toolchain = std::fs::read_to_string(l.dir.join("lean-toolchain"))
        .unwrap_or_else(|_| crate::LEAN_TOOLCHAIN.to_string());
    let sk = skeleton(
        &l,
        &name,
        &relative(&out, &l.dir),
        &relative(&out, &prelude),
        &toolchain,
    );
    for (p, text) in &sk.files {
        let f = out.join(p);
        if f.exists() {
            eprintln!("kept {}", f.display());
            continue;
        }
        if let Some(d) = f.parent() {
            std::fs::create_dir_all(d).unwrap();
        }
        std::fs::write(&f, text).unwrap();
        eprintln!("wrote {}", f.display());
    }
    let Some(log) = log else { return };
    let text = read(&log).unwrap_or_else(|e| fail(&e));
    let cases_file = out.join(&name).join("Cases.lean");
    let mut cases = read(&cases_file).unwrap_or_else(|e| fail(&e));
    let Some(at) = cases.find(MARKER) else {
        fail(&format!(
            "{}: no marker line `{MARKER}`",
            cases_file.display()
        ))
    };
    let mut stubs = String::new();
    let mut added = Vec::new();
    for r in open_rules(&text) {
        if cases.contains(&format!("theorem {r} ")) || cases.contains(&format!("theorem {r}\n")) {
            eprintln!("{r}: has a hand case already");
            continue;
        }
        let Some(c) = l.cases.iter().find(|c| c.name == r) else {
            eprintln!("{r}: not a rule of {} (a log of another library?)", l.ns);
            continue;
        };
        stubs.push_str(&stub(&l.ns, c, &params, &pred));
        added.push(r);
    }
    cases.insert_str(at, &stubs);
    std::fs::write(&cases_file, cases).unwrap();
    eprintln!(
        "{} stub(s) added to {}: {}",
        added.len(),
        cases_file.display(),
        added.join(", ")
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn open_rules_are_read_from_both_log_forms() {
        let log = "info: X/Cases.lean:9:2: k2l_preserve: 77 of 79 rules closed; hand: [«CALC.var»]; open: [«X, Y», «CALC.assign»]\ninfo: k2l_preserve: rule «I1 < I2» not closed; the goal is …\ninfo: k2l_preserve: 3 of 3 rules closed\n";
        assert_eq!(open_rules(log), ["«X, Y»", "«CALC.assign»", "«I1 < I2»"]);
    }

    #[test]
    fn relative_paths_go_up_then_down() {
        assert_eq!(
            relative(Path::new("/a/b/c"), Path::new("/a/d")),
            PathBuf::from("../../d")
        );
        assert_eq!(
            relative(Path::new("/a"), Path::new("/a/d/e")),
            PathBuf::from("d/e")
        );
    }
}
