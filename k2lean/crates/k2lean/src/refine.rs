//! `k2lean refine`: a stuttering bisimulation between two definitions whose steps do not
//! correspond one to one (`k2lean/docs/design.md`, section 3.5).
//!
//! Input: the compiled KORE of `A` and `B` (each generated into a library), the correspondence
//! `k2lean relate --per-rule true` reported (`--correspondence`), whose Lean module (`NS.Tr`)
//! holds the translation `tr` and one simulation lemma per pair of corresponding rules, and a
//! hand module (`--hand-module`, default `NS.Relation`) that supplies the non-local part of the
//! relation, `X : A.Top → B.Top → Prop`, the measures `μ : A.Top → Nat` and `ν : B.Top → Nat`,
//! and the cases listed in `--open` (one `KIND RULE` per line, `#` comments; `KIND` is `fwd_tr`,
//! `fwd_x`, `bwd_tr` or `bwd_x`).
//!
//! The relation is `Stutter.Rel tr X c d := d = tr c ∨ X c d` (`KPrelude.Scaffold`). What each
//! step owes splits per rule and per part of the relation:
//!
//! - `fwd_tr r`: a step of `A` by `r` from `c`, against `tr c`: generated from `fwd.r` when `r`
//!   has a counterpart (one step of `B`, `tr` again);
//! - `fwd_x r`: against a state `X` relates to `c`: generated as a refutation (`cases` on the
//!   hypothesis `X lhs d`, which closes when `X` is an inductive predicate whose indices clash
//!   with the rule's left-hand side);
//! - `bwd_tr r`, `bwd_x r`: the same for the steps of `B`, from `bwd.r`.
//!
//! The other cases are the hand module's: `hand.KIND.r : A.Step.Rel.r (Stutter.FwdTr …)` and so
//! on. The output module states and proves `bisim : StutterBisim A.Step B.Step (Stutter.Rel tr X)
//! μ ν` and the transfer of runs to terminal states in both directions.

use crate::ir::{self, P};
use crate::model::Model;
use crate::preserves;
use crate::rules::{self, Rule};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

fn fail(msg: &str) -> ! {
    eprintln!("refine: {msg}");
    std::process::exit(2)
}

fn write_file(path: &str, text: &str) {
    let p = std::path::Path::new(path);
    if let Some(d) = p.parent().filter(|d| !d.as_os_str().is_empty()) {
        std::fs::create_dir_all(d)
            .unwrap_or_else(|e| fail(&format!("cannot create {}: {e}", d.display())));
    }
    std::fs::write(p, text).unwrap_or_else(|e| fail(&format!("cannot write {path}: {e}")));
}

/// The rules of a definition as `gen` generates its `Step` (the order is immaterial here), and
/// its top sort.
pub fn load_rules(kore: &str) -> (Vec<Rule>, Option<Vec<i64>>, String) {
    let text = std::fs::read_to_string(kore).unwrap_or_else(|e| fail(&format!("{kore}: {e}")));
    let def = ir::load(&text).unwrap_or_else(|e| fail(&format!("{kore}: {e:?}")));
    let m = Model::build(&def).unwrap_or_else(|e| fail(&e));
    let mut roots = BTreeSet::new();
    for ax in &def.axioms {
        if let P::Rewrites(_, l, _) = &ax.pattern
            && rules::absent_sort(l, &m).is_none()
        {
            crate::funcs::applied(&ax.pattern, &def, &mut roots);
        }
    }
    roots.extend(m.anywhere.iter().cloned());
    let fgen = crate::funcs::generate(&def, &m, &roots)
        .unwrap_or_else(|e| fail(&format!("functions: {e}")));
    let (rs, prios, ranked) =
        rules::collect_ranked(&def, &m, &fgen.fns, &[]).unwrap_or_else(|e| fail(&e));
    let top = rules::top_sort(&def).unwrap_or_else(|e| fail(&e));
    (rs, ranked.then_some(prios), top)
}

/// The rule pairs of a `relate` report (`[rules]`: A's rule name to B's).
fn read_pairs(path: &str) -> BTreeMap<String, String> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| fail(&format!("{path}: {e}")));
    let t: toml::Table = text
        .parse()
        .unwrap_or_else(|e| fail(&format!("{path}: {e}")));
    let Some(toml::Value::Table(rs)) = t.get("rules") else {
        fail(&format!("{path}: no [rules] table"))
    };
    rs.iter()
        .map(|(a, v)| {
            let b = match v {
                toml::Value::String(s) => s.clone(),
                toml::Value::Table(t) => match t.get("b") {
                    Some(toml::Value::String(s)) => s.clone(),
                    _ => fail(&format!("{path}: rule {a} without `b`")),
                },
                _ => fail(&format!("{path}: rule {a}: unexpected value")),
            };
            (a.clone(), b)
        })
        .collect()
}

/// The open list: (kind, rule name).
fn read_open(path: &str) -> BTreeSet<(String, String)> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| fail(&format!("{path}: {e}")));
    let mut out = BTreeSet::new();
    for l in text.lines() {
        let l = l.trim();
        if l.is_empty() || l.starts_with('#') {
            continue;
        }
        let Some((k, r)) = l.split_once(' ') else {
            fail(&format!("{path}: `{l}` is not `KIND RULE`"))
        };
        if !["fwd_tr", "fwd_x", "bwd_tr", "bwd_x"].contains(&k) {
            fail(&format!("{path}: unknown kind {k}"));
        }
        out.insert((k.to_string(), r.trim().to_string()));
    }
    out
}

fn intro(xs: &[String]) -> String {
    if xs.is_empty() {
        String::new()
    } else {
        format!("  intro {}\n", xs.join(" "))
    }
}

pub fn main(args: &[String]) {
    let mut opt: BTreeMap<String, String> = BTreeMap::new();
    let mut it = args.iter();
    while let Some(k) = it.next() {
        let v = it
            .next()
            .unwrap_or_else(|| fail(&format!("{k} needs a value")));
        opt.insert(k.trim_start_matches("--").to_string(), v.clone());
    }
    let get = |k: &str| {
        opt.get(k)
            .cloned()
            .unwrap_or_else(|| fail(&format!("--{k} is required")))
    };
    let (na, nb, ns) = (get("name-a"), get("name-b"), get("ns"));
    let (ra, pa, top) = load_rules(&get("kore-a"));
    let (rb, pb, top_b) = load_rules(&get("kore-b"));
    if pa.is_some() || pb.is_some() {
        fail("definitions with priority ranks are not supported");
    }
    if top != top_b {
        fail(&format!("the top sorts differ ({top}, {top_b})"));
    }
    let pairs = read_pairs(&get("correspondence"));
    let open = opt.get("open").map(|p| read_open(p)).unwrap_or_default();
    let hand = opt
        .get("hand-module")
        .cloned()
        .unwrap_or(format!("{ns}.Relation"));
    let x = opt.get("extra").cloned().unwrap_or("X".into());
    let mu = opt.get("measure-a").cloned().unwrap_or("μ".into());
    let nu = opt.get("measure-b").cloned().unwrap_or("ν".into());
    let ca = preserves::ctors(&ra, None);
    let cb = preserves::ctors(&rb, None);
    let names_a: BTreeSet<String> = ra.iter().map(rules::display_name).collect();
    let names_b: BTreeSet<String> = rb.iter().map(rules::display_name).collect();
    let paired_b: BTreeSet<&String> = pairs.values().collect();
    for (k, r) in &open {
        let known = if k.starts_with("fwd") {
            &names_a
        } else {
            &names_b
        };
        if !known.contains(r) {
            fail(&format!("open case {k} {r}: no such rule"));
        }
    }
    let tr = format!("tr_{}", crate::terms::fsuffix(&top));
    let (ta, tb) = (format!("{na}.{top}"), format!("{nb}.{top}"));
    let mut o = String::new();
    writeln!(o, "import {hand}\n").unwrap();
    writeln!(
        o,
        "/-! Generated by `k2lean refine`; do not edit.\n\n\
The stuttering bisimulation between `{na}.Step` and `{nb}.Step` through\n\
`Stutter.Rel {tr} {x}` (`d` is the translation of `c`, or `{x}` relates them), with the measures\n\
`{mu}` and `{nu}` of `{hand}`. One case per rule and direction, in two parts (`Stutter.fwdQ_of`,\n\
`Stutter.bwdQ_of`): at a translation, from the simulation lemma of `relate --per-rule` when the\n\
rule has a counterpart; at a state `{x}` relates, by `cases` on `{x}`. The rest are the hand\n\
module's (`hand.fwd_tr.r`, `hand.fwd_x.r`, `hand.bwd_tr.r`, `hand.bwd_x.r`). -/\n"
    )
    .unwrap();
    writeln!(o, "set_option maxHeartbeats 0\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n").unwrap();
    let mut guard = vec![];
    let mut counts: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    let mut hand_cases = vec![];
    let mut part = |o: &mut String,
                    kind: &'static str,
                    (name, lean): (&str, &str),
                    args: &[String],
                    auto: Option<String>| {
        let e = counts.entry(kind).or_default();
        if open.contains(&(kind.to_string(), name.to_string())) || auto.is_none() {
            e.1 += 1;
            hand_cases.push(format!("{kind} {name}"));
            let sep = if args.is_empty() { "" } else { " " };
            writeln!(
                o,
                "  · exact hand.{kind}.{lean}{sep}{}",
                args.join(" ")
            )
            .unwrap();
        } else {
            e.0 += 1;
            writeln!(o, "  · {}", auto.unwrap()).unwrap();
        }
    };
    writeln!(o, "/-! ## Forward: the steps of `{na}` -/\n").unwrap();
    for (r, c) in ra.iter().zip(&ca) {
        let name = rules::display_name(r);
        let args = rules::ctor_args(&r.step);
        writeln!(
            o,
            "theorem stutter_fwd.{} : {na}.Step.Rel.{} (Stutter.FwdQ {tr} {nb}.Step {x} {mu}) := by\n{}  apply Stutter.fwdQ_of",
            c.lean,
            c.lean,
            intro(&args)
        )
        .unwrap();
        let sep = if args.is_empty() { "" } else { " " };
        let tr_auto = pairs.contains_key(&name).then(|| {
            format!(
                "exact Or.inl ⟨_, .single (fwd.{}{sep}{}), Or.inl rfl⟩",
                c.lean,
                args.join(" ")
            )
        });
        part(&mut o, "fwd_tr", (&name, &c.lean), &args, tr_auto);
        part(
            &mut o,
            "fwd_x",
            (&name, &c.lean),
            &args,
            Some("intro d hX; cases hX <;> first | done | contradiction | (simp_all; done)".to_string()),
        );
        writeln!(o).unwrap();
        guard.push(format!("stutter_fwd.{}", c.lean));
    }
    writeln!(o, "/-! ## Backward: the steps of `{nb}` -/\n").unwrap();
    for (r, c) in rb.iter().zip(&cb) {
        let name = rules::display_name(r);
        let args = rules::ctor_args(&r.step);
        writeln!(
            o,
            "theorem stutter_bwd.{} : {nb}.Step.Rel.{} (Stutter.BwdQ {tr} {na}.Step {x} {nu}) := by\n{}  apply Stutter.bwdQ_of",
            c.lean,
            c.lean,
            intro(&args)
        )
        .unwrap();
        let sep = if args.is_empty() { "" } else { " " };
        let tr_auto = paired_b.contains(&name).then(|| {
            format!(
                "intro c hd\n    obtain ⟨c', hc', e⟩ := bwd.{}{sep}{} c hd.symm\n    exact Or.inl ⟨c', .single hc', Or.inl e⟩",
                c.lean,
                args.join(" ")
            )
        });
        part(&mut o, "bwd_tr", (&name, &c.lean), &args, tr_auto);
        part(
            &mut o,
            "bwd_x",
            (&name, &c.lean),
            &args,
            Some("intro c hX; cases hX <;> first | done | contradiction | (simp_all; done)".to_string()),
        );
        writeln!(o).unwrap();
        guard.push(format!("stutter_bwd.{}", c.lean));
    }
    let list = |cs: &[preserves::Ctor], p: &str| {
        cs.iter()
            .map(|c| format!("{p}.{}", c.lean))
            .collect::<Vec<_>>()
            .join(" ")
    };
    writeln!(o, "/-! ## The stuttering bisimulation and what it transfers -/\n").unwrap();
    writeln!(
        o,
        "theorem bisim : StutterBisim {na}.Step {nb}.Step (Stutter.Rel {tr} {x}) {mu} {nu} :=\n  Stutter.bisim_of\n    (fun h => {na}.Step.rel_of {} h)\n    (fun h => {nb}.Step.rel_of {} h)\n",
        list(&ca, "stutter_fwd"),
        list(&cb, "stutter_bwd")
    )
    .unwrap();
    writeln!(
        o,
        "/-- A run of `{na}` to a terminal state is matched, from the translation of its start, by a run\nof `{nb}` to a terminal state related to it. -/\n\
theorem run_fwd {{c c' : {ta}}} (h : Star {na}.Step c c') (ht : Terminal {na}.Step c') :\n    ∃ d', Star {nb}.Step ({tr} c) d' ∧ Terminal {nb}.Step d' ∧ Stutter.Rel {tr} {x} c' d' :=\n  bisim.terminal_run (Or.inl rfl) h ht\n\n\
/-- A run of `{nb}` from a translation to a terminal state is matched by a run of `{na}` to a\nterminal state related to it. -/\n\
theorem run_bwd {{c : {ta}}} {{d' : {tb}}} (h : Star {nb}.Step ({tr} c) d') (ht : Terminal {nb}.Step d') :\n    ∃ c', Star {na}.Step c c' ∧ Terminal {na}.Step c' ∧ Stutter.Rel {tr} {x} c' d' :=\n  bisim.symm.terminal_run (Or.inl rfl) h ht\n"
    )
    .unwrap();
    guard.extend(["bisim".into(), "run_fwd".into(), "run_bwd".into()]);
    writeln!(o, "#k2l_assert_axioms {}\n\nend {ns}", guard.join(" ")).unwrap();
    write_file(&get("out"), &o);
    let total: (usize, usize) = counts
        .values()
        .fold((0, 0), |(a, b), (x, y)| (a + x, b + y));
    let mut rep = format!(
        "# k2lean refine: {na} against {nb}\n\nrules_a = {}\nrules_b = {}\npairs = {}\nparts = {}\nautomatic = {}\nhand = {}\n\n[parts]\n",
        ra.len(),
        rb.len(),
        pairs.len(),
        total.0 + total.1,
        total.0,
        total.1
    );
    for (k, (a, h)) in &counts {
        writeln!(rep, "{k} = {{ automatic = {a}, hand = {h} }}").unwrap();
    }
    writeln!(rep, "\n[hand]\ncases = {hand_cases:?}").unwrap();
    if let Some(p) = opt.get("report") {
        write_file(p, &rep);
    }
    eprintln!(
        "refine: {} + {} rules, {} pairs; {} case parts, {} generated, {} by hand",
        ra.len(),
        rb.len(),
        pairs.len(),
        total.0 + total.1,
        total.0,
        total.1
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tmp(name: &str, text: &str) -> String {
        let p = std::env::temp_dir().join(format!("k2lean-refine-{}-{name}", std::process::id()));
        std::fs::write(&p, text).unwrap();
        p.to_string_lossy().into_owned()
    }

    #[test]
    fn open_cases_are_kind_and_rule() {
        let p = tmp("open", "# hand cases\nfwd_tr IMP.while\n\nbwd_x IMP-SYNTAX.if(_)_else_ heat\n");
        let o = read_open(&p);
        assert!(o.contains(&("fwd_tr".into(), "IMP.while".into())));
        // a rule name may contain spaces: everything after the kind
        assert!(o.contains(&("bwd_x".into(), "IMP-SYNTAX.if(_)_else_ heat".into())));
        assert_eq!(o.len(), 2);
    }

    #[test]
    fn pairs_are_read_from_a_relate_report() {
        let p = tmp(
            "corr",
            "[symbols]\n\"x\" = { b = \"x\", how = \"same symbol\" }\n\n[rules]\n\"I1 < I2\" = \"I1 < I2\"\n\"a\" = { b = \"b\", refines-to = [\"SortInt\"] }\n",
        );
        let m = read_pairs(&p);
        assert_eq!(m.get("I1 < I2").map(|s| s.as_str()), Some("I1 < I2"));
        assert_eq!(m.get("a").map(|s| s.as_str()), Some("b"));
    }
}
