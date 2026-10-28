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
//! on. With `--hand-module none` there is no hand module: one step of `B` that `A` takes in two
//! (`find_splits`: `A`'s `a1` then `a2` against `B`'s `b`, no side conditions) gives `X` (one
//! constructor, `A` after `a1` against `B` after `b`), `X_inv`, `μ` (1 there), `ν = 0`, `R`, and
//! the parts that need `X`'s constructor: `fwd_tr a1`, `fwd_x a2`, `bwd_tr b`, and `bwd_x r` for
//! each step of `B` at `X` (`A` takes `a2`, then `r`'s counterpart). The output module states and proves `bisim : StutterBisim A.Step B.Step (Stutter.Rel tr X)
//! μ ν` and the transfer of runs to terminal states in both directions.

use crate::ir::{self, P};
use crate::lower::L;
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

/// The rules of a definition as `gen` generates its `Step` (the order is immaterial here), its
/// top sort and its builtin sorts (whose values a translation leaves as they are).
pub fn load_rules(kore: &str) -> (Vec<Rule>, Option<Vec<i64>>, String, BTreeSet<String>) {
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
    let builtin = m
        .sorts
        .iter()
        .filter(|(_, i)| matches!(i.kind, crate::model::Kind::Builtin(_)))
        .map(|(s, _)| s.clone())
        .collect();
    (
        rs,
        (ranked && prios.len() > 1).then_some(prios),
        top,
        builtin,
    )
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

/// One-way matching: `pat`'s variables to subterms of `t`, whose variables are constants.
fn match_l(pat: &L, t: &L, sig: &mut BTreeMap<String, L>) -> bool {
    match (pat, t) {
        (L::Var(v), _) => match sig.get(v) {
            Some(u) => u == t,
            None => {
                sig.insert(v.clone(), t.clone());
                true
            }
        },
        (L::App(h1, a1), L::App(h2, a2)) => {
            h1 == h2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(p, u)| match_l(p, u, sig))
        }
        (L::Typed(e1, t1), L::Typed(e2, t2)) => t1 == t2 && match_l(e1, e2, sig),
        (L::Raw(r1), L::Raw(r2)) => r1 == r2,
        _ => false,
    }
}

/// `a` and `b` equal up to a renaming of variables, one to one, extending `rho` (`a`'s names to
/// `b`'s).
fn alpha_eq(a: &L, b: &L, rho: &mut BTreeMap<String, String>) -> bool {
    match (a, b) {
        (L::Var(x), L::Var(y)) => match rho.get(x) {
            Some(z) => z == y,
            None => {
                if rho.values().any(|z| z == y) {
                    return false;
                }
                rho.insert(x.clone(), y.clone());
                true
            }
        },
        (L::App(h1, a1), L::App(h2, a2)) => {
            h1 == h2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(p, u)| alpha_eq(p, u, rho))
        }
        (L::Typed(e1, t1), L::Typed(e2, t2)) => t1 == t2 && alpha_eq(e1, e2, rho),
        (L::Raw(r1), L::Raw(r2)) => r1 == r2,
        _ => false,
    }
}

/// A rule's left-hand side and right-hand side, its aliases substituted.
fn sides(r: &Rule) -> (L, L) {
    (
        subst_bounded(&r.step.index, &r.step.subst, 16),
        subst_bounded(&r.rhs, &r.step.subst, 16),
    )
}

/// `t` with `s` applied, through chains of bound variables (a rule's aliases: `y ↦ while(C) S`)
/// up to `depth`, so that a variable bound to itself, or to a term over names it shares with the
/// substitution's domain (a match of one rule against another's terms), is substituted once.
fn subst_bounded(t: &L, s: &BTreeMap<String, L>, depth: usize) -> L {
    match t {
        L::Var(v) => match s.get(v) {
            Some(u) if depth > 0 && u != t => subst_bounded(u, s, depth - 1),
            Some(u) => u.clone(),
            None => t.clone(),
        },
        L::App(h, xs) => L::App(
            h.clone(),
            xs.iter().map(|a| subst_bounded(a, s, depth)).collect(),
        ),
        L::Typed(e, ty) => L::Typed(Box::new(subst_bounded(e, s, depth)), ty.clone()),
        L::Raw(_) => t.clone(),
    }
}

/// `t` as a term of library `ns` in a position whose type Lean knows: a constructor `Sort….c` by
/// its dot form `.c`, any other head qualified by `ns`, each variable `v` as `var(v)`.
fn render_dot(t: &L, ns: &str, var: &dyn Fn(&str) -> String) -> String {
    let arg = |a: &L| {
        let r = render_dot(a, ns, var);
        match a {
            L::App(_, xs) if !xs.is_empty() => format!("({r})"),
            L::Raw(x) if x.contains(' ') && !(x.starts_with('(') && x.ends_with(')')) => {
                format!("({r})")
            }
            _ => r,
        }
    };
    match t {
        L::Var(v) => var(v),
        L::Raw(r) => r.clone(),
        L::Typed(e, ty) => format!("({} : {ns}.{ty})", render_dot(e, ns, var)),
        L::App(h, xs) => {
            let head = match h.split_once('.') {
                Some((sort, c)) if sort.starts_with("Sort") && !sort.contains('«') => {
                    format!(".{c}")
                }
                _ => format!("{ns}.{h}"),
            };
            std::iter::once(head)
                .chain(xs.iter().map(arg))
                .collect::<Vec<_>>()
                .join(" ")
        }
    }
}

/// A step of `B` that `A` takes in two (`a1` then `a2`): indices into the rules, and the renaming
/// of `a1`'s variables to `b`'s (design.md, section 3.5).
struct Split {
    a1: usize,
    a2: usize,
    b: usize,
    rho: BTreeMap<String, String>,
}

/// The splits: an unpaired rule `b` of `B` and an unpaired rule `a1` of `A` with the same
/// left-hand side up to renaming, and a rule `a2` of `A` whose left-hand side matches `a1`'s
/// right-hand side, with `a2`'s right-hand side then `b`'s up to the same renaming. The rules of
/// a split have no side conditions (else its parts stay the hand module's).
fn find_splits(
    ra: &[Rule],
    rb: &[Rule],
    paired_a: &BTreeSet<String>,
    paired_b: &BTreeSet<&String>,
) -> Vec<Split> {
    let mut out = vec![];
    let sa: Vec<(L, L)> = ra.iter().map(sides).collect();
    let sb: Vec<(L, L)> = rb.iter().map(sides).collect();
    for (j, b) in rb.iter().enumerate() {
        if paired_b.contains(&rules::display_name(b)) || !b.step.hyps.is_empty() {
            continue;
        }
        let (lb, rhs_b) = &sb[j];
        for (i, a1) in ra.iter().enumerate() {
            if paired_a.contains(&rules::display_name(a1)) || !a1.step.hyps.is_empty() {
                continue;
            }
            let (la1, rhs_a1) = &sa[i];
            let mut rho = BTreeMap::new();
            if !alpha_eq(la1, lb, &mut rho) {
                continue;
            }
            for (k, a2) in ra.iter().enumerate() {
                if k == i || !a2.step.hyps.is_empty() {
                    continue;
                }
                let (la2, rhs_a2) = &sa[k];
                let mut sig = BTreeMap::new();
                if !match_l(la2, rhs_a1, &mut sig) {
                    continue;
                }
                let mut rho2 = rho.clone();
                if alpha_eq(&subst_bounded(rhs_a2, &sig, 0), rhs_b, &mut rho2) {
                    out.push(Split {
                        a1: i,
                        a2: k,
                        b: j,
                        rho: rho2,
                    });
                }
            }
        }
    }
    out
}

/// The translation of `A`'s variable `v` of sort `t`: itself on a builtin sort.
fn tr_var(builtin: &BTreeSet<String>, t: &str, v: &str) -> String {
    if builtin.contains(t) {
        v.to_string()
    } else {
        format!("(tr_{} {v})", crate::terms::fsuffix(t))
    }
}

/// `X`, `X_inv` and the measures of a split (`--hand-module none`): `X` relates `A`'s state
/// after `a1` to `B`'s after `b`, its `B` side a pattern of `B`'s constructors over variables
/// each the translation of `A`'s (`cases` on `X` never inverts a translation); `μ` is 1 there,
/// where `A` stutters, and `ν` is 0.
#[allow(clippy::too_many_arguments)]
fn emit_split(
    o: &mut String,
    sp: &Split,
    ra: &[Rule],
    rb: &[Rule],
    builtin: &BTreeSet<String>,
    na: &str,
    nb: &str,
    top: &str,
    tr: &str,
    x: &str,
    mu: &str,
    nu: &str,
) {
    let (a1, a2, b) = (&ra[sp.a1], &ra[sp.a2], &rb[sp.b]);
    let (_, rhs_a1) = sides(a1);
    let (_, rhs_b) = sides(b);
    let inv: BTreeMap<&String, &String> = sp.rho.iter().map(|(k, v)| (v, k)).collect();
    let ty_b: BTreeMap<&String, &String> = b.step.binders.iter().map(|(n, t)| (n, t)).collect();
    let vars = &a1.step.binders;
    let a_side = render_dot(&rhs_a1, na, &|v| v.to_string());
    let b_side = render_dot(&rhs_b, nb, &|w| match inv.get(&w.to_string()) {
        Some(v) => format!("{v}'"),
        None => format!("{w}'"),
    });
    let ty_a: BTreeMap<&String, &String> = vars.iter().map(|(n, t)| (n, t)).collect();
    let b_tr = render_dot(&rhs_b, nb, &|w| match inv.get(&w.to_string()) {
        Some(v) => tr_var(builtin, ty_a.get(v).map(|t| t.as_str()).unwrap_or(""), v),
        None => w.to_string(),
    });
    let (an, bn) = (rules::display_name(a1), rules::display_name(b));
    let a2n = rules::display_name(a2);
    writeln!(
        o,
        "/-! ## The split: `{bn}` of `{nb}` is `{an}` then `{a2n}` of `{na}` -/\n"
    )
    .unwrap();
    let mut binders = vec![];
    for (v, t) in vars {
        binders.push(format!("({v} : {na}.{t})"));
    }
    for (v, t) in vars {
        let tb = sp
            .rho
            .get(v)
            .and_then(|w| ty_b.get(w))
            .map(|t| t.as_str())
            .unwrap_or(t);
        binders.push(format!("({v}' : {nb}.{tb})"));
    }
    for (v, t) in vars {
        binders.push(format!("(h_{v} : {v}' = {})", tr_var(builtin, t, v)));
    }
    writeln!(
        o,
        "/-- `{na}` after `{an}`, `{nb}` after `{bn}`: `{na}` completes the step by `{a2n}`. -/\ninductive {x} : {na}.{top} → {nb}.{top} → Prop where\n  | split {} :\n      {x} ({a_side})\n        ({b_side})\n",
        binders.join(" ")
    )
    .unwrap();
    let exs: Vec<String> = vars
        .iter()
        .map(|(v, t)| format!("({v} : {na}.{t})"))
        .collect();
    let us = vec!["_"; vars.len()].join(", ");
    writeln!(
        o,
        "theorem {x}_inv {{c : {na}.{top}}} {{d : {nb}.{top}}} (h : {x} c d) :\n    ∃ {}, c = {a_side} ∧\n      d = {b_tr} := by\n  cases h; subst_vars; exact ⟨{us}, rfl, rfl⟩\n",
        exs.join(" ")
    )
    .unwrap();
    let pat = render_dot(&rhs_a1, na, &|_| "_".to_string());
    writeln!(
        o,
        "/-- `{na}`'s measure: 1 after `{an}`, where it stutters. -/\ndef {mu} : {na}.{top} → Nat\n  | {pat} => 1\n  | _ => 0\n\n/-- `{nb}` never stutters. -/\ndef {nu} (_ : {nb}.{top}) : Nat := 0\n\n/-- The relation: `d` is the translation of `c`, or `{x}` relates them. -/\nabbrev R := Stutter.Rel {tr} {x}\n"
    )
    .unwrap();
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
    let (ra, pa, top, builtin) = load_rules(&get("kore-a"));
    let (rb, pb, top_b, _) = load_rules(&get("kore-b"));
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
    let paired_a: BTreeSet<String> = pairs.keys().cloned().collect();
    // `--hand-module none`: no hand module; `X`, the measures and the parts of a split are
    // generated (one split, `find_splits`)
    let generated = hand == "none";
    let split = if generated {
        let mut ss = find_splits(&ra, &rb, &paired_a, &paired_b);
        if ss.len() != 1 {
            fail(&format!(
                "--hand-module none: {} splits found (one step of B taken in two by A), one is supported",
                ss.len()
            ));
        }
        Some(ss.remove(0))
    } else {
        None
    };
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
    if generated {
        let trm = opt.get("tr-module").cloned().unwrap_or(format!("{ns}.Tr"));
        writeln!(o, "import {trm}\nimport KPrelude.Scaffold\n").unwrap();
    } else {
        writeln!(o, "import {hand}\n").unwrap();
    }
    let whose = if generated {
        "below, generated from the one step of `B` that `A` takes in two (`--hand-module none`)"
            .to_string()
    } else {
        format!("of `{hand}`")
    };
    let rest = if generated {
        "The step of the split, and each step of `B` at a state `X` relates, are matched by `A`'s two\nsteps (`A` completes its step, then takes the counterpart)."
    } else {
        "The rest are the hand\nmodule's (`hand.fwd_tr.r`, `hand.fwd_x.r`, `hand.bwd_tr.r`, `hand.bwd_x.r`)."
    };
    writeln!(
        o,
        "/-! Generated by `k2lean refine`; do not edit.\n\n\
The stuttering bisimulation between `{na}.Step` and `{nb}.Step` through\n\
`Stutter.Rel {tr} {x}` (`d` is the translation of `c`, or `{x}` relates them), with the measures\n\
`{mu}` and `{nu}` {whose}. One case per rule and direction, in two parts (`Stutter.fwdQ_of`,\n\
`Stutter.bwdQ_of`): at a translation, from the simulation lemma of `relate --per-rule` when the\n\
rule has a counterpart; at a state `{x}` relates, by `cases` on `{x}`. {rest} -/\n"
    )
    .unwrap();
    writeln!(o, "set_option maxHeartbeats 0\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n").unwrap();
    if let Some(sp) = &split {
        emit_split(
            &mut o, sp, &ra, &rb, &builtin, &na, &nb, &top, &tr, &x, &mu, &nu,
        );
    }
    let mut guard = vec![];
    let mut counts: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    let mut hand_cases = vec![];
    let mut part = |o: &mut String,
                    kind: &'static str,
                    (name, lean): (&str, &str),
                    args: &[String],
                    auto: Option<String>| {
        let e = counts.entry(kind).or_default();
        let listed = open.contains(&(kind.to_string(), name.to_string()));
        match auto {
            Some(tac) if !listed => {
                e.0 += 1;
                writeln!(o, "  · {tac}").unwrap();
            }
            _ => {
                e.1 += 1;
                hand_cases.push(format!("{kind} {name}"));
                let sep = if args.is_empty() { "" } else { " " };
                writeln!(o, "  · exact hand.{kind}.{lean}{sep}{}", args.join(" ")).unwrap();
            }
        }
    };
    // the parts a split generates (`--hand-module none`): `A`'s first step against `B`'s one,
    // `A`'s second step at `X`, `B`'s step against `A`'s two, and `B`'s paired steps at `X`
    // (`A` completes its step, then takes the counterpart)
    let refute = "intro d hX; cases hX <;> first | done | contradiction | (simp_all; done)";
    let under = |n: usize| vec!["_"; n].join(" ");
    let mut split_fwd_tr: Option<(usize, String)> = None;
    let mut split_fwd_x: Option<(usize, String)> = None;
    let mut split_bwd_tr: Option<(usize, String)> = None;
    let mut split_bwd_x: BTreeMap<usize, String> = BTreeMap::new();
    if let Some(sp) = &split {
        let (a1, a2, b) = (&ra[sp.a1], &ra[sp.a2], &rb[sp.b]);
        let inv: BTreeMap<&String, &String> = sp.rho.iter().map(|(k, v)| (v, k)).collect();
        let ty_a: BTreeMap<&String, &String> =
            a1.step.binders.iter().map(|(n, t)| (n, t)).collect();
        let bargs: Vec<String> = rules::ctor_args(&b.step)
            .iter()
            .map(|w| match inv.get(w) {
                Some(v) => tr_var(&builtin, ty_a.get(v).map(|t| t.as_str()).unwrap_or(""), v),
                None => "_".to_string(),
            })
            .collect();
        let n = a1.step.binders.len();
        split_fwd_tr = Some((
            sp.a1,
            format!(
                "exact Or.inl ⟨_, .single ({nb}.Step.{} {}), Or.inr ({x}.split {} {})⟩",
                cb[sp.b].lean,
                bargs.join(" "),
                under(2 * n),
                vec!["rfl"; n].join(" ")
            ),
        ));
        split_fwd_x = Some((
            sp.a2,
            format!(
                "intro d hX; cases hX <;> first | done | contradiction | (simp_all; done) | (subst_vars; exact Or.inr ⟨Or.inl rfl, by simp [{mu}]⟩)"
            ),
        ));
        let (n1, n2) = (
            rules::ctor_args(&a1.step).len(),
            rules::ctor_args(&a2.step).len(),
        );
        split_bwd_tr = Some((
            sp.b,
            format!(
                "intro c hd; have hd := hd.symm; k2l_inv; exact Or.inl ⟨_, .tail (.single ({na}.Step.{} {})) ({na}.Step.{} {}), Or.inl rfl⟩",
                ca[sp.a1].lean,
                under(n1),
                ca[sp.a2].lean,
                under(n2)
            ),
        ));
        let a_of: BTreeMap<&String, usize> = pairs
            .iter()
            .filter_map(|(an, bn)| {
                ra.iter()
                    .position(|r| &rules::display_name(r) == an)
                    .map(|i| (bn, i))
            })
            .collect();
        for (j, r) in rb.iter().enumerate() {
            let Some(&i) = a_of.get(&rules::display_name(r)) else {
                continue;
            };
            let pr = &ra[i];
            let pargs: Vec<&str> = pr
                .step
                .binders
                .iter()
                .map(|_| "_")
                .chain(pr.step.hyps.iter().map(|_| "?_"))
                .collect();
            let closers: Vec<String> = r
                .step
                .hyps
                .iter()
                .map(|(h, _)| format!(" | (simpa only [k2l_rel] using {h})"))
                .collect();
            split_bwd_x.insert(
                j,
                format!(
                    "intro c hX; first | (cases hX <;> first | done | contradiction | (simp_all; done)) | (obtain ⟨{}, rfl, hd⟩ := {x}_inv hX; k2l_injections; k2l_inv; refine Or.inl ⟨_, .tail (.single ({na}.Step.{} {})) ({na}.Step.{} {}), Or.inl ?_⟩ <;> first | rfl | assumption | (simp only [k2l_rel]; done){})",
                    vec!["_"; n].join(", "),
                    ca[sp.a2].lean,
                    under(n2),
                    ca[i].lean,
                    pargs.join(" "),
                    closers.join("")
                ),
            );
        }
    }
    writeln!(o, "/-! ## Forward: the steps of `{na}` -/\n").unwrap();
    for (idx, (r, c)) in ra.iter().zip(&ca).enumerate() {
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
        let tr_auto = pairs
            .contains_key(&name)
            .then(|| {
                format!(
                    "exact Or.inl ⟨_, .single (fwd.{}{sep}{}), Or.inl rfl⟩",
                    c.lean,
                    args.join(" ")
                )
            })
            .or_else(|| {
                split_fwd_tr
                    .as_ref()
                    .filter(|(i, _)| *i == idx)
                    .map(|(_, t)| t.clone())
            });
        part(&mut o, "fwd_tr", (&name, &c.lean), &args, tr_auto);
        let x_auto = match &split_fwd_x {
            Some((i, t)) if *i == idx => t.clone(),
            _ => refute.to_string(),
        };
        part(&mut o, "fwd_x", (&name, &c.lean), &args, Some(x_auto));
        writeln!(o).unwrap();
        guard.push(format!("stutter_fwd.{}", c.lean));
    }
    writeln!(o, "/-! ## Backward: the steps of `{nb}` -/\n").unwrap();
    for (idx, (r, c)) in rb.iter().zip(&cb).enumerate() {
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
        let tr_auto = paired_b
            .contains(&name)
            .then(|| {
                format!(
                    "intro c hd\n    obtain ⟨c', hc', e⟩ := bwd.{}{sep}{} c hd.symm\n    exact Or.inl ⟨c', .single hc', Or.inl e⟩",
                    c.lean,
                    args.join(" ")
                )
            })
            .or_else(|| split_bwd_tr.as_ref().filter(|(i, _)| *i == idx).map(|(_, t)| t.clone()));
        part(&mut o, "bwd_tr", (&name, &c.lean), &args, tr_auto);
        let x_auto = split_bwd_x.get(&idx).cloned().unwrap_or_else(|| {
            "intro c hX; cases hX <;> first | done | contradiction | (simp_all; done)".to_string()
        });
        part(&mut o, "bwd_x", (&name, &c.lean), &args, Some(x_auto));
        writeln!(o).unwrap();
        guard.push(format!("stutter_bwd.{}", c.lean));
    }
    let list = |cs: &[preserves::Ctor], p: &str| {
        cs.iter()
            .map(|c| format!("{p}.{}", c.lean))
            .collect::<Vec<_>>()
            .join(" ")
    };
    writeln!(
        o,
        "/-! ## The stuttering bisimulation and what it transfers -/\n"
    )
    .unwrap();
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
        let p = tmp(
            "open",
            "# hand cases\nfwd_tr IMP.while\n\nbwd_x IMP-SYNTAX.if(_)_else_ heat\n",
        );
        let o = read_open(&p);
        assert!(o.contains(&("fwd_tr".into(), "IMP.while".into())));
        // a rule name may contain spaces: everything after the kind
        assert!(o.contains(&("bwd_x".into(), "IMP-SYNTAX.if(_)_else_ heat".into())));
        assert_eq!(o.len(), 2);
    }

    fn v(x: &str) -> L {
        L::Var(x.into())
    }
    fn app(h: &str, xs: Vec<L>) -> L {
        L::App(h.into(), xs)
    }

    /// The split of ImpUnroll at the level of terms: `if-else`'s left-hand side matches `while`'s
    /// right-hand side (one-armed), and the result is the variant's `while` right-hand side.
    #[test]
    fn a_split_composes_by_matching_and_renaming() {
        let one = |c: L, s: L| app("SortStmt.«if(_)_»", vec![c, s]);
        let two = |c: L, s: L| {
            app(
                "SortStmt.«if(_)_else_»",
                vec![c, s, app("SortStmt.«{}»", vec![])],
            )
        };
        let body = app("SortStmt.«{_}»", vec![v("S")]);
        // a1's right-hand side over a1's variables (C, S); a2's sides over its own (C, S too)
        let rhs_a1 = one(v("C"), body.clone());
        let (la2, rhs_a2) = (one(v("C"), v("S")), two(v("C"), v("S")));
        let mut sig = BTreeMap::new();
        assert!(match_l(&la2, &rhs_a1, &mut sig));
        // a2's S is a1's body: one substitution, though the names coincide
        let comp = subst_bounded(&rhs_a2, &sig, 0);
        assert_eq!(comp, two(v("C"), body.clone()));
        // b's right-hand side with other names
        let rhs_b = two(v("C0"), app("SortStmt.«{_}»", vec![v("S0")]));
        let mut rho = BTreeMap::new();
        assert!(alpha_eq(&comp, &rhs_b, &mut rho));
        assert_eq!(rho.get("C").map(|s| s.as_str()), Some("C0"));
        // a renaming is one to one
        let mut rho = BTreeMap::new();
        assert!(!alpha_eq(
            &app("f", vec![v("x"), v("y")]),
            &app("f", vec![v("z"), v("z")]),
            &mut rho
        ));
        // a constructor clash
        assert!(!match_l(
            &two(v("C"), v("S")),
            &rhs_a1,
            &mut BTreeMap::new()
        ));
    }

    #[test]
    fn aliases_substitute_through_chains_and_stop_at_a_loop() {
        let s: BTreeMap<String, L> = [
            (
                "y".to_string(),
                app("SortStmt.«while(_)_»", vec![v("C"), v("S")]),
            ),
            ("c".to_string(), app("SortK.kseq", vec![v("y")])),
            ("z".to_string(), v("z")),
        ]
        .into_iter()
        .collect();
        assert_eq!(
            subst_bounded(&v("c"), &s, 16),
            app(
                "SortK.kseq",
                vec![app("SortStmt.«while(_)_»", vec![v("C"), v("S")])]
            )
        );
        assert_eq!(subst_bounded(&v("z"), &s, 16), v("z"));
    }

    #[test]
    fn constructors_render_by_their_dot_form() {
        let t = app(
            "SortKItem.inj_Stmt",
            vec![app(
                "SortStmt.«if(_)_»",
                vec![v("C"), app("K.f", vec![v("S")])],
            )],
        );
        assert_eq!(
            render_dot(&t, "KImp", &|x| format!("{x}'")),
            ".inj_Stmt (.«if(_)_» C' (KImp.K.f S'))"
        );
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
