//! `k2lean refine`: a stuttering bisimulation between two definitions whose steps do not
//! correspond one to one (`k2lean/docs/design.md`, section 3.5).
//!
//! Input: the compiled KORE of `A` and `B` (each generated into a library), the correspondence
//! `k2lean relate --per-rule true` reported (`--correspondence`), whose Lean module (`NS.Tr`)
//! holds the translation `tr` and one simulation lemma per pair of corresponding rules, and a
//! hand module (`--hand-module`, default `NS.Relation`) that supplies the non-local part of the
//! relation, `X : A.Top → B.Top → Prop`, the measures `μ : A.Top → Nat` and `ν : B.Top → Nat`,
//! and the parts listed in `--open` (one `KIND.«RULE» | hand` per line, `#` comments; `KIND` is
//! `fwd_tr`, `fwd_x`, `bwd_tr` or `bwd_x`).
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
//! Each part is an obligation by name, as confluence's slots are: stated (`fwd_tr.«r».statement :
//! Prop := A.Step.Rel.«r» (Stutter.FwdTr …)` and so on), and proved by its own theorem
//! (`fwd_tr.«r»`) when generated, by the hand module under that name when listed `| hand`, or left
//! open when listed by its name alone (a field of `Open`, the premise of `bisim` and its
//! corollaries). A part neither generated nor listed is refused.
//!
//! With `--hand-module none` there is no hand module: one step of `B` that `A` takes in two
//! (`find_splits`: `A`'s `a1` then `a2` against `B`'s `b`, no side conditions) gives `X` (one
//! constructor, `A` after `a1` against `B` after `b`), `X_inv`, `μ` (1 there), `ν = 0`, `R`, and
//! the parts that need `X`'s constructor: `fwd_tr a1`, `fwd_x a2`, `bwd_tr b`, and `bwd_x r` for
//! each step of `B` at `X` (`A` takes `a2`, `X_next`, then `r`'s counterpart). The output module
//! states and proves `bisim : StutterBisim A.Step B.Step (Stutter.Rel tr X) μ ν` and the transfer
//! of runs to terminal states in both directions.
//!
//! With priority ranks (both definitions with one list of priorities), a step of a rank `i > 0`
//! carries `hpri`, and its counterpart's step needs the same of the other definition: `relate
//! --per-rule` states it as a premise of `fwd.r` and `bwd.r`, and this module discharges it rule
//! by rule (`emit_priorities`: `pri_fwd.r`, `pri_bwd.r`, and `pri_mid` for the split's second
//! step, which `X` carries).
//!
//! With `--witnesses DIR`, programs on which the two definitions disagree refute the open parts
//! together (`witnesses`, `NS/Witnesses.lean`).

mod witnesses;

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
/// priorities when it has several, its top sort, its builtin sorts (whose values a translation
/// leaves as they are), and whether its library is the ranked one (`successors` without `rules`).
pub fn load_rules(kore: &str) -> (Vec<Rule>, Option<Vec<i64>>, String, BTreeSet<String>, bool) {
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
        ranked,
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

/// The parts the list (`--open`) names, each (kind, rule name) with whether the hand module
/// proves it (`KIND.«RULE» | hand`) or it is open (`KIND.«RULE»`, a field of `Open`).
fn read_open(path: &str) -> BTreeMap<(String, String), bool> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| fail(&format!("{path}: {e}")));
    text.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(|l| {
            crate::refuted::case_entry(l, &["fwd_tr", "fwd_x", "bwd_tr", "bwd_x"], "a part is sufficient for its rule's step of the bisimulation, not necessary, so its refutation says only that this `X` and these measures do not prove it")
                .unwrap_or_else(|e| fail(&format!("{path}: {e}")))
        })
        .collect()
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
            // the dot form takes one name: a constructor of a sort's own part (`SortKItem.Own.c`)
            // is qualified
            let atomic = |c: &str| c.split('«').next().is_some_and(|p| !p.contains('.'));
            let head = match h.split_once('.') {
                Some((sort, c)) if sort.starts_with("Sort") && !sort.contains('«') && atomic(c) => {
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

/// Whether `a` and `b` may be instances of one term, every variable of either taken as anything
/// (an over-approximation: a raw term, a builtin value or a function's result, is taken as
/// anything too).
fn may_unify(a: &L, b: &L) -> bool {
    match (a, b) {
        (L::Var(_), _) | (_, L::Var(_)) | (L::Raw(_), _) | (_, L::Raw(_)) => true,
        (L::App(h1, a1), L::App(h2, a2)) => {
            h1 == h2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| may_unify(x, y))
        }
        (L::Typed(e1, _), _) => may_unify(e1, b),
        (_, L::Typed(e2, _)) => may_unify(a, e2),
    }
}

/// The constructor applications of `t` and the occurrences of each variable; `None` when `t`
/// holds a raw term (a value whose size is not that of a constructor term).
fn size_profile(t: &L, apps: &mut usize, vars: &mut BTreeMap<String, usize>) -> Option<()> {
    match t {
        L::Var(v) => *vars.entry(v.clone()).or_default() += 1,
        L::App(_, xs) => {
            *apps += 1;
            for x in xs {
                size_profile(x, apps, vars)?;
            }
        }
        L::Typed(e, _) => size_profile(e, apps, vars)?,
        L::Raw(_) => return None,
    }
    Some(())
}

/// Whether every instance of `r` is smaller (`sizeOf`) than the instance of `l` it rewrites:
/// fewer constructor applications, and no variable more often than in `l`.
fn shrinks(l: &L, r: &L) -> bool {
    let (mut al, mut ar) = (0, 0);
    let (mut vl, mut vr) = (BTreeMap::new(), BTreeMap::new());
    if size_profile(l, &mut al, &mut vl).is_none() || size_profile(r, &mut ar, &mut vr).is_none() {
        return false;
    }
    ar < al && vr.iter().all(|(v, n)| vl.get(v).is_some_and(|m| n <= m))
}

/// The translation of `A`'s variable `v` of sort `t`: itself on a builtin sort.
fn tr_var(builtin: &BTreeSet<String>, t: &str, v: &str) -> String {
    if builtin.contains(t) {
        v.to_string()
    } else {
        format!("(tr_{} {v})", crate::terms::fsuffix(t))
    }
}

/// `X`, `X_inv`, `X_next` and the measures of a split (`--hand-module none`): `X` relates `A`'s
/// state after `a1` to `B`'s after `b`, its `B` side a pattern of `B`'s constructors over variables
/// each the translation of `A`'s (`cases` on `X` never inverts a translation); `μ` is 1 there,
/// where `A` stutters, and `ν` is 0. When `a2`'s result may be an intermediate state again (`a2`
/// rewrites to a continuation, which may start with the intermediate construct), `μ` is the
/// state's size there instead (`sizeOf`), which `a2` decreases when it removes constructors and
/// copies no variable (`shrinks`; else the split is refused); the result says which. With priorities, `a2`'s step needs that no rule of a rank
/// before `a2`'s applies at the intermediate state (`mid`, that rank when it is not 0), which `X`
/// carries from where the state was reached (`hp`), so that `X_next` completes the step.
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
    mid: Option<usize>,
) -> bool {
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
    if let Some(k) = mid {
        binders.push(format!("(hp : ∀ j, j < {k} → ¬ {na}.App j ({a_side}))"));
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
    // `A` completes its step from a state `X` relates: `a2`'s step, to the translation of `B`'s
    let fields = vec!["_"; 3 * vars.len()].join(" ");
    let hp = if mid.is_some() { " hp" } else { "" };
    let n2 = rules::ctor_args(&a2.step).len();
    writeln!(
        o,
        "/-- From a state `{x}` relates, `{na}` completes its step by `{a2n}`, to a state whose translation\nis `{nb}`'s. -/\ntheorem {x}_next {{c : {na}.{top}}} {{d : {nb}.{top}}} (h : {x} c d) :\n    ∃ c', {na}.Step c c' ∧ d = {tr} c' := by\n  cases h with\n  | split {fields}{hp} => subst_vars; exact ⟨_, {na}.Step.{} {}{hp}, rfl⟩\n",
        a2.lean,
        vec!["_"; n2].join(" ")
    )
    .unwrap();
    let pat = render_dot(&rhs_a1, na, &|_| "_".to_string());
    // `a2`'s result over `a1`'s variables, and whether it may be intermediate again
    let (la2, rhs_a2) = sides(a2);
    let mut sig = BTreeMap::new();
    match_l(&la2, &rhs_a1, &mut sig);
    let again = may_unify(&rhs_a1, &subst_bounded(&rhs_a2, &sig, 0));
    if again && !shrinks(&la2, &rhs_a2) {
        fail(&format!(
            "--hand-module none: `{a2n}` may lead to an intermediate state of the split again, and does not decrease the state's size: no measure is generated"
        ));
    }
    if again {
        writeln!(
            o,
            "/-- `{na}`'s measure: the state's size after `{an}`, where it stutters (`{a2n}` may lead to such a state\nagain, a smaller one); a measure for the proofs, with no code. -/\nnoncomputable def {mu} (c : {na}.{top}) : Nat :=\n  match c with\n  | {pat} => sizeOf c\n  | _ => 0\n\ntheorem {mu}_le (c : {na}.{top}) : {mu} c ≤ sizeOf c := by\n  unfold {mu}; split <;> omega\n"
        )
        .unwrap();
    } else {
        writeln!(
            o,
            "/-- `{na}`'s measure: 1 after `{an}`, where it stutters. -/\ndef {mu} : {na}.{top} → Nat\n  | {pat} => 1\n  | _ => 0\n"
        )
        .unwrap();
    }
    writeln!(
        o,
        "/-- `{nb}` never stutters. -/\ndef {nu} (_ : {nb}.{top}) : Nat := 0\n\n/-- The relation: `d` is the translation of `c`, or `{x}` relates them. -/\nabbrev R := Stutter.Rel {tr} {x}\n"
    )
    .unwrap();
    again
}

/// What the priority lemmas read: the two definitions' rules and constructors, the
/// correspondence, the split, the open list, the ranks, and the names of the module.
struct Pri<'a> {
    ra: &'a [Rule],
    rb: &'a [Rule],
    ca: &'a [preserves::Ctor],
    cb: &'a [preserves::Ctor],
    pairs: &'a BTreeMap<String, String>,
    split: Option<&'a Split>,
    open: &'a BTreeSet<(String, String)>,
    rank: &'a dyn Fn(&Rule) -> usize,
    na: &'a str,
    nb: &'a str,
    top: &'a str,
    tr: &'a str,
}

/// The priority lemmas written: per rule of `A` whose forward part at a translation is generated
/// (`pri_fwd.r`), per rule of `B` likewise (`pri_bwd.r`), whether the split's second step has
/// one (`pri_mid`), and the names for the axiom guard.
#[derive(Default)]
struct Pris {
    fwd: BTreeSet<usize>,
    bwd: BTreeSet<usize>,
    mid: bool,
    names: Vec<String>,
}

/// The priority hypotheses that the generated parts pass to the other side's steps
/// (`docs/design.md`, section 3.5, "Priorities"). A step of a rule of rank `i > 0` holds where no
/// rule of a rank before `i` applies (`hpri`); its counterpart's step needs the same of the other
/// definition, at the related state, which holds rule by rule: casing on which rule would apply
/// there, one of a rank `≥ i` is excluded by the rank, one with a counterpart applies on this side
/// too (`appbwd.q`, `appfwd.q`, the arms of `relate`'s `app_bwd` and `app_fwd`), against `hpri`,
/// and so does the split's `b` (through `a1`, the same left-hand side) and `a1` (through `b`);
/// `a2`'s left-hand side, the intermediate state, clashes with every translation of a paired
/// rule's. Any other rule without a counterpart of a rank before `i` is refused.
///
/// - `pri_fwd.r` (`A`'s rule `r`): `∀ j, j < i → ∀ d, tr lhs = d → ¬ B.App j d`, under `r`'s binders
///   and its `hpri`;
/// - `pri_bwd.r` (`B`'s rule `r`): `∀ c, tr c = lhs → ∀ j, j < i → ¬ A.App j c`;
/// - `pri_mid`: at the split's intermediate state (`a1`'s right-hand side), no rule of a rank before
///   `a2`'s applies, from `a1`'s `hpri` at its left-hand side: a rule that applies at the
///   intermediate state applies at the start (it reads the changed cells by variables, as K's
///   stream rules read `<k>`), or clashes with the intermediate state.
fn emit_priorities(o: &mut String, p: &Pri) -> Pris {
    let mut out = Pris::default();
    let (na, nb, tr, top) = (p.na, p.nb, p.tr, p.top);
    let paired_b: BTreeSet<&String> = p.pairs.values().collect();
    let generated_part =
        |kind: &str, r: &Rule| !p.open.contains(&(kind.to_string(), rules::display_name(r)));
    let fwd: Vec<usize> = (0..p.ra.len())
        .filter(|&i| {
            let r = &p.ra[i];
            (p.rank)(r) > 0
                && generated_part("fwd_tr", r)
                && (p.pairs.contains_key(&rules::display_name(r))
                    || p.split.is_some_and(|s| s.a1 == i))
        })
        .collect();
    // `B`'s rule `r`'s lemma is taken by its generated part at a translation, by its generated part
    // at an `X` state with a split (`A` completes its step, then takes `r`'s counterpart), and by
    // `split_bwd` for the split's `b`
    let bwd: Vec<usize> = (0..p.rb.len())
        .filter(|&j| {
            let r = &p.rb[j];
            let sb = p.split.is_some_and(|s| s.b == j);
            (p.rank)(r) > 0
                && (sb
                    || paired_b.contains(&rules::display_name(r))
                        && (generated_part("bwd_tr", r)
                            || p.split.is_some() && generated_part("bwd_x", r)))
        })
        .collect();
    let mid = p.split.filter(|s| (p.rank)(&p.ra[s.a2]) > 0);
    if fwd.is_empty() && bwd.is_empty() && mid.is_none() {
        return out;
    }
    writeln!(o, "/-! ## Priorities: where no rule of a rank before a step's applies on one side, none applies on the other -/\n").unwrap();
    let binders = |rel: &crate::render::Rel| -> String {
        rel.binders
            .iter()
            .map(|(x, t)| format!(" ({x} : {t})"))
            .chain(rel.hyps.iter().map(|(h, q)| format!(" ({h} : {q})")))
            .collect()
    };
    let fail_unpaired = |q: &Rule, r: &Rule| -> ! {
        fail(&format!(
            "rule {} has no counterpart and is of a rank before {}'s: whether it applies at the related state is not generated (priority ranks, docs/design.md section 3.5)",
            rules::display_name(q),
            rules::display_name(r)
        ))
    };
    // the matches of the split's rules at the other side's translation (`b` is `a1`'s left-hand
    // side, with the same rank)
    if let Some(sp) = p.split {
        let lowest = |r: &Rule| (p.rank)(r);
        let needs_bwd = fwd
            .iter()
            .any(|&i| lowest(&p.rb[sp.b]) < (p.rank)(&p.ra[i]));
        let needs_fwd = bwd
            .iter()
            .any(|&j| lowest(&p.ra[sp.a1]) < (p.rank)(&p.rb[j]));
        let (a1, b) = (&p.ra[sp.a1], &p.rb[sp.b]);
        let k = (p.rank)(b);
        if needs_bwd {
            writeln!(
                o,
                "open {nb} in\n/-- A match of `{}` at a translation is a match of `{}`, its left-hand side. -/\ntheorem split_appbwd {{c : {na}.{top}}}{}\n    (hd : {tr} c = {}) : {na}.App {k} c := by\n  k2l_inv\n  all_goals apply {na}.App.{}\n",
                rules::display_name(b),
                rules::display_name(a1),
                binders(&b.app),
                b.app.index.render_arg(),
                a1.lean
            )
            .unwrap();
            out.names.push("split_appbwd".into());
        }
        if needs_fwd {
            writeln!(
                o,
                "open {na} in\n/-- A match of `{}` translates to a match of `{}`, its left-hand side. -/\ntheorem split_appfwd{} :\n    {nb}.App {k} ({tr} {}) := by\n  apply {nb}.App.{}\n",
                rules::display_name(a1),
                rules::display_name(b),
                binders(&a1.app),
                a1.app.index.render_arg(),
                b.lean
            )
            .unwrap();
            out.names.push("split_appfwd".into());
        }
    }
    if let Some(sp) = mid {
        let (a1, a2) = (&p.ra[sp.a1], &p.ra[sp.a2]);
        let k2 = (p.rank)(a2);
        // a rule of a rank before `a2`'s that applies at the intermediate state, rebuilt at the start
        let rebuild: Vec<String> =
            p.ra.iter()
                .filter(|q| (p.rank)(q) < k2)
                .map(|q| format!("(apply {na}.App.{} <;> assumption)", q.lean))
                .collect();
        let frame = if rebuild.is_empty() {
            String::new()
        } else {
            format!(
                " | exact hpri _ (by omega) (by first | {})",
                rebuild.join(" | ")
            )
        };
        writeln!(
            o,
            "/-- No rule of a rank before `{}`'s applies at the state `{}` leads to, where none of a rank before\n`{}`'s applies at its start. -/\ntheorem pri_mid : {na}.Step.Rel.{} (fun _ c' => ∀ j, j < {k2} → ¬ {na}.App j c') := by\n  intro {} j hj ha\n  cases ha <;> first | exact absurd hj (by decide){frame}\n",
            rules::display_name(a2),
            rules::display_name(a1),
            rules::display_name(a1),
            p.ca[sp.a1].lean,
            p.ca[sp.a1].args.join(" ")
        )
        .unwrap();
        out.names.push("pri_mid".into());
        out.mid = true;
    }
    for &i in &fwd {
        let r = &p.ra[i];
        let k = (p.rank)(r);
        let mut arms = String::new();
        for (j, q) in p.rb.iter().enumerate() {
            let qargs = rules::ctor_args(&q.app).join(" ");
            let arm = if (p.rank)(q) >= k {
                "exact absurd hj (by decide)".to_string()
            } else if paired_b.contains(&rules::display_name(q)) {
                format!("exact hpri _ hj (appbwd.{} {qargs} hd)", q.lean)
            } else if p.split.is_some_and(|s| s.b == j) {
                format!("exact hpri _ hj (split_appbwd {qargs} hd)")
            } else {
                fail_unpaired(q, r)
            };
            writeln!(arms, "  | {} {qargs} => {arm}", q.lean).unwrap();
        }
        writeln!(
            o,
            "theorem pri_fwd.{} : {na}.Step.Rel.{} (fun c _ => ∀ j, j < {k} → ∀ d, {tr} c = d → ¬ {nb}.App j d) := by\n  intro {} j hj d hd hb\n  cases hb with\n{arms}",
            p.ca[i].lean,
            p.ca[i].lean,
            p.ca[i].args.join(" ")
        )
        .unwrap();
        out.names.push(format!("pri_fwd.{}", p.ca[i].lean));
        out.fwd.insert(i);
    }
    for &j in &bwd {
        let r = &p.rb[j];
        let k = (p.rank)(r);
        let mut arms = String::new();
        for (i, q) in p.ra.iter().enumerate() {
            let qargs = rules::ctor_args(&q.app).join(" ");
            let arm = if (p.rank)(q) >= k {
                "exact absurd hj (by decide)".to_string()
            } else if p.pairs.contains_key(&rules::display_name(q)) {
                format!("exact hpri _ hj (hd ▸ appfwd.{} {qargs})", q.lean)
            } else if p.split.is_some_and(|s| s.a1 == i) {
                format!("exact hpri _ hj (hd ▸ split_appfwd {qargs})")
            } else if p.split.is_some_and(|s| s.a2 == i) {
                "cases hd".to_string()
            } else {
                fail_unpaired(q, r)
            };
            writeln!(arms, "  | {} {qargs} => {arm}", q.lean).unwrap();
        }
        writeln!(
            o,
            "theorem pri_bwd.{} : {nb}.Step.Rel.{} (fun d _ => ∀ c, {tr} c = d → ∀ j, j < {k} → ¬ {na}.App j c) := by\n  intro {} c hd j hj ha\n  cases ha with\n{arms}",
            p.cb[j].lean,
            p.cb[j].lean,
            p.cb[j].args.join(" ")
        )
        .unwrap();
        out.names.push(format!("pri_bwd.{}", p.cb[j].lean));
        out.bwd.insert(j);
    }
    out
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
    let (ra, pa, top, builtin, ranked_a) = load_rules(&get("kore-a"));
    let (rb, pb, top_b, _, ranked_b) = load_rules(&get("kore-b"));
    // with priorities, a step of rank `i` carries that no rule of a rank before `i` applies
    // (`hpri`); a rank names the same place on both sides, so the two definitions have one list
    // of priorities
    if pa != pb {
        fail(&format!(
            "the two definitions' priority ranks differ ({:?}, {:?})",
            pa.unwrap_or_default(),
            pb.unwrap_or_default()
        ));
    }
    let prios = pa;
    let rank = |r: &Rule| {
        prios
            .as_ref()
            .and_then(|ps| ps.iter().position(|p| *p == r.priority))
            .unwrap_or(0)
    };
    if top != top_b {
        fail(&format!("the top sorts differ ({top}, {top_b})"));
    }
    let pairs = read_pairs(&get("correspondence"));
    let listed = opt.get("open").map(|p| read_open(p)).unwrap_or_default();
    // every listed part is not generated (the priority lemmas skip them); the open ones are
    // `Open`'s fields
    let open: BTreeSet<(String, String)> = listed.keys().cloned().collect();
    let opened: Vec<(String, String)> = listed
        .iter()
        .filter(|(_, h)| !**h)
        .map(|(c, _)| c.clone())
        .collect();
    let hand = opt
        .get("hand-module")
        .cloned()
        .unwrap_or(format!("{ns}.Relation"));
    let x = opt.get("extra").cloned().unwrap_or("X".into());
    let mu = opt.get("measure-a").cloned().unwrap_or("μ".into());
    let nu = opt.get("measure-b").cloned().unwrap_or("ν".into());
    let ca = preserves::ctors(&ra, prios.as_deref());
    let cb = preserves::ctors(&rb, prios.as_deref());
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
        let sp = ss.remove(0);
        // `b`'s priority hypothesis is `a1`'s, and `a2`'s at the intermediate state follows from
        // `a1`'s at its start (`pri_mid`), which covers the ranks before `a1`'s
        let (k1, k2, kb) = (rank(&ra[sp.a1]), rank(&ra[sp.a2]), rank(&rb[sp.b]));
        if k1 != kb || k2 > k1 {
            fail(&format!(
                "--hand-module none: the split's rules are of ranks {k1} and {k2} against {kb}; generated for one rank, or a second step of a rank before the first's"
            ));
        }
        Some(sp)
    } else {
        None
    };
    for ((k, r), h) in &listed {
        let (known, n) = if k.starts_with("fwd") {
            (&names_a, &na)
        } else {
            (&names_b, &nb)
        };
        if !known.contains(r) {
            fail(&format!("--open: {k}.«{r}»: no rule {r} of {n}"));
        }
        if *h && generated {
            fail(&format!(
                "--open: {k}.«{r}» | hand: there is no hand module (--hand-module none); leave it open (its name alone)"
            ));
        }
    }

    // a part at a translation is generated when its rule has a counterpart or is the split's (`a1`,
    // `b`), and one at an `X` state is always attempted: any other part is listed
    let missing: Vec<String> = ra
        .iter()
        .enumerate()
        .filter(|(i, r)| {
            !paired_a.contains(&rules::display_name(r))
                && !split.as_ref().is_some_and(|s| s.a1 == *i)
        })
        .map(|(_, r)| ("fwd_tr", rules::display_name(r)))
        .chain(
            rb.iter()
                .enumerate()
                .filter(|(j, r)| {
                    !paired_b.contains(&rules::display_name(r))
                        && !split.as_ref().is_some_and(|s| s.b == *j)
                })
                .map(|(_, r)| ("bwd_tr", rules::display_name(r))),
        )
        .filter(|(k, r)| !listed.contains_key(&(k.to_string(), r.clone())))
        .map(|(k, r)| format!("{k}.«{r}»"))
        .collect();
    if !missing.is_empty() {
        fail(&format!(
            "{} parts are not generated (their rules have no counterpart) and not listed in --open: list each `KIND.«RULE» | hand` (the hand module's) or `KIND.«RULE»` (open): {}",
            missing.len(),
            missing.join(", ")
        ));
    }
    // a program on which the two definitions disagree refutes the terminal corollaries, so the
    // open parts under which they hold; they are generated with `X` (`not_terminal_of_X`)
    if opt.contains_key("witnesses") {
        if opened.is_empty() {
            fail(
                "--witnesses: no part is open, so the bisimulation is proved and no two runs disagree; list the parts the witnesses refute in --open",
            );
        }
        if split.is_none() {
            fail(
                "--witnesses: the runs to terminal states are compared by `run_terminal`, which is generated with `X` (--hand-module none), not with a hand module's",
            );
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
        "The rest are the hand\nmodule's, under the part's name (`fwd_tr.«r»`, `fwd_x.«r»`, `bwd_tr.«r»`, `bwd_x.«r»`), or open."
    };
    writeln!(
        o,
        "/-! Generated by `k2lean refine`; do not edit.\n\n\
The stuttering bisimulation between `{na}.Step` and `{nb}.Step` through\n\
`Stutter.Rel {tr} {x}` (`d` is the translation of `c`, or `{x}` relates them), with the measures\n\
`{mu}` and `{nu}` {whose}. One case per rule and direction, in two parts (`Stutter.fwdQ_of`,\n\
`Stutter.bwdQ_of`): at a translation, from the simulation lemma of `relate --per-rule` when the\n\
rule has a counterpart; at a state `{x}` relates, by `cases` on `{x}`. {rest} Each part is an\n\
obligation by name (stated below): generated, the hand module's, or open (a field of `Open`, the\n\
premise of `bisim`), as `--open` lists it. -/\n"
    )
    .unwrap();
    writeln!(o, "set_option maxHeartbeats 0\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n").unwrap();
    // whether `μ` is the state's size (`emit_split`)
    let mut sized = false;
    if let Some(sp) = &split {
        let k2 = rank(&ra[sp.a2]);
        sized = emit_split(
            &mut o,
            sp,
            &ra,
            &rb,
            &builtin,
            &na,
            &nb,
            &top,
            &tr,
            &x,
            &mu,
            &nu,
            (k2 > 0).then_some(k2),
        );
    }
    // each part stated, whoever proves it: generated below, the hand module, or `Open`
    let stmt = |kind: &str, lean: &str| -> String {
        let (n, q, s, m) = match kind {
            "fwd_tr" => (&na, "FwdTr", &nb, &mu),
            "fwd_x" => (&na, "FwdX", &nb, &mu),
            "bwd_tr" => (&nb, "BwdTr", &na, &nu),
            _ => (&nb, "BwdX", &na, &nu),
        };
        format!("{n}.Step.Rel.{lean} (Stutter.{q} {tr} {s}.Step {x} {m})")
    };
    writeln!(
        o,
        "/-! ## The parts' statements\n\nEach part is an obligation by name: proved below, by the hand module, or open (a field of\n`Open`), as the list (`--open`) marks it. -/\n"
    )
    .unwrap();
    for (cs, kinds) in [(&ca, ["fwd_tr", "fwd_x"]), (&cb, ["bwd_tr", "bwd_x"])] {
        for c in cs.iter() {
            for k in kinds {
                writeln!(
                    o,
                    "def {k}.{}.statement : Prop := {}",
                    c.lean,
                    stmt(k, &c.lean)
                )
                .unwrap();
            }
        }
    }
    // a name for `Open`'s premise that no rule's variable takes (the cases introduce them)
    let mut ov = "O".to_string();
    while ca.iter().chain(&cb).any(|c| c.args.contains(&ov)) {
        ov.push('\'');
    }
    if !opened.is_empty() {
        writeln!(
            o,
            "\n/-- The parts left open (`--open`, a name alone): the premise of `bisim`. -/\nstructure Open : Prop where"
        )
        .unwrap();
        for (k, r) in &opened {
            let rs = if k.starts_with("fwd") { &ra } else { &rb };
            let l = &rs
                .iter()
                .find(|x| &rules::display_name(x) == r)
                .unwrap()
                .lean;
            writeln!(o, "  «{k}.{r}» : {k}.{l}.statement").unwrap();
        }
    }
    o.push('\n');
    let (ob, oa) = if opened.is_empty() {
        (String::new(), String::new())
    } else {
        (format!(" ({ov} : Open)"), format!("{ov} "))
    };
    // the priority hypotheses of the other side's steps, per rule whose generated part takes
    // one (design.md, section 3.5, "Priorities")
    let pri = emit_priorities(
        &mut o,
        &Pri {
            ra: &ra,
            rb: &rb,
            ca: &ca,
            cb: &cb,
            pairs: &pairs,
            split: split.as_ref(),
            open: &open,
            rank: &rank,
            na: &na,
            nb: &nb,
            top: &top,
            tr: &tr,
        },
    );
    let mut guard = vec![];
    // per kind: generated, by hand, open
    let mut counts: BTreeMap<&str, (usize, usize, usize)> = BTreeMap::new();
    let (mut hand_cases, mut open_cases) = (vec![], vec![]);
    // a part: its own theorem when generated (the statement written out), the hand module's under
    // its name when listed `| hand`, `Open`'s field when listed alone; the term its step's case takes
    let mut part = |o: &mut String,
                    kind: &'static str,
                    (name, lean): (&str, &str),
                    args: &[String],
                    auto: Option<String>|
     -> String {
        let e = counts.entry(kind).or_default();
        let applied = |f: String| {
            if args.is_empty() {
                f
            } else {
                format!("({f} {})", args.join(" "))
            }
        };
        match (listed.get(&(kind.to_string(), name.to_string())), auto) {
            (None, Some(tac)) => {
                e.0 += 1;
                writeln!(
                    o,
                    "theorem {kind}.{lean} : {} := by\n{}  {}\n",
                    stmt(kind, lean),
                    intro(args),
                    tac.replace("\n    ", "\n  ")
                )
                .unwrap();
                applied(format!("{kind}.{lean}"))
            }
            (Some(true), _) => {
                e.1 += 1;
                hand_cases.push(format!("{kind}.«{name}»"));
                applied(format!("{kind}.{lean}"))
            }
            (Some(false), _) => {
                e.2 += 1;
                open_cases.push(format!("{kind}.«{name}»"));
                applied(format!("{ov}.«{kind}.{name}»"))
            }
            (None, None) => {
                unreachable!("{kind}.«{name}»: refused above, neither generated nor listed")
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
    // the other side's priority hypothesis, for a step of a rule of rank `> 0`: `fwd.r`'s premise
    // (`B`'s at the translation), `bwd.r`'s (`A`'s at the state translated)
    let pri_f = |i: usize, args: &str| {
        if pri.fwd.contains(&i) {
            format!(" (fun j hj => pri_fwd.{} {args} j hj _ rfl)", ca[i].lean)
        } else {
            String::new()
        }
    };
    let pri_b = |j: usize, args: &str, c: &str, e: &str| {
        if pri.bwd.contains(&j) {
            format!(" (pri_bwd.{} {args} {c} {e})", cb[j].lean)
        } else {
            String::new()
        }
    };
    if let Some(sp) = &split {
        let (a1, b) = (&ra[sp.a1], &rb[sp.b]);
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
        let a1args = ca[sp.a1].args.join(" ");
        let hp = if pri.mid {
            format!(" (pri_mid {a1args})")
        } else {
            String::new()
        };
        split_fwd_tr = Some((
            sp.a1,
            format!(
                "exact Or.inl ⟨_, .single ({nb}.Step.{} {}{}), Or.inr ({x}.split {} {}{hp})⟩",
                cb[sp.b].lean,
                bargs.join(" "),
                pri_f(sp.a1, &a1args),
                under(2 * n),
                vec!["rfl"; n].join(" ")
            ),
        ));
        split_fwd_x = Some((
            sp.a2,
            format!(
                "intro d hX; cases hX <;> first | done | contradiction | (simp_all; done) | (subst_vars; exact Or.inr ⟨Or.inl rfl, {}⟩)",
                if sized {
                    format!("Nat.lt_of_le_of_lt ({mu}_le _) (by simp [{mu}]; omega)")
                } else {
                    format!("by simp [{mu}]")
                }
            ),
        ));
        // `B`'s step against `A`'s two from a translation (`split_bwd`): `a1` where no rule of a
        // rank before `b`'s applies in `A` (`pri_bwd.b`), then `a2` at the intermediate state
        // (`pri_mid`); at a translation, and at a state `X` relates once `A` has completed its
        // step there (`X_next`), since `b`'s left-hand side may match `B`'s side of `X`
        let n1 = rules::ctor_args(&a1.step).len();
        let (have, hp1, hp2) = if pri.bwd.contains(&sp.b) {
            (
                format!(
                    " have hp := pri_bwd.{} {} c hd;",
                    cb[sp.b].lean,
                    cb[sp.b].args.join(" ")
                ),
                " hp".to_string(),
                if pri.mid {
                    format!(" (pri_mid {} hp)", under(n1))
                } else {
                    String::new()
                },
            )
        } else {
            (String::new(), String::new(), String::new())
        };
        let bargs_all = cb[sp.b].args.join(" ");
        writeln!(
            o,
            "/-- `{}` of `{nb}` from a translation is `{}` then `{}` of `{na}`. -/\ntheorem split_bwd : {nb}.Step.Rel.{} (fun d d' => ∀ c, {tr} c = d → ∃ c', Relation.TransGen {na}.Step c c' ∧ d' = {tr} c') := by\n  intro {bargs_all} c hd;{have} k2l_inv; exact ⟨_, .tail (.single ({na}.Step.{} {}{hp1})) ({na}.Step.{} {}{hp2}), rfl⟩\n",
            rules::display_name(b),
            rules::display_name(a1),
            rules::display_name(&ra[sp.a2]),
            cb[sp.b].lean,
            ca[sp.a1].lean,
            under(n1),
            ca[sp.a2].lean,
            under(rules::ctor_args(&ra[sp.a2].step).len())
        )
        .unwrap();
        guard.push("split_bwd".into());
        split_bwd_tr = Some((
            sp.b,
            format!(
                "intro c hd; obtain ⟨c', hc', e⟩ := split_bwd {bargs_all} c hd.symm; exact Or.inl ⟨c', hc', Or.inl e⟩"
            ),
        ));
        split_bwd_x.insert(
            sp.b,
            format!(
                "intro c hX; first | (cases hX <;> first | done | contradiction | (simp_all; done)) | (obtain ⟨c₁, h₁, e⟩ := {x}_next hX; obtain ⟨c₂, h₂, e₂⟩ := split_bwd {bargs_all} c₁ e.symm; exact Or.inl ⟨c₂, .trans (.single h₁) h₂, Or.inl e₂⟩)"
            ),
        );
        // a paired step of `B` at a state `X` relates: `A` completes its step (`X_next`), then
        // takes the counterpart from the translation (`bwd.r`)
        for (j, r) in rb.iter().enumerate() {
            if !paired_b.contains(&rules::display_name(r)) {
                continue;
            }
            let args = cb[j].args.join(" ");
            split_bwd_x.insert(
                j,
                format!(
                    "intro c hX; first | (cases hX <;> first | done | contradiction | (simp_all; done)) | (obtain ⟨c₁, h₁, e⟩ := {x}_next hX; obtain ⟨c₂, h₂, e₂⟩ := bwd.{} {args} c₁ e.symm{}; exact Or.inl ⟨c₂, .tail (.single h₁) h₂, Or.inl e₂⟩)",
                    cb[j].lean,
                    pri_b(j, &args, "c₁", "e.symm")
                ),
            );
        }
    }
    writeln!(o, "/-! ## Forward: the steps of `{na}` -/\n").unwrap();
    for (idx, (r, c)) in ra.iter().zip(&ca).enumerate() {
        let name = rules::display_name(r);
        let args = &c.args;
        let sep = if args.is_empty() { "" } else { " " };
        let tr_auto = pairs
            .contains_key(&name)
            .then(|| {
                format!(
                    "exact Or.inl ⟨_, .single (fwd.{}{sep}{}{}), Or.inl rfl⟩",
                    c.lean,
                    args.join(" "),
                    pri_f(idx, &args.join(" "))
                )
            })
            .or_else(|| {
                split_fwd_tr
                    .as_ref()
                    .filter(|(i, _)| *i == idx)
                    .map(|(_, t)| t.clone())
            });
        let ht = part(&mut o, "fwd_tr", (&name, &c.lean), args, tr_auto);
        // a rule of a rank before `a2`'s may match `A`'s side of `X` (one that does not read what
        // `a1` changed: K's stream rules), where `X`'s `hp` says no such rule applies
        let x_auto = match (&split_fwd_x, &split) {
            (Some((i, t)), _) if *i == idx => t.clone(),
            (_, Some(sp)) if pri.mid && rank(r) < rank(&ra[sp.a2]) => format!(
                "intro d hX; first | (cases hX <;> first | done | contradiction | (simp_all; done)) | (cases hX with | split {} hp => exact (hp {} (by decide) (by apply {na}.App.{} <;> assumption)).elim)",
                vec!["_"; 3 * ra[sp.a1].step.binders.len()].join(" "),
                rank(r),
                c.lean
            ),
            _ => refute.to_string(),
        };
        let hx = part(&mut o, "fwd_x", (&name, &c.lean), args, Some(x_auto));
        writeln!(
            o,
            "theorem stutter_fwd.{}{ob} : {na}.Step.Rel.{} (Stutter.FwdQ {tr} {nb}.Step {x} {mu}) := by\n{}  exact Stutter.fwdQ_of {ht} {hx}\n",
            c.lean,
            c.lean,
            intro(args)
        )
        .unwrap();
        guard.push(format!("stutter_fwd.{}", c.lean));
    }
    writeln!(o, "/-! ## Backward: the steps of `{nb}` -/\n").unwrap();
    for (idx, (r, c)) in rb.iter().zip(&cb).enumerate() {
        let name = rules::display_name(r);
        let args = &c.args;
        let sep = if args.is_empty() { "" } else { " " };
        let tr_auto = paired_b
            .contains(&name)
            .then(|| {
                format!(
                    "intro c hd\n    obtain ⟨c', hc', e⟩ := bwd.{}{sep}{} c hd.symm{}\n    exact Or.inl ⟨c', .single hc', Or.inl e⟩",
                    c.lean,
                    args.join(" "),
                    pri_b(idx, &args.join(" "), "c", "hd.symm")
                )
            })
            .or_else(|| split_bwd_tr.as_ref().filter(|(i, _)| *i == idx).map(|(_, t)| t.clone()));
        let ht = part(&mut o, "bwd_tr", (&name, &c.lean), args, tr_auto);
        let x_auto = split_bwd_x.get(&idx).cloned().unwrap_or_else(|| {
            "intro c hX; cases hX <;> first | done | contradiction | (simp_all; done)".to_string()
        });
        let hx = part(&mut o, "bwd_x", (&name, &c.lean), args, Some(x_auto));
        writeln!(
            o,
            "theorem stutter_bwd.{}{ob} : {nb}.Step.Rel.{} (Stutter.BwdQ {tr} {na}.Step {x} {nu}) := by\n{}  exact Stutter.bwdQ_of {ht} {hx}\n",
            c.lean,
            c.lean,
            intro(args)
        )
        .unwrap();
        guard.push(format!("stutter_bwd.{}", c.lean));
    }
    let list = |cs: &[preserves::Ctor], p: &str| {
        cs.iter()
            .map(|c| {
                if oa.is_empty() {
                    format!("{p}.{}", c.lean)
                } else {
                    format!("({p}.{} {ov})", c.lean)
                }
            })
            .collect::<Vec<_>>()
            .join(" ")
    };
    writeln!(
        o,
        "/-! ## The stuttering bisimulation and what it transfers -/\n"
    )
    .unwrap();
    let bi = if oa.is_empty() {
        "bisim".to_string()
    } else {
        format!("(bisim {ov})")
    };
    writeln!(
        o,
        "theorem bisim{ob} : StutterBisim {na}.Step {nb}.Step (Stutter.Rel {tr} {x}) {mu} {nu} :=\n  Stutter.bisim_of\n    (fun h => {na}.Step.rel_of {} h)\n    (fun h => {nb}.Step.rel_of {} h)\n",
        list(&ca, "stutter_fwd"),
        list(&cb, "stutter_bwd")
    )
    .unwrap();
    writeln!(
        o,
        "/-- A run of `{na}` to a terminal state is matched, from the translation of its start, by a run\nof `{nb}` to a terminal state related to it. -/\n\
theorem run_fwd{ob} {{c c' : {ta}}} (h : Star {na}.Step c c') (ht : Terminal {na}.Step c') :\n    ∃ d', Star {nb}.Step ({tr} c) d' ∧ Terminal {nb}.Step d' ∧ Stutter.Rel {tr} {x} c' d' :=\n  {bi}.terminal_run (Or.inl rfl) h ht\n\n\
/-- A run of `{nb}` from a translation to a terminal state is matched by a run of `{na}` to a\nterminal state related to it. -/\n\
theorem run_bwd{ob} {{c : {ta}}} {{d' : {tb}}} (h : Star {nb}.Step ({tr} c) d') (ht : Terminal {nb}.Step d') :\n    ∃ c', Star {na}.Step c c' ∧ Terminal {na}.Step c' ∧ Stutter.Rel {tr} {x} c' d' :=\n  {bi}.symm.terminal_run (Or.inl rfl) h ht\n"
    )
    .unwrap();
    guard.extend(pri.names.iter().cloned());
    if split.is_some() {
        guard.push(format!("{x}_next"));
    }
    guard.extend(["bisim".into(), "run_fwd".into(), "run_bwd".into()]);
    // a generated `X` never relates a terminal state of `A` (`X_next`), so two runs to terminal
    // states end in translations of each other
    if split.is_some() {
        writeln!(
            o,
            "/-- `{x}` never relates a terminal state of `{na}`, which completes its step from there (`{x}_next`). -/\n\
theorem not_terminal_of_{x} {{c : {ta}}} {{d : {tb}}} (h : {x} c d) : ¬ Terminal {na}.Step c :=\n  fun ht => let ⟨_, hc, _⟩ := {x}_next h; ht _ hc\n\n\
/-- A run of `{na}` to a terminal state and the run of `{nb}` from the translation of its start to a\nterminal state end in translations of each other. -/\n\
theorem run_terminal{ob} {{c c' : {ta}}} (h : Star {na}.Step c c') (ht : Terminal {na}.Step c') :\n    ∃ d', Star {nb}.Step ({tr} c) d' ∧ Terminal {nb}.Step d' ∧ d' = {tr} c' := by\n  obtain ⟨d', hd, htd, hr | hx⟩ := run_fwd {oa}h ht\n  · exact ⟨d', hd, htd, hr⟩\n  · exact absurd ht (not_terminal_of_{x} hx)\n\n\
theorem run_terminal_back{ob} {{c : {ta}}} {{d' : {tb}}} (h : Star {nb}.Step ({tr} c) d') (ht : Terminal {nb}.Step d') :\n    ∃ c', Star {na}.Step c c' ∧ Terminal {na}.Step c' ∧ d' = {tr} c' := by\n  obtain ⟨c', hc, htc, hr | hx⟩ := run_bwd {oa}h ht\n  · exact ⟨c', hc, htc, hr⟩\n  · exact absurd htc (not_terminal_of_{x} hx)\n"
        )
        .unwrap();
        guard.extend([
            format!("not_terminal_of_{x}"),
            "run_terminal".into(),
            "run_terminal_back".into(),
        ]);
    }
    writeln!(o, "#k2l_assert_axioms {}\n\nend {ns}", guard.join(" ")).unwrap();
    write_file(&get("out"), &o);
    let total: (usize, usize, usize) = counts
        .values()
        .fold((0, 0, 0), |(a, b, c), (x, y, z)| (a + x, b + y, c + z));
    let mut rep = format!(
        "# k2lean refine: {na} against {nb}\n\nrules_a = {}\nrules_b = {}\npairs = {}\nparts = {}\nautomatic = {}\nhand = {}\nopen = {}\n\n[parts]\n",
        ra.len(),
        rb.len(),
        pairs.len(),
        total.0 + total.1 + total.2,
        total.0,
        total.1,
        total.2
    );
    for (k, (a, h, n)) in &counts {
        writeln!(rep, "{k} = {{ automatic = {a}, hand = {h}, open = {n} }}").unwrap();
    }
    if prios.is_some() {
        writeln!(
            rep,
            "\n[priorities]\nranks = {}\nfwd = {}\nbwd = {}\nmid = {}",
            prios.as_ref().map_or(0, |ps| ps.len()),
            pri.fwd.len(),
            pri.bwd.len(),
            pri.mid
        )
        .unwrap();
    }
    writeln!(
        rep,
        "\n[hand]\ncases = {hand_cases:?}\n\n[open]\ncases = {open_cases:?}"
    )
    .unwrap();
    if let Some(dir) = opt.get("witnesses") {
        let out = get("out");
        let path = std::path::Path::new(&out).with_file_name("Witnesses.lean");
        let (text, names) = witnesses::emit(&witnesses::Ctx {
            dir,
            kore_a: &get("kore-a"),
            na: &na,
            nb: &nb,
            ns: &ns,
            ta: &ta,
            tr: &tr,
            ranked: (ranked_a, ranked_b),
        });
        write_file(&path.to_string_lossy(), &text);
        writeln!(
            rep,
            "\n[witnesses]  # programs on which the two definitions disagree (`witness.NAME.disagrees`), which refute the open parts together (`Open.refuted`)\nnames = {names:?}\nopen_refuted_by = {:?}",
            names[0]
        )
        .unwrap();
    }
    if let Some(p) = opt.get("report") {
        write_file(p, &rep);
    }
    eprintln!(
        "refine: {} + {} rules, {} pairs; {} case parts, {} generated, {} by hand, {} open",
        ra.len(),
        rb.len(),
        pairs.len(),
        total.0 + total.1 + total.2,
        total.0,
        total.1,
        total.2
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
    fn open_parts_are_named_hand_or_open() {
        let p = tmp(
            "open",
            "# parts not generated\nfwd_tr.«IMP.while» | hand  # by hand\n\nbwd_x.«IMP-SYNTAX.if(_)_else_ heat»\n",
        );
        let o = read_open(&p);
        assert_eq!(o.get(&("fwd_tr".into(), "IMP.while".into())), Some(&true));
        // a rule name may contain spaces inside `«»`
        assert_eq!(
            o.get(&("bwd_x".into(), "IMP-SYNTAX.if(_)_else_ heat".into())),
            Some(&false)
        );
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

    /// `vmpop`'s split at the level of terms: `pop-done` rewrites `#pop ~> K` to `K`, which may be
    /// `#pop ~> K'` again (a variable unifies with anything), and removes constructors without
    /// copying a variable; kimp's `if-else` leads to the two-armed form, never the one-armed again.
    #[test]
    fn a_split_whose_second_step_may_lead_to_its_intermediate_state_shrinks() {
        let k = |item: L, rest: L| app("SortK.kseq", vec![item, rest]);
        let pop = app("SortKItem.Own.«#pop»", vec![]);
        let st = |kk: L, s: L| app("T", vec![app("K", vec![kk]), app("S", vec![s])]);
        let cons = |x: L, s: L| app("SortStack.«_:_»", vec![x, s]);
        // a1's right-hand side, a2's sides
        let mid = st(k(pop.clone(), v("K")), cons(v("G"), v("S")));
        let after = st(v("K"), v("S"));
        assert!(may_unify(&mid, &after));
        assert!(shrinks(&mid, &after));
        // a copied variable, a raw term, or as many constructors do not shrink
        assert!(!shrinks(
            &mid,
            &st(k(pop.clone(), v("K")), cons(v("G"), v("G")))
        ));
        assert!(!shrinks(&mid, &st(v("K"), L::Raw("(f S)".into()))));
        assert!(!shrinks(&mid, &st(k(pop, v("K")), cons(v("G"), v("S")))));
        let one = app("SortStmt.«if(_)_»", vec![v("C"), v("S")]);
        let two = app(
            "SortStmt.«if(_)_else_»",
            vec![v("C"), v("S"), app("SortStmt.«{}»", vec![])],
        );
        assert!(!may_unify(&k(one, v("K")), &k(two, v("K"))));
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
