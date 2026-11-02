//! `k2lean refine`: a stuttering bisimulation between two definitions whose steps do not
//! correspond one to one (`k2lean/docs/design.md`, section 3.5).
//!
//! Input: the compiled KORE of `A` and `B` (each generated into a library), the correspondence
//! `k2lean relate --per-rule true` reported (`--correspondence`), whose Lean module (`NS.Tr`)
//! holds the translation `tr` and one simulation lemma per pair of corresponding rules, and the
//! parts listed in `--open` (one `KIND.«RULE» | hand` or `KIND.«RULE»` per line, `#` comments;
//! `KIND` is `fwd_tr`, `fwd_x`, `bwd_tr` or `bwd_x`). The non-local part of the relation,
//! `X : A.Top → B.Top → Prop`, and the measures `μ : A.Top → Nat` and `ν : B.Top → Nat` are
//! generated (below), or a relation module's (`--relation-module M`, which then holds the hand
//! parts too).
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
//! A rule with no counterpart whose name the other side's rule with no counterpart has too (its
//! namesake: the two differ in what they read) has its parts at a translation attempted
//! generically (`near_attempt`): the configuration split by the rules' patterns, each case
//! refuted by the legality, or matched by the namesake's step, or excluded by an earlier rule's
//! match; and so is a priority lemma's arm at an earlier rule with no counterpart that may apply
//! (`pri_arm`). A case no closer closes fails the proof at the part's name, and the author lists
//! it.
//!
//! Each part is an obligation by name, as confluence's slots are: stated (`fwd_tr.«r».statement :
//! Prop := A.Step.Rel.«r» (Stutter.FwdTr …)` and so on), and proved by its own theorem
//! (`fwd_tr.«r»`) when generated, by the hand module under that name when listed `| hand`, or left
//! open when listed by its name alone (a field of `Open`, the premise of `bisim` and its
//! corollaries). A part neither generated nor listed is refused.
//!
//! Without a relation module, one step of `B` that `A` takes in two (`find_splits`: `A`'s `a1`
//! then `a2` against `B`'s `b`, no side conditions) gives `X` (one constructor, `A` after `a1`
//! against `B` after `b`), `X_inv`, `μ` (1 there), `ν = 0`, and the parts that need `X`'s
//! constructor: `fwd_tr a1`, `fwd_x a2`, `bwd_tr b`, and `bwd_x r` for each step of `B` at `X`
//! (`A` takes `a2`, `X_next`, then `r`'s counterpart); with no such step, `X` relates nothing and
//! the measures are 0. `X`, the measures, the parts' statements and `Open` are in
//! `NS/RefineDefs.lean`, which the hand module (`--hand-module M`, the parts listed `| hand`)
//! imports; the output module imports it (or the hand module) and states and proves
//! `bisim : StutterBisim A.Step B.Step (Stutter.Rel tr X) μ ν` and the transfer of runs to
//! terminal states in both directions.
//!
//! Under a legality (`--assume-invariant NAME`, a predicate of `A`'s configurations that `A`'s
//! steps preserve, `NAME.preserved`, as `gen --invariant` proves one), the relation is
//! `Stutter.RelI tr X NAME` (`NAME c ∧ Stutter.Rel tr X c d`) and every part is owed at the
//! configurations satisfying it (`Stutter.FwdTrI` and so on): an optimization that holds only on
//! reachable configurations (a cache, a check the invariant makes redundant) relates. The
//! generated parts do not use it; the hand parts do.
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
            crate::refuted::case_entry(l, &["fwd_tr", "fwd_x", "bwd_tr", "bwd_x", "pri_fwd", "pri_bwd"], "a part is sufficient for its rule's step of the bisimulation, not necessary, so its refutation says only that this `X` and these measures do not prove it")
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

/// A pattern of `k2l_cases`: a variable left as it is (`_`), or cased on, the arguments of its
/// constructors cased as the subpatterns say, by position (`⟨p0, …⟩`).
#[derive(Clone, Debug, PartialEq)]
enum Pat {
    Leave,
    Case(Vec<Pat>),
}

impl Pat {
    /// The coarsest pattern that cases as much as both.
    fn merge(&self, o: &Pat) -> Pat {
        match (self, o) {
            (Pat::Leave, p) | (p, Pat::Leave) => p.clone(),
            (Pat::Case(a), Pat::Case(b)) => Pat::Case(
                (0..a.len().max(b.len()))
                    .map(|i| {
                        a.get(i)
                            .unwrap_or(&Pat::Leave)
                            .merge(b.get(i).unwrap_or(&Pat::Leave))
                    })
                    .collect(),
            ),
        }
    }

    fn render(&self) -> String {
        match self {
            Pat::Leave => "_".into(),
            Pat::Case(xs) => {
                let n = xs
                    .iter()
                    .rposition(|p| *p != Pat::Leave)
                    .map_or(0, |i| i + 1);
                let inner: Vec<String> = xs[..n].iter().map(Pat::render).collect();
                format!("⟨{}⟩", inner.join(", "))
            }
        }
    }
}

/// The shape a variable is cased to so that `t` matches or clashes at each case by constructors: a
/// constructor application of a generated sort cases on its arguments' shapes, a Bool literal on
/// the two values; an injection (a function of the arity-indexed family), any other builtin value
/// or a variable is left.
fn shape(t: &L) -> Pat {
    match t {
        L::App(h, xs) if h.starts_with("Sort") && !h.contains(".inj_") => {
            Pat::Case(xs.iter().map(shape).collect())
        }
        L::Raw(r) if r == "true" || r == "false" => Pat::Case(vec![]),
        L::Typed(e, _) => shape(e),
        _ => Pat::Leave,
    }
}

/// The case split of the variables of `own` (a rule's left-hand side, its variables' sorts in
/// `types`) at which one of `others` (the left-hand sides whose match the attempt decides) has a
/// constructor or a Bool literal, as deep as theirs: after it, each of `others` matches or clashes
/// at each case by constructors (pattern compilation). A variable of `K` or `KItem` (the
/// computation, whose injections are functions) or of a builtin sort other than `Bool` is not
/// cased. In the order the variables are first met.
fn case_split(
    own: &L,
    others: &[L],
    types: &BTreeMap<String, String>,
    builtin: &BTreeSet<String>,
) -> Vec<(String, Pat)> {
    fn walk(own: &L, other: &L, ok: &dyn Fn(&str) -> bool, out: &mut Vec<(String, Pat)>) {
        match (own, other) {
            (L::Var(v), t) => {
                let p = shape(t);
                if p == Pat::Leave || !ok(v) {
                    return;
                }
                match out.iter_mut().find(|(w, _)| w == v) {
                    Some((_, q)) => *q = q.merge(&p),
                    None => out.push((v.clone(), p)),
                }
            }
            (L::App(h1, a1), L::App(h2, a2)) if h1 == h2 && a1.len() == a2.len() => {
                for (x, y) in a1.iter().zip(a2) {
                    walk(x, y, ok, out);
                }
            }
            (L::Typed(e1, _), L::Typed(e2, _)) => walk(e1, e2, ok, out),
            (L::Typed(e, _), t) => walk(e, t, ok, out),
            (t, L::Typed(e, _)) => walk(t, e, ok, out),
            _ => {}
        }
    }
    let ok = |v: &str| {
        types.get(v).is_some_and(|t| {
            t != "SortK" && t != "SortKItem" && (t == "SortBool" || !builtin.contains(t))
        })
    };
    let mut out = vec![];
    for o in others {
        walk(own, o, &ok, &mut out);
    }
    out
}

/// The case split as tactics, one per line (`k2l_cases v with p`, on every goal after the first).
fn render_split(split: &[(String, Pat)]) -> Vec<String> {
    split
        .iter()
        .enumerate()
        .map(|(i, (v, p))| {
            let all = if i == 0 { "" } else { "all_goals " };
            format!("{all}k2l_cases {v} with {}", p.render())
        })
        .collect()
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
        "/-- From a state `{x}` relates, `{na}` completes its step by `{a2n}`, to a state whose translation\nis `{nb}`'s. -/\ntheorem {x}_next {{c : {na}.{top}}} {{d : {nb}.{top}}} (h : {x} c d) :\n    ∃ c', {na}.Step c c' ∧ d = {tr} c' := by\n  cases h with\n  | «split» {fields}{hp} => subst_vars; exact ⟨_, {na}.Step.{} {}{hp}, rfl⟩\n",
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
/// A legality (`--assume-invariant`): the predicate, its preservation by `A`'s steps
/// (`--invariant-preserved`) and the module stating them (`--invariant-module`).
struct Inv {
    name: String,
    pres: String,
    module: String,
    /// `A`'s generated invariant (`NA.Invariant` of `NA.Invariants`), whose `init_holds` states it
    /// at the initial configuration
    generated: bool,
    /// what unfolds it (`--invariant-unfold`, the `invariant-unfold.txt` of `gen --invariant`, with
    /// the predicate itself), for the generic attempts' closers; names relative to `A`'s namespace
    unfold: Option<Vec<String>>,
}

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
    /// the legality (`--assume-invariant`), which every lemma takes at `A`'s state
    inv: Option<&'a str>,
    /// the list (`--open`): a lemma listed `pri_fwd.«r» | hand` is the hand module's
    listed: &'a BTreeMap<(String, String), bool>,
    /// the legality's refutation (`k2l_inv_absurd hinv in NA […]`, with `--invariant-unfold`): an
    /// earlier rule without a counterpart that may apply gets a generic attempt
    inv_absurd: Option<&'a str>,
    builtin: &'a BTreeSet<String>,
}

/// The priority lemmas written: per rule of `A` whose forward part at a translation is generated
/// (`pri_fwd.r`), per rule of `B` likewise (`pri_bwd.r`), whether the split's second step has
/// one (`pri_mid`), the names for the axiom guard, and the lemmas the hand module proves.
#[derive(Default)]
struct Pris {
    fwd: BTreeSet<usize>,
    bwd: BTreeSet<usize>,
    mid: bool,
    names: Vec<String>,
    hand: Vec<(String, String)>,
    /// whether an arm is a generic attempt (`KPrelude.RefineAttempt`)
    attempts: bool,
}

/// The priority hypotheses that the generated parts pass to the other side's steps
/// (`docs/design.md`, section 3.5, "Priorities"). A step of a rule of rank `i > 0` holds where no
/// rule of a rank before `i` applies (`hpri`); its counterpart's step needs the same of the other
/// definition, at the related state, which holds rule by rule: casing on which rule would apply
/// there, one of a rank `≥ i` is excluded by the rank, one with a counterpart applies on this side
/// too (`appbwd.q`, `appfwd.q`, the arms of `relate`'s `app_bwd` and `app_fwd`), against `hpri`,
/// and so does the split's `b` (through `a1`, the same left-hand side) and `a1` (through `b`);
/// `a2`'s left-hand side, the intermediate state, clashes with every translation of a paired
/// rule's. Any other rule without a counterpart of a rank before `i` applies nowhere `r` does when
/// their left-hand sides clash (`may_unify`); otherwise whether it applies at the related state is
/// a fact of the two definitions (under a legality, often only of the legal states): under a
/// legality whose unfolding set is given, its arm is a generic attempt (`r`'s configuration split
/// by `q`'s pattern, each case a clash or refuted by the legality, `pri_arm`); else the lemma is
/// the hand module's (`pri_fwd.«r» | hand` in the list), or the part that takes it is listed.
///
/// Each lemma is stated in the definitions' module (`pri_fwd.r.statement`), under the legality
/// when there is one (`Inv c`, unused by the generated arms):
/// - `pri_fwd.r` (`A`'s rule `r`): `∀ j, j < i → ∀ d, tr lhs = d → ¬ B.App j d`, under `r`'s binders
///   and its `hpri`;
/// - `pri_bwd.r` (`B`'s rule `r`): `∀ c, tr c = lhs → ∀ j, j < i → ¬ A.App j c`;
/// - `pri_mid`: at the split's intermediate state (`a1`'s right-hand side), no rule of a rank before
///   `a2`'s applies, from `a1`'s `hpri` at its left-hand side: a rule that applies at the
///   intermediate state applies at the start (it reads the changed cells by variables, as K's
///   stream rules read `<k>`), or clashes with the intermediate state.
fn emit_priorities(o: &mut String, d: &mut String, p: &Pri) -> Pris {
    let mut out = Pris::default();
    let (na, nb, tr, top) = (p.na, p.nb, p.tr, p.top);
    let hand = |kind: &str, r: &Rule| {
        p.listed
            .get(&(kind.to_string(), rules::display_name(r)))
            .copied()
            .unwrap_or(false)
    };
    // the legality's premise at `A`'s state, and its name in the proofs
    let (ifw, ibw, hi) = match p.inv {
        Some(i) => (format!("{i} c → "), format!("{i} c → "), " _hinv"),
        None => (String::new(), String::new(), ""),
    };
    let lhs = |r: &Rule| sides(r).0;
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
    writeln!(d, "/-! ## The priority lemmas' statements\n\nWhere no rule of a rank before a step's applies on one side, none applies on the other: generated,\nor the hand module's when listed `| hand`. -/\n").unwrap();
    let binders = |rel: &crate::render::Rel| -> String {
        rel.binders
            .iter()
            .map(|(x, t)| format!(" ({x} : {t})"))
            .chain(rel.hyps.iter().map(|(h, q)| format!(" ({h} : {q})")))
            .collect()
    };
    let fail_unpaired = |q: &Rule, r: &Rule, kind: &str, part: &str| -> ! {
        fail(&format!(
            "rule {} has no counterpart, is of a rank before {}'s and may apply where it does: whether it applies at the related state is not generated (priority ranks, docs/design.md section 3.5); list `{kind}.«{}» | hand` (the hand module proves the lemma), or the part `{part}.«{}»`",
            rules::display_name(q),
            rules::display_name(r),
            rules::display_name(r),
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
        let ty = format!(
            "{na}.Step.Rel.{} (fun c _ => {ifw}∀ j, j < {k} → ∀ d, {tr} c = d → ¬ {nb}.App j d)",
            p.ca[i].lean
        );
        writeln!(d, "def pri_fwd.{}.statement : Prop := {ty}", p.ca[i].lean).unwrap();
        out.fwd.insert(i);
        if hand("pri_fwd", r) {
            out.hand.push(("pri_fwd".into(), p.ca[i].lean.clone()));
            continue;
        }
        let mut arms = String::new();
        let mut attempted = false;
        for (j, q) in p.rb.iter().enumerate() {
            let qargs = rules::ctor_args(&q.app).join(" ");
            let arm = if (p.rank)(q) >= k {
                "exact absurd hj (by decide)".to_string()
            } else if paired_b.contains(&rules::display_name(q)) {
                format!("exact hpri _ hj (appbwd.{} {qargs} hd)", q.lean)
            } else if p.split.is_some_and(|s| s.b == j) {
                format!("exact hpri _ hj (split_appbwd {qargs} hd)")
            } else if !may_unify(&lhs(r), &lhs(q)) {
                // the two left-hand sides clash: `q` applies nowhere `r` does
                "cases hd".to_string()
            } else if let Some(arm) = pri_arm(
                &lhs(r),
                &lhs(q),
                &r.step.binders.iter().cloned().collect(),
                p.builtin,
                &p.inv_absurd
                    .iter()
                    .map(|c| c.to_string())
                    .chain(p.ra.iter().filter(|e| (p.rank)(e) < k && may_unify(&lhs(r), &lhs(e))).map(|e| {
                        format!(
                            "(exfalso; refine hpri {} (by decide) ?_; apply ({na}.App.{}{}) <;> k2l_near_hyp)",
                            (p.rank)(e),
                            e.lean,
                            " _".repeat(e.app.binders.len())
                        )
                    }))
                    .collect::<Vec<_>>(),
                &format!("pri_fwd.«{}»", rules::display_name(r)),
            ) {
                // `q`'s names left inaccessible: they would shadow `r`'s, which the split cases
                attempted |= p.inv_absurd.is_some();
                out.attempts = true;
                writeln!(
                    arms,
                    "  | {}{} => {arm}",
                    q.lean,
                    " _".repeat(rules::ctor_args(&q.app).len())
                )
                .unwrap();
                continue;
            } else {
                fail_unpaired(q, r, "pri_fwd", "fwd_tr")
            };
            writeln!(arms, "  | {} {qargs} => {arm}", q.lean).unwrap();
        }
        let h = if attempted { " hinv" } else { hi };
        writeln!(
            o,
            "theorem pri_fwd.{} : {ty} := by\n  intro {}{h} j hj d hd hb\n  cases hb with\n{arms}",
            p.ca[i].lean,
            p.ca[i].args.join(" ")
        )
        .unwrap();
        out.names.push(format!("pri_fwd.{}", p.ca[i].lean));
    }
    for &j in &bwd {
        let r = &p.rb[j];
        let k = (p.rank)(r);
        let ty = format!(
            "{nb}.Step.Rel.{} (fun d _ => ∀ c, {ibw}{tr} c = d → ∀ j, j < {k} → ¬ {na}.App j c)",
            p.cb[j].lean
        );
        writeln!(d, "def pri_bwd.{}.statement : Prop := {ty}", p.cb[j].lean).unwrap();
        out.bwd.insert(j);
        if hand("pri_bwd", r) {
            out.hand.push(("pri_bwd".into(), p.cb[j].lean.clone()));
            continue;
        }
        let mut arms = String::new();
        let mut attempted = false;
        for (i, q) in p.ra.iter().enumerate() {
            let qargs = rules::ctor_args(&q.app).join(" ");
            let arm = if (p.rank)(q) >= k {
                "exact absurd hj (by decide)".to_string()
            } else if p.pairs.contains_key(&rules::display_name(q)) {
                format!("exact hpri _ hj (hd ▸ appfwd.{} {qargs})", q.lean)
            } else if p.split.is_some_and(|s| s.a1 == i) {
                format!("exact hpri _ hj (hd ▸ split_appfwd {qargs})")
            } else if p.split.is_some_and(|s| s.a2 == i) || !may_unify(&lhs(q), &lhs(r)) {
                // `a2`'s left-hand side, or one that clashes with `r`'s
                "cases hd".to_string()
            } else if let Some(arm) = pri_arm(
                &lhs(q),
                &lhs(r),
                &q.app.binders.iter().cloned().collect(),
                p.builtin,
                &p.inv_absurd
                    .iter()
                    .map(|c| c.to_string())
                    .chain(p.rb.iter().filter(|e| (p.rank)(e) < k && may_unify(&lhs(r), &lhs(e))).map(|e| {
                        format!(
                            "(exfalso; rw [← hd] at hpri; refine hpri {} (by decide) ?_; (try simp only [k2l_tr]); apply ({nb}.App.{}{}) <;> k2l_near_hyp)",
                            (p.rank)(e),
                            e.lean,
                            " _".repeat(e.app.binders.len())
                        )
                    }))
                    .collect::<Vec<_>>(),
                &format!("pri_bwd.«{}»", rules::display_name(r)),
            ) {
                // `A`'s configuration is `q`'s left-hand side, split by `r`'s pattern
                attempted |= p.inv_absurd.is_some();
                out.attempts = true;
                arm
            } else {
                fail_unpaired(q, r, "pri_bwd", "bwd_tr")
            };
            writeln!(arms, "  | {} {qargs} => {arm}", q.lean).unwrap();
        }
        let h = if attempted { " hinv" } else { hi };
        writeln!(
            o,
            "theorem pri_bwd.{} : {ty} := by\n  intro {} c{h} hd j hj ha\n  cases ha with\n{arms}",
            p.cb[j].lean,
            p.cb[j].args.join(" ")
        )
        .unwrap();
        out.names.push(format!("pri_bwd.{}", p.cb[j].lean));
    }
    d.push('\n');
    out
}

/// The generic attempt at a priority lemma's arm, where the other side's earlier rule `q` has no
/// counterpart and may apply: the configuration `own` (the stepping rule's left-hand side
/// forward, `q`'s backward, where it is `A`'s) split by the pattern `other`, each case closed by
/// the first of `closers` that applies (`k2l_strict`): a clash of the translation with `q`'s
/// left-hand side (`cases hd`), the legality's refutation, or a match of an earlier rule of the
/// stepping side, which its priority hypothesis excludes (`q` is often its namesake). `None` when
/// only the clash would be tried: after the split, `q`'s pattern matches at some case.
fn pri_arm(
    own: &L,
    other: &L,
    types: &BTreeMap<String, String>,
    builtin: &BTreeSet<String>,
    closers: &[String],
    lemma: &str,
) -> Option<String> {
    if closers.is_empty() {
        return None;
    }
    let split = case_split(own, std::slice::from_ref(other), types, builtin);
    let mut steps: Vec<String> = split
        .iter()
        .map(|(v, pat)| format!("(k2l_cases {v} with {})", pat.render()))
        .collect();
    let alts: Vec<String> = std::iter::once("k2l_strict (cases hd; done)".to_string())
        .chain(closers.iter().map(|c| format!("k2l_strict {c}")))
        .chain(std::iter::once(format!(
            "fail \"{lemma}: no closer applies at this case (a clash, the legality, an earlier rule's match); list it `| hand`\""
        )))
        .collect();
    steps.push(format!("(first | {})", alts.join(" | ")));
    Some(steps.join(" <;> "))
}

/// What the generic attempt at a part reads: the stepping rule `own`, its namesake `near` on the
/// other side and the arguments of its `Step` constructor, the rules of a rank before each's that
/// may apply where `own` does (the stepping side's with their ranks), and the legality's refutation
/// (`k2l_inv_absurd …`).
struct Near<'a> {
    fwd: bool,
    /// the part's name, for the failure's message
    part: String,
    own: &'a Rule,
    near: &'a Rule,
    near_args: &'a [String],
    /// the stepping side's earlier rules (a match refutes `hpri`) and their ranks
    earlier_own: Vec<(&'a Rule, usize)>,
    /// the other side's earlier rules (their clashes give the namesake's priority premise)
    earlier_other: Vec<&'a Rule>,
    na: &'a str,
    nb: &'a str,
    builtin: &'a BTreeSet<String>,
    inv_absurd: Option<&'a str>,
}

/// The generic attempt at a part at a translation of a rule with no counterpart and a namesake
/// (`fwd_tr.r` with `A`'s `r`, `bwd_tr.r` with `B`'s): the two rules differ in what they read, and
/// whether the namesake steps where `r` does is decided case by case. The configuration is split
/// by the patterns (`case_split`: the namesake's left-hand side and the earlier rules'), backward
/// then the translation inverted; each case is closed by the first closer that applies
/// (`k2l_strict`): the legality refutes it (`k2l_inv_absurd`), the namesake steps there to the
/// translation of `r`'s result (its premises by `k2l_near_hyp`: the rule's hypotheses, the clashes
/// of the earlier rules, the legality's facts), or an earlier rule of the stepping side applies,
/// which its priority hypothesis excludes. A case no closer closes fails the proof at the part's
/// name, and the author lists the part (`docs/design.md`, section 3.5).
fn near_attempt(n: &Near) -> String {
    let lhs = |r: &Rule| sides(r).0;
    let (step_side, app_side) = if n.fwd { (n.nb, n.na) } else { (n.na, n.nb) };
    let types: BTreeMap<String, String> = n.own.step.binders.iter().cloned().collect();
    let others: Vec<L> = std::iter::once(lhs(n.near))
        .chain(n.earlier_own.iter().map(|(q, _)| lhs(q)))
        .chain(n.earlier_other.iter().map(|q| lhs(q)))
        .collect();
    let split = case_split(&lhs(n.own), &others, &types, n.builtin);
    let mut lines: Vec<String> = vec![];
    if !n.fwd {
        lines.push("intro c hd".into());
    }
    lines.extend(render_split(&split));
    if !n.fwd {
        lines.push("all_goals k2l_inv".into());
        // `B`'s map patterns and partial operations on translations are translations, as in
        // `relate`'s backward lemmas
        let lhs_hyps: BTreeSet<&String> = n.own.app.hyps.iter().map(|(h, _)| h).collect();
        for (hn, hp) in &n.own.step.hyps {
            if lhs_hyps.contains(hn)
                && hp.starts_with("KPrelude.MapHook.concat (KPrelude.MapHook.element")
            {
                let m = hp.rsplit("some ").next().unwrap_or_default().trim();
                if let Some(t) = types.get(m) {
                    lines.push(format!(
                        "all_goals first | (obtain ⟨_, _, _, _, _, _, _⟩ := map_bwd_{} {hn}) | skip",
                        crate::terms::fsuffix(t)
                    ));
                    lines.push("all_goals k2l_inv".into());
                }
            } else if hp.contains("= some") {
                lines.push(format!(
                    "all_goals first | (simp only [k2l_rel, Option.map_eq_some_iff] at {hn}; obtain ⟨_, _, rfl⟩ := {hn}) | skip"
                ));
            }
        }
    }
    let mut alts: Vec<String> = vec![];
    if let Some(c) = n.inv_absurd {
        alts.push(format!("k2l_strict {c}"));
    }
    if n.fwd {
        // the namesake's arguments: the translation of `r`'s variable of the same name and sort
        // where `r` has one that the split left (the two rules come from one text, so a shared name
        // is a shared position), else what unification determines; its hypotheses and priority
        // premise are goals
        let near_vars: BTreeMap<&String, &String> =
            n.near.step.binders.iter().map(|(b, t)| (b, t)).collect();
        let split_vars: BTreeSet<&str> = split.iter().map(|(v, _)| v.as_str()).collect();
        let args: Vec<String> = n
            .near_args
            .iter()
            .map(|a| match (near_vars.get(a), types.get(a)) {
                (None, _) => "?_".to_string(),
                (Some(tb), Some(ta)) if *tb == ta && !split_vars.contains(a.as_str()) => {
                    tr_var(n.builtin, ta, a)
                }
                _ => "_".to_string(),
            })
            .collect();
        alts.push(format!(
            "k2l_strict (refine Or.inl ⟨_, .single ({step_side}.Step.{} {}), Or.inl rfl⟩ <;> k2l_near_hyp)",
            n.near.lean,
            args.join(" ")
        ));
    } else {
        alts.push(format!(
            "k2l_strict (exact Or.inl ⟨_, .single (by apply ({step_side}.Step.{}{}) <;> k2l_near_hyp), by k2l_near_fin⟩)",
            n.near.lean,
            " _".repeat(n.near.step.binders.len())
        ));
    }
    let untr = if n.fwd {
        ""
    } else {
        " (try simp only [k2l_tr]);"
    };
    for (q, k) in &n.earlier_own {
        alts.push(format!(
            "k2l_strict (exfalso; refine hpri {k} (by decide) ?_;{untr} apply ({app_side}.App.{}{}) <;> k2l_near_hyp)",
            q.lean,
            " _".repeat(q.app.binders.len())
        ));
    }
    alts.push(format!(
        "fail \"{}: no closer applies at this case (the legality, the namesake's step, an earlier rule's match); list the part in --open\"",
        n.part
    ));
    lines.push("all_goals first".into());
    let mut out = lines.join("\n    ");
    for a in alts {
        write!(out, "\n      | {a}").unwrap();
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
    // `--relation-module M`: `X`, the measures and the hand parts are `M`'s (a shape the generator
    // does not build); otherwise `X` and the measures are generated and the hand parts are
    // `--hand-module`'s (`none`: there is none)
    if opt.contains_key("relation-module") && opt.contains_key("hand-module") {
        fail("--hand-module: with --relation-module, the hand parts are the relation module's");
    }
    let generated = !opt.contains_key("relation-module");
    let hand: Option<String> = if generated {
        opt.get("hand-module").filter(|m| *m != "none").cloned()
    } else {
        opt.get("relation-module").cloned()
    };
    // a legality: a predicate of `A`'s configurations that its steps preserve; the relation and
    // every part hold under it (`Stutter.RelI`)
    let inv = opt.get("assume-invariant").map(|i| Inv {
        name: i.clone(),
        pres: opt
            .get("invariant-preserved")
            .cloned()
            .unwrap_or(format!("{i}.preserved")),
        module: opt
            .get("invariant-module")
            .cloned()
            .unwrap_or(format!("{na}.Invariants")),
        generated: *i == format!("{na}.Invariant") && !opt.contains_key("invariant-module"),
        unfold: opt.get("invariant-unfold").map(|f| {
            if !std::path::Path::new(f).is_file() {
                fail(&format!("--invariant-unfold: no file {f}"));
            }
            std::iter::once(i.clone())
                .chain(crate::claims::read_unfold(&std::path::PathBuf::from(f)))
                .collect()
        }),
    });
    if inv.is_none()
        && (opt.contains_key("invariant-preserved")
            || opt.contains_key("invariant-module")
            || opt.contains_key("invariant-unfold"))
    {
        fail(
            "--invariant-preserved, --invariant-module and --invariant-unfold need --assume-invariant",
        );
    }
    let x = opt.get("extra").cloned().unwrap_or("X".into());
    let mu = opt.get("measure-a").cloned().unwrap_or("μ".into());
    let nu = opt.get("measure-b").cloned().unwrap_or("ν".into());
    let ca = preserves::ctors(&ra, prios.as_deref());
    let cb = preserves::ctors(&rb, prios.as_deref());
    let names_a: BTreeSet<String> = ra.iter().map(rules::display_name).collect();
    let names_b: BTreeSet<String> = rb.iter().map(rules::display_name).collect();
    let paired_b: BTreeSet<&String> = pairs.values().collect();
    let paired_a: BTreeSet<String> = pairs.keys().cloned().collect();
    // without a relation module, `X`, the measures and the parts of a split are generated (one
    // split, `find_splits`; with none, `X` relates nothing)
    let split = if generated {
        let mut ss = find_splits(&ra, &rb, &paired_a, &paired_b);
        if ss.len() > 1 {
            fail(&format!(
                "{} splits found (one step of B taken in two by A), at most one is generated; write `X` and the measures in a relation module (--relation-module)",
                ss.len()
            ));
        }
        if ss.is_empty() {
            None
        } else {
            let sp = ss.remove(0);
            // `b`'s priority hypothesis is `a1`'s, and `a2`'s at the intermediate state follows from
            // `a1`'s at its start (`pri_mid`), which covers the ranks before `a1`'s
            let (k1, k2, kb) = (rank(&ra[sp.a1]), rank(&ra[sp.a2]), rank(&rb[sp.b]));
            if k1 != kb || k2 > k1 {
                fail(&format!(
                    "the split's rules are of ranks {k1} and {k2} against {kb}; generated for one rank, or a second step of a rank before the first's"
                ));
            }
            Some(sp)
        }
    } else {
        None
    };
    for ((k, r), h) in &listed {
        if k.starts_with("pri_") && !*h {
            fail(&format!(
                "--open: {k}.«{r}»: a priority lemma is the hand module's (`| hand`) or generated; to leave its step open, list the part that takes it"
            ));
        }
        let (known, n) = if k.contains("fwd") {
            (&names_a, &na)
        } else {
            (&names_b, &nb)
        };
        if !known.contains(r) {
            fail(&format!("--open: {k}.«{r}»: no rule {r} of {n}"));
        }
        if *h && hand.is_none() {
            fail(&format!(
                "--open: {k}.«{r}» | hand: there is no hand module (--hand-module M); leave it open (its name alone)"
            ));
        }
    }

    // a rule with no counterpart whose name the other side's rule with no counterpart has too (its
    // namesake): the two differ in what they read, and its parts at a translation are attempted
    // generically (`near_attempt`)
    let near: BTreeMap<usize, usize> = ra
        .iter()
        .enumerate()
        .filter(|(i, r)| {
            !paired_a.contains(&rules::display_name(r))
                && !split.as_ref().is_some_and(|s| s.a1 == *i)
        })
        .filter_map(|(i, r)| {
            rb.iter()
                .enumerate()
                .find(|(j, q)| {
                    rules::display_name(q) == rules::display_name(r)
                        && !paired_b.contains(&rules::display_name(q))
                        && !split.as_ref().is_some_and(|s| s.b == *j)
                })
                .map(|(j, _)| (i, j))
        })
        .collect();
    let near_b: BTreeSet<usize> = near.values().copied().collect();
    // a part at a translation is generated when its rule has a counterpart or is the split's (`a1`,
    // `b`), and attempted when it has a namesake; one at an `X` state is always attempted: any
    // other part is listed
    let missing: Vec<String> = ra
        .iter()
        .enumerate()
        .filter(|(i, r)| {
            !paired_a.contains(&rules::display_name(r))
                && !split.as_ref().is_some_and(|s| s.a1 == *i)
                && !near.contains_key(i)
        })
        .map(|(_, r)| ("fwd_tr", rules::display_name(r)))
        .chain(
            rb.iter()
                .enumerate()
                .filter(|(j, r)| {
                    !paired_b.contains(&rules::display_name(r))
                        && !split.as_ref().is_some_and(|s| s.b == *j)
                        && !near_b.contains(j)
                })
                .map(|(_, r)| ("bwd_tr", rules::display_name(r))),
        )
        .filter(|(k, r)| !listed.contains_key(&(k.to_string(), r.clone())))
        .map(|(k, r)| format!("{k}.«{r}»"))
        .collect();
    if !missing.is_empty() {
        fail(&format!(
            "{} parts are not generated (their rules have no counterpart, nor a rule of the same name on the other side) and not listed in --open: list each `KIND.«RULE» | hand` (the hand module's) or `KIND.«RULE»` (open): {}",
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
        if !generated {
            fail(
                "--witnesses: the runs to terminal states are compared by `run_terminal`, which is generated with `X`, not with a relation module's (--relation-module)",
            );
        }
        if inv.as_ref().is_some_and(|i| !i.generated) {
            fail(
                "--witnesses: under a legality, a witness owes it at its start, which is generated from the first definition's invariant (`NS.Invariant.init_holds`, --assume-invariant NS.Invariant without --invariant-module)",
            );
        }
    }
    // the parts attempted generically (a namesake, not listed); under a legality their closers
    // unfold it by its unfolding set
    let attempted: Vec<String> = near
        .iter()
        .flat_map(|(i, j)| {
            [
                ("fwd_tr", rules::display_name(&ra[*i])),
                ("bwd_tr", rules::display_name(&rb[*j])),
            ]
        })
        .filter(|(k, r)| !listed.contains_key(&(k.to_string(), r.clone())))
        .map(|(k, r)| format!("{k}.«{r}»"))
        .collect();
    let unfold = inv
        .as_ref()
        .and_then(|i| i.unfold.as_ref())
        .map(|u| u.join(", "));
    if inv.is_some() && unfold.is_none() && !attempted.is_empty() {
        fail(&format!(
            "under a legality, the generic attempts at {} read what the invariant says: pass --invariant-unfold (the invariant-unfold.txt that `gen --invariant` writes beside the first definition's library), or list them in --open",
            attempted.join(", ")
        ));
    }
    let inv_absurd = unfold
        .as_ref()
        .map(|u| format!("k2l_inv_absurd hinv in {na} [{u}]"));
    let inv_facts = unfold
        .as_ref()
        .map(|u| format!("k2l_inv_facts hinv in {na} [{u}]"));
    let tr = format!("tr_{}", crate::terms::fsuffix(&top));
    let (ta, tb) = (format!("{na}.{top}"), format!("{nb}.{top}"));
    let defs_module = opt
        .get("defs-module")
        .cloned()
        .unwrap_or(format!("{ns}.RefineDefs"));
    // the relation, and the suffix of the parts' predicates (`Stutter.FwdTrI`) and the legality's
    // argument under a legality
    let (rel, qi, qinv) = match &inv {
        Some(i) => (
            format!("Stutter.RelI {tr} {x} {}", i.name),
            "I",
            format!(" {}", i.name),
        ),
        None => (format!("Stutter.Rel {tr} {x}"), "", String::new()),
    };
    // `X`, the measures, the parts' statements and `Open`: their own module when generated
    // (`NS/RefineDefs.lean`, which the hand module imports), else at the head of the output module
    let mut d = String::new();
    let whose = match (generated, &split) {
        (true, Some(_)) => {
            format!("generated from the one step of `B` that `A` takes in two (`{defs_module}`)")
        }
        (true, None) => format!(
            "generated: no step of `B` is taken in two by `A`, so `{x}` relates nothing and the measures are 0 (`{defs_module}`)"
        ),
        (false, _) => format!("of `{}`", hand.as_deref().unwrap_or_default()),
    };
    let rest = if generated {
        "The step of a split, and each step of `B` at a state `X` relates, are matched by `A`'s two\nsteps (`A` completes its step, then takes the counterpart). The parts listed `| hand` are the\nhand module's (`--hand-module`), under the part's name."
    } else {
        "The rest are the relation\nmodule's, under the part's name (`fwd_tr.«r»`, `fwd_x.«r»`, `bwd_tr.«r»`, `bwd_x.«r»`), or open."
    };
    let legality = match &inv {
        Some(i) => format!(
            "\n\nUnder the legality `{}` (`--assume-invariant`), a predicate of `{na}`'s configurations that its\nsteps preserve (`{}`): the relation holds only at configurations satisfying it, and every part is\nowed only there (`Stutter.FwdTrI`, `Stutter.BwdTrI`, …); the parts from a counterpart do not use it, the\ngeneric attempts at a rule against its namesake do.",
            i.name, i.pres
        ),
        None => String::new(),
    };
    let mut o = String::new();
    writeln!(
        o,
        "/-! Generated by `k2lean refine`; do not edit.\n\n\
The stuttering bisimulation between `{na}.Step` and `{nb}.Step` through\n\
`{rel}` (`d` is the translation of `c`, or `{x}` relates them), with the measures\n\
`{mu}` and `{nu}` {whose}. One case per rule and direction, in two parts (`Stutter.fwdQ_of`,\n\
`Stutter.bwdQ_of`): at a translation, from the simulation lemma of `relate --per-rule` when the\n\
rule has a counterpart; at a state `{x}` relates, by `cases` on `{x}`. {rest} Each part is an\n\
obligation by name (stated with `{x}`): generated, the hand module's, or open (a field of `Open`, the\n\
premise of `bisim`), as `--open` lists it.{legality} -/\n"
    )
    .unwrap();
    writeln!(o, "set_option maxHeartbeats 0\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n").unwrap();
    // where the definitions go with a relation module
    let defs_at = o.len();
    // whether `μ` is the state's size (`emit_split`)
    let mut sized = false;
    if generated && split.is_none() {
        writeln!(
            d,
            "/-! ## `{x}` and the measures: no step of `{nb}` is taken in two by `{na}` -/\n\n\
/-- No step of `{nb}` is taken in two by `{na}`: `{x}` relates nothing. -/\n\
inductive {x} : {ta} → {tb} → Prop\n\n\
/-- `{na}`'s measure: it never stutters. -/\ndef {mu} (_ : {ta}) : Nat := 0\n\n\
/-- `{nb}`'s measure: it never stutters. -/\ndef {nu} (_ : {tb}) : Nat := 0\n\n\
/-- From a state `{x}` relates (there is none), `{na}` completes its step. -/\n\
theorem {x}_next {{c : {ta}}} {{d : {tb}}} (h : {x} c d) : ∃ c', {na}.Step c c' ∧ d = {tr} c' :=\n  nomatch h\n"
        )
        .unwrap();
    }
    if let Some(sp) = &split {
        let k2 = rank(&ra[sp.a2]);
        sized = emit_split(
            &mut d,
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
        format!("{n}.Step.Rel.{lean} (Stutter.{q}{qi} {tr} {s}.Step {x}{qinv} {m})")
    };
    writeln!(
        d,
        "/-! ## The parts' statements\n\nEach part is an obligation by name: proved below, by the hand module, or open (a field of\n`Open`), as the list (`--open`) marks it. -/\n"
    )
    .unwrap();
    for (cs, kinds) in [(&ca, ["fwd_tr", "fwd_x"]), (&cb, ["bwd_tr", "bwd_x"])] {
        for c in cs.iter() {
            for k in kinds {
                writeln!(
                    d,
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
            d,
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
            writeln!(d, "  «{k}.{r}» : {k}.{l}.statement").unwrap();
        }
    }
    d.push('\n');
    let (ob, oa) = if opened.is_empty() {
        (String::new(), String::new())
    } else {
        (format!(" ({ov} : Open)"), format!("{ov} "))
    };
    // the priority hypotheses of the other side's steps, per rule whose generated part takes
    // one (design.md, section 3.5, "Priorities")
    let mut po = String::new();
    let pri = emit_priorities(
        &mut po,
        &mut d,
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
            inv: inv.as_ref().map(|i| i.name.as_str()),
            listed: &listed,
            inv_absurd: inv_absurd.as_deref(),
            builtin: &builtin,
        },
    );
    // the generic attempts' premises (`near_attempt`, `pri_arm`): the rule's hypotheses through the
    // translation, a priority premise by the earlier rules' clashes, a side condition from what the
    // legality says at the case; before the priority lemmas, whose arms use them
    if !attempted.is_empty() || pri.attempts {
        let facts = inv_facts
            .as_ref()
            .map(|f| format!("\n  | ({f}; simp_all; done)\n  | ({f}; k2l_arith_omega)"))
            .unwrap_or_default();
        writeln!(
            o,
            "/-! ## The generic attempts' premises -/\n\n\
set_option hygiene false in\n\
/-- A premise of a namesake's step, or of an earlier rule's match, in a generic attempt: a hypothesis\n\
of the rule (through the translation), a priority premise (each earlier rule clashes at the case),\n\
a side condition from what the legality says there. -/\n\
local macro \"k2l_near_hyp\" : tactic => `(tactic| first\n  | assumption\n  | rfl\n  | (intro j hj hb; cases hb <;> first | omega | (exact absurd hj (by decide)))\n  | (simp only [k2l_rel, *, Option.map_some]; done)\n  | (simp only [k2l_rel] at * <;> simp_all <;> done)\n  | k2l_assumption\n  | (simp [k2l_eq] at *; done)\n  | k2l_arith_omega{facts})\n\n\
/-- `d' = tr c'` after a backward step of a generic attempt. -/\n\
local macro \"k2l_near_fin\" : tactic => `(tactic| first | exact Or.inl rfl | (left; simp only [k2l_rel]; done) | (left; simp only [k2l_rel] at * <;> simp_all <;> done))\n"
        )
        .unwrap();
    }
    o.push_str(&po);
    for ((k, r), _) in listed.iter().filter(|((k, _), _)| k.starts_with("pri_")) {
        let rs = if k == "pri_fwd" { &ra } else { &rb };
        let l = &rs
            .iter()
            .find(|x| &rules::display_name(x) == r)
            .unwrap()
            .lean;
        if !pri.hand.contains(&(k.clone(), l.clone())) {
            fail(&format!(
                "--open: {k}.«{r}»: no such priority lemma (its rule is of the first rank, has no counterpart, or its part is listed)"
            ));
        }
    }
    let mut guard = vec![];
    // per kind: generated, by hand, open
    let mut counts: BTreeMap<&str, (usize, usize, usize)> = BTreeMap::new();
    let (mut hand_cases, mut open_cases) = (vec![], vec![]);
    // the hand parts' theorems, checked against their statements
    let mut hand_lean: Vec<String> = vec![];
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
                // under a legality the part has one more premise, `Inv c`, which the generated
                // proofs do not use: first forward, after the state `c` backward
                let tac = match (&inv, kind.starts_with("fwd")) {
                    (None, _) => tac,
                    (Some(_), true) => format!("intro hinv; {tac}"),
                    (Some(_), false) => {
                        let rest = tac.strip_prefix("intro c ").unwrap_or_else(|| {
                            unreachable!(
                                "{kind}.«{name}»: a backward part's proof introduces `c` first"
                            )
                        });
                        format!("intro c hinv {rest}")
                    }
                };
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
                hand_lean.push(format!("{kind}.{lean}"));
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
    // under a legality, the parts introduce it as `hinv` (`A`'s state), and pass it on; at the
    // state `A` reaches from an `X` state (`X_next`'s step `h₁`), by its preservation
    let hinv = if inv.is_some() { " hinv" } else { "" };
    let hinv1 = inv
        .as_ref()
        .map(|i| format!(" ({} _ _ hinv h₁)", i.pres))
        .unwrap_or_default();
    let pri_f = |i: usize, args: &str| {
        if pri.fwd.contains(&i) {
            format!(
                " (fun j hj => pri_fwd.{} {args}{hinv} j hj _ rfl)",
                ca[i].lean
            )
        } else {
            String::new()
        }
    };
    let pri_b = |j: usize, args: &str, c: &str, h: &str, e: &str| {
        if pri.bwd.contains(&j) {
            format!(" (pri_bwd.{} {args} {c}{h} {e})", cb[j].lean)
        } else {
            String::new()
        }
    };
    if let Some(sp) = &split {
        let (a1, b) = (&ra[sp.a1], &rb[sp.b]);
        let unrho: BTreeMap<&String, &String> = sp.rho.iter().map(|(k, v)| (v, k)).collect();
        let ty_a: BTreeMap<&String, &String> =
            a1.step.binders.iter().map(|(n, t)| (n, t)).collect();
        let bargs: Vec<String> = rules::ctor_args(&b.step)
            .iter()
            .map(|w| match unrho.get(w) {
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
                    " have hp := pri_bwd.{} {} c{hinv} hd;",
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
        let ib = inv
            .as_ref()
            .map(|i| format!("{} c → ", i.name))
            .unwrap_or_default();
        writeln!(
            o,
            "/-- `{}` of `{nb}` from a translation is `{}` then `{}` of `{na}`. -/\ntheorem split_bwd : {nb}.Step.Rel.{} (fun d d' => ∀ c, {ib}{tr} c = d → ∃ c', Relation.TransGen {na}.Step c c' ∧ d' = {tr} c') := by\n  intro {bargs_all} c{hinv} hd;{have} k2l_inv; exact ⟨_, .tail (.single ({na}.Step.{} {}{hp1})) ({na}.Step.{} {}{hp2}), rfl⟩\n",
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
                "intro c hd; obtain ⟨c', hc', e⟩ := split_bwd {bargs_all} c{hinv} hd.symm; exact Or.inl ⟨c', hc', Or.inl e⟩"
            ),
        ));
        split_bwd_x.insert(
            sp.b,
            format!(
                "intro c hX; first | (cases hX <;> first | done | contradiction | (simp_all; done)) | (obtain ⟨c₁, h₁, e⟩ := {x}_next hX; obtain ⟨c₂, h₂, e₂⟩ := split_bwd {bargs_all} c₁{hinv1} e.symm; exact Or.inl ⟨c₂, .trans (.single h₁) h₂, Or.inl e₂⟩)"
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
                    pri_b(j, &args, "c₁", &hinv1, "e.symm")
                ),
            );
        }
    }
    let lhs_of = |r: &Rule| sides(r).0;
    // the generic attempt at a rule's part at a translation from its namesake
    let attempt = |fwd: bool, i: usize, j: usize| {
        let (own, nr, rs_own, rs_other, near_c) = if fwd {
            (&ra[i], &rb[j], &ra, &rb, &cb[j])
        } else {
            (&rb[j], &ra[i], &rb, &ra, &ca[i])
        };
        let l = lhs_of(own);
        near_attempt(&Near {
            fwd,
            part: format!(
                "{}.«{}»",
                if fwd { "fwd_tr" } else { "bwd_tr" },
                rules::display_name(own)
            ),
            own,
            near: nr,
            near_args: &near_c.args,
            earlier_own: rs_own
                .iter()
                .filter(|q| rank(q) < rank(own) && may_unify(&l, &lhs_of(q)))
                .map(|q| (q, rank(q)))
                .collect(),
            earlier_other: rs_other
                .iter()
                .filter(|q| rank(q) < rank(nr) && may_unify(&l, &lhs_of(q)))
                .collect(),
            na: &na,
            nb: &nb,
            builtin: &builtin,
            inv_absurd: inv_absurd.as_deref(),
        })
    };
    let near_back: BTreeMap<usize, usize> = near.iter().map(|(i, j)| (*j, *i)).collect();
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
            })
            .or_else(|| near.get(&idx).map(|&j| attempt(true, idx, j)));
        let ht = part(&mut o, "fwd_tr", (&name, &c.lean), args, tr_auto);
        // a rule of a rank before `a2`'s may match `A`'s side of `X` (one that does not read what
        // `a1` changed: K's stream rules), where `X`'s `hp` says no such rule applies
        let x_auto = match (&split_fwd_x, &split) {
            (Some((i, t)), _) if *i == idx => t.clone(),
            (_, Some(sp)) if pri.mid && rank(r) < rank(&ra[sp.a2]) => format!(
                "intro d hX; first | (cases hX <;> first | done | contradiction | (simp_all; done)) | (cases hX with | «split» {} hp => exact (hp {} (by decide) (by apply {na}.App.{} <;> assumption)).elim)",
                vec!["_"; 3 * ra[sp.a1].step.binders.len()].join(" "),
                rank(r),
                c.lean
            ),
            _ => refute.to_string(),
        };
        let hx = part(&mut o, "fwd_x", (&name, &c.lean), args, Some(x_auto));
        writeln!(
            o,
            "theorem stutter_fwd.{}{ob} : {na}.Step.Rel.{} (Stutter.FwdQ{qi} {tr} {nb}.Step {x}{qinv} {mu}) := by\n{}  exact Stutter.fwdQ{qi}_of {ht} {hx}\n",
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
                    pri_b(idx, &args.join(" "), "c", hinv, "hd.symm")
                )
            })
            .or_else(|| split_bwd_tr.as_ref().filter(|(i, _)| *i == idx).map(|(_, t)| t.clone()))
            .or_else(|| near_back.get(&idx).map(|&i| attempt(false, i, idx)));
        let ht = part(&mut o, "bwd_tr", (&name, &c.lean), args, tr_auto);
        let x_auto = split_bwd_x.get(&idx).cloned().unwrap_or_else(|| {
            "intro c hX; cases hX <;> first | done | contradiction | (simp_all; done)".to_string()
        });
        let hx = part(&mut o, "bwd_x", (&name, &c.lean), args, Some(x_auto));
        writeln!(
            o,
            "theorem stutter_bwd.{}{ob} : {nb}.Step.Rel.{} (Stutter.BwdQ{qi} {tr} {na}.Step {x}{qinv} {nu}) := by\n{}  exact Stutter.bwdQ{qi}_of {ht} {hx}\n",
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
    let bisim_of = match &inv {
        Some(i) => format!("Stutter.bisimI_of {}", i.pres),
        None => "Stutter.bisim_of".to_string(),
    };
    writeln!(
        o,
        "theorem bisim{ob} : StutterBisim {na}.Step {nb}.Step ({rel}) {mu} {nu} :=\n  {bisim_of}\n    (fun h => {na}.Step.rel_of {} h)\n    (fun h => {nb}.Step.rel_of {} h)\n",
        list(&ca, "stutter_fwd"),
        list(&cb, "stutter_bwd")
    )
    .unwrap();
    // under a legality, the runs start at a configuration satisfying it
    let (hi, start) = match &inv {
        Some(i) => (format!(" (hi : {} c)", i.name), "⟨hi, Or.inl rfl⟩"),
        None => (String::new(), "(Or.inl rfl)"),
    };
    writeln!(
        o,
        "/-- A run of `{na}` to a terminal state is matched, from the translation of its start, by a run\nof `{nb}` to a terminal state related to it. -/\n\
theorem run_fwd{ob} {{c c' : {ta}}}{hi} (h : Star {na}.Step c c') (ht : Terminal {na}.Step c') :\n    ∃ d', Star {nb}.Step ({tr} c) d' ∧ Terminal {nb}.Step d' ∧ {rel} c' d' :=\n  {bi}.terminal_run {start} h ht\n\n\
/-- A run of `{nb}` from a translation to a terminal state is matched by a run of `{na}` to a\nterminal state related to it. -/\n\
theorem run_bwd{ob} {{c : {ta}}} {{d' : {tb}}}{hi} (h : Star {nb}.Step ({tr} c) d') (ht : Terminal {nb}.Step d') :\n    ∃ c', Star {na}.Step c c' ∧ Terminal {na}.Step c' ∧ {rel} c' d' :=\n  {bi}.symm.terminal_run {start} h ht\n"
    )
    .unwrap();
    guard.extend(pri.names.iter().cloned());
    if generated {
        guard.push(format!("{x}_next"));
    }
    guard.extend(["bisim".into(), "run_fwd".into(), "run_bwd".into()]);
    // a generated `X` never relates a terminal state of `A` (`X_next`), so two runs to terminal
    // states end in translations of each other
    let (hia, ha, rp) = match &inv {
        Some(_) => (hi.clone(), "hi ", "_, "),
        None => (String::new(), "", ""),
    };
    if generated {
        writeln!(
            o,
            "/-- `{x}` never relates a terminal state of `{na}`, which completes its step from there (`{x}_next`). -/\n\
theorem not_terminal_of_{x} {{c : {ta}}} {{d : {tb}}} (h : {x} c d) : ¬ Terminal {na}.Step c :=\n  fun ht => let ⟨_, hc, _⟩ := {x}_next h; ht _ hc\n\n\
/-- A run of `{na}` to a terminal state and the run of `{nb}` from the translation of its start to a\nterminal state end in translations of each other. -/\n\
theorem run_terminal{ob} {{c c' : {ta}}}{hia} (h : Star {na}.Step c c') (ht : Terminal {na}.Step c') :\n    ∃ d', Star {nb}.Step ({tr} c) d' ∧ Terminal {nb}.Step d' ∧ d' = {tr} c' := by\n  obtain ⟨d', hd, htd, {rp}hr | hx⟩ := run_fwd {oa}{ha}h ht\n  · exact ⟨d', hd, htd, hr⟩\n  · exact absurd ht (not_terminal_of_{x} hx)\n\n\
theorem run_terminal_back{ob} {{c : {ta}}} {{d' : {tb}}}{hia} (h : Star {nb}.Step ({tr} c) d') (ht : Terminal {nb}.Step d') :\n    ∃ c', Star {na}.Step c c' ∧ Terminal {na}.Step c' ∧ d' = {tr} c' := by\n  obtain ⟨c', hc, htc, {rp}hr | hx⟩ := run_bwd {oa}{ha}h ht\n  · exact ⟨c', hc, htc, hr⟩\n  · exact absurd htc (not_terminal_of_{x} hx)\n"
        )
        .unwrap();
        guard.extend([
            format!("not_terminal_of_{x}"),
            "run_terminal".into(),
            "run_terminal_back".into(),
        ]);
    }
    // the hand parts and priority lemmas prove their statements as stated
    for h in hand_lean
        .iter()
        .cloned()
        .chain(pri.hand.iter().map(|(k, l)| format!("{k}.{l}")))
    {
        writeln!(o, "#k2l_proves {h}").unwrap();
    }
    writeln!(o, "#k2l_assert_axioms {}\n\nend {ns}", guard.join(" ")).unwrap();
    let inv_import = inv
        .as_ref()
        .map(|i| format!("import {}\n", i.module))
        .unwrap_or_default();
    let out = get("out");
    let attempts_import = if attempted.is_empty() && !pri.attempts {
        ""
    } else {
        "import KPrelude.RefineAttempt\n"
    };
    let head = if generated {
        let trm = opt.get("tr-module").cloned().unwrap_or(format!("{ns}.Tr"));
        let defs = format!(
            "import {trm}\nimport KPrelude.Scaffold\n{inv_import}\n\
/-! Generated by `k2lean refine`; do not edit.\n\n\
`{x}`, the measures and the parts' statements of the stuttering bisimulation between `{na}.Step`\n\
and `{nb}.Step` through `{rel}`, and `Open`, the parts left open. The hand module\n\
(`--hand-module`) imports this module and proves the parts listed `| hand` under their names; the\n\
bisimulation is proved in the module that imports it. -/\n\n\
set_option maxHeartbeats 0\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n\n{d}end {ns}\n"
        );
        write_file(
            &std::path::Path::new(&out)
                .with_file_name(format!(
                    "{}.lean",
                    defs_module.rsplit('.').next().unwrap_or("RefineDefs")
                ))
                .to_string_lossy(),
            &defs,
        );
        format!(
            "import {}\n{attempts_import}\n",
            hand.as_deref().unwrap_or(&defs_module)
        )
    } else {
        // with a relation module the definitions open the output module
        format!(
            "import {}\n{inv_import}{attempts_import}\n",
            hand.as_deref().unwrap_or_default()
        )
    };
    let (pre, rest) = o.split_at(defs_at);
    let defs_here = if generated { "" } else { d.as_str() };
    write_file(&out, &format!("{head}{pre}{defs_here}{rest}"));
    let total: (usize, usize, usize) = counts
        .values()
        .fold((0, 0, 0), |(a, b, c), (x, y, z)| (a + x, b + y, c + z));
    let legal = inv
        .as_ref()
        .map(|i| format!("legality = {:?}\n", i.name))
        .unwrap_or_default();
    let mut rep = format!(
        "# k2lean refine: {na} against {nb}\n\n{legal}rules_a = {}\nrules_b = {}\npairs = {}\nparts = {}\nautomatic = {}\nhand = {}\nopen = {}\n\n[parts]\n",
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
            "\n[priorities]\nranks = {}\nfwd = {}\nbwd = {}\nmid = {}\nhand = {:?}",
            prios.as_ref().map_or(0, |ps| ps.len()),
            pri.fwd.len(),
            pri.bwd.len(),
            pri.mid,
            pri.hand
                .iter()
                .map(|(k, l)| format!("{k}.{l}"))
                .collect::<Vec<_>>()
        )
        .unwrap();
    }
    writeln!(
        rep,
        "\n[attempts]\ncases = {attempted:?}\n\n[hand]\ncases = {hand_cases:?}\n\n[open]\ncases = {open_cases:?}"
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
            top: &top,
            tr: &tr,
            ranked: (ranked_a, ranked_b),
            inv: inv.as_ref().map(|i| i.name.as_str()),
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
