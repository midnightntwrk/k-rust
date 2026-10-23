//! Determinism of `Step` modulo a generated list of overlapping rule pairs, proved through
//! relations split by a key (`gen --det2`, `k2lean/docs/design.md`, §3.1).
//!
//! Statements (what a reader uses):
//! - `overlaps : List (Overlap top)`: the same-rank pairs the classifier could not separate;
//!   `noOverlap c : Bool` holds when no listed pair has both rules applicable at `c`;
//! - with an empty list: `Step.deterministic`, `step_complete`, `step_iff`;
//! - otherwise: `Step.deterministic_of (h : noOverlap c = true)`, `step_complete_of`,
//!   `step_iff_of_noOverlap`; per rule, `Rules.r.det` takes one hypothesis
//!   `(Rules.p lhs).applies = false` per listed partner `p`.
//!
//! Proof (internal, in namespace `Det`): `Det.key c` names the first item of the `<k>` cell
//! (its K constructor, the injection into `KItem`, and the injected sort's own constructor where
//! every rule has one there). Per rank `i`, `Det.K{i}_{k}` holds the constructors of the rules with
//! key `k`, `Det.W{i}` those whose key is not determined by their left-hand side, and
//! `Det.split{i} : REL c c' → Det.K{i} (Det.key c) c c' ∨ Det.W{i} c c'` is one linear case split.
//! A rule with a key inverts only `Det.K{i}_{k}` and `Det.W{i}`; a rule without inverts `REL`.
//! Each surviving goal gets the certificate the pair classifier (`pairs.rs`, untrusted) chooses
//! (`k2l_case tag => closer`); goals it did not predict get `k2l_default`.

use crate::index::CtorInfo;
use crate::lower::L;
use crate::names;
use crate::pairs::PairOut;
use crate::rules::{Rule, ctor_args, ctor_sig, display_name};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

/// The key of a left-hand side: the constructors of the first `<k>` item that every rule with the
/// same prefix also has.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    /// `<k> .K </k>`
    DotK,
    /// `kseq (f x) _` with `f` an injection into `KItem` and `x` not a constructor
    Inj(String),
    /// `kseq (f (g …)) _`: `g` (with its arity) the injected sort's own constructor
    Own(String, String, usize),
    /// `kseq (f …) _` for a `KItem` constructor `f` of arity other than one
    Ctor(String, usize),
}

/// The constructors from the top cell to the `<k>` cell: (constructor, arity, child index).
type CellPath = Vec<(String, usize, usize)>;

fn find_k<'l>(l: &'l L, info: &CtorInfo, path: &mut CellPath) -> Option<&'l L> {
    let L::App(h, args) = l else { return None };
    if !info.contains_key(h) || !h.contains("«<") {
        return None;
    }
    if h.ends_with("«<k>»") && args.len() == 1 {
        return Some(&args[0]);
    }
    for (i, a) in args.iter().enumerate() {
        path.push((h.clone(), args.len(), i));
        if let Some(x) = find_k(a, info, path) {
            return Some(x);
        }
        path.pop();
    }
    None
}

/// The raw key of a left-hand side (before truncation), with the path to its `<k>` cell.
fn raw_key(l: &L, info: &CtorInfo) -> Option<(CellPath, Key)> {
    let mut path = Vec::new();
    let k = find_k(l, info, &mut path)?;
    let L::App(h, args) = k else { return None };
    if h.ends_with("SortK.dotk") && args.is_empty() {
        return Some((path, Key::DotK));
    }
    if !(h.ends_with("SortK.kseq") && args.len() == 2) {
        return None;
    }
    let L::App(f, fa) = &args[0] else { return None };
    if !info.contains_key(f) {
        return None;
    }
    if fa.len() != 1 {
        return Some((path, Key::Ctor(f.clone(), fa.len())));
    }
    match &fa[0] {
        L::App(g, ga) if info.contains_key(g) => {
            Some((path, Key::Own(f.clone(), g.clone(), ga.len())))
        }
        _ => Some((path, Key::Inj(f.clone()))),
    }
}

fn wild(n: usize) -> String {
    vec!["_"; n].join(" ")
}

fn app(f: &str, args: &str) -> String {
    if args.is_empty() {
        f.to_string()
    } else {
        format!("({f} {args})")
    }
}

/// The `match` pattern of a key below the cell path.
fn key_pattern(path: &CellPath, key: &Key) -> String {
    let inner = match key {
        Key::DotK => "SortK.dotk".to_string(),
        Key::Inj(f) => format!("(SortK.kseq ({f} _) _)"),
        Key::Own(f, g, n) => format!("(SortK.kseq ({f} {}) _)", app(g, &wild(*n))),
        Key::Ctor(f, n) => format!("(SortK.kseq {} _)", app(f, &wild(*n))),
    };
    // the `<k>` cell itself, then its ancestors
    let mut pat = format!("(SortKCell.«<k>» {inner})");
    for (h, n, i) in path.iter().rev() {
        let args: Vec<String> = (0..*n)
            .map(|j| if j == *i { pat.clone() } else { "_".into() })
            .collect();
        pat = format!("({h} {})", args.join(" "));
    }
    pat.trim_start_matches('(')
        .trim_end_matches(')')
        .to_string()
}

/// The certificate of the goal where rule `r` is inverted against rule `p`, from the class of
/// the pair (`None`: the default closer).
fn certificate(o: &PairOut, partner: &Rule, hno: Option<&str>, fns: &[String]) -> Option<String> {
    // first identify the results of a partial call or projection made by both rules
    // a refutation does not need the goal (`rhs = rhs'`, two large configurations): `exfalso`
    // keeps `simp … at *` off it
    let refutes = !matches!(o.class.as_str(), "joinable");
    certificate0(o, partner, hno, fns).map(|c| {
        if refutes {
            format!("(k2l_det_fundep; exfalso; {c})")
        } else {
            format!("(k2l_det_fundep; {c})")
        }
    })
}

fn certificate0(o: &PairOut, partner: &Rule, hno: Option<&str>, fns: &[String]) -> Option<String> {
    match o.class.as_str() {
        // a literal in one rule against a variable equated to another literal in the other:
        // both are hypotheses of the relation, so inversion does not see the clash
        "clash" if o.detail.starts_with("lit") => Some("k2l_lits".into()),
        "clash" => None,
        "exclusive" if o.detail.starts_with("eval") => {
            Some(format!("k2l_eval [{}]", fns.join(", ")))
        }
        "exclusive" if o.detail.starts_with("complement") => Some("k2l_bool_cases".into()),
        "exclusive" if o.detail.starts_with("smt") => Some(format!("k2l_smt [{}]", fns.join(", "))),
        "exclusive" if o.detail.starts_with("case split") => {
            Some(format!("k2l_split_cases [{}]", fns.join(", ")))
        }
        "exclusive" => None,
        "joinable" => Some("k2l_join".into()),
        "overlap" => {
            let h = hno.expect("overlap partner without hypothesis");
            let mut args: Vec<String> = partner
                .app
                .binders
                .iter()
                .map(|_| "_".to_string())
                .collect();
            args.extend(
                partner
                    .app
                    .hyps
                    .iter()
                    .map(|_| "(by assumption)".to_string()),
            );
            Some(format!(
                "exact absurd ((Rules.{}.applies {}).symm.trans {h}) (by decide)",
                partner.lean,
                args.join(" ")
            ))
        }
        _ => None,
    }
}

pub struct Out {
    pub text: String,
    pub overlaps: usize,
    pub report: String,
}

/// The options of `gen --det2`.
pub struct Opts {
    /// The term universe is the arity-indexed family (the injection-algebra proofs differ).
    pub arity: bool,
    /// Pairs of rules (display names) listed as overlapping whatever their class
    /// (`--det2-overlap A,B`): the theorem then assumes them apart, which exercises the
    /// conditional statements on a definition whose classification finds no overlap.
    pub forced: Vec<(String, String)>,
    /// `maxHeartbeats` of the module (`--det2-heartbeats N`, default 400000).
    pub heartbeats: u64,
}

impl Opts {
    pub fn from_args(rest: &[String], arity: bool) -> Opts {
        let mut o = Opts {
            arity,
            forced: vec![],
            heartbeats: 400_000,
        };
        let mut it = rest.iter();
        while let Some(x) = it.next() {
            match x.as_str() {
                "--det2-overlap" => {
                    let v = it.next().expect("--det2-overlap RULE_A,RULE_B");
                    let (a, b) = v.split_once(',').expect("--det2-overlap RULE_A,RULE_B");
                    o.forced.push((a.trim().to_string(), b.trim().to_string()));
                }
                "--det2-heartbeats" => {
                    o.heartbeats = it
                        .next()
                        .and_then(|n| n.parse().ok())
                        .expect("--det2-heartbeats N");
                }
                _ => {}
            }
        }
        o
    }
}

/// `rel(i)`: the relation of rank `i` that the lemmas invert (`Step`, or `Step0 i` when ranked).
#[allow(clippy::too_many_arguments)]
pub fn emit(
    def: &crate::ir::Def,
    m: &crate::model::Model,
    rs: &[Rule],
    prios: &[i64],
    ranked: bool,
    top: &str,
    ns: &str,
    info: &CtorInfo,
    unfold: &[String],
    fns: &crate::lower::Fns,
    opts: &Opts,
) -> Out {
    // the definitions a pair's requires clauses call, transitively (the unfoldings of `k2l_eval`)
    let eqs = crate::funcs::equations(def);
    let fn_names = |a: usize, b: usize| -> Vec<String> {
        let mut syms: BTreeSet<String> = BTreeSet::new();
        crate::funcs::applied(&rs[a].kore.1, def, &mut syms);
        crate::funcs::applied(&rs[b].kore.1, def, &mut syms);
        let mut todo: Vec<String> = syms.iter().cloned().collect();
        while let Some(f) = todo.pop() {
            for e in eqs.get(&f).into_iter().flatten() {
                let mut more = BTreeSet::new();
                crate::funcs::applied(&e.rhs, def, &mut more);
                for q in &e.requires {
                    crate::funcs::applied(q, def, &mut more);
                }
                for g in more {
                    if syms.insert(g.clone()) {
                        todo.push(g);
                    }
                }
            }
        }
        let leans: BTreeSet<&str> = syms
            .iter()
            .filter_map(|f| fns.get(f).map(|s| s.lean.as_str()))
            .collect();
        let mut out: Vec<String> = unfold
            .iter()
            .filter(|u| {
                leans.iter().any(|l| {
                    u.as_str() == *l || u.strip_prefix(*l).is_some_and(|r| r.starts_with(".rule"))
                })
            })
            .cloned()
            .collect();
        // recursive definitions are not in the unfold list: their equation lemmas fire on
        // constructor arguments only
        for l in &leans {
            if l.starts_with("K.") && !out.iter().any(|u| u == l) {
                out.push(l.to_string());
            }
        }
        out
    };
    let rank = |r: &Rule| prios.iter().position(|p| *p == r.priority).unwrap_or(0);
    let rel = |i: usize| {
        if ranked {
            format!("Step0 {i}")
        } else {
            "Step".to_string()
        }
    };
    let nranks = if ranked { prios.len() } else { 1 };
    // the classes of every same-rank pair (untrusted)
    let classes =
        crate::pairs::classify_same_rank(def, m, rs, &|r| if ranked { rank(r) } else { 0 });
    let class_of = |a: usize, b: usize| classes.get(&(a.min(b), a.max(b)));
    // forced overlaps (`Opts::forced`)
    let forced: BTreeSet<(usize, usize)> = opts
        .forced
        .iter()
        .map(|(a, b)| {
            let find = |n: &str| {
                rs.iter()
                    .position(|r| display_name(r) == n)
                    .unwrap_or_else(|| panic!("--det2-overlap: no rule {n}"))
            };
            let (fa, fb) = (find(a), find(b));
            (fa.min(fb), fa.max(fb))
        })
        .collect();
    let is_overlap = |a: usize, b: usize| {
        forced.contains(&(a.min(b), a.max(b)))
            || class_of(a, b).is_some_and(|o| o.class == "overlap")
    };
    let mut overlaps: Vec<(usize, usize)> = Vec::new();
    for ((a, b), o) in &classes {
        if o.class == "overlap" || forced.contains(&(*a, *b)) {
            overlaps.push((*a, *b));
        }
    }
    // partners of each rule, with the index of the pair in `overlaps` and whether the rule is `fst`
    let mut partners: BTreeMap<usize, Vec<(usize, usize, bool)>> = BTreeMap::new();
    for (k, (a, b)) in overlaps.iter().enumerate() {
        partners.entry(*a).or_default().push((*b, k, true));
        partners.entry(*b).or_default().push((*a, k, false));
    }
    // keys, truncated where some rule has no constructor under an injection
    let raw: Vec<Option<(CellPath, Key)>> =
        rs.iter().map(|r| raw_key(&r.step.index, info)).collect();
    let var_under: BTreeSet<String> = raw
        .iter()
        .filter_map(|k| match k {
            Some((_, Key::Inj(f))) => Some(f.clone()),
            _ => None,
        })
        .collect();
    let keys: Vec<Option<(CellPath, Key)>> = raw
        .into_iter()
        .map(|k| {
            k.map(|(p, k)| match k {
                Key::Own(f, _, _) if var_under.contains(&f) => (p, Key::Inj(f)),
                other => (p, other),
            })
        })
        .collect();
    // one cell path for all keyed rules (the configuration's), else no key at all
    let paths: BTreeSet<&CellPath> = keys.iter().flatten().map(|(p, _)| p).collect();
    let keys: Vec<Option<Key>> = if paths.len() == 1 {
        keys.iter()
            .map(|k| k.as_ref().map(|(_, k)| k.clone()))
            .collect()
    } else {
        vec![None; rs.len()]
    };
    let path: CellPath = paths
        .iter()
        .next()
        .map(|p| (*p).clone())
        .unwrap_or_default();
    let key_list: Vec<Key> = keys
        .iter()
        .flatten()
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let knum: BTreeMap<&Key, usize> = key_list
        .iter()
        .enumerate()
        .map(|(i, k)| (k, i + 1))
        .collect();

    let mut o = format!(
        "import {ns}.Adequacy\nimport KPrelude.Determinism\n\n/-! Generated by k2lean; do not edit.\n\n\
Determinism of `Step`{}. `overlaps` lists the pairs of rules of one rank that can both apply at\n\
one configuration ({} pairs): there `Step` has two successors in general, which is the\n\
definition's own nondeterminism (`krun` takes the first rule in its order). At a configuration\n\
where no listed pair applies with both rules (`noOverlap c = true`) the successor is unique.\n\n\
The proof inverts the second step through relations split by the first item of the `<k>` cell\n\
(namespace `Det`, internal) and closes each remaining goal with the certificate chosen by the\n\
generator's pair classification; the kernel checks every one. -/\n\n\
set_option maxHeartbeats {}\nset_option maxRecDepth 100000\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n\n",
        if ranked { " with priority ranks" } else { "" },
        overlaps.len(),
        opts.heartbeats
    );
    // the injection algebra and the closers that use this definition's names
    let inj: BTreeSet<(String, String)> = crate::terms::inj_pairs(m).into_iter().collect();
    let simple = |s: &str| m.sorts.get(s).is_some_and(|x| x.is_simple());
    let mut alg = Vec::new();
    for (b, a) in &inj {
        for (a2, d) in &inj {
            if a2 != a || !inj.contains(&(b.clone(), d.clone())) {
                continue;
            }
            let (fb, fa, fd) = (
                names::short_sort(b),
                names::short_sort(a),
                names::short_sort(d),
            );
            let n = format!("Det.comp_{fb}_{fa}_{fd}");
            let proof = if simple(b) {
                "rfl".to_string()
            } else if opts.arity {
                "match x with\n  | Term.inj _ _ _ _ => rfl".to_string()
            } else {
                "by cases x <;> rfl".to_string()
            };
            let _ = writeln!(
                o,
                "@[k2l_det_alg] theorem {n} (x : {b}) : inj_{fa}_{fd} (inj_{fb}_{fa} x) = inj_{fb}_{fd} x :=\n  {proof}"
            );
            alg.push(n);
        }
        for (c, a2) in &inj {
            if a2 != a || c == b || !inj.contains(&(b.clone(), c.clone())) {
                continue;
            }
            let (fb, fa, fc) = (
                names::short_sort(b),
                names::short_sort(a),
                names::short_sort(c),
            );
            let n = format!("Det.projinj_{fb}_{fa}_{fc}");
            let proof = if simple(b) {
                format!("by first | rfl | simp [inj_{fb}_{fa}, proj_{fa}_{fc}, inj_{fb}_{fc}]")
            } else if opts.arity {
                format!(
                    "match x with\n  | Term.inj _ l h _ => by simp [inj_{fb}_{fa}, proj_{fa}_{fc}, inj_{fb}_{fc}, sub_{fb}_{fc} l h]"
                )
            } else {
                format!(
                    "by cases x <;> first | rfl | simp [inj_{fb}_{fa}, proj_{fa}_{fc}, inj_{fb}_{fc}]"
                )
            };
            let _ = writeln!(
                o,
                "@[k2l_det_alg] theorem {n} (x : {b}) : proj_{fa}_{fc} (inj_{fb}_{fa} x) = some (inj_{fb}_{fc} x) :=\n  {proof}"
            );
            alg.push(n);
        }
    }
    let _ = write!(
        o,
        "\n\
/-- Equal right-hand sides under both matches. -/\nlocal macro \"k2l_join\" : tactic => `(tactic| first | k2l_self | (simp_all; done))\n\n\
/-- Every closer in turn, with a warning: a goal the classification did not predict. -/\n\
local macro \"k2l_fallback\" : tactic => `(tactic| (k2l_warn_fallback; first\n  | k2l_self\n  | k2l_refute_eqs\n  | k2l_bool_cases\n  | k2l_eval\n  | k2l_omega\n  | (k2l_map_facts; simp_all; done)\n  | (k2l_proj_inv; simp_all [k2l_det_alg]; done)))\n\n\
/-- The certificate of a goal the classification puts in the clash class: an equation\nhypothesis whose sides are different constructors (otherwise the fallback). -/\n\
local macro \"k2l_default\" : tactic => `(tactic| (k2l_note_default; first | k2l_refute_eqs | (exfalso; k2l_list_facts; k2l_det_fundep; k2l_map_facts; k2l_det_fundep; first | done | k2l_refute_eqs | k2l_lits) | k2l_fallback))\n\n",
    );
    // the key
    // an enumeration, not `Nat`: a match on it is one `casesOn` step, where a match on `Nat`
    // literals tests the literals in turn and re-evaluates the key at each test
    let ctors: Vec<String> = (1..=key_list.len()).map(|n| format!("k{n}")).collect();
    let _ = writeln!(
        o,
        "/-- internal (determinism): the keys, and `none` for a configuration without one. -/\ninductive Det.Key where\n  | none{}\n",
        ctors.iter().map(|c| format!(" | {c}")).collect::<String>()
    );
    let _ = writeln!(
        o,
        "/-- internal: the first item of the `<k>` cell, as a key. -/\ndef Det.key (c : {top}) : Det.Key :=\n  match c with"
    );
    for k in &key_list {
        let _ = writeln!(o, "  | {} => .k{}", key_pattern(&path, k), knum[k]);
    }
    let _ = writeln!(o, "  | _ => .none\n");
    let mut report = String::new();
    let _ = writeln!(
        report,
        "keys = {}\nwild_rules = {}",
        key_list.len(),
        keys.iter().filter(|k| k.is_none()).count()
    );
    // per rank: the split relations and the lifting
    let mut group_of: Vec<Option<usize>> = vec![None; rs.len()];
    let mut inv_total = 0usize;
    let mut largest = 0usize;
    for i in 0..nranks {
        let idx: Vec<usize> = (0..rs.len())
            .filter(|&x| !ranked || rank(&rs[x]) == i)
            .collect();
        let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        let mut w = Vec::new();
        for &x in &idx {
            match &keys[x] {
                Some(k) => groups.entry(knum[k]).or_default().push(x),
                None => w.push(x),
            }
        }
        let ctor = |x: usize, relname: &str| {
            let r = &rs[x];
            format!(
                "  | {}{} :\n      {relname} {}\n        {}\n",
                r.lean,
                ctor_sig(&r.step),
                r.step.index.render_arg(),
                r.rhs.subst(&r.step.subst).render_arg()
            )
        };
        for (k, g) in &groups {
            let _ = writeln!(
                o,
                "/-- internal: the rank-{i} rules with key {k}. -/\ninductive Det.K{i}_{k} : {top} → {top} → Prop where"
            );
            for &x in g {
                o.push_str(&ctor(x, &format!("Det.K{i}_{k}")));
                group_of[x] = Some(*k);
            }
            o.push('\n');
            largest = largest.max(g.len());
        }
        let _ = writeln!(
            o,
            "/-- internal: the rank-{i} rules whose key their left-hand side does not determine. -/\ninductive Det.W{i} : {top} → {top} → Prop where"
        );
        for &x in &w {
            o.push_str(&ctor(x, &format!("Det.W{i}")));
        }
        let _ = writeln!(
            o,
            "\n/-- internal: the rank-{i} rules of a key. -/\ndef Det.K{i} : Det.Key → {top} → {top} → Prop"
        );
        for k in groups.keys() {
            let _ = writeln!(o, "  | .k{k} => Det.K{i}_{k}");
        }
        let _ = writeln!(o, "  | _ => fun _ _ => False\n");
        let _ = writeln!(
            o,
            "theorem Det.split{i} {{c c' : {top}}} (h : {} c c') : Det.K{i} (Det.key c) c c' ∨ Det.W{i} c c' := by\n  cases h with",
            rel(i)
        );
        for &x in &idx {
            let r = &rs[x];
            let args = ctor_args(&r.step).join(" ");
            match group_of[x] {
                Some(k) => {
                    let _ = writeln!(
                        o,
                        "  | {0} {args} => exact .inl (Det.K{i}_{k}.{0} {args})",
                        r.lean
                    );
                }
                None => {
                    let _ = writeln!(
                        o,
                        "  | {0} {args} => exact .inr (Det.W{i}.{0} {args})",
                        r.lean
                    );
                }
            }
        }
        o.push('\n');
        let sq: usize = groups.values().map(|g| g.len() * (g.len() + w.len())).sum();
        inv_total += sq + w.len() * idx.len();
        let _ = writeln!(
            report,
            "rank{i}_groups = {}\nrank{i}_wild = {}",
            groups.len(),
            w.len()
        );
        // the rules of each group (for the inversion lists below)
        for (k, g) in groups {
            for x in g {
                let _ = (k, x);
            }
        }
    }
    let _ = writeln!(
        report,
        "largest_group = {largest}\ninversions = {inv_total}"
    );
    // per-rule lemmas
    let mut ncert: BTreeMap<String, usize> = BTreeMap::new();
    for (x, r) in rs.iter().enumerate() {
        let i = if ranked { rank(r) } else { 0 };
        let lhs = r.step.index.render_arg();
        let rhs = r.rhs.subst(&r.step.subst).render_arg();
        let mut hnos = String::new();
        let mut hno_name: BTreeMap<usize, String> = BTreeMap::new();
        for (n, (p, _, _)) in partners.get(&x).into_iter().flatten().enumerate() {
            let h = format!("k2l_hno{}", n + 1);
            let _ = write!(
                hnos,
                "\n    ({h} : (Rules.{} {lhs}).applies = false)",
                rs[*p].lean
            );
            hno_name.insert(*p, h);
        }
        // the constructors this lemma inverts
        let same: Vec<usize> = (0..rs.len())
            .filter(|&y| !ranked || rank(&rs[y]) == i)
            .collect();
        let inverted: Vec<usize> = match group_of[x] {
            Some(k) => same
                .iter()
                .copied()
                .filter(|&y| group_of[y] == Some(k) || group_of[y].is_none())
                .collect(),
            None => same.clone(),
        };
        let doc = if hno_name.is_empty() {
            format!(
                "/-- Every `{}` step from the left-hand side of `{}` is the rule's own step. -/\n",
                rel(i),
                names::string_lit(&display_name(r)).trim_matches('"')
            )
        } else {
            format!(
                "/-- Every `{}` step from the left-hand side of `{}` is the rule's own step, where none of\nits overlapping partners applies. -/\n",
                rel(i),
                names::string_lit(&display_name(r)).trim_matches('"')
            )
        };
        // a rule without key inverts every constructor of its rank: more heartbeats
        let hb = if group_of[x].is_none() {
            "set_option maxHeartbeats 4000000 in\n"
        } else {
            ""
        };
        let _ = write!(
            o,
            "{hb}{doc}theorem Rules.{}.det{}{hnos} {{c₂ : {top}}}\n    (h₂ : {} {lhs} c₂) : {rhs} = c₂ := by\n",
            r.lean,
            ctor_sig(&r.step),
            rel(i)
        );
        match group_of[x] {
            Some(_) => {
                // `h₂` is not needed after the split: clearing it keeps the closers' `at *` small
                let _ = writeln!(
                    o,
                    "  rcases Det.split{i} h₂ with h | h <;> (clear h₂; cases h)"
                );
            }
            None => {
                let _ = writeln!(o, "  cases h₂");
            }
        }
        for &y in &inverted {
            let cert = if y == x {
                Some("k2l_self".to_string())
            } else if is_overlap(x, y) {
                let fake = PairOut {
                    class: "overlap".into(),
                    detail: String::new(),
                    depth: 0,
                    smt: None,
                    cases: vec![],
                };
                certificate(&fake, &rs[y], hno_name.get(&y).map(|s| s.as_str()), &[])
            } else {
                class_of(x, y).and_then(|c| certificate(c, &rs[y], None, &fn_names(x, y)))
            };
            if let Some(c) = cert {
                *ncert
                    .entry(
                        c.trim_start_matches("(k2l_det_fundep; ")
                            .trim_start_matches("exfalso; ")
                            .split_whitespace()
                            .next()
                            .unwrap_or("")
                            .trim_end_matches(')')
                            .to_string(),
                    )
                    .or_default() += 1;
                let _ = writeln!(o, "  k2l_case {} => {c}", rs[y].lean);
            }
        }
        let _ = writeln!(o, "  all_goals k2l_default\n");
    }
    for (c, n) in &ncert {
        let _ = writeln!(report, "\"certificates.{c}\" = {n}");
    }
    // the overlaps and the global theorems
    let _ = writeln!(
        o,
        "/-- The pairs of rules of one rank that can both apply at one configuration: every pair the\ngenerator's classification could not separate. Each other pair is proved never to apply at\nonce (`Rules.r.det`). -/\ndef overlaps : List (Overlap {top}) := ["
    );
    let items: Vec<String> = overlaps
        .iter()
        .map(|(a, b)| format!("  ⟨R.{}, R.{}⟩", rs[*a].lean, rs[*b].lean))
        .collect();
    let _ = writeln!(o, "{}]\n", items.join(",\n"));
    let _ = writeln!(
        o,
        "/-- No pair of `overlaps` has both of its rules applicable at `c`. -/\ndef noOverlap (c : {top}) : Bool := noOverlapIn overlaps c\n"
    );
    let empty = overlaps.is_empty();
    let sfx = if empty { "" } else { "_of" };
    let hyp = if empty {
        String::new()
    } else {
        " (h : noOverlap c = true)".to_string()
    };
    let det0 = if ranked {
        "Step0.deterministic"
    } else {
        "Step.deterministic"
    };
    let _ = writeln!(
        o,
        "{}theorem {det0}{sfx} {{{}c c₁ c₂ : {top}}}{hyp} (h₁ : {} c c₁) (h₂ : {} c c₂) : c₁ = c₂ := by\n  cases h₁ with",
        if empty {
            ""
        } else {
            "/-- At a configuration where no listed pair applies with both rules, `Step` has at most one\nsuccessor. -/\n"
        },
        if ranked { "i : Nat} {" } else { "" },
        if ranked { "Step0 i" } else { "Step" },
        if ranked { "Step0 i" } else { "Step" }
    );
    for (x, r) in rs.iter().enumerate() {
        let args = ctor_args(&r.step).join(" ");
        let mut hs = Vec::new();
        for (p, k, fst) in partners.get(&x).into_iter().flatten() {
            let _ = p;
            let app = ctor_args(&r.app).join(" ");
            hs.push(format!(
                "(noOverlapIn_{} (o := ⟨R.{}, R.{}⟩) h (KPrelude.mem_of_getElem? (i := {k}) rfl) (Rules.{}.applies {app}))",
                if *fst { "fst" } else { "snd" },
                rs[overlaps[*k].0].lean,
                rs[overlaps[*k].1].lean,
                r.lean
            ));
        }
        let hs = if hs.is_empty() {
            String::new()
        } else {
            format!(" {}", hs.join(" "))
        };
        let _ = writeln!(
            o,
            "  | {0} {args} => exact Rules.{0}.det {args}{hs} h₂",
            r.lean
        );
    }
    o.push('\n');
    if ranked {
        let _ = writeln!(
            o,
            "theorem Step.deterministic{sfx} {{c c₁ c₂ : {top}}}{hyp} (h₁ : Step c c₁) (h₂ : Step c c₂) : c₁ = c₂ := by\n  obtain ⟨i, a₁, hi⟩ := Step.base h₁\n  obtain ⟨j, a₂, hj⟩ := Step.base h₂\n  rcases Nat.lt_trichotomy i j with h' | rfl | h'\n  · exact absurd (Step0.app a₁) (hj i h')\n  · exact Step0.deterministic{sfx} {}a₁ a₂\n  · exact absurd (Step0.app a₂) (hi j h')\n",
            if empty { "" } else { "h " }
        );
    }
    if empty {
        let _ = writeln!(
            o,
            "/-- With determinism, the executable step is complete. -/\ntheorem step_complete {{c c' : {top}}} (h : Step c c') : step c = .next c' := by\n  obtain ⟨c'', hc⟩ := step_progress h\n  rw [hc, Step.deterministic (step_sound hc) h]\n\ntheorem step_iff {{c c' : {top}}} : step c = .next c' ↔ Step c c' := ⟨step_sound, step_complete⟩\n"
        );
    } else {
        let _ = writeln!(
            o,
            "/-- Where no listed pair applies with both rules, the executable step is complete. -/\ntheorem step_complete_of {{c c' : {top}}} (h : noOverlap c = true) (hs : Step c c') : step c = .next c' := by\n  obtain ⟨c'', hc⟩ := step_progress hs\n  rw [hc, Step.deterministic_of h (step_sound hc) hs]\n\n\
theorem step_iff_of_noOverlap {{c c' : {top}}} (h : noOverlap c = true) : step c = .next c' ↔ Step c c' :=\n  ⟨step_sound, step_complete_of h⟩\n"
        );
    }
    let _ = writeln!(o, "end {ns}");
    let _ = writeln!(report, "overlaps = {}", overlaps.len());
    let _ = writeln!(report, "classified_pairs = {}", classes.len());
    let mut by_class: BTreeMap<String, usize> = BTreeMap::new();
    for c in classes.values() {
        *by_class.entry(c.class.clone()).or_default() += 1;
    }
    for (c, n) in by_class {
        let _ = writeln!(report, "\"pairs.{c}\" = {n}");
    }
    Out {
        text: o,
        overlaps: overlaps.len(),
        report,
    }
}

/// The axiom guard names the conditional theorems when the overlap list is not empty.
pub fn fix_guard(guard: &str, ns: &str, overlaps: usize) -> String {
    if overlaps == 0 {
        return guard.to_string();
    }
    guard.replace(
        &format!("{ns}.Step.deterministic {ns}.step_complete {ns}.step_iff"),
        &format!("{ns}.Step.deterministic_of {ns}.step_complete_of {ns}.step_iff_of_noOverlap"),
    )
}
