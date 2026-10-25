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
        // one rule's result is undefined wherever both apply: its partial call, at the values
        // the other rule's pattern fixes, evaluates to `none`
        "exclusive"
            if o.detail.starts_with("eval: the") && o.detail.ends_with("result is undefined") =>
        {
            Some(format!("k2l_undef [{}]", fns.join(", ")))
        }
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
    /// The modules, by path relative to the project: `NS/Determinism.lean` (the theorems) and the
    /// modules it imports, `NS/Determinism/Pre.lean` (the key, the split relations, `overlaps`),
    /// `NS/Determinism/L{k}.lean` (the per-rule lemmas, in modules of bounded cost) and
    /// `NS/Determinism/Witness.lean` (a witness of each listed overlap).
    pub files: Vec<(String, String)>,
    pub overlaps: usize,
    /// Listed pairs that have no checked witness; with any, the library does not state
    /// `overlaps_witnessed`.
    pub unwitnessed: usize,
    /// The theorems `overlap_witness_k` of the pairs that have one.
    pub witnessed: Vec<String>,
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
    /// `maxHeartbeats` of the lemma modules (`--det2-heartbeats N`, default 400000).
    pub heartbeats: u64,
    /// One disjointness lemma per unordered pair separated by its side conditions, used from both
    /// rules' lemmas (`--det2-disjoint`), instead of a certificate in each.
    pub disjoint: bool,
    /// The cost bound of one lemma module (`--det2-module-cost N`, default 2000): the sum over
    /// its lemmas of the constructors each inverts, and 2 per certificate beyond a literal clash.
    pub module_cost: usize,
    /// The length above which a `String` or token literal makes an overlap witness unchecked
    /// (`--det2-long-literal N`, default [`LONG_LITERAL`]): such a witness is reported and its
    /// pair stays listed in `overlaps` without a witness.
    pub long_literal: usize,
    /// The same bound for a `Bytes` literal (`--det2-long-bytes N`, default [`LONG_BYTES`]).
    pub long_bytes: usize,
}

impl Opts {
    pub fn from_args(rest: &[String], arity: bool) -> Opts {
        let mut o = Opts {
            arity,
            forced: vec![],
            heartbeats: 400_000,
            module_cost: 2000,
            long_literal: LONG_LITERAL,
            long_bytes: LONG_BYTES,
            disjoint: rest.iter().any(|x| x == "--det2-disjoint"),
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
                "--det2-module-cost" => {
                    o.module_cost = it
                        .next()
                        .and_then(|n| n.parse().ok())
                        .expect("--det2-module-cost N");
                }
                "--det2-long-literal" => {
                    o.long_literal = it
                        .next()
                        .and_then(|n| n.parse().ok())
                        .expect("--det2-long-literal N");
                }
                "--det2-long-bytes" => {
                    o.long_bytes = it
                        .next()
                        .and_then(|n| n.parse().ok())
                        .expect("--det2-long-bytes N");
                }
                _ => {}
            }
        }
        o
    }
}

/// The first `<k>` item of a rule without key, when it is a variable `y` that the rule reads as a
/// value `G` of a sort through `proj_KItem_S y = some G`: (`y`'s projection hypothesis, `G`).
fn head_var(r: &Rule, info: &CtorInfo) -> Option<(String, String)> {
    let mut path = Vec::new();
    let k = find_k(&r.step.index, info, &mut path)?;
    let L::App(h, args) = k else { return None };
    if !(h.ends_with("SortK.kseq") && args.len() == 2) {
        return None;
    }
    let L::Var(y) = &args[0] else { return None };
    r.step.hyps.iter().find_map(|(hn, p)| {
        let t: Vec<&str> = p.split_whitespace().collect();
        match t.as_slice() {
            [f, v, "=", "some", g] if f.starts_with("proj_KItem_") && v == y => {
                Some((hn.clone(), g.to_string()))
            }
            _ => None,
        }
    })
}

/// The `(from, to)` sorts of every injection `inj{from, to}(…)` in `p` (with `vars_only`, of a
/// variable only).
fn injections(p: &crate::ir::P, vars_only: bool, out: &mut BTreeSet<(String, String)>) {
    use crate::ir::P;
    let rec = |x: &P, out: &mut BTreeSet<(String, String)>| injections(x, vars_only, out);
    match p {
        P::App(f, ps, args) => {
            if f == "inj"
                && let [a, b] = ps.as_slice()
                && let (Some(a), Some(b)) = (a.name(), b.name())
                && (!vars_only || matches!(args.first(), Some(P::Var(..))))
            {
                out.insert((a.to_string(), b.to_string()));
            }
            for a in args {
                rec(a, out);
            }
        }
        P::And(_, ps) | P::Or(_, ps) => ps.iter().for_each(|x| rec(x, out)),
        P::Not(_, a) => rec(a, out),
        P::Equals(_, _, a, b)
        | P::In(_, _, a, b)
        | P::Implies(_, a, b)
        | P::Iff(_, a, b)
        | P::Rewrites(_, a, b) => {
            rec(a, out);
            rec(b, out);
        }
        P::Ceil(_, _, a) | P::Floor(_, _, a) | P::Exists(_, _, _, a) | P::Forall(_, _, _, a) => {
            rec(a, out)
        }
        _ => {}
    }
}

/// `text` with every whole identifier of `names` followed by `'` (the partner's names in a
/// disjointness lemma, which states both rules' binders).
fn primed(text: &str, names: &BTreeSet<String>) -> String {
    let ident =
        |c: char| c.is_alphanumeric() || c == '_' || c == '\'' || c == '.' || c == '!' || c == '?';
    let mut out = String::new();
    let cs: Vec<char> = text.chars().collect();
    let mut i = 0;
    while i < cs.len() {
        if ident(cs[i]) && (i == 0 || !ident(cs[i - 1])) {
            let mut j = i;
            while j < cs.len() && ident(cs[j]) {
                j += 1;
            }
            let w: String = cs[i..j].iter().collect();
            out.push_str(&w);
            if names.contains(&w) {
                out.push('\'');
            }
            i = j;
        } else {
            out.push(cs[i]);
            i += 1;
        }
    }
    out
}

/// The header of a generated determinism module.
fn header(imports: &[String], doc: &str, heartbeats: u64, ns: &str) -> String {
    let mut o = String::new();
    for i in imports {
        let _ = writeln!(o, "import {i}");
    }
    let _ = write!(
        o,
        "\n/-! Generated by k2lean; do not edit.\n\n{doc} -/\n\nset_option maxHeartbeats {heartbeats}\nset_option maxRecDepth 100000\nset_option linter.unusedVariables false\nset_option linter.unusedSectionVars false\n\nnamespace {ns}\n\nopen KPrelude\n\n"
    );
    o
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
    // the unfoldings of a certificate: for a verdict by evaluation, the definitions the
    // classifier's evaluation applied (its derivation, which the certificate replays); otherwise
    // the definitions the pair's requires clauses call, transitively. The transitive set can be
    // far larger than a refutation needs (a `==K` between sorts without a common leaf under a
    // call into signature recovery), and `simp` over it does not finish.
    let eqs = crate::funcs::equations(def);
    let fn_names = |a: usize, b: usize, used: Option<&BTreeSet<String>>| -> Vec<String> {
        let mut syms: BTreeSet<String> = BTreeSet::new();
        if let Some(u) = used {
            syms.extend(u.iter().cloned());
        } else {
            crate::funcs::applied(&rs[a].kore.1, def, &mut syms);
            crate::funcs::applied(&rs[b].kore.1, def, &mut syms);
        }
        let mut todo: Vec<String> = if used.is_some() {
            vec![]
        } else {
            syms.iter().cloned().collect()
        };
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
    let t0 = std::time::Instant::now();
    let classes =
        crate::pairs::classify_same_rank(def, m, rs, &|r| if ranked { rank(r) } else { 0 }, false);
    if std::env::var_os("K2LEAN_WITNESS_TRACE").is_some() {
        let hwm = std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|t| {
                t.lines()
                    .find(|l| l.starts_with("VmHWM"))
                    .map(|l| l.to_string())
            })
            .unwrap_or_default();
        eprintln!(
            "det2: classification {:.1} s, {hwm}",
            t0.elapsed().as_secs_f64()
        );
    }
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

    let pre_mod = format!("{ns}.Determinism.Pre");
    let mut o = header(
        &[format!("{ns}.Adequacy"), "KPrelude.Determinism".into()],
        &format!(
            "Internal part of `{ns}.Determinism`: the key of a configuration (the first item of its\n\
`<k>` cell), the relations split by it, and `overlaps`, the pairs of rules of one rank that can\n\
both apply at one configuration ({} pairs)",
            overlaps.len()
        ),
        opts.heartbeats,
        ns,
    );
    // the injection algebra
    let inj: BTreeSet<(String, String)> = crate::terms::inj_pairs(m).into_iter().collect();
    let simple = |s: &str| m.sorts.get(s).is_some_and(|x| x.is_simple());
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
        }
    }
    // a projection of an injection whose leaves it does not include is `none` (the leaf table),
    // for the projections the pairs' side conditions test (the patterns `inj{S, A}(…)` of the
    // equations of the functions their requires call) and the injections of their left-hand
    // sides: what refutes a sort predicate `isS(X)` at a variable `X` of a disjoint sort
    let mut tested: BTreeSet<(String, String)> = BTreeSet::new();
    let mut injected: BTreeSet<(String, String)> = BTreeSet::new();
    {
        let mut syms: BTreeSet<String> = BTreeSet::new();
        for r in rs {
            crate::funcs::applied(&r.kore.1, def, &mut syms);
            injections(&r.kore.0, true, &mut injected);
        }
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
        for f in &syms {
            for e in eqs.get(f).into_iter().flatten() {
                for a in &e.args {
                    injections(a, false, &mut tested);
                }
            }
        }
    }
    // and for the projections a rule without a key tests: such a rule, whose item is a variable
    // `X:S` injected into `A`, is a case of every rule's determinism theorem, and it matches
    // another rule's `inj{T, A}(…)` only where the projection from `A` to `S` of that injection
    // is defined, which it is not when `T` and `S` have no common leaf (KMIR's `ERR:MIRError`
    // against a cooling rule's `HOLE:Evaluation`). In the arity universe only: there the
    // projection of an injection is a test of the term's leaf, which the generic closers do not
    // decide at a variable term of a sort with many leaves (KMIR's `Evaluation`); the per-sort
    // libraries of the gate close these cases without the lemmas, so they are not added there
    // (design.md §9)
    for (r, k) in rs.iter().zip(&keys) {
        if opts.arity && k.is_none() {
            injections(&r.kore.0, true, &mut tested);
        }
    }
    let leaves_of = |x: &str| -> BTreeSet<String> {
        m.sorts
            .get(x)
            .map(|i| i.leaves.iter().cloned().collect())
            .unwrap_or_default()
    };
    let mut nproj = 0usize;
    for (sv, a) in &tested {
        if !inj.contains(&(sv.clone(), a.clone())) {
            continue;
        }
        let from: BTreeSet<&String> = injected.iter().map(|(t, _)| t).collect();
        for t in from {
            if t == sv || !inj.contains(&(t.clone(), a.clone())) {
                continue;
            }
            if !leaves_of(t).is_disjoint(&leaves_of(sv)) {
                continue;
            }
            let (ft, fa, fs) = (
                names::short_sort(t),
                names::short_sort(a),
                names::short_sort(sv),
            );
            let proof = if simple(t) {
                format!("by simp [inj_{ft}_{fa}, proj_{fa}_{fs}]")
            } else if opts.arity && simple(sv) {
                // a sort that is its own leaf: its projection tests the leaf tag itself
                format!(
                    "match x with\n  | Term.inj _ l h _ => by\n    have hn : l ≠ .«{sv}» := by intro he; subst he; revert h; decide\n    simp [inj_{ft}_{fa}, proj_{fa}_{fs}, hn]"
                )
            } else if opts.arity {
                format!(
                    "match x with\n  | Term.inj _ l h _ => by\n    have hl : leafOK .«{sv}» l = false := by revert h; cases l <;> decide\n    simp [inj_{ft}_{fa}, proj_{fa}_{fs}, hl]"
                )
            } else {
                format!("by cases x <;> first | rfl | simp [inj_{ft}_{fa}, proj_{fa}_{fs}]")
            };
            let _ = writeln!(
                o,
                "@[k2l_det_alg] theorem Det.projnone_{ft}_{fa}_{fs} (x : {t}) : proj_{fa}_{fs} (inj_{ft}_{fa} x) = none :=\n  {proof}"
            );
            nproj += 1;
        }
    }
    // the key: an enumeration, not `Nat` (a match on it is one `casesOn` step, where a match on
    // `Nat` literals tests the literals in turn and re-evaluates the key at each test), computed
    // in three layers (the configuration's `<k>` cell, its first item, the item's constructors) so
    // that the key of a configuration whose first item is a variable reduces to that item's key
    let ctors: Vec<String> = (1..=key_list.len()).map(|n| format!("k{n}")).collect();
    let _ = writeln!(
        o,
        "\n/-- internal (determinism): the keys, and `none` for a configuration without one. -/\ninductive Det.Key where\n  | none{}\n",
        ctors.iter().map(|c| format!(" | {c}")).collect::<String>()
    );
    // the item's key
    let item_keys: Vec<&Key> = key_list
        .iter()
        .filter(|k| !matches!(k, Key::DotK))
        .collect();
    let item_ty = "SortKItem";
    let _ = writeln!(
        o,
        "/-- internal: the key of a first `<k>` item. -/\ndef Det.ikey (x : {item_ty}) : Det.Key :=\n  match x with"
    );
    for k in &item_keys {
        let pat = match k {
            Key::Inj(f) => format!("{f} _"),
            Key::Own(f, g, n) => format!("{f} {}", app(g, &wild(*n))),
            Key::Ctor(f, n) => app(f, &wild(*n))
                .trim_start_matches('(')
                .trim_end_matches(')')
                .to_string(),
            Key::DotK => unreachable!(),
        };
        let _ = writeln!(o, "  | {pat} => .k{}", knum[k]);
    }
    let _ = writeln!(o, "  | _ => .none\n");
    // the `<k>` content's key
    let k_ty = "SortK";
    let kseq = info
        .keys()
        .find(|c| c.ends_with("SortK.kseq"))
        .cloned()
        .unwrap_or_else(|| "SortK.kseq".into());
    let dotk = info
        .keys()
        .find(|c| c.ends_with("SortK.dotk"))
        .cloned()
        .unwrap_or_else(|| "SortK.dotk".into());
    let k_ctors = info.get(&kseq).map(|x| x.0).unwrap_or(2);
    let _ = writeln!(
        o,
        "/-- internal: the key of the content of the `<k>` cell. -/\ndef Det.kkey (k : {k_ty}) : Det.Key :=\n  match k with\n  | {kseq} x _ => Det.ikey x"
    );
    let dot = key_list
        .iter()
        .find(|k| matches!(k, Key::DotK))
        .map(|k| knum[k]);
    match dot {
        Some(n) => {
            let _ = writeln!(o, "  | {dotk} => .k{n}");
            if opts.arity || k_ctors > 2 {
                let _ = writeln!(o, "  | _ => .none");
            }
        }
        None => {
            let _ = writeln!(o, "  | _ => .none");
        }
    }
    o.push('\n');
    // the configuration's key: down the cell path to `<k>`
    let mut pat = "(SortKCell.«<k>» k)".to_string();
    for (h, n, i) in path.iter().rev() {
        let args: Vec<String> = (0..*n)
            .map(|j| if j == *i { pat.clone() } else { "_".into() })
            .collect();
        pat = format!("({h} {})", args.join(" "));
    }
    let pat = pat
        .trim_start_matches('(')
        .trim_end_matches(')')
        .to_string();
    let path_exhaustive = !opts.arity
        && path
            .iter()
            .all(|(h, _, _)| info.get(h).is_some_and(|x| x.0 == 1))
        && info.get("SortKCell.«<k>»").is_none_or(|x| x.0 == 1);
    let _ = writeln!(
        o,
        "/-- internal: the first item of the `<k>` cell, as a key. -/\ndef Det.key (c : {top}) : Det.Key :=\n  match c with"
    );
    if path.is_empty() && key_list.is_empty() {
        let _ = writeln!(o, "  | _ => .none\n");
    } else {
        let _ = writeln!(o, "  | {pat} => Det.kkey k");
        if !path_exhaustive {
            let _ = writeln!(o, "  | _ => .none");
        }
        o.push('\n');
    }
    let mut report = String::new();
    let _ = writeln!(
        report,
        "keys = {}\nwild_rules = {}\nprojection_none_lemmas = {nproj}",
        key_list.len(),
        keys.iter().filter(|k| k.is_none()).count()
    );
    // per rank: the split relations and the lifting
    let mut group_of: Vec<Option<usize>> = vec![None; rs.len()];
    let mut inv_total = 0usize;
    let mut largest = 0usize;
    let mut wild_of: Vec<usize> = Vec::with_capacity(nranks);
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
        wild_of.push(w.len());
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
    }
    let _ = writeln!(
        report,
        "largest_group = {largest}\ninversions = {inv_total}"
    );
    // the overlaps
    let _ = writeln!(
        o,
        "/-- The pairs of rules of one rank that can both apply at one configuration: every pair the\ngenerator's classification could not separate. Each other pair is proved never to apply at\nonce (`Rules.r.det`); each listed pair is witnessed (`overlaps_witnessed`). -/\ndef overlaps : List (Overlap {top}) := ["
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
    let _ = writeln!(o, "end {ns}");
    let mut files = vec![(format!("{ns}/Determinism/Pre.lean"), o)];

    // the pairs separated by their side conditions (not by a constructor or a literal): with
    // `--det2-disjoint`, one lemma each, which both rules' lemmas use
    let mut disj: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut dmods: Vec<String> = Vec::new();
    if opts.disjoint {
        let mut dl: Vec<String> = Vec::new();
        for ((a, b), c) in &classes {
            if forced.contains(&(*a, *b)) || c.class != "exclusive" {
                continue;
            }
            let Some(cert) = certificate(c, &rs[*b], None, &fn_names(*a, *b, c.used.as_ref()))
            else {
                continue;
            };
            disj.insert((*a, *b));
            let (ra, rb) = (&rs[*a], &rs[*b]);
            let names_b: BTreeSet<String> = rb
                .step
                .binders
                .iter()
                .map(|(n, _)| n.clone())
                .chain(rb.step.hyps.iter().map(|(n, _)| n.clone()))
                .collect();
            let mut sig = String::new();
            for (n, ty) in &ra.step.binders {
                let _ = write!(sig, " {{{n} : {ty}}}");
            }
            for (n, ty) in &rb.step.binders {
                let _ = write!(sig, " {{{n}' : {}}}", primed(ty, &names_b));
            }
            for (h, p) in &ra.step.hyps {
                let _ = write!(sig, "\n    ({h} : {p})");
            }
            for (h, p) in &rb.step.hyps {
                let _ = write!(sig, "\n    ({h}' : {})", primed(p, &names_b));
            }
            let lb = primed(&rb.step.index.render_arg(), &names_b);
            dl.push(format!(
                "/-- internal: `{}` and `{}` never both step from one configuration. -/\ntheorem Det.disj.{}.{}{sig}\n    (k2l_hc : {} = {lb}) : False := by\n  cases k2l_hc\n  first | {cert} | k2l_default\n\n",
                names::string_lit(&display_name(ra)).trim_matches('"'),
                names::string_lit(&display_name(rb)).trim_matches('"'),
                ra.lean,
                rb.lean,
                ra.step.index.render_arg()
            ));
        }
        let per = 60usize;
        for (k, ch) in dl.chunks(per).enumerate() {
            let name = format!("D{}", k + 1);
            let mut t = header(
                std::slice::from_ref(&pre_mod),
                &format!(
                    "Internal part of `{ns}.Determinism`: the pairs of rules separated by their side conditions, module {}",
                    k + 1
                ),
                opts.heartbeats,
                ns,
            );
            for l in ch {
                t.push_str(l);
            }
            let _ = writeln!(t, "end {ns}");
            files.push((format!("{ns}/Determinism/{name}.lean"), t));
            dmods.push(format!("{ns}.Determinism.{name}"));
        }
        let _ = writeln!(report, "disjointness_lemmas = {}", dl.len());
    }
    // per-rule lemmas, in modules of bounded cost
    let mut ncert: BTreeMap<String, usize> = BTreeMap::new();
    let mut lemmas: Vec<(usize, String)> = Vec::new(); // (cost, text)
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
        let head = if group_of[x].is_none() {
            head_var(r, info)
        } else {
            None
        };
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
        // a rule without key that cannot be split by its head's sort inverts every constructor of
        // its rank: more heartbeats
        let mut t = String::new();
        let _ = write!(
            t,
            "{doc}theorem Rules.{}.det{}{hnos} {{c₂ : {top}}}\n    (h₂ : {} {lhs} c₂) : {rhs} = c₂ := by\n",
            r.lean,
            ctor_sig(&r.step),
            rel(i)
        );
        let mut cost = 0usize;
        match (group_of[x], &head) {
            (Some(_), _) => {
                // `h₂` is not needed after the split: clearing it keeps the closers' `at *` small
                if opts.disjoint {
                    let _ = writeln!(
                        t,
                        "  rcases Det.split{i} h₂ with h | h <;> clear h₂\n  all_goals (k2l_gen_index h; cases h)"
                    );
                } else {
                    let _ = writeln!(
                        t,
                        "  rcases Det.split{i} h₂ with h | h <;> (clear h₂; cases h)"
                    );
                }
                cost += inverted.len();
            }
            (None, Some((hp, g))) => {
                // the first item is `inj_S_KItem g`: split `g` by its leaf until the key reduces,
                // then invert one key's relation per case
                let proj = r
                    .step
                    .hyps
                    .iter()
                    .find(|(h, _)| h == hp)
                    .map(|(_, p)| p.split_whitespace().next().unwrap_or("").to_string())
                    .unwrap_or_default();
                let _ = writeln!(
                    t,
                    "  have k2l_e := {} {hp}\n  subst k2l_e\n  rcases Det.split{i} h₂ with h | h <;> clear h₂\n  k2l_key_cases h [{g}]\n  all_goals {}",
                    proj.replacen("proj_", "inj_proj_", 1),
                    if opts.disjoint {
                        "(k2l_gen_index h; cases h)"
                    } else {
                        "cases h"
                    }
                );
                cost += wild_of[i] * 4 + 4 * largest;
            }
            (None, None) => {
                if opts.disjoint {
                    let _ = writeln!(t, "  k2l_gen_index h₂\n  cases h₂");
                } else {
                    let _ = writeln!(t, "  cases h₂");
                }
                cost += inverted.len();
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
                    used: None,
                };
                certificate(&fake, &rs[y], hno_name.get(&y).map(|s| s.as_str()), &[])
            } else {
                class_of(x, y)
                    .and_then(|c| certificate(c, &rs[y], None, &fn_names(x, y, c.used.as_ref())))
            };
            if let Some(c) = cert {
                let kind = c
                    .trim_start_matches("(k2l_det_fundep; ")
                    .trim_start_matches("exfalso; ")
                    .split_whitespace()
                    .next()
                    .unwrap_or("")
                    .trim_end_matches(')')
                    .to_string();
                if kind != "k2l_lits" {
                    cost += 2;
                }
                *ncert.entry(kind).or_default() += 1;
                if !opts.disjoint {
                    let _ = writeln!(t, "  k2l_case {} => {c}", rs[y].lean);
                } else if disj.contains(&(x.min(y), x.max(y))) {
                    // the pair's disjointness lemma, from this rule's side
                    let (a, b) = (x.min(y), x.max(y));
                    let own: Vec<String> = rs[x].step.hyps.iter().map(|(h, _)| h.clone()).collect();
                    let other: Vec<String> = rs[y]
                        .step
                        .hyps
                        .iter()
                        .map(|_| "(by assumption)".to_string())
                        .collect();
                    let (ha, hb, hc) = if x == a {
                        (own, other, "k2l_hc")
                    } else {
                        (other, own, "k2l_hc.symm")
                    };
                    let mut args = ha;
                    args.extend(hb);
                    let _ = writeln!(
                        t,
                        "  k2l_case {} => exact (Det.disj.{}.{} {} {hc}).elim",
                        rs[y].lean,
                        rs[a].lean,
                        rs[b].lean,
                        args.join(" ")
                    );
                } else {
                    let _ = writeln!(t, "  k2l_case {} => (cases k2l_hc <;> {c})", rs[y].lean);
                }
            }
        }
        if opts.disjoint {
            let _ = writeln!(t, "  all_goals (cases k2l_hc <;> k2l_default)\n");
        } else {
            let _ = writeln!(t, "  all_goals k2l_default\n");
        }
        // the heartbeats of a lemma grow with its work: the constructors it inverts and the
        // certificates it runs (a bound against a runaway proof, not a cost)
        let ncerts = t.matches("\n  k2l_case ").count()
            - t.matches("=> (k2l_det_fundep; exfalso; k2l_lits)").count();
        let hb = opts.heartbeats + 2_000 * inverted.len() as u64 + 60_000 * ncerts as u64;
        let hb = if group_of[x].is_none() && head.is_none() {
            hb.max(4_000_000)
        } else {
            hb
        };
        if hb != opts.heartbeats {
            t = format!("set_option maxHeartbeats {hb} in\n{t}");
        }
        lemmas.push((cost, t));
    }
    if std::env::var_os("K2LEAN_WITNESS_TRACE").is_some() {
        let hwm = std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|t| {
                t.lines()
                    .find(|l| l.starts_with("VmHWM"))
                    .map(|l| l.to_string())
            })
            .unwrap_or_default();
        eprintln!("det2: lemmas {:.1} s, {hwm}", t0.elapsed().as_secs_f64());
    }
    // modules of bounded cost, in rule order
    let mut chunks: Vec<Vec<String>> = vec![vec![]];
    let mut acc = 0usize;
    for (c, t) in lemmas {
        if acc > 0 && acc + c > opts.module_cost {
            chunks.push(vec![]);
            acc = 0;
        }
        acc += c;
        chunks.last_mut().unwrap().push(t);
    }
    let _ = writeln!(report, "lemma_modules = {}", chunks.len());
    let mut lmods = Vec::new();
    for (k, ch) in chunks.iter().enumerate() {
        let name = format!("L{}", k + 1);
        let mut imps = vec![pre_mod.clone()];
        imps.extend(dmods.iter().cloned());
        let mut t = header(
            &imps,
            &format!(
                "Internal part of `{ns}.Determinism`: per-rule determinism lemmas, module {}",
                k + 1
            ),
            opts.heartbeats,
            ns,
        );
        for l in ch {
            t.push_str(l);
        }
        let _ = writeln!(t, "end {ns}");
        files.push((format!("{ns}/Determinism/{name}.lean"), t));
        lmods.push(format!("{ns}.Determinism.{name}"));
    }
    for (c, n) in &ncert {
        let _ = writeln!(report, "\"certificates.{c}\" = {n}");
    }

    // a witness of each listed overlap (forced ones excepted: they are listed on purpose)
    let mut unwitnessed = 0usize;
    let mut witnessed = Vec::new();
    let mut witnessed_mod = None;
    if !overlaps.is_empty() {
        let real: Vec<(usize, usize)> = overlaps
            .iter()
            .copied()
            .filter(|p| {
                !forced.contains(p) || class_of(p.0, p.1).is_some_and(|o| o.class == "overlap")
            })
            .collect();
        let ws = crate::pairs::witnesses(def, m, rs, &real, top);
        let mut conv = crate::convert::Conv::new(m, def);
        conv.bytes_as_list = true;
        let mut t = header(
            std::slice::from_ref(&pre_mod),
            &format!(
                "Part of `{ns}.Determinism`: each pair of `overlaps` is a real nondeterminism of `Step`.\n\
For each one, a configuration at which both rules step, to different configurations. Each fact\n\
is a theorem by evaluation (`k2l_decide`): the kernel's evaluation of its `Decidable` instance, or,\n\
where that reaches a definition by well-founded recursion, which the kernel does not unfold, both\n\
sides evaluated with that definition's unfolding equation and the values compared by the kernel.\n\
The heartbeat bound is five times the lemma modules' (an evaluation is also bounded by its own\n\
step budget)"
            ),
            // an evaluation of a fact costs more than a lemma's inversion: KEVM's fact that no
            // higher-priority rule applies at witness 0 takes 496,000 (2026-10-25)
            opts.heartbeats.saturating_mul(5),
            ns,
        );
        let mut names_ok = Vec::new();
        let mut missing = Vec::new();
        for (k, (a, b)) in overlaps.iter().enumerate() {
            let w = match ws.get(&(*a, *b)) {
                Some(Ok(w)) => w,
                Some(Err(e)) => {
                    missing.push(format!(
                        "{} / {}: {e}",
                        display_name(&rs[*a]),
                        display_name(&rs[*b])
                    ));
                    continue;
                }
                None => {
                    missing.push(format!(
                        "{} / {}: listed by --det2-overlap",
                        display_name(&rs[*a]),
                        display_name(&rs[*b])
                    ));
                    continue;
                }
            };
            let render = |p: &crate::ir::P| conv.value(p, top).map(|l| l.render());
            let (Ok(c), Ok(c1), Ok(c2)) = (render(&w.config), render(&w.next.0), render(&w.next.1))
            else {
                missing.push(format!(
                    "{} / {}: the witness has no Lean value",
                    display_name(&rs[*a]),
                    display_name(&rs[*b])
                ));
                continue;
            };
            let i = if ranked { rank(&rs[*a]) } else { 0 };
            // a cost bound, not a proof failure: a witness is checked by evaluation, and the
            // kernel's cost of a literal grows with its length (design.md §3.1); a witness over
            // the bound is reported, not checked, and its pair stays in `overlaps`
            let (mut text, mut bytes) = (0, 0);
            for p in [&w.config, &w.next.0, &w.next.1] {
                longest_literal(m, p, &mut text, &mut bytes);
            }
            let over = if text > opts.long_literal {
                Some(("characters", text, opts.long_literal, "--det2-long-literal"))
            } else if bytes > opts.long_bytes {
                Some(("bytes", bytes, opts.long_bytes, "--det2-long-bytes"))
            } else {
                None
            };
            if let Some((unit, n, bound, flag)) = over {
                missing.push(format!(
                    "{} / {}: the witness holds a literal of {n} {unit}, longer than {bound} ({flag}), and is not checked",
                    display_name(&rs[*a]),
                    display_name(&rs[*b]),
                ));
                continue;
            }
            // Each fact is its own theorem: elaborated together in one term, the evaluations
            // exceeded 10 GB (KEVM, 2026-10-24), and a fact shared by both steps is proved once.
            let step_of = |fact: &str| {
                let sound = format!("(RuleResult.sound_of_next? {fact})");
                if ranked {
                    let mut arms = String::new();
                    for j in 0..i {
                        let _ = write!(arms, "\n      | {j}, _ => rank{j}_stuck Det.w{k}_s{j}");
                    }
                    let _ = write!(arms, "\n      | _ + {i}, hj => absurd hj (by omega)");
                    format!("Step0.lift {sound}\n    (fun j hj => match j, hj with{arms})")
                } else {
                    sound
                }
            };
            let mut stuck = String::new();
            if ranked {
                for j in 0..i {
                    let _ = writeln!(
                        stuck,
                        "theorem Det.w{k}_s{j} : firstDefined (bucketOf{j} Det.w{k}) Det.w{k} none = .stuck := by k2l_decide"
                    );
                }
            }
            let _ = write!(
                t,
                "/-- internal: the configuration of the witness of overlap {k}. -/\ndef Det.w{k} : {top} :=\n  {c}\n\
/-- internal: the step of the first rule. -/\ndef Det.w{k}_1 : {top} :=\n  {c1}\n\
/-- internal: the step of the second rule. -/\ndef Det.w{k}_2 : {top} :=\n  {c2}\n\n\
/-- internal: the facts of the witness of overlap {k}, each by evaluation. -/\n\
theorem Det.w{k}_a : (Rules.{} Det.w{k}).next? = some Det.w{k}_1 := by k2l_decide\n\
theorem Det.w{k}_b : (Rules.{} Det.w{k}).next? = some Det.w{k}_2 := by k2l_decide\n\
theorem Det.w{k}_ne : Det.w{k}_1 ≠ Det.w{k}_2 := by k2l_decide\n{stuck}\n\
/-- `{}` and `{}` both step from one configuration, to different ones. -/\n\
theorem overlap_witness_{k} : Overlap.Witnessed Step (⟨R.{}, R.{}⟩ : Overlap {top}) :=\n  \
⟨Det.w{k}, Det.w{k}_1, Det.w{k}_2, Det.w{k}_a, Det.w{k}_b, Det.w{k}_ne,\n    \
{},\n    {}⟩\n\n",
                rs[*a].lean,
                rs[*b].lean,
                names::string_lit(&display_name(&rs[*a])).trim_matches('"'),
                names::string_lit(&display_name(&rs[*b])).trim_matches('"'),
                rs[*a].lean,
                rs[*b].lean,
                step_of(&format!("Det.w{k}_a")),
                step_of(&format!("Det.w{k}_b")),
            );
            names_ok.push(format!("overlap_witness_{k}"));
        }
        unwitnessed = missing.len();
        witnessed = names_ok.clone();
        if missing.is_empty() {
            let _ = write!(
                t,
                "/-- Every listed pair is a real nondeterminism of `Step`: `overlaps` is exact. -/\ntheorem overlaps_witnessed : ∀ o ∈ overlaps, o.Witnessed Step := by\n  intro o ho\n  simp only [overlaps, List.mem_cons, List.not_mem_nil, or_false] at ho\n  rcases ho with {}\n  {}\n\n",
                (0..names_ok.len())
                    .map(|_| "rfl")
                    .collect::<Vec<_>>()
                    .join(" | "),
                names_ok
                    .iter()
                    .map(|n| format!("· exact {n}"))
                    .collect::<Vec<_>>()
                    .join("\n  ")
            );
        } else {
            let _ = write!(
                t,
                "/-! {} listed pairs have no checked witness, so `overlaps_witnessed` is not stated. They stay\nin `overlaps`, so `Step.deterministic_of` assumes them apart as it does every listed pair; only\nthe claim that the list is exact is not made:\n{}\n-/\n\n",
                missing.len(),
                missing
                    .iter()
                    .map(|m| format!("- {}", m.replace("-/", "- /")))
                    .collect::<Vec<_>>()
                    .join("\n")
            );
        }
        let _ = writeln!(t, "end {ns}");
        files.push((format!("{ns}/Determinism/Witness.lean"), t));
        witnessed_mod = Some(format!("{ns}.Determinism.Witness"));
        let _ = writeln!(
            report,
            "witnessed = {}\nunwitnessed = {unwitnessed}",
            names_ok.len()
        );
        for mm in &missing {
            let _ = writeln!(report, "# unwitnessed: {:.300}", mm);
        }
    }

    // the theorems
    let mut imports = lmods.clone();
    imports.extend(witnessed_mod);
    let mut o = header(
        &imports,
        &format!(
            "Determinism of `Step`{}. `overlaps` lists the pairs of rules of one rank that can both apply at\n\
one configuration ({} pairs): there `Step` has two successors in general, which is the\n\
definition's own nondeterminism (`krun` takes the first rule in its order); each listed pair\n\
is witnessed by a configuration where both rules step to different results\n\
(`overlaps_witnessed`). At a configuration where no listed pair applies with both rules\n\
(`noOverlap c = true`) the successor is unique.\n\n\
The proof inverts the second step through relations split by the first item of the `<k>` cell\n\
(namespace `Det`, internal) and closes each remaining goal with the certificate chosen by the\n\
generator's pair classification; the kernel checks every one",
            if ranked { " with priority ranks" } else { "" },
            overlaps.len()
        ),
        opts.heartbeats,
        ns,
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
        for (_, k, fst) in partners.get(&x).into_iter().flatten() {
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
    files.insert(0, (format!("{ns}/Determinism.lean"), o));
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
        files,
        overlaps: overlaps.len(),
        unwitnessed,
        witnessed,
        report,
    }
}

/// The default of `--det2-long-literal`: the kernel encodes a `String` literal of 400 characters
/// in 9.9 s (100 in 0.84 s, 2026-10-24), a cost quadratic in its length, and a string hook may
/// decode it by well-founded recursion.
pub const LONG_LITERAL: usize = 256;

/// The default of `--det2-long-bytes`, 2^17: a witness writes a `Bytes` value as the list of its
/// bytes, which the kernel compares in time and memory linear in its length, but with a large
/// constant in memory (`==` on equal lists of 2^16 bytes: 4.6 s, 1.7 GB; of 2^18 bytes: 21 s,
/// 5.3 GB, and 26 s, 7.4 GB for lists that differ at the end; 2026-10-25), so the bound keeps one
/// comparison near 15 s and 4 GB, and a fact that compares or measures the value a few times to
/// tens of seconds, while a larger value is reported instead of filling the build's memory.
pub const LONG_BYTES: usize = 1 << 17;

/// The longest `String` or token literal (`text`) and `Bytes` literal (`bytes`) in `p`, joined
/// into the running maxima.
fn longest_literal(m: &crate::model::Model, p: &crate::ir::P, text: &mut usize, bytes: &mut usize) {
    use crate::ir::P;
    use crate::model::{Builtin, Kind};
    match p {
        P::Dv(s, v) => {
            let n = v.chars().count();
            let is_bytes = s
                .name()
                .and_then(|s| m.sorts.get(s))
                .is_some_and(|i| matches!(i.kind, Kind::Builtin(Builtin::Bytes)));
            let max = if is_bytes { bytes } else { text };
            *max = (*max).max(n);
        }
        P::App(_, _, args) | P::And(_, args) | P::Or(_, args) => {
            for a in args {
                longest_literal(m, a, text, bytes);
            }
        }
        P::Not(_, a) => longest_literal(m, a, text, bytes),
        P::Implies(_, a, b) | P::Iff(_, a, b) => {
            longest_literal(m, a, text, bytes);
            longest_literal(m, b, text, bytes);
        }
        _ => {}
    }
}

/// The axiom guard of determinism alone, `NSTest/DetAxioms.lean`, for a library with `overlaps`
/// listed pairs: the unconditional theorems without overlaps; otherwise the conditional ones, and
/// `overlaps_witnessed` when every pair is witnessed, or else each witnessed pair's
/// `overlap_witness_k`. It imports `NS.Determinism` and what that imports, not `NS.Equations`
/// (KEVM's does not build yet); the library's whole guard `NSTest.Axioms` imports it.
pub fn guard(ns: &str, overlaps: usize, unwitnessed: usize, witnessed: &[String]) -> String {
    let mut names: Vec<String> = if overlaps == 0 {
        vec![
            "Step.deterministic".into(),
            "step_complete".into(),
            "step_iff".into(),
        ]
    } else {
        vec![
            "Step.deterministic_of".into(),
            "step_complete_of".into(),
            "step_iff_of_noOverlap".into(),
        ]
    };
    if overlaps > 0 {
        if unwitnessed == 0 {
            names.push("overlaps_witnessed".into());
        } else {
            names.extend(witnessed.iter().cloned());
        }
    }
    let mut o = format!(
        "import {ns}.Determinism\nimport KPrelude.Tactic\n\n/-! Generated by k2lean; do not edit. Build-time guard of determinism alone: the theorems of\n`{ns}.Determinism` use only `propext`, `Quot.sound` and `Classical.choice` (no `sorryAx`, no added\naxioms). It imports `{ns}.Determinism` and what that imports, not `{ns}.Equations`; the guard\n`{ns}Test.Axioms` imports it. -/\n\nopen {ns} KPrelude\n\n"
    );
    for chunk in names.chunks(8) {
        let ns_names: Vec<String> = chunk.iter().map(|n| format!("{ns}.{n}")).collect();
        let _ = writeln!(o, "#k2l_assert_axioms {}", ns_names.join(" "));
    }
    o
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_guard_names_each_witness_when_one_is_missing() {
        let g = guard("N", 0, 0, &[]);
        assert!(g.contains("#k2l_assert_axioms N.Step.deterministic N.step_complete N.step_iff\n"));
        let g = guard(
            "N",
            2,
            0,
            &["overlap_witness_0".into(), "overlap_witness_1".into()],
        );
        assert!(g.contains("N.step_iff_of_noOverlap N.overlaps_witnessed\n"));
        let g = guard("N", 2, 1, &["overlap_witness_1".into()]);
        assert!(g.contains("N.step_iff_of_noOverlap N.overlap_witness_1\n"));
        assert!(!g.contains("overlaps_witnessed") && !g.contains("import N.Equations"));
    }

    #[test]
    fn the_partners_names_are_primed_as_whole_identifiers() {
        let names: BTreeSet<String> = ["K".to_string(), "r".to_string()].into_iter().collect();
        assert_eq!(
            primed("K.isKResult (SortK.kseq K r) = some r_2", &names),
            "K.isKResult (SortK.kseq K' r') = some r_2"
        );
    }
}
