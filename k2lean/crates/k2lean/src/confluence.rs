//! `k2lean confluence`: the determinism of observations modulo scheduling, as a scaffold
//! (`k2lean/docs/design.md`, section 3.6).
//!
//! Statement, for a program hypothesis `H` (a preserved predicate the hand module supplies) and
//! an observation `obs` (a projection of configuration cells, `--obs`):
//! `H c → Star Step c n₁ → Terminal Step n₁ → Star Step c n₂ → Terminal Step n₂ → n₁ = n₂`, hence
//! `obs n₁ = obs n₂`. It follows from the diamond property (`KPrelude.terminal_unique_of_diamond`,
//! no termination hypothesis) or, with `--join local`, from local confluence and a measure every
//! step decreases (Newman's lemma, `terminal_unique_of_local`; the hand module supplies `μ` and
//! `μ_dec`).
//!
//! The joins are one obligation per ordered pair of rules (`pair.r₁.r₂`): two instances of the
//! rules whose left-hand sides are one configuration have successors that join. Each is
//! attempted by generic arguments, in order: the instances are refuted (the left-hand sides do
//! not unify, `cases`), or are one instance (the same successor), or act at two bindings of a cell
//! map matched at a free key (threads) and commute (`MapHook.concat_element_same_or_comm`), or
//! one updates a binding and the other inserts a fresh one (`concat_element_comm_insert`), or
//! each applies after the other unchanged; the two final states are closed by `k2l_join_eq`
//! (equal up to the commutativity of integer addition). The pairs listed in `--open` are the hand
//! module's (`hand.pair.r₁.r₂`, of the same type).
//!
//! The report (`--report`) classifies the pairs without Lean: by the pair classifier of
//! `pairs.rs` with two free-key matches taken as one binding (`clash`, `exclusive`, `joinable`,
//! `overlap`), and, for two rules that match one cell map at free keys, by their footprints on
//! the other cells (`independent`: neither writes a cell the other reads or writes, so they
//! commute by the map lemma; `conflict`: the cells they race on). `--report-only` writes only
//! the report (definitions whose `Lean` module of n² pairs is beyond a gate's budget, SIMPLE).

use crate::ir::{self, Def, P};
use crate::lower::L;
use crate::model::Model;
use crate::rules::{self, Rule};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

fn fail(msg: &str) -> ! {
    eprintln!("confluence: {msg}");
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

pub(crate) struct Lib {
    pub def: Def,
    pub m: Model,
    pub rules: Vec<Rule>,
    pub prios: Vec<i64>,
    pub ranked: bool,
    pub top: String,
}

pub(crate) fn load(kore: &str) -> Lib {
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
    let (rules, prios, ranked) =
        rules::collect_ranked(&def, &m, &fgen.fns, &[]).unwrap_or_else(|e| fail(&e));
    let top = rules::top_sort(&def).unwrap_or_else(|e| fail(&e));
    Lib {
        def,
        m,
        rules,
        prios,
        ranked,
        top,
    }
}

const MAP_HYP: &str = "KPrelude.MapHook.concat (KPrelude.MapHook.element";

/// A map hypothesis `concat (element K V) REST = some X`: (REST, X).
fn map_hyp(h: &str) -> Option<(String, String)> {
    if !h.starts_with(MAP_HYP) {
        return None;
    }
    let (lhs, x) = h.rsplit_once(" = some ")?;
    let rest = lhs.rsplit(' ').next()?;
    let ok = |t: &str| !t.is_empty() && !t.contains(['(', ')']);
    (ok(rest) && ok(x)).then(|| (rest.to_string(), x.trim().to_string()))
}

/// How a rule uses a cell map matched at a free key.
#[derive(Clone, Debug, PartialEq)]
enum MapRole {
    /// `hm : (K ↦ V) R = some m` on the left, `hr : (K ↦ W) R = some r` on the right: an update
    /// of one binding.
    Update {
        hm: String,
        hr: String,
    },
    /// `hr : (K ↦ W) M = some r` with `M` the cell's content on the left: an insertion.
    Insert {
        hr: String,
    },
    None,
}

fn map_role(r: &Rule) -> MapRole {
    let lhs_hyps: BTreeSet<&String> = r.app.hyps.iter().map(|(h, _)| h).collect();
    // only maps that are a cell's whole content: the free-key cell maps of the configuration,
    // not maps matched inside a binding (an environment, a store at a bound key)
    let in_lhs = cell_vars(&r.step.index);
    let in_rhs = cell_vars(&r.rhs.subst(&r.step.subst));
    let mut matches = vec![];
    let mut results = vec![];
    for (h, p) in &r.step.hyps {
        let Some((rest, x)) = map_hyp(p) else {
            continue;
        };
        if lhs_hyps.contains(h) {
            if in_lhs.contains(&x) && free_key(r, h, p) {
                matches.push((h.clone(), rest, x));
            }
        } else if in_rhs.contains(&x) {
            results.push((h.clone(), rest, x));
        }
    }
    if let [(hm, rest, _)] = matches.as_slice() {
        let rs: Vec<&(String, String, String)> =
            results.iter().filter(|(_, r2, _)| r2 == rest).collect();
        return match rs.as_slice() {
            [(hr, _, _)] => MapRole::Update {
                hm: hm.clone(),
                hr: hr.clone(),
            },
            _ => MapRole::None,
        };
    }
    match results.as_slice() {
        [(hr, rest, _)] if matches.is_empty() && in_lhs.contains(rest) => {
            MapRole::Insert { hr: hr.clone() }
        }
        _ => MapRole::None,
    }
}

/// Whether the key of a map hypothesis is free: none of its variables occurs in the left-hand
/// side's index or in another left-hand-side hypothesis (a key bound elsewhere, such as a store
/// location read off `<k>`, makes the match unique).
fn free_key(r: &Rule, h: &str, p: &str) -> bool {
    key_bound_only_by(r, h, p, None)
}

/// Whether the key of a map hypothesis `h` is bound by `h` and, if given, by the hypothesis
/// `outer` only: the second binding of a two-binding match whose key the first binding names (a
/// message to a named process, `resume(Q)` at one binding and `<pid> Q` at the other), still a
/// binding of the thread map, matched in the first binding's rest.
fn key_bound_only_by(r: &Rule, h: &str, p: &str, outer: Option<&str>) -> bool {
    let Some(rest) = p.strip_prefix(MAP_HYP) else {
        return false;
    };
    let key = first_arg(rest.trim_start());
    // the words of a term, outside `«…»`-quoted names (a cell `<k>` is not a variable `k`)
    let words = |t: &str| -> BTreeSet<String> {
        let mut bare = String::new();
        let mut quoted = false;
        for ch in t.chars() {
            match ch {
                '«' => quoted = true,
                '»' => {
                    quoted = false;
                    bare.push(' ')
                }
                _ if !quoted => bare.push(ch),
                _ => {}
            }
        }
        bare.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
            .filter(|w| {
                !w.is_empty()
                    && w.chars()
                        .next()
                        .is_some_and(|c| c.is_lowercase() || c.is_uppercase())
            })
            .map(String::from)
            .collect()
    };
    let binders: BTreeSet<&String> = r.step.binders.iter().map(|(b, _)| b).collect();
    let kv: BTreeSet<String> = words(key)
        .into_iter()
        .filter(|w| binders.contains(w))
        .collect();
    if kv.is_empty() {
        return false;
    }
    let mut elsewhere = r.step.index.render();
    for (h2, p2) in &r.app.hyps {
        if h2 != h && Some(h2.as_str()) != outer {
            elsewhere.push(' ');
            elsewhere.push_str(p2);
        }
    }
    let ew = words(&elsewhere);
    kv.iter().all(|v| !ew.contains(v))
}

/// How a rule of `--threads` replaces bindings of the thread map (`MStep a b`): which hypotheses
/// match its bindings (`a`, outer first), and how the rule builds `b`.
#[derive(Clone, Debug, PartialEq)]
enum VRole {
    /// `hm : (K ↦ V) R = some m`, `hr : (K ↦ W) R = some r`: one thread's step.
    Update { hm: String, hr: String },
    /// `hm` with `m` itself on the right: a step that reads one thread and leaves the map alone.
    Keep { hm: String },
    /// `hm` with its rest `R` on the right: the binding removed (a thread's end).
    Remove { hm: String },
    /// `hms` match one binding (`(K ↦ V) R = some m`) or two (`(K₁ ↦ V₁) rest = some m`,
    /// `(K₂ ↦ V₂) R = some rest`); `hb : (K ↦ W) (K' ↦ W') = some b` builds what replaces them
    /// and `hr : b R = some r` the map on the right. With one binding `b` adds a key (a spawn); with
    /// two `b` has their keys (two threads meeting).
    Replace {
        hms: Vec<String>,
        hb: String,
        hr: String,
    },
}

impl VRole {
    /// The hypotheses that match the bindings, outer first.
    fn matches(&self) -> Vec<&String> {
        match self {
            VRole::Update { hm, .. } | VRole::Keep { hm } | VRole::Remove { hm } => vec![hm],
            VRole::Replace { hms, .. } => hms.iter().collect(),
        }
    }

    /// Whether `b` may have a key `a` does not (`Rule.ins`).
    fn inserts(&self) -> bool {
        matches!(self, VRole::Replace { hms, .. } if hms.len() == 1)
    }
}

/// The keys of the `element`s in a hypothesis, in order.
fn element_keys(h: &str) -> Vec<&str> {
    h.match_indices("KPrelude.MapHook.element ")
        .map(|(i, m)| first_arg(&h[i + m.len()..]))
        .collect()
}

/// The thread-map role of a rule for `--threads` (`None`: a global rule), for the thread map in
/// the cell `<threads>`.
fn view_role(r: &Rule, role: &MapRole, threads: &str) -> Option<VRole> {
    if let MapRole::Update { hm, hr } = role {
        return Some(VRole::Update {
            hm: hm.clone(),
            hr: hr.clone(),
        });
    }
    let lhs_hyps: BTreeSet<&String> = r.app.hyps.iter().map(|(h, _)| h).collect();
    let in_lhs = cell_vars(&r.step.index);
    let in_rhs = cell_vars(&r.rhs.subst(&r.step.subst));
    let lhs_maps: Vec<(&String, &String, String, String)> = r
        .step
        .hyps
        .iter()
        .filter(|(h, _)| lhs_hyps.contains(h))
        .filter_map(|(h, p)| map_hyp(p).map(|(rest, x)| (h, p, rest, x)))
        .collect();
    // the match of the thread map's content: whatever else reads its key (an owner check on
    // another cell), a step at one binding of the thread map is a view; without the cell's
    // content as a variable, a match at a free key
    let tvar = match cell_content(&r.step.index, threads) {
        Some(L::Var(v)) => Some(v),
        _ => None,
    };
    let tops: Vec<_> = lhs_maps
        .iter()
        .filter(|(h, p, _, x)| match tvar {
            Some(t) => x == t,
            None => in_lhs.contains(x) && free_key(r, h, p),
        })
        .collect();
    let [(hm, _, rest, x)] = tops.as_slice() else {
        return None;
    };
    if in_rhs.contains(x) {
        return Some(VRole::Keep { hm: (*hm).clone() });
    }
    if in_rhs.contains(rest) {
        return Some(VRole::Remove { hm: (*hm).clone() });
    }
    // one binding rebound beside the rest (`map_role`'s update, when the key is read elsewhere)
    let rebound: Vec<&String> = r
        .step
        .hyps
        .iter()
        .filter(|(h, p)| {
            !lhs_hyps.contains(h)
                && map_hyp(p).is_some_and(|(rr, y)| &rr == rest && in_rhs.contains(&y))
        })
        .map(|(h, _)| h)
        .collect();
    if let [hr] = rebound.as_slice() {
        return Some(VRole::Update {
            hm: (*hm).clone(),
            hr: (*hr).clone(),
        });
    }
    // a second binding matched in the rest
    let inner: Vec<_> = lhs_maps
        .iter()
        .filter(|(h, p, _, x2)| x2 == rest && key_bound_only_by(r, h, p, Some(hm.as_str())))
        .collect();
    let (hms, base) = match inner.as_slice() {
        [] => (vec![(*hm).clone()], rest.clone()),
        [(hm2, _, rest2, _)] => (vec![(*hm).clone(), (*hm2).clone()], rest2.clone()),
        _ => return None,
    };
    // `hr : b R = some r`, with `r` the map on the right, and `hb : … = some b` from elements
    let pre = "KPrelude.MapHook.concat ";
    let (hr, b) = r.step.hyps.iter().find_map(|(h, p)| {
        let (lhs, rv) = p.rsplit_once(" = some ")?;
        let mut ws = lhs.strip_prefix(pre)?.split(' ');
        let (bv, rr) = (ws.next()?, ws.next()?);
        (ws.next().is_none() && rr == base && in_rhs.contains(rv.trim()))
            .then(|| (h.clone(), bv.to_string()))
    })?;
    let hb = r.step.hyps.iter().find_map(|(h, p)| {
        let (lhs, bv) = p.rsplit_once(" = some ")?;
        let lhs = lhs.strip_prefix('(').unwrap_or(lhs);
        (bv.trim() == b && lhs.starts_with("KPrelude.MapHook.concat (KPrelude.MapHook.element "))
            .then(|| (h.clone(), p.clone()))
    })?;
    let ks = element_keys(&hb.1);
    if ks.len() != 2 {
        return None;
    }
    // two bindings: `b` rebinds their keys, in order
    if hms.len() == 2 {
        let hyp = |h: &String| &r.step.hyps.iter().find(|(x, _)| x == h).unwrap().1;
        let ka: Vec<&str> = hms
            .iter()
            .filter_map(|h| element_keys(hyp(h)).first().copied())
            .collect();
        if ka != ks {
            return None;
        }
    }
    Some(VRole::Replace { hms, hb: hb.0, hr })
}

/// How a rule changes a shared cell holding a map at some of its bindings (`MCh`): the bindings
/// `a` it matches, replaced by `b`, the rest `R` kept. Each role names the hypotheses that give
/// `a R = x` (the cell's content on the left) and `b R = y` (on the right).
#[derive(Clone, Debug, PartialEq)]
enum KRole {
    /// `hm : (K ↦ V) R = some x`, `hr : (K ↦ W) R = some y`: a write at one binding.
    Update { hm: String, hr: String },
    /// `hm : (K ↦ V) R = some x` with `x` on the right: a read of one binding.
    Keep { hm: String },
    /// `hm : (K ↦ V) R = some x` with `R` on the right: a removal.
    Remove { hm: String },
    /// `hr : (K ↦ W) x = some y`: an insertion (`a` empty, the rest the whole content).
    Insert { hr: String },
    /// `hm : (K ↦ V) R = some x`, `hb : (K ↦ V) (K' ↦ W) = some b`, `hr : b R = some y`: a read of
    /// one binding with one added beside it (`MCh.SmallR`).
    Extend { hm: String, hb: String, hr: String },
}

impl KRole {
    /// The proofs of `a R = x` and `b R = y` from the rule's hypotheses.
    fn proofs(&self) -> (String, String) {
        match self {
            KRole::Update { hm, hr } | KRole::Extend { hm, hr, .. } => (hm.clone(), hr.clone()),
            KRole::Keep { hm } => (hm.clone(), hm.clone()),
            KRole::Remove { hm } => (
                hm.clone(),
                format!("(MapHook.concat_unit_left (MapHook.wf_right_of_concat {hm}))"),
            ),
            KRole::Insert { hr } => (
                format!("(MapHook.concat_unit_left (MapHook.wf_right_of_concat {hr}))"),
                hr.clone(),
            ),
        }
    }

    /// The proof that the change matches at most one binding and puts at most one back
    /// (`MCh.Small`), or, with `wide` (a cell some rule extends), `MCh.SmallR`.
    fn small(&self, wide: bool) -> String {
        let s = match self {
            KRole::Update { .. } | KRole::Keep { .. } => {
                "MCh.small_of (.inl ⟨_, _, rfl⟩) (.inl ⟨_, _, rfl⟩)"
            }
            KRole::Remove { .. } => "MCh.small_of (.inl ⟨_, _, rfl⟩) (.inr rfl)",
            KRole::Insert { .. } => "MCh.small_of (.inr rfl) (.inl ⟨_, _, rfl⟩)",
            KRole::Extend { hb, .. } => return format!("MCh.smallR_extend {hb}"),
        };
        if wide {
            format!("MCh.smallR_of_small ({s})")
        } else {
            s.to_string()
        }
    }

    /// In the replay, from `hx : a R' = some x'` and `hy : b R' = some y'`: the equation to
    /// eliminate, and the rule's hypotheses restated.
    fn replay(&self, hx: &str, hy: &str) -> (String, Vec<(String, String)>) {
        match self {
            KRole::Update { hm, hr } | KRole::Extend { hm, hr, .. } => (
                String::new(),
                vec![(hm.clone(), hx.into()), (hr.clone(), hy.into())],
            ),
            KRole::Keep { hm } => (
                format!("  cases Option.some.inj ({hx}.symm.trans {hy})\n"),
                vec![(hm.clone(), hx.into())],
            ),
            KRole::Remove { hm } => (
                format!("  cases MapHook.eq_of_concat_unit_left {hy}\n"),
                vec![(hm.clone(), hx.into())],
            ),
            KRole::Insert { hr } => (
                format!("  cases MapHook.eq_of_concat_unit_left {hx}\n"),
                vec![(hr.clone(), hy.into())],
            ),
        }
    }
}

/// The content of the cell `<cell>` in a configuration term.
fn cell_content<'a>(l: &'a L, cell: &str) -> Option<&'a L> {
    if let L::App(h, a) = l {
        if is_cell(h).as_deref() == Some(cell) {
            return match a.as_slice() {
                [x] => Some(x),
                _ => None,
            };
        }
        return a.iter().find_map(|x| cell_content(x, cell));
    }
    None
}

/// How a rule touches the shared cell `<cell>`, if it holds a map: `Some(None)` when it leaves the
/// cell alone, `Some(Some(role))` when it changes it at some bindings only (`KRole`), and `None`
/// when it reads or writes the whole map (a side condition on it, a rest read elsewhere, an
/// `update`).
fn keyed_role(r: &Rule, cell: &str, touched: bool) -> Option<Option<KRole>> {
    if !touched {
        return Some(None);
    }
    let rhs = r.rhs.subst(&r.step.subst);
    let (L::Var(x), L::Var(y)) = (
        cell_content(&r.step.index, cell)?,
        cell_content(&rhs, cell)?,
    ) else {
        return None;
    };
    let lhs_hyps: BTreeSet<&String> = r.app.hyps.iter().map(|(h, _)| h).collect();
    // the occurrences of a variable in the rule: both sides and every hypothesis
    let text = format!(
        "{} {} {}",
        r.step.index.render(),
        rhs.render(),
        r.step
            .hyps
            .iter()
            .map(|(_, p)| p.as_str())
            .collect::<Vec<_>>()
            .join(" ")
    );
    // outside `«…»`-quoted names (a cell `<k>` is not a variable `k`)
    let mut bare = String::new();
    let mut quoted = false;
    for ch in text.chars() {
        match ch {
            '«' => quoted = true,
            '»' => {
                quoted = false;
                bare.push(' ')
            }
            _ if !quoted => bare.push(ch),
            _ => {}
        }
    }
    let count = |v: &str| {
        bare.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
            .filter(|w| *w == v)
            .count()
    };
    let hyp = |lhs: bool, rest: &str, m: &str| -> Option<String> {
        let hs: Vec<&String> = r
            .step
            .hyps
            .iter()
            .filter(|(h, p)| {
                lhs_hyps.contains(h) == lhs
                    && map_hyp(p).is_some_and(|(rr, mm)| rr == rest && mm == m)
            })
            .map(|(h, _)| h)
            .collect();
        match hs.as_slice() {
            [h] => Some((*h).clone()),
            _ => None,
        }
    };
    let matches: Vec<(String, String)> = r
        .step
        .hyps
        .iter()
        .filter(|(h, _)| lhs_hyps.contains(h))
        .filter_map(|(h, p)| map_hyp(p).and_then(|(rest, m)| (&m == x).then(|| (h.clone(), rest))))
        .collect();
    let role = match matches.as_slice() {
        // the cell's content, its bindings matched; each variable where the shape puts it only
        [(hm, rest)] if y == x => {
            (count(x) == 3 && count(rest) == 1).then(|| KRole::Keep { hm: hm.clone() })
        }
        [(hm, rest)] if y == rest => {
            (count(x) == 2 && count(rest) == 2).then(|| KRole::Remove { hm: hm.clone() })
        }
        [(hm, rest)] => match hyp(false, rest, y) {
            Some(hr) => (count(x) == 2 && count(rest) == 2 && count(y) == 2)
                .then(|| KRole::Update { hm: hm.clone(), hr }),
            // `(K ↦ V) (K' ↦ W) = some b` and `b R = some y`: the matched binding kept, one added
            None => {
                let elem = |h: &str| -> Option<String> {
                    let t = r.step.hyps.iter().find(|(n, _)| n == h)?.1.as_str();
                    Some(first_arg(t.strip_prefix("KPrelude.MapHook.concat ")?).to_string())
                };
                let e = elem(hm)?;
                let (hr, b) = r.step.hyps.iter().find_map(|(h, p)| {
                    let (lhs, m) = p.rsplit_once(" = some ")?;
                    let mut w = lhs.strip_prefix("KPrelude.MapHook.concat ")?.split(' ');
                    let (b, rr) = (w.next()?, w.next()?);
                    (w.next().is_none() && !lhs_hyps.contains(h) && rr == rest && m.trim() == y)
                        .then(|| (h.clone(), b.to_string()))
                })?;
                let hb = r.step.hyps.iter().find_map(|(h, p)| {
                    let (lhs, m) = p.rsplit_once(" = some ")?;
                    let inner = lhs.strip_prefix("(KPrelude.MapHook.concat ")?;
                    let second = inner.strip_prefix(&e)?.trim_start();
                    (!lhs_hyps.contains(h)
                        && m.trim() == b
                        && second.starts_with("(KPrelude.MapHook.element "))
                    .then(|| h.clone())
                })?;
                (count(x) == 2 && count(rest) == 2 && count(y) == 2 && count(&b) == 2).then(|| {
                    KRole::Extend {
                        hm: hm.clone(),
                        hb,
                        hr,
                    }
                })
            }
        },
        [] if y != x => {
            let hr = hyp(false, x, y)?;
            (count(x) == 2 && count(y) == 2).then_some(KRole::Insert { hr })
        }
        _ => None,
    }?;
    Some(Some(role))
}

/// The first argument of an application's argument list (`(a b) c` → `(a b)`, `k c` → `k`).
fn first_arg(t: &str) -> &str {
    if t.starts_with('(') {
        let mut d = 0;
        for (i, ch) in t.char_indices() {
            match ch {
                '(' => d += 1,
                ')' => {
                    d -= 1;
                    if d == 0 {
                        return &t[..=i];
                    }
                }
                _ => {}
            }
        }
        t
    } else {
        t.split(' ').next().unwrap_or(t)
    }
}

/// The variables that are the whole content of a cell.
fn cell_vars(l: &L) -> BTreeSet<String> {
    fn go(l: &L, out: &mut BTreeSet<String>) {
        if let L::App(h, a) = l {
            if is_cell(h).is_some()
                && let [L::Var(v)] = a.as_slice()
            {
                out.insert(v.clone());
            }
            a.iter().for_each(|x| go(x, out));
        }
    }
    let mut out = BTreeSet::new();
    go(l, &mut out);
    out
}

fn is_cell(head: &str) -> Option<String> {
    let i = head.find(".«<")?;
    let name = head[i + ".«<".len()..].strip_suffix(">»")?;
    Some(name.to_string())
}

/// The cells a rule reads and writes, outside the bindings of free-key cell maps: a leaf cell
/// is written when its right-hand side differs from its left-hand side, and read when its
/// left-hand side is not a variable or its variable occurs elsewhere (another cell, a side
/// condition). A cell map's content is reported under the map cell's name.
fn footprint(r: &Rule) -> BTreeMap<String, (bool, bool)> {
    let lhs = &r.step.index;
    let rhs = r.rhs.subst(&r.step.subst);
    let hyps: String = r
        .step
        .hyps
        .iter()
        .map(|(_, p)| p.as_str())
        .collect::<Vec<_>>()
        .join(" ");
    let mut leaves: Vec<(String, L, L)> = vec![];
    fn walk(a: &L, b: &L, out: &mut Vec<(String, L, L)>, name: Option<String>) {
        if let (L::App(ha, xa), L::App(hb, xb)) = (a, b)
            && ha == hb
            && xa.len() == xb.len()
            && xa
                .iter()
                .any(|x| matches!(x, L::App(h, _) if is_cell(h).is_some()))
        {
            for (x, y) in xa.iter().zip(xb) {
                let n = match x {
                    L::App(h, _) => is_cell(h),
                    _ => None,
                };
                walk(x, y, out, n);
            }
            return;
        }
        out.push((name.unwrap_or_else(|| "?".into()), a.clone(), b.clone()));
    }
    walk(lhs, &rhs, &mut leaves, None);
    let rendered: Vec<String> = leaves
        .iter()
        .map(|(_, a, b)| format!("{} {}", a.render(), b.render()))
        .collect();
    let mut out: BTreeMap<String, (bool, bool)> = BTreeMap::new();
    for (i, (name, a, b)) in leaves.iter().enumerate() {
        // a leaf that is a variable standing for a whole cell: name it by the variable's type
        let name = if name == "?" {
            match a {
                L::Var(v) => r
                    .step
                    .binders
                    .iter()
                    .find(|(x, _)| x == v)
                    .map(|(_, t)| t.trim_start_matches("Sort").to_string())
                    .unwrap_or_else(|| "?".into()),
                _ => "?".into(),
            }
        } else {
            name.clone()
        };
        let write = a.render() != b.render();
        let elsewhere = |v: &String| {
            let occurs = |t: &str| {
                t.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
                    .any(|w| w == v)
            };
            occurs(&hyps)
                || rendered
                    .iter()
                    .enumerate()
                    .any(|(j, t)| j != i && occurs(t))
        };
        let read = match a {
            L::Var(v) => elsewhere(v),
            _ => true,
        };
        let e = out.entry(name).or_default();
        e.0 |= read;
        e.1 |= write;
    }
    out
}

/// The cells two rules race on: one writes what the other reads or writes, outside `map`.
fn conflicts(
    a: &BTreeMap<String, (bool, bool)>,
    b: &BTreeMap<String, (bool, bool)>,
    map: &BTreeSet<String>,
) -> Vec<String> {
    a.iter()
        .filter(|(c, _)| !map.contains(*c))
        .filter_map(|(c, (ra, wa))| {
            let (rb, wb) = b.get(c).copied().unwrap_or((false, false));
            ((*wa && (rb || wb)) || (wb && *ra)).then(|| c.clone())
        })
        .collect()
}

/// The cell holding a free-key map: the cell (by name) whose content is the variable a map
/// hypothesis matches.
fn map_cells(r: &Rule) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let lhs = &r.step.index;
    let mut targets = BTreeSet::new();
    for (_, p) in &r.step.hyps {
        if let Some((rest, x)) = map_hyp(p) {
            targets.insert(rest);
            targets.insert(x);
        }
    }
    fn go(l: &L, t: &BTreeSet<String>, out: &mut BTreeSet<String>) {
        if let L::App(h, a) = l {
            if let Some(n) = is_cell(h)
                && a.len() == 1
                && matches!(&a[0], L::Var(v) if t.contains(v))
            {
                out.insert(n);
            }
            a.iter().for_each(|x| go(x, t, out));
        }
    }
    go(lhs, &targets, &mut out);
    out
}

/// The observation: the path to each named cell in a rule's left-hand side, as a match pattern.
pub(crate) fn proj_def(
    lib: &Lib,
    name: &str,
    def: &str,
    cells: &[String],
    content: Option<&str>,
) -> String {
    let mut pats: Vec<(String, String)> = vec![]; // (cell type, path)
    // the pattern of the top configuration with `x{i}` at each observed cell
    fn find(l: &L, cell: &str, path: &mut Vec<usize>) -> Option<String> {
        if let L::App(h, a) = l {
            if is_cell(h).as_deref() == Some(cell) {
                return Some(h.split(".«").next().unwrap_or(h).to_string());
            }
            for (i, x) in a.iter().enumerate() {
                path.push(i);
                if let Some(t) = find(x, cell, path) {
                    return Some(t);
                }
                path.pop();
            }
        }
        None
    }
    let mut shape: Option<L> = None;
    let mut paths = vec![];
    for c in cells {
        let mut found = None;
        for r in &lib.rules {
            let mut p = vec![];
            if let Some(t) = find(&r.step.index, c, &mut p) {
                found = Some((t, p));
                shape.get_or_insert_with(|| r.step.index.clone());
                break;
            }
        }
        let Some((t, p)) = found else {
            fail(&format!(
                "--obs: no rule's left-hand side shows the cell <{c}>"
            ))
        };
        pats.push((t, String::new()));
        paths.push(p);
    }
    // build the pattern: walk the shape, keeping constructors on the paths, `_` elsewhere
    fn pat(l: &L, paths: &[(usize, Vec<usize>)], depth: usize, ns: &str, content: bool) -> String {
        if let Some((i, _)) = paths.iter().find(|(_, p)| p.len() == depth) {
            return match (content, l) {
                (true, L::App(h, _)) => format!("({ns}.{h} x{i})"),
                _ => format!("x{i}"),
            };
        }
        match l {
            L::App(h, a) => {
                let args: Vec<String> = a
                    .iter()
                    .enumerate()
                    .map(|(k, x)| {
                        let sub: Vec<(usize, Vec<usize>)> = paths
                            .iter()
                            .filter(|(_, p)| p.len() > depth && p[depth] == k)
                            .cloned()
                            .collect();
                        if sub.is_empty() {
                            "_".to_string()
                        } else {
                            pat(x, &sub, depth + 1, ns, content)
                        }
                    })
                    .collect();
                format!("({ns}.{h} {})", args.join(" "))
            }
            _ => "_".into(),
        }
    }
    let shape = shape.unwrap();
    let indexed: Vec<(usize, Vec<usize>)> = paths.into_iter().enumerate().collect();
    let p = pat(&shape, &indexed, 0, name, content.is_some());
    let tys: Vec<String> = match content {
        Some(t) => vec![format!("{name}.{t}"); cells.len()],
        None => pats.iter().map(|(t, _)| format!("{name}.{t}")).collect(),
    };
    let xs: Vec<String> = (0..cells.len()).map(|i| format!("x{i}")).collect();
    let (ty, val) = if cells.len() == 1 {
        (tys[0].clone(), xs[0].clone())
    } else {
        (tys.join(" × "), format!("({})", xs.join(", ")))
    };
    let cells_doc: Vec<String> = cells.iter().map(|c| format!("`<{c}>`")).collect();
    format!(
        "/-- The projection to the cell{} {}. -/\ndef {def} : {name}.{} → {ty}\n  | {p} => {val}\n",
        if cells.len() == 1 { "" } else { "s" },
        cells_doc.join(", "),
        lib.top
    )
}

fn intro(xs: &[String]) -> String {
    if xs.is_empty() {
        String::new()
    } else {
        format!("  intro {}\n", xs.join(" "))
    }
}

/// The views' module under a program hypothesis `inv` (`--assume-invariant`): each premise holds
/// at the configurations satisfying `inv`, `joins_of` and `join_static` take it, and
/// `terminal_unique_of` (and `obs_confluent_of`) hold from a configuration satisfying it, by
/// `terminal_unique_of_diamond` with `H := inv` and its preservation `pres`.
fn under_invariant(o: &str, name: &str, inv: &str, pres: &str, module: &str) -> String {
    fn sub(o: &mut String, a: &str, b: &str, all: bool) {
        let n = o.matches(a).count();
        assert!(
            n == 1 || (all && n > 0),
            "confluence --assume-invariant: `{a}` found {n} times in the views"
        );
        *o = o.replace(a, b);
    }
    let mut o = o.to_string();
    sub(
        &mut o,
        &format!("import {name}.Preserves\n"),
        &format!("import {name}.Preserves\nimport {module}\n"),
        false,
    );
    // the premises: `inv c →` after the configuration's binder
    for (a, b) in [
        (
            "}, StepBy r₁ c c₁ → StepBy r₂ c c₂ →\n    DiamondMod",
            format!("}}, {inv} c → StepBy r₁ c c₁ → StepBy r₂ c c₂ →\n    DiamondMod"),
        ),
        (
            "{a₁ b₁ ch₁ bs₁ a₂ b₂ ch₂ bs₂ k}, StepBy r₁ c c₁",
            format!("{{a₁ b₁ ch₁ bs₁ a₂ b₂ ch₂ bs₂ k}}, {inv} c → StepBy r₁ c c₁"),
        ),
    ] {
        sub(&mut o, a, &b, false);
    }
    if o.contains("def KeyJoins") {
        sub(
            &mut o,
            "{ch₁ ch₂}, StepBy r₁ c c₁",
            &format!("{{ch₁ ch₂}}, {inv} c → StepBy r₁ c c₁"),
            false,
        );
        sub(
            &mut o,
            "exact K r₁ r₂ hr b₁ b₂",
            "exact K r₁ r₂ hr hinv b₁ b₂",
            true,
        );
    }
    // the generic joins take it, to pass it to the premises
    sub(
        &mut o,
        "(hs : staticOK r₁ r₂ = true)",
        &format!("(hinv : {inv} c) (hs : staticOK r₁ r₂ = true)"),
        false,
    );
    sub(
        &mut o,
        "refine S r₁ r₂ hk₁ hk₂ hr hd b₁",
        "refine S r₁ r₂ hk₁ hk₂ hr hd hinv b₁",
        true,
    );
    sub(
        &mut o,
        &format!("(h₁ : {name}.Step c c₁)\n    (h₂ : {name}.Step c c₂) : DiamondMod"),
        &format!(
            "(hinv : {inv} c)\n    (h₁ : {name}.Step c c₁) (h₂ : {name}.Step c c₂) : DiamondMod"
        ),
        false,
    );
    sub(
        &mut o,
        "exact O r₁ r₂ hs v₁",
        "exact O r₁ r₂ hs hinv v₁",
        false,
    );
    sub(&mut o, " hs v₁ v₂", " hinv hs v₁ v₂", false);
    // the theorems: from a configuration satisfying it
    sub(
        &mut o,
        "    (h₁ : Star ",
        &format!("    (hinv : {inv} c) (h₁ : Star "),
        true,
    );
    sub(
        &mut o,
        "terminal_unique_of_diamond (H := fun _ => True) StepEquiv.eq (fun _ _ _ _ => trivial)",
        &format!("terminal_unique_of_diamond (H := {inv}) StepEquiv.eq {pres}"),
        false,
    );
    sub(
        &mut o,
        "(fun _ h₁ h₂ => joins_of",
        "(fun hinv h₁ h₂ => joins_of",
        false,
    );
    sub(
        &mut o,
        " h₁ h₂) trivial h₁ t₁ h₂ t₂",
        " hinv h₁ h₂) hinv h₁ t₁ h₂ t₂",
        false,
    );
    if o.contains("theorem obs_confluent_of") {
        sub(&mut o, " h₁ t₁ h₂ t₂)", " hinv h₁ t₁ h₂ t₂)", false);
    }
    o
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
    let lib = load(&get("kore"));
    let name = get("name");
    let report_only = opt.get("report-only").is_some_and(|v| v == "true");
    let local = match opt.get("join").map(|s| s.as_str()) {
        None | Some("diamond") => false,
        Some("local") => true,
        Some(o) => fail(&format!("--join {o}: expected diamond or local")),
    };
    let rs = &lib.rules;
    let rank = |r: &Rule| lib.prios.iter().position(|p| *p == r.priority).unwrap_or(0);
    // the classes of the unordered pairs, two free-key matches taken as one binding
    let same = crate::pairs::classify_same_rank(&lib.def, &lib.m, rs, &rank, true);
    let roles: Vec<MapRole> = rs.iter().map(map_role).collect();
    let feet: Vec<_> = rs.iter().map(footprint).collect();
    let maps: Vec<BTreeSet<String>> = rs.iter().map(map_cells).collect();
    // the report
    let mut by_class: BTreeMap<String, usize> = BTreeMap::new();
    let mut distinct: BTreeMap<String, usize> = BTreeMap::new();
    let mut races: BTreeMap<String, usize> = BTreeMap::new();
    let mut critical: Vec<String> = vec![];
    let n = rs.len();
    for i in 0..n {
        for j in i..n {
            if rank(&rs[i]) != rank(&rs[j]) {
                *by_class.entry("priority".into()).or_default() += 1;
                continue;
            }
            // one binding (or no free-key match)
            if i != j {
                let o = &same[&(i, j)];
                // an overlap of rules that write disjoint cells commutes
                let c = conflicts(&feet[i], &feet[j], &BTreeSet::new());
                let class = match o.class.as_str() {
                    "overlap" if c.is_empty() => "overlap-independent".to_string(),
                    "overlap" => "overlap-conflict".to_string(),
                    x => x.to_string(),
                };
                *by_class.entry(class.clone()).or_default() += 1;
                if class == "overlap-conflict" {
                    critical.push(format!(
                        "{} | {} (one binding: {}; cells {})",
                        rules::display_name(&rs[i]),
                        rules::display_name(&rs[j]),
                        o.detail,
                        c.join(", ")
                    ));
                }
            }
            // two bindings of one cell map
            let shared: BTreeSet<String> = maps[i].intersection(&maps[j]).cloned().collect();
            if rs[i].multi && rs[j].multi && !shared.is_empty() {
                let c = conflicts(&feet[i], &feet[j], &shared);
                let both_update = matches!(roles[i], MapRole::Update { .. })
                    && matches!(roles[j], MapRole::Update { .. });
                let class = if !both_update {
                    "map-structure"
                } else if c.is_empty() {
                    "independent"
                } else {
                    "conflict"
                };
                *distinct.entry(class.into()).or_default() += 1;
                for x in &c {
                    *races.entry(x.clone()).or_default() += 1;
                }
                if class != "independent" {
                    critical.push(format!(
                        "{} | {} (two bindings: {})",
                        rules::display_name(&rs[i]),
                        rules::display_name(&rs[j]),
                        if c.is_empty() {
                            "the map's bindings change".to_string()
                        } else {
                            c.join(", ")
                        }
                    ));
                }
            }
        }
    }
    let mut rep = format!(
        "# k2lean confluence: the pairs of rules of {name}\n\nrules = {n}\nmulti = {}\nranks = {}\nunordered_pairs = {}\ncritical = {}\n\n[one_binding]\n",
        rs.iter().filter(|r| r.multi).count(),
        if lib.ranked {
            lib.prios.len().max(1)
        } else {
            1
        },
        n * (n + 1) / 2,
        critical.len()
    );
    for (k, v) in &by_class {
        writeln!(rep, "{k} = {v}").unwrap();
    }
    writeln!(rep, "\n[two_bindings]").unwrap();
    for (k, v) in &distinct {
        writeln!(rep, "{k} = {v}").unwrap();
    }
    writeln!(
        rep,
        "\n[races]  # pairs at two bindings that both touch the cell, one writing"
    )
    .unwrap();
    for (k, v) in &races {
        writeln!(rep, "{:?} = {v}", k).unwrap();
    }
    writeln!(rep, "\n[critical]\npairs = [").unwrap();
    for c in &critical {
        writeln!(rep, "  {c:?},").unwrap();
    }
    writeln!(rep, "]").unwrap();
    if report_only {
        if let Some(p) = opt.get("report") {
            write_file(p, &rep);
        }
        eprintln!(
            "confluence: {n} rules, {} unordered pairs, {} critical (report only)",
            n * (n + 1) / 2,
            critical.len()
        );
        return;
    }
    if let Some(threads) = opt.get("threads") {
        // the per-pair options that the views do not take yet (PLAN4: CNF-11); the program
        // hypothesis is `--assume-invariant`
        for k in ["hyp", "hand-module", "join", "open"] {
            if opt.contains_key(k) {
                fail(&format!("--threads does not take --{k} yet"));
            }
        }
        let ns = get("ns");
        let obs: Option<Vec<String>> = opt
            .get("obs")
            .map(|o| o.split(',').map(|s| s.to_string()).collect());
        let (mut out, counts) = views::emit(
            &lib,
            &name,
            &ns,
            threads,
            obs.as_deref(),
            &roles,
            &feet,
            &rank,
        );
        // a program hypothesis: a preserved invariant, as `claims --assume-invariant` takes one
        if let Some(inv) = opt.get("assume-invariant") {
            let pres = opt
                .get("invariant-preserved")
                .cloned()
                .unwrap_or(format!("{inv}.preserved"));
            let module = opt
                .get("invariant-module")
                .cloned()
                .unwrap_or(format!("{name}.Invariants"));
            out = under_invariant(&out, &name, inv, &pres, &module);
        } else if opt.contains_key("invariant-preserved") || opt.contains_key("invariant-module") {
            fail("--invariant-preserved and --invariant-module need --assume-invariant");
        }
        write_file(&get("out"), &out);
        if let Some(p) = opt.get("report") {
            write_file(p, &(rep + &counts.report()));
        }
        eprintln!(
            "confluence: {} rules by threads, {} pairs left open, {} same-thread pairs{}",
            counts.rules,
            counts.open_global + counts.open_cells + counts.open_priority + counts.open_insert,
            counts.same_thread,
            counts
                .key_joins
                .map_or(String::new(), |k| format!(", {k} in KeyJoins"))
        );
        return;
    }
    if lib.ranked && lib.prios.len() > 1 {
        fail("the Lean scaffold supports definitions without priority ranks (use --report-only)");
    }
    let ns = get("ns");
    let hand = opt
        .get("hand-module")
        .cloned()
        .unwrap_or(format!("{ns}.Hand"));
    let h = opt.get("hyp").cloned().unwrap_or("H".into());
    let open: BTreeSet<(String, String)> = match opt.get("open") {
        Some(p) => std::fs::read_to_string(p)
            .unwrap_or_else(|e| fail(&format!("{p}: {e}")))
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .map(|l| match l.split_once(" | ") {
                Some((a, b)) => (a.trim().to_string(), b.trim().to_string()),
                None => fail(&format!("{p}: `{l}` is not `RULE | RULE`")),
            })
            .collect(),
        None => BTreeSet::new(),
    };
    let names: BTreeSet<String> = rs.iter().map(rules::display_name).collect();
    for (a, b) in &open {
        if !names.contains(a) || !names.contains(b) {
            fail(&format!("open pair {a} | {b}: no such rule"));
        }
    }
    let cells: Vec<String> = get("obs").split(',').map(|s| s.to_string()).collect();
    let (j, refl, step) = if local {
        ("JoinMod", ".refl _", "Star.single")
    } else {
        ("DiamondMod", "Or.inl rfl", "Or.inr")
    };
    let top = format!("{name}.{}", lib.top);
    let mut o = String::new();
    writeln!(o, "import {hand}\nimport KPrelude.Tactic\n").unwrap();
    writeln!(
        o,
        "/-! Generated by `k2lean confluence`; do not edit.\n\n\
Under the hypothesis `{h}` of `{hand}`, every two runs of `{name}.Step` from one configuration that\n\
end in terminal configurations end in the same one, so in particular they observe the same\n\
`obs`. One obligation per ordered pair of rules (`pair.r₁.r₂`, {} of them): the successors of two\n\
instances of the rules at one configuration {}. The pairs the generic arguments do not close\n\
are the hand module's (`hand.pair.r₁.r₂`). -/\n",
        n * n,
        if local {
            "join (`JoinMod`; with the measure `μ` of the hand module, Newman's lemma)"
        } else {
            "join in at most one step each (`DiamondMod`)"
        }
    )
    .unwrap();
    writeln!(o, "set_option maxHeartbeats 0\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n").unwrap();
    o.push_str(&proj_def(&lib, &name, "obs", &cells, None));
    o.push('\n');
    let args_of = |r: &Rule| rules::ctor_args(&r.step);
    let mut guard = vec![];
    let mut counts = (0usize, 0usize);
    let mut hand_pairs = vec![];
    for (i, r1) in rs.iter().enumerate() {
        let a1 = args_of(r1);
        let taken: BTreeSet<&String> = a1.iter().collect();
        for (k, r2) in rs.iter().enumerate() {
            let mut suf = "_r".to_string();
            while args_of(r2)
                .iter()
                .any(|x| taken.contains(&format!("{x}{suf}")))
            {
                suf.push('\'');
            }
            let a2: Vec<String> = args_of(r2).iter().map(|x| format!("{x}{suf}")).collect();
            let hyps1: Vec<(String, String)> = r1
                .step
                .hyps
                .iter()
                .map(|(x, _)| (x.clone(), x.clone()))
                .collect();
            let hyps2: Vec<(String, String)> = r2
                .step
                .hyps
                .iter()
                .map(|(x, _)| (x.clone(), format!("{x}{suf}")))
                .collect();
            let (l1, l2) = (&r1.lean, &r2.lean);
            let ty = format!(
                "{name}.Step.Rel.{l1} (fun c c₁ => {name}.Step.Rel.{l2} (fun c' c₂ => c' = c → {h} c → {j} {name}.Step Eq c₁ c₂))"
            );
            let mut xs = a1.clone();
            xs.extend(a2.iter().cloned());
            xs.extend(["hc".to_string(), "hH".to_string()]);
            writeln!(
                o,
                "theorem pair.{l1}.{l2} :\n    {ty} := by\n{}",
                intro(&xs)
            )
            .unwrap();
            let listed = open.contains(&(rules::display_name(r1), rules::display_name(r2)));
            if listed {
                counts.1 += 1;
                hand_pairs.push(format!(
                    "{} | {}",
                    rules::display_name(r1),
                    rules::display_name(r2)
                ));
                writeln!(o, "  exact hand.pair.{l1}.{l2} {}\n", xs.join(" ")).unwrap();
                guard.push(format!("pair.{l1}.{l2}"));
                continue;
            }
            counts.0 += 1;
            // a step of `r` with the hypotheses `named` (constructor binder := value)
            let ctor = |r: &Rule, named: &[(String, String)]| {
                let mut s = format!("{name}.Step.{}", r.lean);
                for (b, v) in named {
                    write!(s, " ({b} := {v})").unwrap();
                }
                s.push_str(" ..");
                format!("{step} ({s})")
            };
            let replace = |hs: &[(String, String)], with: &[(&String, String)]| {
                hs.iter()
                    .map(|(b, v)| {
                        with.iter()
                            .find(|(x, _)| *x == b)
                            .map(|(x, w)| ((*x).clone(), w.clone()))
                            .unwrap_or((b.clone(), v.clone()))
                    })
                    .collect::<Vec<_>>()
            };
            let mut alts = vec![format!("exact ⟨_, _, {refl}, {refl}, rfl⟩")];
            if i == k {
                // one instance: its right-hand-side hypotheses determine the same values
                let lhs_hyps: BTreeSet<&String> = r1.app.hyps.iter().map(|(x, _)| x).collect();
                let unify: Vec<String> = r1
                    .step
                    .hyps
                    .iter()
                    .filter(|(x, p)| !lhs_hyps.contains(x) && p.contains("= some "))
                    .map(|(x, _)| format!("cases {x}.symm.trans {x}{suf}"))
                    .collect();
                if !unify.is_empty() {
                    alts.push(format!(
                        "({}; exact ⟨_, _, {refl}, {refl}, rfl⟩)",
                        unify.join("; ")
                    ));
                }
            }
            let sfx = |x: &String| format!("{x}{suf}");
            match (&roles[i], &roles[k]) {
                (MapRole::Update { hm, hr }, MapRole::Update { hm: hm2, hr: hr2 }) => {
                    let s2 = replace(&hyps2, &[(hm2, "a₁".into()), (hr2, "a₂".into())]);
                    let s1 = replace(&hyps1, &[(hm, "a₃".into()), (hr, "a₄".into())]);
                    alts.push(format!(
                        "(rcases MapHook.concat_element_same_or_comm {hm} {} {hr} {} with ⟨hk, hv, hR⟩ | ⟨R₁₂, R₂₁, m', a₁, a₂, a₃, a₄⟩\n       · cases hk; cases hv; cases hR; cases {hr}.symm.trans {}\n         first | exact ⟨_, _, {refl}, {refl}, rfl⟩ | (exfalso; simp_all) | omega\n       · exact ⟨_, _, {}, {}, by k2l_join_eq⟩)",
                        sfx(hm2),
                        sfx(hr2),
                        sfx(hr2),
                        ctor(r2, &s2),
                        ctor(r1, &s1)
                    ));
                }
                (MapRole::Update { hm, hr }, MapRole::Insert { hr: hr2 }) => {
                    let s2 = replace(&hyps2, &[(hr2, "a₃".into())]);
                    let s1 = replace(&hyps1, &[(hm, "a₁".into()), (hr, "a₂".into())]);
                    alts.push(format!(
                        "(obtain ⟨R₂₁, m', a₁, a₂, a₃⟩ := MapHook.concat_element_comm_insert {hm} {hr} {}\n       exact ⟨_, _, {}, {}, by k2l_join_eq⟩)",
                        sfx(hr2),
                        ctor(r2, &s2),
                        ctor(r1, &s1)
                    ));
                }
                (MapRole::Insert { hr }, MapRole::Update { hm: hm2, hr: hr2 }) => {
                    let s2 = replace(&hyps2, &[(hm2, "a₁".into()), (hr2, "a₂".into())]);
                    let s1 = replace(&hyps1, &[(hr, "a₃".into())]);
                    alts.push(format!(
                        "(obtain ⟨R₂₁, m', a₁, a₂, a₃⟩ := MapHook.concat_element_comm_insert {} {} {hr}\n       exact ⟨_, _, {}, {}, by k2l_join_eq⟩)",
                        sfx(hm2),
                        sfx(hr2),
                        ctor(r2, &s2),
                        ctor(r1, &s1)
                    ));
                }
                _ => {}
            }
            alts.push(format!(
                "exact ⟨_, _, {}, {}, by k2l_join_eq⟩",
                ctor(r2, &hyps2),
                ctor(r1, &hyps1)
            ));
            writeln!(o, "  cases hc\n  all_goals first").unwrap();
            for a in &alts {
                writeln!(o, "    | {a}").unwrap();
            }
            writeln!(o).unwrap();
            guard.push(format!("pair.{l1}.{l2}"));
        }
    }
    // assembly
    writeln!(o, "/-! ## Every two steps from one configuration join -/\n").unwrap();
    for r1 in rs {
        let l1 = &r1.lean;
        let a1 = args_of(r1);
        let mut xs = a1.clone();
        xs.extend(["c₂".to_string(), "h₂".to_string()]);
        let parts: Vec<String> = rs
            .iter()
            .map(|r2| format!("(pair.{l1}.{} {})", r2.lean, a1.join(" ")))
            .collect();
        writeln!(
            o,
            "theorem left.{l1} :\n    {name}.Step.Rel.{l1} (fun c c₁ => ∀ c₂, {name}.Step c c₂ → {h} c → {j} {name}.Step Eq c₁ c₂) := by\n{}  exact {name}.Step.rel_of {} h₂ rfl\n",
            intro(&xs),
            parts.join(" ")
        )
        .unwrap();
    }
    let lefts: Vec<String> = rs.iter().map(|r| format!("left.{}", r.lean)).collect();
    writeln!(
        o,
        "theorem joins {{c c₁ c₂ : {top}}} (hH : {h} c) (h₁ : {name}.Step c c₁) (h₂ : {name}.Step c c₂) :\n    {j} {name}.Step Eq c₁ c₂ :=\n  {name}.Step.rel_of {} h₁ c₂ h₂ hH\n",
        lefts.join(" ")
    )
    .unwrap();
    let uniq = if local {
        format!("terminal_unique_of_local StepEquiv.eq {h}.preserved μ μ_dec joins")
    } else {
        format!("terminal_unique_of_diamond StepEquiv.eq {h}.preserved joins")
    };
    writeln!(
        o,
        "/-- Two runs from a configuration satisfying `{h}` that end in terminal configurations end in the same one. -/\n\
theorem terminal_unique {{c n₁ n₂ : {top}}} (hc : {h} c) (h₁ : Star {name}.Step c n₁) (t₁ : Terminal {name}.Step n₁)\n    (h₂ : Star {name}.Step c n₂) (t₂ : Terminal {name}.Step n₂) : n₁ = n₂ :=\n  {uniq} hc h₁ t₁ h₂ t₂\n\n\
/-- The observation is determined: whatever the schedule, a terminal configuration observes the same `obs`. -/\n\
theorem obs_confluent {{c n₁ n₂ : {top}}} (hc : {h} c) (h₁ : Star {name}.Step c n₁) (t₁ : Terminal {name}.Step n₁)\n    (h₂ : Star {name}.Step c n₂) (t₂ : Terminal {name}.Step n₂) : obs n₁ = obs n₂ :=\n  congrArg obs (terminal_unique hc h₁ t₁ h₂ t₂)\n"
    )
    .unwrap();
    guard.extend([
        "joins".into(),
        "terminal_unique".into(),
        "obs_confluent".into(),
    ]);
    writeln!(o, "#k2l_assert_axioms {}\n\nend {ns}", guard.join(" ")).unwrap();
    write_file(&get("out"), &o);
    writeln!(
        rep,
        "\n[lean]\nordered_pairs = {}\ngenerated = {}\nhand = {}\nhand_pairs = {hand_pairs:?}",
        n * n,
        counts.0,
        counts.1
    )
    .unwrap();
    if let Some(p) = opt.get("report") {
        write_file(p, &rep);
    }
    eprintln!(
        "confluence: {n} rules, {} ordered pairs, {} generated, {} by hand; {} critical unordered pairs",
        n * n,
        counts.0,
        counts.1,
        critical.len()
    );
}

/// `--threads CELL`: the joins of a definition whose threads are the bindings of a cell map
/// (SIMPLE's `<threads>`), proved through one view per rule instead of one obligation per pair
/// (`k2lean/docs/design.md`, §3.6).
mod views {
    use super::{Lib, MapRole};
    use crate::model::Model;
    use crate::names;
    use crate::rules::{self, Rule};
    use std::collections::{BTreeMap, BTreeSet};
    use std::fmt::Write as _;

    /// The parts of a thread rule's frame proof that depend on its `VRole`: what comes before the
    /// view (`pre`), the proofs of `a R = m` and `b R = r`, of `KeysIn b a` when it inserts nothing,
    /// the bindings' pattern, the names the replay introduces, what it does with them before the
    /// rule applies, and the rule's hypotheses it restates.
    type Frame = (
        String,
        String,
        String,
        &'static str,
        &'static str,
        String,
        Vec<(String, String)>,
    );

    /// A leaf cell of the configuration: its label, its sort, and its field name.
    pub(super) struct Leaf {
        pub label: String,
        pub sort: String,
        pub field: String,
    }

    fn is_cell_sort(m: &Model, s: &str) -> Option<String> {
        let info = m.sorts.get(s)?;
        let [c] = info.own.as_slice() else {
            return None;
        };
        let k = &m.ctors[c].klabel;
        (k.starts_with('<') && k.ends_with('>')).then(|| c.clone())
    }

    /// The Lean term of the top cell, given the term at each leaf.
    pub(super) type TopTerm = Box<dyn Fn(&dyn Fn(usize) -> String) -> String>;

    /// The configuration's cells: the leaves under nested cells, in order, and the Lean term of
    /// the top cell with `leaf(i)` at each leaf.
    pub(super) fn tree(lib: &Lib, name: &str) -> (Vec<Leaf>, TopTerm) {
        enum Node {
            Inner(String, Vec<Node>),
            Leaf(usize),
        }
        fn walk(m: &Model, s: &str, leaves: &mut Vec<Leaf>, name: &str) -> Node {
            let c =
                is_cell_sort(m, s).unwrap_or_else(|| super::fail(&format!("{s} is not a cell")));
            let args = m.ctors[&c].args.clone();
            if !args.is_empty() && args.iter().all(|a| is_cell_sort(m, a).is_some()) {
                Node::Inner(
                    format!("{name}.{}", m.ctor_path(&c)),
                    args.iter().map(|a| walk(m, a, leaves, name)).collect(),
                )
            } else {
                let label = m.ctors[&c]
                    .klabel
                    .trim_start_matches('<')
                    .trim_end_matches('>')
                    .to_string();
                leaves.push(Leaf {
                    field: names::ident(&label.replace('-', "_")),
                    label,
                    sort: s.to_string(),
                });
                Node::Leaf(leaves.len() - 1)
            }
        }
        let mut leaves = vec![];
        let root = walk(&lib.m, &lib.top, &mut leaves, name);
        fn render(n: &Node, f: &dyn Fn(usize) -> String) -> String {
            match n {
                Node::Leaf(i) => f(*i),
                Node::Inner(c, a) => {
                    let xs: Vec<String> = a.iter().map(|x| render(x, f)).collect();
                    format!("({c} {})", xs.join(" "))
                }
            }
        }
        (leaves, Box::new(move |f| render(&root, f)))
    }

    /// How a rule touches a shared cell.
    #[derive(Clone, Copy, PartialEq, Debug)]
    pub(super) enum Touch {
        None,
        Read,
        Write,
        /// At some bindings of a map (`MCh`), for a cell every rule touches so.
        Keyed,
    }

    impl Touch {
        /// The touch constrains the change in `InClass` (none, or a read).
        fn in_class(self) -> bool {
            matches!(self, Touch::None | Touch::Read)
        }
    }

    /// A key pattern, as `KPrelude.KeyPat`.
    #[derive(Clone, PartialEq)]
    pub(super) enum KeyP {
        Any,
        Dotk,
        /// The first item: injection, constructor, whether it is a `KResult`.
        Item(Option<String>, Option<String>, Option<bool>),
        /// The first two items (a cooling rule: the value, then its freezer).
        Item2(
            Option<String>,
            Option<String>,
            Option<bool>,
            Option<String>,
            Option<String>,
        ),
    }

    fn optb_lean(x: &Option<bool>) -> String {
        x.map(|b| format!("(some {b})")).unwrap_or("none".into())
    }

    /// `KeyPat.conf1`: `conf`, or opposite `KResult` flags.
    fn conf1(
        (i1, o1, r1): (&Option<String>, &Option<String>, &Option<bool>),
        (i2, o2, r2): (&Option<String>, &Option<String>, &Option<bool>),
    ) -> bool {
        conf(i1, o1, i2, o2) || matches!((r1, r2), (Some(a), Some(b)) if a != b)
    }

    fn opt_lean(x: &Option<String>) -> String {
        x.as_ref()
            .map(|x| format!("(some {x:?})"))
            .unwrap_or("none".into())
    }

    /// `KeyPat.conf`: no item has both descriptions.
    fn conf(
        i1: &Option<String>,
        o1: &Option<String>,
        i2: &Option<String>,
        o2: &Option<String>,
    ) -> bool {
        match (i1, i2) {
            (Some(a), Some(b)) => a != b || matches!((o1, o2), (Some(x), Some(y)) if x != y),
            _ => false,
        }
    }

    impl KeyP {
        fn lean(&self) -> String {
            match self {
                KeyP::Any => "KeyPat.any".into(),
                KeyP::Dotk => "KeyPat.dotk".into(),
                KeyP::Item(i, o, r) => format!(
                    "KeyPat.item {} {} {}",
                    opt_lean(i),
                    opt_lean(o),
                    optb_lean(r)
                ),
                KeyP::Item2(i, o, r, j, p) => format!(
                    "KeyPat.item2 {} {} {} {} {}",
                    opt_lean(i),
                    opt_lean(o),
                    optb_lean(r),
                    opt_lean(j),
                    opt_lean(p)
                ),
            }
        }
        /// `KeyPat.disj`.
        fn disj(&self, other: &KeyP) -> bool {
            match (self, other) {
                (KeyP::Dotk, KeyP::Item(..) | KeyP::Item2(..))
                | (KeyP::Item(..) | KeyP::Item2(..), KeyP::Dotk) => true,
                (KeyP::Item(i1, o1, r1), KeyP::Item(i2, o2, r2))
                | (KeyP::Item(i1, o1, r1), KeyP::Item2(i2, o2, r2, _, _))
                | (KeyP::Item2(i1, o1, r1, _, _), KeyP::Item(i2, o2, r2)) => {
                    conf1((i1, o1, r1), (i2, o2, r2))
                }
                (KeyP::Item2(i1, o1, r1, j1, p1), KeyP::Item2(i2, o2, r2, j2, p2)) => {
                    conf1((i1, o1, r1), (i2, o2, r2)) || conf(j1, p1, j2, p2)
                }
                _ => false,
            }
        }
    }

    /// The key of a thread rule, read off its map hypothesis: the first item of the thread's `<k>`
    /// (its injection, and the constructor under it when known, and then whether it is a `KResult`:
    /// `kres_of` the injected sort), or, when the first item is a variable (a cooling rule's value),
    /// the first two, with the first a `KResult` when the rule requires it (`kres_req`).
    fn key_pat(hyp: &str, kres_of: &dyn Fn(&str) -> Option<bool>, kres_req: bool) -> KeyP {
        let Some(i) = hyp.find("«<k>» ") else {
            return KeyP::Any;
        };
        let rest = &hyp[i + "«<k>» ".len()..];
        if rest.starts_with("SortK.dotk") {
            return KeyP::Dotk;
        }
        let Some(rest) = rest.strip_prefix("(SortK.kseq ") else {
            return KeyP::Any;
        };
        let n1 = term_end(rest);
        let (i1, o1) = item_pat(&rest[..n1]);
        if let Some(inj) = &i1 {
            let r = o1.as_ref().and_then(|_| kres_of(inj));
            return KeyP::Item(i1, o1, r);
        }
        let Some(rest) = rest[n1..].strip_prefix(" (SortK.kseq ") else {
            return KeyP::Any;
        };
        let (i2, o2) = item_pat(&rest[..term_end(rest)]);
        if i2.is_none() {
            return KeyP::Any;
        }
        KeyP::Item2(None, None, kres_req.then_some(true), i2, o2)
    }

    /// The length of the first term of `s`: a parenthesized application, or a name (`«…»` quoted
    /// names may hold parentheses and spaces).
    fn term_end(s: &str) -> usize {
        let (mut depth, mut quoted) = (0i32, false);
        for (k, ch) in s.char_indices() {
            match ch {
                '«' => quoted = true,
                '»' => quoted = false,
                _ if quoted => {}
                '(' => depth += 1,
                ')' if depth == 0 => return k,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        return k + 1;
                    }
                }
                ' ' if depth == 0 => return k,
                _ => {}
            }
        }
        s.len()
    }

    /// The injection into `KItem` of an item of `<k>` and the constructor of the injected value,
    /// each when the item's text fixes it (`(SortKItem.inj_Exp (SortExp.Own.«_+_» …))`, `(SortKItem.inj_KItem
    /// SortKItem.Own.«#freezer…»)`); nothing for a variable.
    fn item_pat(item: &str) -> (Option<String>, Option<String>) {
        let Some(rest) = item.strip_prefix('(') else {
            return (None, None);
        };
        let head: String = rest
            .chars()
            .take_while(|c| *c != ' ' && *c != ')')
            .collect();
        let Some(inj) = head.strip_prefix("SortKItem.") else {
            return (None, None);
        };
        let after = &rest[head.len()..];
        let own = if let Some(r) = after.strip_prefix(" (") {
            let o = own_name(r);
            (!o.is_empty() && !o.chars().next().unwrap().is_lowercase() || r.starts_with("Sort"))
                .then_some(o)
        } else if let Some(r) = after.strip_prefix(' ') {
            // a constant: a constructor without arguments
            r.starts_with("Sort").then(|| own_name(r))
        } else {
            None
        };
        (Some(inj.to_string()), own)
    }

    /// The constructor name heading `r`: `SortExp.Own.«_+_» …` → `«_+_»`, `SortExp.Own.f x` → `f`.
    fn own_name(r: &str) -> String {
        let mut tok = String::new();
        let mut quoted = false;
        for ch in r.chars() {
            if !quoted && (ch == ' ' || ch == ')') {
                break;
            }
            if ch == '«' {
                quoted = true;
            } else if ch == '»' {
                quoted = false;
            }
            tok.push(ch);
        }
        match tok.rfind('«') {
            Some(i) if tok.ends_with('»') => tok[i..].to_string(),
            _ => tok.rsplit('.').next().unwrap_or(&tok).to_string(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit(
        lib: &Lib,
        name: &str,
        ns: &str,
        threads: &str,
        obs: Option<&[String]>,
        roles: &[MapRole],
        feet: &[BTreeMap<String, (bool, bool)>],
        rank: &dyn Fn(&Rule) -> usize,
    ) -> (String, super::Counts) {
        let (leaves, top) = tree(lib, name);
        let ti = leaves
            .iter()
            .position(|l| l.label == threads)
            .unwrap_or_else(|| super::fail(&format!("--threads: no cell <{threads}>")));
        let tcell = &leaves[ti];
        let tctor = is_cell_sort(&lib.m, &tcell.sort).unwrap();
        let tmap = lib.m.ctors[&tctor].args[0].clone();
        let shared: Vec<&Leaf> = leaves
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != ti)
            .map(|(_, l)| l)
            .collect();
        let topt = format!("{name}.{}", lib.top);
        let ty = |s: &str| format!("{name}.{s}");
        // the shared cells holding a map that every rule touching them changes at some bindings
        // only (`super::keyed_role`): per cell, each rule's role
        let keyed: Vec<Option<Vec<Option<super::KRole>>>> = shared
            .iter()
            .map(|l| {
                let roles: Option<Vec<Option<super::KRole>>> = lib
                    .rules
                    .iter()
                    .enumerate()
                    .map(|(ri, r)| {
                        let touched = feet[ri].iter().any(|(k, (rd, wr))| {
                            (k == &l.label || k == l.sort.trim_start_matches("Sort"))
                                && (*rd || *wr)
                        });
                        super::keyed_role(r, &l.label, touched)
                    })
                    .collect();
                roles.filter(|rs| rs.iter().any(|x| x.is_some()))
            })
            .collect();
        let is_keyed = |f: usize| keyed[f].is_some();
        // a keyed cell some rule extends (reads a binding and adds one): its changes are `SmallR`
        let wide = |f: usize| {
            keyed[f].as_ref().is_some_and(|rs| {
                rs.iter()
                    .any(|r| matches!(r, Some(super::KRole::Extend { .. })))
            })
        };
        let any_keyed = keyed.iter().any(|k| k.is_some());
        // a keyed cell's constructor and the map it holds
        let cell_of = |f: usize| -> (String, String) {
            let c = is_cell_sort(&lib.m, &shared[f].sort).unwrap();
            (lib.m.ctor_path(&c), lib.m.ctors[&c].args[0].clone())
        };
        let mut o = String::new();
        writeln!(
            o,
            "import {name}.Preserves\nimport KPrelude.Scaffold\nimport KPrelude.Tactic\n"
        )
        .unwrap();
        writeln!(
            o,
            "/-! Generated by `k2lean confluence --threads {threads}`; do not edit. -/\n"
        )
        .unwrap();
        writeln!(o, "set_option maxHeartbeats 0\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n").unwrap();
        // the shared cells, the configuration from the threads and them, and their changes
        writeln!(
            o,
            "/-- The cells of a configuration other than `<{threads}>`. -/\nstructure Shared where"
        )
        .unwrap();
        for (f, l) in shared.iter().enumerate() {
            // a keyed cell by the map it holds
            let t = if is_keyed(f) {
                cell_of(f).1
            } else {
                l.sort.clone()
            };
            writeln!(o, "  {} : {}", l.field, ty(&t)).unwrap();
        }
        let mk_body = top(&|i| {
            if i == ti {
                return "tc".to_string();
            }
            let f = if i < ti { i } else { i - 1 };
            if is_keyed(f) {
                format!("({name}.{} s.{})", cell_of(f).0, leaves[i].field)
            } else {
                format!("s.{}", leaves[i].field)
            }
        });
        writeln!(o, "\n/-- The configuration of the cell `<{threads}>` `tc` and the shared cells `s`. -/\ndef mkc (tc : {}) (s : Shared) : {topt} :=\n  {mk_body}\n", ty(&tcell.sort)).unwrap();
        writeln!(o, "/-- The configuration of the threads `m` and the shared cells `s`. -/\nabbrev mk (m : {}) (s : Shared) : {topt} := mkc ({name}.{} m) s\n", ty(&tmap), lib.m.ctor_path(&tctor)).unwrap();
        if any_keyed {
            writeln!(o, "/-- A change of the shared cells: per cell, none, or the value it has and the value it gets; for a\ncell holding a map changed at some bindings, none or the bindings and what replaces them. -/\nstructure Change where").unwrap();
        } else {
            writeln!(o, "/-- A change of the shared cells: per cell, none, or the value it has and the value it gets. -/\nstructure Change where").unwrap();
        }
        for (f, l) in shared.iter().enumerate() {
            if is_keyed(f) {
                writeln!(o, "  {} : MCh {} := none", l.field, ty(&cell_of(f).1)).unwrap();
            } else {
                writeln!(o, "  {} : Ch {} := none", l.field, ty(&l.sort)).unwrap();
            }
        }
        // the lemmas of a field's kind of change
        let chn = |f: usize| if is_keyed(f) { "MCh" } else { "Ch" };
        let conj = |f: &dyn Fn(&str) -> String| -> String {
            shared
                .iter()
                .map(|l| f(&l.field))
                .collect::<Vec<_>>()
                .join(" ∧ ")
        };
        let anon = |f: &dyn Fn(&str) -> String| -> String {
            format!(
                "⟨{}⟩",
                shared
                    .iter()
                    .map(|l| f(&l.field))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        // projections of the n-fold conjunction
        let n = shared.len();
        let proj = |h: &str, i: usize| -> String {
            let mut t = h.to_string();
            for _ in 0..i {
                t.push_str(".2");
            }
            if i + 1 < n {
                t.push_str(".1");
            }
            t
        };
        writeln!(
            o,
            "\ndef Change.pre (c : Change) (s : Shared) : Prop :=\n  {}",
            conj(&|f| format!("c.{f}.pre s.{f}"))
        )
        .unwrap();
        writeln!(
            o,
            "{}def Change.apply (c : Change) (s : Shared) : Shared :=\n  {}",
            if any_keyed { "noncomputable " } else { "" },
            anon(&|f| format!("c.{f}.apply s.{f}"))
        )
        .unwrap();
        writeln!(
            o,
            "def Change.Compat (a b : Change) : Prop :=\n  {}",
            conj(&|f| format!("a.{f}.Compat b.{f}"))
        )
        .unwrap();
        if any_keyed {
            let ks: Vec<String> = (0..n)
                .filter(|&f| is_keyed(f))
                .map(|f| format!("a.{0}.Compat b.{0}", shared[f].field))
                .collect();
            writeln!(o, "/-- The changes of the cells holding a map commute at their bindings (`MCh.Compat`). -/\ndef Change.KCompat (a b : Change) : Prop :=\n  {}", ks.join(" ∧ ")).unwrap();
            let sm: Vec<String> = (0..n)
                .filter(|&f| is_keyed(f))
                .map(|f| {
                    let r = if wide(f) { "SmallR" } else { "Small" };
                    format!("c.{}.{r}", shared[f].field)
                })
                .collect();
            let doc = if (0..n).any(|f| is_keyed(f) && wide(f)) {
                "at one binding (`MCh.Small`), or a read of\none with one added (`MCh.SmallR`)"
            } else {
                "at one binding (`MCh.Small`)"
            };
            writeln!(o, "/-- The changes of the cells holding a map are a rule's, {doc}. -/\ndef Change.Small (c : Change) : Prop :=\n  {}", sm.join(" ∧ ")).unwrap();
            let nk = ks.len();
            let sy: Vec<String> = (0..nk)
                .map(|i| {
                    let mut t = "h".to_string();
                    if nk > 1 {
                        for _ in 0..i {
                            t.push_str(".2");
                        }
                        if i + 1 < nk {
                            t.push_str(".1");
                        }
                    }
                    format!("MCh.Compat.symm {t}")
                })
                .collect();
            let body = if nk == 1 {
                sy[0].clone()
            } else {
                format!("⟨{}⟩", sy.join(", "))
            };
            writeln!(o, "\ntheorem Change.KCompat.symm {{a b : Change}} (h : a.KCompat b) : b.KCompat a :=\n  {body}").unwrap();
        }
        let pa: Vec<String> = (0..n)
            .map(|i| {
                format!(
                    "{}.pre_apply {} {} {}",
                    chn(i),
                    proj("h", i),
                    proj("ha", i),
                    proj("hb", i)
                )
            })
            .collect();
        writeln!(o, "\ntheorem Change.pre_apply {{a b : Change}} {{s : Shared}} (h : a.Compat b) (ha : a.pre s) (hb : b.pre s) :\n    b.pre (a.apply s) :=\n  ⟨{}⟩", pa.join(",\n    ")).unwrap();
        let sy: Vec<String> = (0..n).map(|i| format!("{}.symm", proj("h", i))).collect();
        writeln!(o, "\ntheorem Change.Compat.symm {{a b : Change}} (h : a.Compat b) : b.Compat a :=\n  ⟨{}⟩", sy.join(", ")).unwrap();
        let ac: Vec<String> = (0..n)
            .map(|i| {
                format!(
                    "{}.apply_comm {} {} {}",
                    chn(i),
                    proj("h", i),
                    proj("ha", i),
                    proj("hb", i)
                )
            })
            .collect();
        writeln!(o, "\ntheorem Change.apply_comm {{a b : Change}} {{s : Shared}} (h : a.Compat b) (ha : a.pre s) (hb : b.pre s) :\n    b.apply (a.apply s) = a.apply (b.apply s) := by\n  simp only [Change.apply, {}]", ac.join(",\n    ")).unwrap();
        // a step of one thread, and its frame
        let els = lib.m.sort(&tmap).elems.clone();
        let (kt, vt) = (ty(&els[0]), ty(&els[1]));
        let mt = ty(&tmap);
        writeln!(o, "\n/-- A step that replaces the bindings `a` of the thread map by `b` (one thread's step: `k ↦ t` by\n`k ↦ t'`; its end: by nothing; a spawn: by `k ↦ t'` and a new binding), keeping the rest `R`, and\nchanges the shared cells by `ch`. -/\ndef MStep (a b : {mt}) (ch : Change) (c c' : {topt}) : Prop :=\n  ∃ m R r s, c = mk m s ∧ MapHook.concat a R = some m ∧ MapHook.concat b R = some r ∧ ch.pre s ∧\n    c' = mk r (ch.apply s)").unwrap();
        writeln!(o, "\n/-- The step is a step of `Step` wherever no rule of a rank before `i` applies. -/\ndef Local (i : Nat) (a b : {mt}) (ch : Change) : Prop :=\n  ∀ d d', MStep a b ch d d' → (∀ j, j < i → ¬ {name}.App j d) → {name}.Step d d'").unwrap();
        // mk is injective
        let svars: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
        let svars2: Vec<String> = (0..n).map(|i| format!("y{i}")).collect();
        let _ = (&svars, &svars2);
        writeln!(o, "\ntheorem mkc_inj {{tc tc' s s'}} (h : mkc tc s = mkc tc' s') : tc = tc' ∧ s = s' := by\n  cases s; cases s'; cases h; exact ⟨rfl, rfl⟩").unwrap();
        writeln!(o, "\ntheorem mk_inj {{m m' s s'}} (h : mk m s = mk m' s') : m = m' ∧ s = s' := by\n  cases s; cases s'; cases h; exact ⟨rfl, rfl⟩").unwrap();
        writeln!(o, "\n/-- Two steps at parts of the thread map with no key in common, one of them inserting no key,
commute. -/\ntheorem mstep_comm {{a₁ b₁ a₂ b₂ ch₁ ch₂}} {{c c₁ c₂ : {topt}}}\n    (h₁ : MStep a₁ b₁ ch₁ c c₁) (h₂ : MStep a₂ b₂ ch₂ c c₂)\n    (dA : ∀ k, MapHook.lookup a₁ k = none ∨ MapHook.lookup a₂ k = none)\n    (dB : MapHook.KeysIn b₁ a₁ ∨ MapHook.KeysIn b₂ a₂) (hc : ch₁.Compat ch₂) :\n    ∃ c₁₂, MStep a₂ b₂ ch₂ c₁ c₁₂ ∧ MStep a₁ b₁ ch₁ c₂ c₁₂ := by\n  obtain ⟨m, R₁, r₁, s, rfl, hm₁, hr₁, hp₁, rfl⟩ := h₁\n  obtain ⟨m₂, R₂, r₂, s₂, he, hm₂, hr₂, hp₂, rfl⟩ := h₂\n  obtain ⟨rfl, rfl⟩ := mk_inj he\n  obtain ⟨R₁₂, R₂₁, m', a₁, a₂, a₃, a₄⟩ := MapHook.concat_frame hm₁ hr₁ hm₂ hr₂ dA dB\n  refine ⟨mk m' (ch₂.apply (ch₁.apply s)), ⟨_, _, _, _, rfl, a₁, a₂, Change.pre_apply hc hp₁ hp₂, rfl⟩,\n    ⟨_, _, _, _, rfl, a₃, a₄, Change.pre_apply hc.symm hp₂ hp₁, ?_⟩⟩\n  rw [Change.apply_comm hc hp₁ hp₂]").unwrap();
        // shared-only steps (the threads unchanged)
        writeln!(o, "\n/-- A step that leaves the threads alone and changes the shared cells by `ch`. -/\ndef SStep (ch : Change) (c c' : {topt}) : Prop :=\n  ∃ tc s, c = mkc tc s ∧ ch.pre s ∧ c' = mkc tc (ch.apply s)").unwrap();
        writeln!(o, "\ndef LocalS (i : Nat) (ch : Change) : Prop :=\n  ∀ d d', SStep ch d d' → (∀ j, j < i → ¬ {name}.App j d) → {name}.Step d d'").unwrap();
        writeln!(o, "\ntheorem mstep_sstep_comm {{a₁ b₁ ch₁ ch₂}} {{c c₁ c₂ : {topt}}}\n    (h₁ : MStep a₁ b₁ ch₁ c c₁) (h₂ : SStep ch₂ c c₂) (hc : ch₁.Compat ch₂) :\n    ∃ c₁₂, SStep ch₂ c₁ c₁₂ ∧ MStep a₁ b₁ ch₁ c₂ c₁₂ := by\n  obtain ⟨m, R₁, r₁, s, rfl, hm₁, hr₁, hp₁, rfl⟩ := h₁\n  obtain ⟨tc₂, s₂, he, hp₂, rfl⟩ := h₂\n  obtain ⟨rfl, rfl⟩ := mkc_inj he\n  refine ⟨mk r₁ (ch₂.apply (ch₁.apply s)), ⟨_, _, rfl, Change.pre_apply hc hp₁ hp₂, rfl⟩,\n    ⟨_, _, _, _, rfl, hm₁, hr₁, Change.pre_apply hc.symm hp₂ hp₁, ?_⟩⟩\n  rw [Change.apply_comm hc hp₁ hp₂]").unwrap();
        writeln!(o, "\ntheorem sstep_comm {{ch₁ ch₂}} {{c c₁ c₂ : {topt}}}\n    (h₁ : SStep ch₁ c c₁) (h₂ : SStep ch₂ c c₂) (hc : ch₁.Compat ch₂) :\n    ∃ c₁₂, SStep ch₂ c₁ c₁₂ ∧ SStep ch₁ c₂ c₁₂ := by\n  obtain ⟨tc, s, rfl, hp₁, rfl⟩ := h₁\n  obtain ⟨tc₂, s₂, he, hp₂, rfl⟩ := h₂\n  obtain ⟨rfl, rfl⟩ := mkc_inj he\n  refine ⟨mkc tc (ch₂.apply (ch₁.apply s)), ⟨_, _, rfl, Change.pre_apply hc hp₁ hp₂, rfl⟩,\n    ⟨_, _, rfl, Change.pre_apply hc.symm hp₂ hp₁, ?_⟩⟩\n  rw [Change.apply_comm hc hp₁ hp₂]").unwrap();
        writeln!(o, "\n/-- Two steps that match one key of the thread map match one thread there. -/\ntheorem mstep_same {{a₁ b₁ a₂ b₂ ch₁ ch₂}} {{c c₁ c₂ : {topt}}} {{bs₁ bs₂ : List ({kt} × {vt})}}\n    (h₁ : MStep a₁ b₁ ch₁ c c₁) (h₂ : MStep a₂ b₂ ch₂ c c₂) (d₁ : MapHook.Binds a₁ bs₁)\n    (d₂ : MapHook.Binds a₂ bs₂) {{p q}} (hp : p ∈ bs₁) (hq : q ∈ bs₂) (e : p.1 = q.1) : p.2 = q.2 := by\n  obtain ⟨m, R₁, r₁, s, rfl, hm₁, -, -, rfl⟩ := h₁\n  obtain ⟨m₂, R₂, r₂, s₂, he, hm₂, -, -, rfl⟩ := h₂\n  obtain ⟨rfl, rfl⟩ := mk_inj he\n  exact MapHook.binds_same hm₁ hm₂ d₁ d₂ hp hq e").unwrap();
        // the key of a thread: its first `<k>` item
        let vctor = is_cell_sort(&lib.m, &els[1]);
        let kpos = vctor.as_ref().and_then(|c| {
            lib.m.ctors[c].args.iter().position(|a| {
                is_cell_sort(&lib.m, a).is_some_and(|kc| lib.m.ctors[&kc].klabel == "<k>")
            })
        });
        let (Some(vc), Some(kpos)) = (vctor, kpos) else {
            super::fail("--threads: the threads are expected to be cells with a <k> cell");
        };
        let kcell = lib.m.ctors[&vc].args[kpos].clone();
        let kctor = is_cell_sort(&lib.m, &kcell).unwrap();
        let kitem = lib.m.sort("SortKItem");
        let mut own_arms = String::new();
        for l in &kitem.leaves {
            let st = lib.m.sort(l);
            let inj = lib.m.leaf_ctor("SortKItem", l);
            let short = inj.rsplit('.').next().unwrap_or(&inj).to_string();
            if l == "SortKItem" && !kitem.own.is_empty() {
                continue;
            }
            if st.own.is_empty() || l == "SortKItem" {
                writeln!(own_arms, "    | .{short} _ => ({:?}, \"\")", short).unwrap();
                continue;
            }
            let mut inner = String::new();
            for c in &st.own {
                let cl = lib.m.ctors[c].lean.clone();
                writeln!(inner, "      | .{cl} .. => {:?}", cl).unwrap();
            }
            writeln!(
                own_arms,
                "    | .{short} x => ({:?}, match x with\n{inner}      )",
                short
            )
            .unwrap();
        }
        // the own constructors of KItem itself (freezers)
        if !kitem.own.is_empty() {
            let mut inner = String::new();
            for c in &kitem.own {
                let cl = lib.m.ctors[c].lean.clone();
                writeln!(inner, "      | .{cl} .. => {:?}", cl).unwrap();
            }
            writeln!(
                own_arms,
                "    | .inj_KItem x => (\"inj_KItem\", match x with\n{inner}      )"
            )
            .unwrap();
        }
        let vargs: Vec<String> = (0..lib.m.ctors[&vc].args.len())
            .map(|i| {
                if i == kpos {
                    "kc".to_string()
                } else {
                    "_".to_string()
                }
            })
            .collect();
        writeln!(o, "\n/-- An item of a thread's `<k>`: its injection into `KItem` and the constructor of the injected\nvalue. -/\ndef kitem (it : {name}.SortKItem) : String × String :=\n        match it with\n{own_arms}").unwrap();
        // without a sort `KResult` no item is one, and the library need not define `isKResult`
        let (it, kres) = if lib.m.sorts.contains_key("SortKResult") {
            ("it", format!("{name}.K.isKResult (.kseq it .dotk)"))
        } else {
            ("_", "false".to_string())
        };
        writeln!(o, "/-- What a key reads of a thread's `<k>` (`KeyView`): its number of items up to 2, and each\nitem (`(\"dotk\", \"\")` past the end). -/\ndef tkey (t : {vt}) : KeyView :=\n  match t with\n  | {name}.{} {} =>\n    match kc with\n    | {name}.{} k =>\n      ⟨match k with | .dotk => 0 | .kseq _ r => (match r with | .dotk => 0 | .kseq _ _ => 1) + 1,\n       fun i => match k with\n         | .dotk => (\"dotk\", \"\")\n         | .kseq it r =>\n           match i with\n           | 0 => kitem it\n           | _ => match r with\n             | .dotk => (\"dotk\", \"\")\n             | .kseq it₂ _ => kitem it₂,\n       match k with | .dotk => false | .kseq {it} _ => {kres}⟩\n",
            lib.m.ctor_path(&vc), vargs.join(" "), lib.m.ctor_path(&kctor)).unwrap();
        // the rules: their kind, rank, class and key
        let field_of = |key: &str| -> Option<usize> {
            shared
                .iter()
                .position(|l| l.label == key || l.sort.trim_start_matches("Sort") == key)
        };
        #[derive(PartialEq, Clone, Copy)]
        enum Kind {
            Thread,
            Shared,
            Global,
        }
        let mut kinds = vec![];
        let mut touches: Vec<Vec<Touch>> = vec![];
        let mut keys: Vec<String> = vec![];
        let mut keyps: Vec<Vec<KeyP>> = vec![];
        let vroles: Vec<Option<super::VRole>> = lib
            .rules
            .iter()
            .zip(roles)
            .map(|(r, ro)| super::view_role(r, ro, threads))
            .collect();
        // whether an item injected by `inj_S` with a constructor of `S` is a `KResult`: `S` is
        // one of `KResult`'s leaves (`None` without a sort `KResult`)
        let kres_leaves: Option<BTreeSet<String>> = lib
            .m
            .sorts
            .contains_key("SortKResult")
            .then(|| lib.m.sort("SortKResult").leaves.iter().cloned().collect());
        let kres_of = |inj: &str| -> Option<bool> {
            let sort = format!("Sort{}", inj.strip_prefix("inj_")?);
            kres_leaves.as_ref().map(|ls| ls.contains(&sort))
        };
        for (ri, r) in lib.rules.iter().enumerate() {
            let mut touch = vec![Touch::None; n];
            let mut unknown = false;
            let mut threads_touched = false;
            for (key, (rd, wr)) in &feet[ri] {
                if key == &tcell.label || key == tcell.sort.trim_start_matches("Sort") {
                    threads_touched = *rd || *wr;
                    continue;
                }
                match field_of(key) {
                    Some(f) => {
                        touch[f] = if *wr {
                            Touch::Write
                        } else if *rd {
                            Touch::Read
                        } else {
                            Touch::None
                        }
                    }
                    None => unknown = true,
                }
            }
            for (f, k) in keyed.iter().enumerate() {
                if let Some(rs) = k {
                    touch[f] = if rs[ri].is_some() {
                        Touch::Keyed
                    } else {
                        Touch::None
                    };
                }
            }
            let kind = match (&vroles[ri], &roles[ri], unknown, threads_touched) {
                (Some(_), _, false, _) => Kind::Thread,
                (None, MapRole::None, false, false) if !r.multi => Kind::Shared,
                _ => Kind::Global,
            };
            kinds.push(kind);
            touches.push(touch);
            // one key per binding the rule matches
            let kps: Vec<KeyP> = match &vroles[ri] {
                Some(vr) if kind == Kind::Thread => {
                    // a cooling rule requires its first item to be a `KResult` (`isKResult`, not
                    // under a negation, as a heating rule's)
                    let kres_req = r.step.hyps.iter().any(|(_, h)| {
                        h.contains("K.isKResult") && !h.contains("BoolHook.not (K.isKResult")
                    });
                    vr.matches()
                        .iter()
                        .map(|hm| {
                            let p = &r.step.hyps.iter().find(|(h, _)| h == *hm).unwrap().1;
                            key_pat(p, &kres_of, kres_req)
                        })
                        .collect()
                }
                _ => vec![],
            };
            keys.push(format!(
                "[{}]",
                kps.iter().map(|k| k.lean()).collect::<Vec<_>>().join(", ")
            ));
            keyps.push(kps);
        }
        // the classes: the distinct ways of touching the shared cells
        let mut classes: Vec<Vec<Touch>> = vec![];
        let cls: Vec<usize> = touches
            .iter()
            .map(|t| {
                if let Some(i) = classes.iter().position(|c| c == t) {
                    i
                } else {
                    classes.push(t.clone());
                    classes.len() - 1
                }
            })
            .collect();
        writeln!(o, "\n/-- The ways a rule touches the shared cells. -/\ninductive Cls where\n  {}\n  deriving DecidableEq", (0..classes.len()).map(|i| format!("| c{i}")).collect::<Vec<_>>().join(" ")).unwrap();
        writeln!(o, "\ndef InClass : Cls → Change → Prop").unwrap();
        for (ci, c) in classes.iter().enumerate() {
            let parts: Vec<String> = (0..n)
                .filter_map(|f| match c[f] {
                    Touch::None => Some(format!("ch.{} = none", shared[f].field)),
                    Touch::Read => Some(format!("(∃ x, ch.{} = some (x, x))", shared[f].field)),
                    Touch::Write | Touch::Keyed => None,
                })
                .collect();
            writeln!(
                o,
                "  | .c{ci}, ch => {}",
                if parts.is_empty() {
                    "True".into()
                } else {
                    parts.join(" ∧ ")
                }
            )
            .unwrap();
        }
        let compat = |a: &[Touch], b: &[Touch]| {
            (0..n).all(|f| {
                a[f] == Touch::None
                    || b[f] == Touch::None
                    || (a[f] == Touch::Read && b[f] == Touch::Read)
                    || (a[f] == Touch::Keyed && b[f] == Touch::Keyed)
            })
        };
        writeln!(o, "\ndef compatTbl : Cls → Cls → Bool").unwrap();
        for (i, a) in classes.iter().enumerate() {
            for (j, b) in classes.iter().enumerate() {
                writeln!(o, "  | .c{i}, .c{j} => {}", compat(a, b)).unwrap();
            }
        }
        // compat_of: by cases on the two classes; each compatible pair field by field
        let idx = |i: usize, k: usize| -> String {
            // the i-th component of an InClass conjunction of k parts
            if k <= 1 {
                return String::new();
            }
            let mut t = String::new();
            for _ in 0..i {
                t.push_str(".2");
            }
            if i + 1 < k {
                t.push_str(".1");
            }
            t
        };
        let mut arms = String::new();
        // with keyed cells, their compatibility at the bindings (`Change.KCompat`) as `hk`
        let hk_arg = if any_keyed { ", _" } else { "" };
        let keyed_fs: Vec<usize> = (0..n).filter(|&f| is_keyed(f)).collect();
        for (i, a) in classes.iter().enumerate() {
            for (j, b) in classes.iter().enumerate() {
                if !compat(a, b) {
                    writeln!(
                        arms,
                        "  | .c{i}, .c{j}, h, _, _, _, _{hk_arg} => by simp [compatTbl] at h"
                    )
                    .unwrap();
                    continue;
                }
                let ka = a.iter().filter(|t| t.in_class()).count();
                let kb = b.iter().filter(|t| t.in_class()).count();
                let pos = |c: &[Touch], f: usize| c[..f].iter().filter(|t| t.in_class()).count();
                let fs: Vec<String> = (0..n)
                    .map(|f| {
                        if a[f] == Touch::Keyed && b[f] == Touch::Keyed {
                            let k = keyed_fs.iter().position(|&g| g == f).unwrap();
                            format!("hk{}", idx(k, keyed_fs.len()))
                        } else if a[f] == Touch::None {
                            format!("Or.inl h₁{}", idx(pos(a, f), ka))
                        } else if b[f] == Touch::None {
                            format!("Or.inr (Or.inl h₂{})", idx(pos(b, f), kb))
                        } else {
                            format!(
                                "Or.inr (Or.inr ⟨h₁{}, h₂{}⟩)",
                                idx(pos(a, f), ka),
                                idx(pos(b, f), kb)
                            )
                        }
                    })
                    .collect();
                let hk = if any_keyed { ", hk" } else { "" };
                writeln!(
                    arms,
                    "  | .c{i}, .c{j}, _, _, _, h₁, h₂{hk} => ⟨{}⟩",
                    fs.join(", ")
                )
                .unwrap();
            }
        }
        let hk_ty = if any_keyed {
            " → ch₁.KCompat ch₂"
        } else {
            ""
        };
        writeln!(o, "\ntheorem compat_of : ∀ (a b : Cls), compatTbl a b = true → ∀ (ch₁ ch₂ : Change),\n    InClass a ch₁ → InClass b ch₂{hk_ty} → ch₁.Compat ch₂\n{arms}").unwrap();
        // priorities: which cells the rules of each rank read, and that a step leaving them alone
        // keeps a rule of that rank from applying where it did not
        let max_rank = lib
            .rules
            .iter()
            .zip(&kinds)
            .filter(|(_, k)| **k != Kind::Global)
            .map(|(r, _)| rank(r))
            .max()
            .unwrap_or(0);
        let mut reads: Vec<Option<Vec<usize>>> = vec![]; // per rank below max_rank: the fields, or None if threads
        for j in 0..max_rank {
            let mut fs: Vec<usize> = vec![];
            let mut threads_read = false;
            for (ri, r) in lib.rules.iter().enumerate() {
                if rank(r) != j {
                    continue;
                }
                if kinds[ri] == Kind::Thread
                    || kinds[ri] == Kind::Global && !matches!(roles[ri], MapRole::None)
                {
                    threads_read = true;
                }
                for (key, (rd, wr)) in &feet[ri] {
                    if key == &tcell.label || key == tcell.sort.trim_start_matches("Sort") {
                        if *rd || *wr {
                            threads_read = true;
                        }
                        continue;
                    }
                    match field_of(key) {
                        Some(f) => {
                            if (*rd || *wr) && !fs.contains(&f) {
                                fs.push(f)
                            }
                        }
                        None => threads_read = true,
                    }
                }
            }
            fs.sort();
            reads.push((!threads_read).then_some(fs));
        }
        let safe_tbl = |j: usize, c: usize| -> bool {
            reads[j]
                .as_ref()
                .is_some_and(|fs| fs.iter().all(|&f| classes[c][f] == Touch::None))
        };
        for (j, r) in reads.iter().enumerate() {
            if r.is_none() {
                writeln!(o, "\n/-- The rules of rank {j} read the threads. -/\ndef appSafe{j} (_ : Cls) : Bool := false").unwrap();
                continue;
            }
            writeln!(o, "\ndef appSafe{j} : Cls → Bool").unwrap();
            for c in 0..classes.len() {
                writeln!(o, "  | .c{c} => {}", safe_tbl(j, c)).unwrap();
            }
        }
        let mut ite = "false".to_string();
        for j in (0..max_rank).rev() {
            ite = format!("if j = {j} then appSafe{j} c else {ite}");
        }
        writeln!(o, "\n/-- A step of the class leaves alone every cell the rules of rank `j` read. -/\ndef appSafe (j : Nat) (c : Cls) : Bool :=\n  {ite}").unwrap();
        let app = |j: &str, c: &str| format!("{name}.App {j} {c}");
        for (j, fs) in reads.iter().enumerate() {
            let Some(fs) = fs else { continue };
            let hyps: Vec<String> = fs
                .iter()
                .map(|&f| format!("ch.{} = none", shared[f].field))
                .collect();
            let hyp = if hyps.is_empty() {
                "True".to_string()
            } else {
                hyps.join(" ∧ ")
            };
            let rules_j: Vec<&Rule> = lib.rules.iter().filter(|r| rank(r) == j).collect();
            let alts: Vec<String> = rules_j
                .iter()
                .map(|r| format!("    | (apply {name}.App.{} <;> assumption)", r.lean))
                .collect();
            let hs: Vec<String> = (0..fs.len()).map(|i| format!("hf{i}")).collect();
            let pat = if hs.is_empty() {
                "-".to_string()
            } else if hs.len() == 1 {
                format!("⟨{}⟩", hs[0])
            } else {
                format!("⟨{}⟩", hs.join(", "))
            };
            for (nm, def) in [
                ("app_back", "MStep a b ch c c'"),
                ("app_back_s", "SStep ch c c'"),
            ] {
                let binders = if nm == "app_back" { "{a b ch}" } else { "{ch}" };
                let (destr, s1) = if nm == "app_back" {
                    ("⟨m, R, r, s, rfl, -, -, -, rfl⟩", "r")
                } else {
                    ("⟨tc, s, rfl, -, rfl⟩", "tc")
                };
                let _ = s1;
                let mut body = if hs.len() == 1 {
                    format!("  have hf0 := hf\n  obtain {destr} := h\n")
                } else {
                    format!("  obtain {pat} := hf\n  obtain {destr} := h\n")
                };
                for (i, &f) in fs.iter().enumerate() {
                    writeln!(body, "  have e{i} : (ch.apply s).{} = s.{} := by simp only [Change.apply, {}.apply, {}]", shared[f].field, shared[f].field, chn(f), hs[i]).unwrap();
                }
                let es: Vec<String> = (0..fs.len()).map(|i| format!("e{i}")).collect();
                writeln!(body, "  generalize ch.apply s = s' at ha{}\n  cases s; cases s'\n  simp only [mk, mkc] at ha{} ⊢", es.iter().map(|e| format!(" {e}")).collect::<String>(), es.iter().map(|e| format!(" {e}")).collect::<String>()).unwrap();
                if !es.is_empty() {
                    writeln!(body, "  subst {}", es.join(" ")).unwrap();
                }
                writeln!(
                    body,
                    "  cases ha\n  all_goals first\n{}",
                    if alts.is_empty() {
                        "    | skip".into()
                    } else {
                        alts.join("\n")
                    }
                )
                .unwrap();
                writeln!(o, "\ntheorem {nm}_{j} {binders} {{c c' : {topt}}} (h : {def}) (hf : {hyp})\n    (ha : {}) : {} := by\n{body}", app(&j.to_string(), "c'"), app(&j.to_string(), "c")).unwrap();
            }
            // the cells, from the class
            let arms: Vec<String> = (0..classes.len())
                .map(|c| {
                    if safe_tbl(j, c) {
                        let parts: Vec<String> = fs
                            .iter()
                            .map(|&f| {
                                let k = classes[c].iter().filter(|t| t.in_class()).count();
                                let pos = classes[c][..f].iter().filter(|t| t.in_class()).count();
                                format!("hc{}", idx(pos, k))
                            })
                            .collect();
                        let v = if parts.is_empty() {
                            "trivial".into()
                        } else if parts.len() == 1 {
                            parts[0].clone()
                        } else {
                            format!("⟨{}⟩", parts.join(", "))
                        };
                        format!("  | .c{c}, _, _, hc => {v}")
                    } else {
                        format!("  | .c{c}, _, h, _ => by simp [appSafe, appSafe{j}] at h")
                    }
                })
                .collect();
            writeln!(o, "\ntheorem none_of_class_{j} : ∀ (c : Cls) (ch : Change), appSafe {j} c = true → InClass c ch → {hyp}\n{}", arms.join("\n")).unwrap();
        }
        // app_back for every rank
        let mut arms_t = String::new();
        let mut arms_s = String::new();
        for (j, fs) in reads.iter().enumerate() {
            if fs.is_some() {
                writeln!(
                    arms_t,
                    "  | {j}, c, h, hc, ht, ha => app_back_{j} ht (none_of_class_{j} c _ h hc) ha"
                )
                .unwrap();
                writeln!(
                    arms_s,
                    "  | {j}, c, h, hc, ht, ha => app_back_s_{j} ht (none_of_class_{j} c _ h hc) ha"
                )
                .unwrap();
            } else {
                writeln!(
                    arms_t,
                    "  | {j}, c, h, _, _, _ => by simp [appSafe, appSafe{j}] at h"
                )
                .unwrap();
                writeln!(
                    arms_s,
                    "  | {j}, c, h, _, _, _ => by simp [appSafe, appSafe{j}] at h"
                )
                .unwrap();
            }
        }
        writeln!(
            arms_t,
            "  | _ + {max_rank}, _, h, _, _, _ => by simp [appSafe] at h"
        )
        .unwrap();
        writeln!(
            arms_s,
            "  | _ + {max_rank}, _, h, _, _, _ => by simp [appSafe] at h"
        )
        .unwrap();
        writeln!(o, "\ntheorem app_back {{a b ch}} {{c c' : {topt}}} : ∀ (j : Nat) (cl : Cls), appSafe j cl = true → InClass cl ch →\n    MStep a b ch c c' → {} → {}\n{arms_t}", app("j", "c'"), app("j", "c")).unwrap();
        writeln!(o, "\ntheorem app_back_s {{ch}} {{c c' : {topt}}} : ∀ (j : Nat) (cl : Cls), appSafe j cl = true → InClass cl ch →\n    SStep ch c c' → {} → {}\n{arms_s}", app("j", "c'"), app("j", "c")).unwrap();
        writeln!(o, "\ndef safe (cl : Cls) (i : Nat) : Bool := (List.range i).all (fun j => appSafe j cl)\n\ntheorem safe_spec {{cl : Cls}} {{i j : Nat}} (h : safe cl i = true) (hj : j < i) : appSafe j cl = true := by\n  unfold safe at h\n  rw [List.all_eq_true] at h\n  exact h j (List.mem_range.2 hj)").unwrap();
        // the rules
        let rs = &lib.rules;
        writeln!(
            o,
            "\n/-- The rules. -/\ninductive Rule where\n{}\n  deriving DecidableEq",
            rs.iter()
                .map(|r| format!("  | {}", r.lean))
                .collect::<Vec<_>>()
                .join("\n")
        )
        .unwrap();
        writeln!(
            o,
            "\ninductive RKind where\n  | thread | shared | global\n  deriving DecidableEq"
        )
        .unwrap();
        writeln!(
            o,
            "\ndef Rule.rank : Rule → Nat\n{}",
            rs.iter()
                .map(|r| format!("  | .{} => {}", r.lean, rank(r)))
                .collect::<Vec<_>>()
                .join("\n")
        )
        .unwrap();
        writeln!(
            o,
            "\ndef Rule.kind : Rule → RKind\n{}",
            rs.iter()
                .zip(&kinds)
                .map(|(r, k)| format!(
                    "  | .{} => .{}",
                    r.lean,
                    match k {
                        Kind::Thread => "thread",
                        Kind::Shared => "shared",
                        Kind::Global => "global",
                    }
                ))
                .collect::<Vec<_>>()
                .join("\n")
        )
        .unwrap();
        writeln!(
            o,
            "\ndef Rule.cls : Rule → Cls\n{}",
            rs.iter()
                .zip(&cls)
                .map(|(r, c)| format!("  | .{} => .c{c}", r.lean))
                .collect::<Vec<_>>()
                .join("\n")
        )
        .unwrap();
        writeln!(
            o,
            "\n/-- The keys of a rule, one per binding of the thread map it matches. -/\ndef Rule.pats : Rule → List KeyPat\n{}",
            rs.iter()
                .zip(&keys)
                .map(|(r, k)| format!("  | .{} => {k}", r.lean))
                .collect::<Vec<_>>()
                .join("\n")
        )
        .unwrap();
        writeln!(
            o,
            "\n/-- Whether a rule adds a binding to the thread map. -/\ndef Rule.ins : Rule → Bool\n{}",
            rs.iter()
                .zip(&vroles)
                .map(|(r, v)| format!(
                    "  | .{} => {}",
                    r.lean,
                    v.as_ref().is_some_and(|v| v.inserts())
                ))
                .collect::<Vec<_>>()
                .join("\n")
        )
        .unwrap();
        writeln!(o, "\n/-- A step by rule `r`: every per-rule property of `r` holds of it. -/\ndef StepBy : Rule → {topt} → {topt} → Prop\n{}", rs.iter().map(|r| format!("  | .{l}, c, c' => ∀ Q, {name}.Step.Rel.{l} Q → Q c c'", l = r.lean)).collect::<Vec<_>>().join("\n")).unwrap();
        let small = if any_keyed { " ∧ ch.Small" } else { "" };
        writeln!(o, "\n/-- What a step by `r` is, beyond `Step`: a step at bindings `bs` of the thread map, a step of the shared\ncells, or nothing more (`global`). -/\ndef VPart (r : Rule) (c c' : {topt}) : Prop :=\n  match r.kind with\n  | .thread => ∃ a b bs ch, MStep a b ch c c' ∧ MapHook.Binds a bs ∧ (r.ins = false → MapHook.KeysIn b a) ∧\n      Local r.rank a b ch ∧ InClass r.cls ch ∧ KeyPat.Fits tkey r.pats bs{small}\n  | .shared => ∃ ch, SStep ch c c' ∧ LocalS r.rank ch ∧ InClass r.cls ch{small}\n  | .global => True").unwrap();
        writeln!(o, "\ndef ViewOf (r : Rule) (c c' : {topt}) : Prop :=\n  {name}.App r.rank c ∧ (∀ j, j < r.rank → ¬ {name}.App j c) ∧ StepBy r c c' ∧ VPart r c c'").unwrap();
        // the frames
        let mut frame_names = vec![];
        for (ri, r) in rs.iter().enumerate() {
            let l = &r.lean;
            let rk = rank(r);
            let mut args = rules::ctor_args(&r.step);
            if rk > 0 && !args.iter().any(|a| a == "hpri") {
                args.push("hpri".into());
            }
            let app_named: String = r
                .app
                .hyps
                .iter()
                .map(|(h, _)| format!(" ({h} := {h})"))
                .collect();
            let pri = if rk > 0 {
                "hpri".to_string()
            } else {
                "fun j hj => absurd hj (Nat.not_lt_zero j)".to_string()
            };
            let touch = &touches[ri];
            let c = &classes[cls[ri]];
            let k = c.iter().filter(|t| t.in_class()).count();
            // the rule's role at each keyed cell it changes
            let kr = |f: usize| keyed[f].as_ref().and_then(|rs| rs[ri].as_ref());
            let inclass = {
                let parts: Vec<&str> = (0..n)
                    .filter_map(|f| match touch[f] {
                        Touch::None => Some("rfl"),
                        Touch::Read => Some("⟨_, rfl⟩"),
                        Touch::Write | Touch::Keyed => None,
                    })
                    .collect();
                if parts.is_empty() {
                    "trivial".to_string()
                } else if parts.len() == 1 {
                    parts[0].to_string()
                } else {
                    format!("⟨{}⟩", parts.join(", "))
                }
            };
            let _ = k;
            let chlit = {
                let fs: Vec<String> = (0..n)
                    .filter(|&i| touch[i] != Touch::None)
                    .map(|i| format!("{} := some (_, _)", shared[i].field))
                    .collect();
                if fs.is_empty() {
                    "{}".to_string()
                } else {
                    format!("{{ {} }}", fs.join(", "))
                }
            };
            let pres: Vec<String> = (0..n)
                .map(|i| match kr(i) {
                    Some(role) => {
                        let (hx, hy) = role.proofs();
                        format!("MCh.pre_of {hx} {hy}")
                    }
                    None if touch[i] == Touch::None => format!("{}.pre_none", chn(i)),
                    None => "Ch.pre_self".into(),
                })
                .collect();
            let unders = vec!["_"; n].join(", ");
            let vars: Vec<String> = (0..n).map(|i| format!("v{i}")).collect();
            // the replay: a whole cell is the one the rule saw; a keyed cell has the rule's bindings
            // beside another rest, whose map the step makes (`MCh.apply_of`)
            let mut cases_pre = String::new();
            let mut applied = vec![];
            let mut keyed_eqs = String::new();
            let mut keyed_renames: Vec<(String, String)> = vec![];
            for i in (0..n).filter(|&i| touch[i] != Touch::None) {
                match kr(i) {
                    Some(role) => {
                        let (hx, hy) = (format!("hx{i}"), format!("hy{i}"));
                        writeln!(
                            cases_pre,
                            "  obtain ⟨_, _, {hx}, {hy}⟩ := {} _ rfl",
                            proj("hpre", i)
                        )
                        .unwrap();
                        applied.push(format!("MCh.apply_of {hx} {hy}"));
                        let (eq, rn) = role.replay(&hx, &hy);
                        keyed_eqs.push_str(&eq);
                        keyed_renames.extend(rn);
                    }
                    None => writeln!(cases_pre, "  cases ({} _ rfl)", proj("hpre", i)).unwrap(),
                }
            }
            if !applied.is_empty() {
                writeln!(
                    cases_pre,
                    "  simp only [Change.apply, Ch.apply, {}]",
                    applied.join(", ")
                )
                .unwrap();
                cases_pre.push_str(&keyed_eqs);
            }
            // a variable standing for a whole keyed cell, split into the cell's constructor and
            // the map it holds (`mkc` builds the cell from the map)
            let splits: String = r
                .step
                .binders
                .iter()
                .filter(|(_, t)| (0..n).any(|f| is_keyed(f) && *t == shared[f].sort))
                .map(|(v, _)| format!("  k2l_cases {v}\n"))
                .collect();
            // that the keyed changes are the rule's, at one binding
            let small_pf = if any_keyed {
                let ps: Vec<String> = (0..n)
                    .filter(|&f| is_keyed(f))
                    .map(|f| match kr(f) {
                        Some(role) => role.small(wide(f)),
                        None if wide(f) => "MCh.smallR_of_small MCh.small_none".into(),
                        None => "MCh.small_none".into(),
                    })
                    .collect();
                if ps.len() == 1 {
                    format!(", {}", ps[0])
                } else {
                    format!(", ⟨{}⟩", ps.join(", "))
                }
            } else {
                String::new()
            };
            // the step's equation: by computation, or for a keyed cell by `MCh.apply_of`
            let step_eq = {
                let ap: Vec<String> = (0..n)
                    .filter_map(kr)
                    .map(|role| {
                        let (hx, hy) = role.proofs();
                        format!("MCh.apply_of {hx} {hy}")
                    })
                    .collect();
                if ap.is_empty() {
                    "rfl".to_string()
                } else {
                    format!(
                        "(by simp only [mk, mkc, Change.apply, Ch.apply, {}] <;> rfl)",
                        ap.join(", ")
                    )
                }
            };
            let vpart = match kinds[ri] {
                Kind::Thread => {
                    let vr = vroles[ri].as_ref().unwrap();
                    // the rule's hypotheses as the replay restates them: `(old, new)`
                    let (pre, b_of, ins, unders_b, intro_r, replay, renames): Frame = match vr {
                        super::VRole::Update { hm, hr } => (
                            String::new(),
                            format!("{hm}, {hr}"),
                            "fun _ => MapHook.keysIn_element".into(),
                            "[(_, _)]",
                            "hm', hr'",
                            String::new(),
                            vec![(hm.clone(), "hm'".into()), (hr.clone(), "hr'".into())],
                        ),
                        super::VRole::Keep { hm } => (
                            String::new(),
                            format!("{hm}, {hm}"),
                            "fun _ => MapHook.keysIn_refl".into(),
                            "[(_, _)]",
                            "hm', hr'",
                            "  cases Option.some.inj (hm'.symm.trans hr')\n".into(),
                            vec![(hm.clone(), "hm'".into())],
                        ),
                        super::VRole::Remove { hm } => (
                            String::new(),
                            format!(
                                "{hm}, MapHook.concat_unit_left (MapHook.wf_rest_of_concat_element {hm})"
                            ),
                            "fun _ => MapHook.keysIn_unit".into(),
                            "[(_, _)]",
                            "hm', hr'",
                            "  cases MapHook.eq_of_concat_unit_left hr'\n".into(),
                            vec![(hm.clone(), "hm'".into())],
                        ),
                        super::VRole::Replace { hms, hr, .. } if hms.len() == 1 => (
                            String::new(),
                            format!("{}, {hr}", hms[0]),
                            "fun h => absurd h (by decide)".into(),
                            "[(_, _)]",
                            "hm', hr'",
                            String::new(),
                            vec![(hms[0].clone(), "hm'".into()), (hr.clone(), "hr'".into())],
                        ),
                        super::VRole::Replace { hms, hb, hr } => (
                            format!(
                                "  obtain ⟨_, hpair, hpairm⟩ := MapHook.concat_pair_of_chain {} {}\n",
                                hms[0], hms[1]
                            ),
                            format!("hpairm, {hr}"),
                            format!("fun _ => MapHook.keysIn_pair hpair {hb}"),
                            "[(_, _), (_, _)]",
                            "hpairm', hr'",
                            "  obtain ⟨_, hm2', hm'⟩ := MapHook.chain_of_pair hpair hpairm'\n"
                                .into(),
                            vec![
                                (hms[0].clone(), "hm'".into()),
                                (hms[1].clone(), "hm2'".into()),
                                (hr.clone(), "hr'".into()),
                            ],
                        ),
                    };
                    let binds = match vr {
                        super::VRole::Replace { hms, .. } if hms.len() == 2 => {
                            "MapHook.binds_pair hpair"
                        }
                        _ => "MapHook.binds_element",
                    };
                    let renames: Vec<(String, String)> = renames
                        .into_iter()
                        .chain(keyed_renames.iter().cloned())
                        .collect();
                    let mut named = String::new();
                    for (h, n) in &renames {
                        write!(named, " ({h} := {n})").unwrap();
                    }
                    if rk > 0 {
                        named.push_str(" (hpri := hpri')");
                    }
                    for (h, _) in &r.step.hyps {
                        if h != "hpri" && !renames.iter().any(|(o, _)| o == h) {
                            write!(named, " ({h} := {h})").unwrap();
                        }
                    }
                    // the projections the rule's hypotheses take, as equations
                    // (`proj_eq_some_S_T`), so that a cooling rule's `KResult` hypothesis, stated
                    // on the projected value, reads as one on its first item
                    let mut projs = BTreeSet::new();
                    for (_, h) in &r.step.hyps {
                        for (k, _) in h.match_indices("proj_") {
                            let n: String = h[k + "proj_".len()..]
                                .chars()
                                .take_while(|c| c.is_alphanumeric() || *c == '_')
                                .collect();
                            if !n.is_empty() && !n.starts_with("eq") {
                                projs.insert(format!("{name}.proj_eq_some_{n}"));
                            }
                        }
                    }
                    let proj_simp = if projs.is_empty() {
                        String::new()
                    } else {
                        format!(
                            "(try simp only [{}] at *); (try subst_vars); ",
                            projs.into_iter().collect::<Vec<_>>().join(", ")
                        )
                    };
                    let key = format!(
                        "(by first | rfl | ({proj_simp}simp only [KeyPat.matches, KeyPat.firstOK, KeyPat.itemOK, tkey, kitem, Option.all, KPrelude.BoolHook.and, Bool.true_and, Bool.and_eq_true, beq_iff_eq] at *; simp_all))"
                    );
                    let fits: String = vr.matches().iter().map(|_| format!("{key}, ")).collect();
                    format!(
                        "  simp only [VPart, Rule.kind, Rule.rank, Rule.cls, Rule.pats, InClass]\n{splits}{pre}  refine ⟨_, _, {unders_b}, {chlit}, ⟨_, _, _, ⟨{unders}⟩, rfl, {b_of}, ⟨{}⟩, {step_eq}⟩, {binds}, {ins}, ?_, {inclass}, ⟨{fits}trivial⟩{small_pf}⟩\n  rintro d d' ⟨_, _, _, ⟨{}⟩, rfl, {intro_r}, hpre, rfl⟩ hpri'\n{replay}{}  exact {name}.Step.{l} {named} ..",
                        pres.join(", "),
                        vars.join(", "),
                        cases_pre
                    )
                }
                Kind::Shared => {
                    let mut named = String::new();
                    if rk > 0 {
                        named.push_str(" (hpri := hpri')");
                    }
                    for (h, _) in &r.step.hyps {
                        if h != "hpri" {
                            let n = keyed_renames
                                .iter()
                                .find(|(o, _)| o == h)
                                .map_or(h, |(_, n)| n);
                            write!(named, " ({h} := {n})").unwrap();
                        }
                    }
                    format!(
                        "  simp only [VPart, Rule.kind, Rule.rank, Rule.cls, InClass]\n{splits}  refine ⟨{chlit}, ⟨_, ⟨{unders}⟩, rfl, ⟨{}⟩, {step_eq}⟩, ?_, {inclass}{small_pf}⟩\n  rintro d d' ⟨_, ⟨{}⟩, rfl, hpre, rfl⟩ hpri'\n{}  exact {name}.Step.{l}{named} ..",
                        pres.join(", "),
                        vars.join(", "),
                        cases_pre
                    )
                }
                Kind::Global => "  simp only [VPart, Rule.kind]".to_string(),
            };
            // the relation and its hypothesis bound beside the rule's variables: `Q`, `hQ`, unless
            // the rule has a variable of that name (`resume(Q)`)
            let (q, hq) = if args.iter().any(|a| a == "Q" || a == "hQ") {
                ("k2l_Q", "k2l_hQ")
            } else {
                ("Q", "hQ")
            };
            writeln!(o, "\ntheorem frame.{l} : {name}.Step.Rel.{l} (fun c c' => ∃ r, ViewOf r c c') := by\n  intro {}\n  refine ⟨.{l}, {name}.App.{l}{app_named} .., {pri}, fun {q} {hq} => {hq} {}, ?_⟩\n{vpart}",
                args.join(" "), args.join(" ")).unwrap();
            frame_names.push(format!("frame.{l}"));
        }
        writeln!(o, "\ntheorem view_of {{c c' : {topt}}} (h : {name}.Step c c') : ∃ r, ViewOf r c c' :=\n  {name}.Step.rel_of {} h", frame_names.join(" ")).unwrap();
        // the pairs decided without looking at them
        writeln!(o, "\ntheorem compatTbl_symm : ∀ a b : Cls, compatTbl a b = compatTbl b a := by\n  intro a b; cases a <;> cases b <;> rfl").unwrap();
        writeln!(o, "\n/-- Two rules whose steps from one configuration join by the generic arguments, unless both step
one thread: of different ranks (they never both apply), or each stepping bindings of the thread
map or the shared cells, touching compatible cells, not enabling a rule of a rank before the
other's, and not both adding bindings. -/
def staticOK (r₁ r₂ : Rule) : Bool :=
  r₁.rank != r₂.rank ||
    (match r₁.kind, r₂.kind with
     | .thread, .thread =>
       compatTbl r₁.cls r₂.cls && safe r₁.cls r₂.rank && safe r₂.cls r₁.rank && !(r₁.ins && r₂.ins)
     | .thread, .shared | .shared, .thread | .shared, .shared =>
       compatTbl r₁.cls r₂.cls && safe r₁.cls r₂.rank && safe r₂.cls r₁.rank
     | _, _ => false)").unwrap();
        writeln!(o, "\n/-- The joins of two steps at one thread by two rules of one rank, each with a key (the first items
of the thread's `<k>`) that may be the other's, the bindings each view matches given (`Binds`, as
many as the rule's keys by `Fits`). Nothing generic decides them: they are the determinism of one
thread. -/
def SameThreadJoins : Prop :=
  ∀ r₁ r₂, r₁.kind = .thread → r₂.kind = .thread → r₁.rank = r₂.rank → KeyPat.pdisj r₁.pats r₂.pats = false →
    ∀ {{c c₁ c₂ : {topt}}} {{a₁ b₁ ch₁ bs₁ a₂ b₂ ch₂ bs₂ k}}, StepBy r₁ c c₁ → StepBy r₂ c c₂ →
      MStep a₁ b₁ ch₁ c c₁ → MStep a₂ b₂ ch₂ c c₂ → MapHook.Binds a₁ bs₁ → MapHook.Binds a₂ bs₂ →
      KeyPat.Fits tkey r₁.pats bs₁ → KeyPat.Fits tkey r₂.pats bs₂ → MapHook.lookup a₁ k ≠ none →
      MapHook.lookup a₂ k ≠ none → DiamondMod {name}.Step Eq c₁ c₂").unwrap();
        if any_keyed {
            writeln!(o, "\n/-- A step by rule `r` that changes the shared cells by `ch`, the rule's change (`Change.Small`, of\nthe rule's class). -/\ndef ChOf (r : Rule) (ch : Change) (c c' : {topt}) : Prop :=\n  ((∃ a b, MStep a b ch c c') ∨ SStep ch c c') ∧ ch.Small ∧ InClass r.cls ch").unwrap();
            writeln!(o, "\n/-- The joins of two steps by rules of one rank whose changes of a cell holding a map overlap: a key\nthat both match, or one matches and the other adds, or both add (`MCh.Compat` fails). They are\nthe races at one binding, such as two steps that remove one binding. -/\ndef KeyJoins : Prop :=\n  ∀ r₁ r₂, r₁.rank = r₂.rank → ∀ {{c c₁ c₂ : {topt}}} {{ch₁ ch₂}}, StepBy r₁ c c₁ → StepBy r₂ c c₂ →\n    ChOf r₁ ch₁ c c₁ → ChOf r₂ ch₂ c c₂ → ¬ ch₁.KCompat ch₂ → DiamondMod {name}.Step Eq c₁ c₂").unwrap();
        }
        let mut js = format!("\ntheorem join_static (S : SameThreadJoins) {{r₁ r₂ : Rule}} {{c c₁ c₂ : {topt}}} (hs : staticOK r₁ r₂ = true)
    (v₁ : ViewOf r₁ c c₁) (v₂ : ViewOf r₂ c c₂) : DiamondMod {name}.Step Eq c₁ c₂ := by
  obtain ⟨a₁, p₁, b₁, w₁⟩ := v₁
  obtain ⟨a₂, p₂, b₂, w₂⟩ := v₂
  by_cases hr : r₁.rank ≠ r₂.rank
  · rcases Nat.lt_or_gt_of_ne hr with h | h
    · exact absurd a₁ (p₂ _ h)
    · exact absurd a₂ (p₁ _ h)
  have hr := Decidable.of_not_not hr
  have hne : (r₁.rank != r₂.rank) = false := by simp only [hr, bne_self_eq_false]
  simp only [staticOK, hne, Bool.false_or] at hs
  unfold VPart at w₁ w₂
  revert w₁ w₂ hs
  cases hk₁ : r₁.kind <;> cases hk₂ : r₂.kind <;> intro w₁ w₂ hs <;> simp only [Bool.and_eq_true, Bool.false_eq_true] at hs
  · obtain ⟨a₁, b₁', bs₁, ch₁, ts₁, d₁, n₁, l₁, i₁, m₁⟩ := w₁
    obtain ⟨a₂, b₂', bs₂, ch₂, ts₂, d₂, n₂, l₂, i₂, m₂⟩ := w₂
    obtain ⟨⟨⟨hc, hs₁⟩, hs₂⟩, hn⟩ := hs
    by_cases hk : ∃ p ∈ bs₁, ∃ q ∈ bs₂, p.1 = q.1
    · obtain ⟨p, hp, q, hq, e⟩ := hk
      cases hd : KeyPat.pdisj r₁.pats r₂.pats
      · refine S r₁ r₂ hk₁ hk₂ hr hd b₁ b₂ ts₁ ts₂ d₁ d₂ m₁ m₂ (k := p.1) ?_ ?_
        · rw [(d₁ p.1 p.2).2 hp]; simp
        · rw [e, (d₂ q.1 q.2).2 hq]; simp
      · exact (KeyPat.pdisj_sound hd m₁ m₂ hp hq (mstep_same ts₁ ts₂ d₁ d₂ hp hq e)).elim
    · obtain ⟨c₁₂, x, y⟩ := mstep_comm ts₁ ts₂ (MapHook.binds_disj d₁ d₂ hk) (or_of_not_both n₁ n₂ hn)
        (compat_of _ _ hc _ _ i₁ i₂)
      refine ⟨c₁₂, c₁₂, Or.inr (l₂ _ _ x ?_), Or.inr (l₁ _ _ y ?_), rfl⟩
      · intro j hj ha; exact p₂ j hj (app_back j _ (safe_spec hs₁ hj) i₁ ts₁ ha)
      · intro j hj ha; exact p₁ j hj (app_back j _ (safe_spec hs₂ hj) i₂ ts₂ ha)
  · obtain ⟨a₁, b₁', bs₁, ch₁, ts₁, -, -, l₁, i₁, -⟩ := w₁
    obtain ⟨ch₂, ss₂, l₂, i₂⟩ := w₂
    obtain ⟨⟨hc, hs₁⟩, hs₂⟩ := hs
    obtain ⟨c₁₂, x, y⟩ := mstep_sstep_comm ts₁ ss₂ (compat_of _ _ hc _ _ i₁ i₂)
    refine ⟨c₁₂, c₁₂, Or.inr (l₂ _ _ x ?_), Or.inr (l₁ _ _ y ?_), rfl⟩
    · intro j hj ha; exact p₂ j hj (app_back j _ (safe_spec hs₁ hj) i₁ ts₁ ha)
    · intro j hj ha; exact p₁ j hj (app_back_s j _ (safe_spec hs₂ hj) i₂ ss₂ ha)
  · obtain ⟨ch₁, ss₁, l₁, i₁⟩ := w₁
    obtain ⟨a₂, b₂', bs₂, ch₂, ts₂, -, -, l₂, i₂, -⟩ := w₂
    obtain ⟨⟨hc, hs₁⟩, hs₂⟩ := hs
    obtain ⟨c₁₂, x, y⟩ := mstep_sstep_comm ts₂ ss₁ (compat_of _ _ ((compatTbl_symm _ _).trans hc) _ _ i₂ i₁)
    refine ⟨c₁₂, c₁₂, Or.inr (l₂ _ _ y ?_), Or.inr (l₁ _ _ x ?_), rfl⟩
    · intro j hj ha; exact p₂ j hj (app_back_s j _ (safe_spec hs₁ hj) i₁ ss₁ ha)
    · intro j hj ha; exact p₁ j hj (app_back j _ (safe_spec hs₂ hj) i₂ ts₂ ha)
  · obtain ⟨ch₁, ss₁, l₁, i₁⟩ := w₁
    obtain ⟨ch₂, ss₂, l₂, i₂⟩ := w₂
    obtain ⟨⟨hc, hs₁⟩, hs₂⟩ := hs
    obtain ⟨c₁₂, x, y⟩ := sstep_comm ss₁ ss₂ (compat_of _ _ hc _ _ i₁ i₂)
    refine ⟨c₁₂, c₁₂, Or.inr (l₂ _ _ x ?_), Or.inr (l₁ _ _ y ?_), rfl⟩
    · intro j hj ha; exact p₂ j hj (app_back_s j _ (safe_spec hs₁ hj) i₁ ss₁ ha)
    · intro j hj ha; exact p₁ j hj (app_back_s j _ (safe_spec hs₂ hj) i₂ ss₂ ha)");
        if any_keyed {
            // the views' `Small`, and before each generic join the keyed cells' compatibility:
            // otherwise the join is `KeyJoins`'
            let chof = |side: &str, n: &str| {
                if side == "t" {
                    format!("⟨Or.inl ⟨_, _, ts{n}⟩, k{n}, i{n}⟩")
                } else {
                    format!("⟨Or.inr ss{n}, k{n}, i{n}⟩")
                }
            };
            let split = |ind: &str, s1: &str, s2: &str| {
                format!(
                    "{ind}by_cases hkc : ¬ ch₁.KCompat ch₂\n{ind}· exact K r₁ r₂ hr b₁ b₂ {} {} hkc\n{ind}have hkc := Classical.not_not.1 hkc\n",
                    chof(s1, "₁"),
                    chof(s2, "₂")
                )
            };
            for (a, b) in [
                (
                    "(S : SameThreadJoins) {r₁ r₂",
                    "(S : SameThreadJoins) (K : KeyJoins) {r₁ r₂",
                ),
                ("m₁⟩ := w₁", "m₁, k₁⟩ := w₁"),
                ("m₂⟩ := w₂", "m₂, k₂⟩ := w₂"),
                ("l₁, i₁, -⟩ := w₁", "l₁, i₁, -, k₁⟩ := w₁"),
                ("l₂, i₂, -⟩ := w₂", "l₂, i₂, -, k₂⟩ := w₂"),
                ("⟨ch₁, ss₁, l₁, i₁⟩ := w₁", "⟨ch₁, ss₁, l₁, i₁, k₁⟩ := w₁"),
                ("⟨ch₂, ss₂, l₂, i₂⟩ := w₂", "⟨ch₂, ss₂, l₂, i₂, k₂⟩ := w₂"),
                ("_ _ i₁ i₂)", "_ _ i₁ i₂ hkc)"),
                ("_ _ i₂ i₁)", "_ _ i₂ i₁ hkc.symm)"),
            ] {
                js = js.replace(a, b);
            }
            js = js.replacen(
                "    · obtain ⟨c₁₂, x, y⟩ := mstep_comm",
                &format!(
                    "    · {}      obtain ⟨c₁₂, x, y⟩ := mstep_comm",
                    split("      ", "t", "t").trim_start()
                ),
                1,
            );
            let mut parts = js.split("    obtain ⟨⟨hc, hs₁⟩, hs₂⟩ := hs\n");
            let mut out = parts.next().unwrap().to_string();
            for (k, rest) in parts.enumerate() {
                let (s1, s2) = [("t", "s"), ("s", "t"), ("s", "s")][k];
                out.push_str("    obtain ⟨⟨hc, hs₁⟩, hs₂⟩ := hs\n");
                out.push_str(&split("    ", s1, s2));
                out.push_str(rest);
            }
            js = out;
        }
        o.push_str(&js);
        o.push('\n');
        writeln!(o, "\n/-- The joins the generic arguments leave in every configuration: one per ordered pair of rules that
`staticOK` rejects. -/\ndef OpenJoins : Prop :=\n  ∀ r₁ r₂, staticOK r₁ r₂ = false → ∀ {{c c₁ c₂ : {topt}}}, StepBy r₁ c c₁ → StepBy r₂ c c₂ →\n    DiamondMod {name}.Step Eq c₁ c₂").unwrap();
        let (kb, ka) = if any_keyed {
            (" (K : KeyJoins)", " K")
        } else {
            ("", "")
        };
        writeln!(o, "\ntheorem joins_of (O : OpenJoins) (S : SameThreadJoins){kb} {{c c₁ c₂ : {topt}}} (h₁ : {name}.Step c c₁)\n    (h₂ : {name}.Step c c₂) : DiamondMod {name}.Step Eq c₁ c₂ := by\n  obtain ⟨r₁, v₁⟩ := view_of h₁\n  obtain ⟨r₂, v₂⟩ := view_of h₂\n  cases hs : staticOK r₁ r₂\n  · exact O r₁ r₂ hs v₁.2.2.1 v₂.2.2.1\n  · exact join_static S{ka} hs v₁ v₂").unwrap();
        writeln!(o, "\n/-- Given the joins left open, two runs that end in terminal configurations end in the same one. -/\ntheorem terminal_unique_of (O : OpenJoins) (S : SameThreadJoins){kb} {{c n₁ n₂ : {topt}}}\n    (h₁ : Star {name}.Step c n₁) (t₁ : Terminal {name}.Step n₁) (h₂ : Star {name}.Step c n₂)\n    (t₂ : Terminal {name}.Step n₂) : n₁ = n₂ :=\n  terminal_unique_of_diamond (H := fun _ => True) StepEquiv.eq (fun _ _ _ _ => trivial)\n    (fun _ h₁ h₂ => joins_of O S{ka} h₁ h₂) trivial h₁ t₁ h₂ t₂").unwrap();
        let mut guard = "mstep_comm compat_of app_back app_back_s view_of join_static joins_of terminal_unique_of".to_string();
        if let Some(cells) = obs {
            o.push('\n');
            o.push_str(&super::proj_def(lib, name, "obs", cells, None));
            writeln!(o, "\n/-- A corollary of `terminal_unique_of`: the observed cells of the two terminal configurations agree. -/\ntheorem obs_confluent_of (O : OpenJoins) (S : SameThreadJoins){kb} {{c n₁ n₂ : {topt}}}\n    (h₁ : Star {name}.Step c n₁) (t₁ : Terminal {name}.Step n₁) (h₂ : Star {name}.Step c n₂)\n    (t₂ : Terminal {name}.Step n₂) : obs n₁ = obs n₂ :=\n  congrArg obs (terminal_unique_of O S{ka} h₁ t₁ h₂ t₂)").unwrap();
            guard.push_str(" obs_confluent_of");
        }
        writeln!(o, "\n#k2l_assert_axioms {guard}").unwrap();
        // the count
        let safe = |c: usize, i: usize| (0..i).all(|j| j < max_rank && safe_tbl(j, c));
        let mut c = super::Counts {
            rules: rs.len(),
            thread: kinds.iter().filter(|k| **k == Kind::Thread).count(),
            shared: kinds.iter().filter(|k| **k == Kind::Shared).count(),
            global: kinds.iter().filter(|k| **k == Kind::Global).count(),
            classes: classes.len(),
            key_joins: any_keyed.then_some(0),
            ..super::Counts::default()
        };
        let ins = |k: usize| vroles[k].as_ref().is_some_and(|v| v.inserts());
        for (i, r1) in rs.iter().enumerate() {
            for (j, r2) in rs.iter().enumerate() {
                if rank(r1) != rank(r2) {
                    continue;
                }
                let pdisj = keyps[i].iter().all(|p| keyps[j].iter().all(|q| p.disj(q)));
                if kinds[i] == Kind::Thread && kinds[j] == Kind::Thread && !pdisj {
                    c.same_thread += 1;
                }
                if kinds[i] == Kind::Global || kinds[j] == Kind::Global {
                    c.open_global += 1;
                } else if !compat(&classes[cls[i]], &classes[cls[j]]) {
                    c.open_cells += 1;
                } else if !(safe(cls[i], rank(r2)) && safe(cls[j], rank(r1))) {
                    c.open_priority += 1;
                } else if ins(i) && ins(j) {
                    c.open_insert += 1;
                } else if let Some(k) = c.key_joins.as_mut()
                    && (0..n).any(|f| {
                        classes[cls[i]][f] == Touch::Keyed && classes[cls[j]][f] == Touch::Keyed
                    })
                {
                    *k += 1;
                }
            }
        }
        writeln!(o, "\nend {ns}").unwrap();
        (o, c)
    }

    #[cfg(test)]
    mod key_tests {
        use super::*;

        #[test]
        fn keys_read_the_first_item_or_the_freezer_after_a_value() {
            let kres = |inj: &str| Some(inj == "inj_Val");
            // heating: the operator, not a value
            let h = "MapHook.concat (MapHook.element k (SortThreadCell.«<thread>» k (SortKCell.«<k>» (SortK.kseq (SortKItem.inj_Exp (SortExp.Own.«_(_)» E Es)) DotVar4)) G)) D = some m";
            assert!(
                key_pat(h, &kres, false)
                    == KeyP::Item(Some("inj_Exp".into()), Some("«_(_)»".into()), Some(false))
            );
            // cooling: a value, then its freezer (a constant one too)
            let c = |f: &str| {
                format!(
                    "(SortThreadCell.«<thread>» k (SortKCell.«<k>» (SortK.kseq y_2 (SortK.kseq (SortKItem.inj_KItem {f}) DotVar4)) G)"
                )
            };
            let k1 = key_pat(
                &c("(SortKItem.Own.«#freezer_+_0_» (SortK.kseq y_3 SortK.dotk))"),
                &kres,
                true,
            );
            let k2 = key_pat(&c("SortKItem.Own.«#freezerreturn_;_»"), &kres, true);
            assert!(
                k1 == KeyP::Item2(
                    None,
                    None,
                    Some(true),
                    Some("inj_KItem".into()),
                    Some("«#freezer_+_0_»".into())
                )
            );
            assert!(
                k2 == KeyP::Item2(
                    None,
                    None,
                    Some(true),
                    Some("inj_KItem".into()),
                    Some("«#freezerreturn_;_»".into())
                )
            );
            // two freezers are disjoint, and a value from an operator
            let heat = key_pat(h, &kres, false);
            assert!(k1.disj(&k2) && k1.disj(&heat) && !k1.disj(&k1));
            // `<k>` empty
            assert!(key_pat("(SortKCell.«<k>» SortK.dotk)", &kres, false) == KeyP::Dotk);
        }
    }
}

/// What `--threads` leaves open, counted over ordered pairs of rules of one rank.
#[derive(Default)]
pub(crate) struct Counts {
    rules: usize,
    thread: usize,
    shared: usize,
    global: usize,
    classes: usize,
    /// a global rule (`OpenJoins`)
    open_global: usize,
    /// two rules touching one cell where one writes (`OpenJoins`)
    open_cells: usize,
    /// a rule that may enable one of a rank before the other's (`OpenJoins`)
    open_priority: usize,
    /// two rules that add bindings to the thread map (`OpenJoins`)
    open_insert: usize,
    /// two thread rules whose keys may be equal, at one binding (`SameThreadJoins`)
    same_thread: usize,
    /// with cells holding a map changed at some bindings: two rules of one rank, otherwise
    /// decided generically, that change one such cell (`KeyJoins`, where their keys overlap)
    key_joins: Option<usize>,
}

impl Counts {
    fn report(&self) -> String {
        format!(
            "\n[threads]\nrules = {}\nthread = {}\nshared = {}\nglobal = {}\nclasses = {}\nopen = {}\nopen-global = {}\nopen-cells = {}\nopen-priority = {}\nopen-insert = {}\nsame-thread = {}\n",
            self.rules,
            self.thread,
            self.shared,
            self.global,
            self.classes,
            self.open_global + self.open_cells + self.open_priority + self.open_insert,
            self.open_global,
            self.open_cells,
            self.open_priority,
            self.open_insert,
            self.same_thread
        ) + &self
            .key_joins
            .map_or(String::new(), |k| format!("key-joins = {k}\n"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_hypotheses_name_their_rest_and_map() {
        let h = "KPrelude.MapHook.concat (KPrelude.MapHook.element (SortWidCell.«<wid>» Gen0) (SortWorkerCell.«<worker>» (SortWidCell.«<wid>» Gen0) (SortTodoCell.«<todo>» C))) DotVar2 = some m";
        assert_eq!(map_hyp(h), Some(("DotVar2".into(), "m".into())));
        assert_eq!(map_hyp("KPrelude.IntHook.gt C (0 : Int) = true"), None);
    }

    #[test]
    fn cell_heads_are_recognized() {
        assert_eq!(is_cell("SortAccCell.«<acc>»"), Some("acc".into()));
        assert_eq!(is_cell("SortK.kseq"), None);
    }

    #[test]
    fn element_keys_read_each_binding_of_a_map_literal() {
        // rendezvous: the two threads rebound at their keys
        let h = "(KPrelude.MapHook.concat (KPrelude.MapHook.element k (SortThreadCell.«<thread>» k (SortKCell.«<k>» DotVar4) G)) (KPrelude.MapHook.element k_3 (SortThreadCell.«<thread>» k_3 (SortKCell.«<k>» DotVar6) G')) : Option SortThreadCellMap) = some r";
        assert_eq!(element_keys(h), vec!["k", "k_3"]);
        // spawn: a constructor key
        let s = "KPrelude.MapHook.concat (KPrelude.MapHook.element (SortIdCell.«<id>» (f N)) t) R = some m";
        assert_eq!(element_keys(s), vec!["(SortIdCell.«<id>» (f N))"]);
    }
}
