//! Termination measures for recursive functions.
//!
//! A recursive K function is a well-founded Lean definition. Lean's own measure search
//! (`GuessLex`) only tries `sizeOf` of each parameter; this module adds the measures that K
//! definitions count with, computed from the lowered equations.
//!
//! `plan` (one function, tried first): integer distances `(u - t).toNat` from a bound that holds
//! at a recursive call (the call's requires, a failed earlier guard-only equation, the range of a
//! defined partial hook), and constructor ranks of a parameter along a fallback chain, combined
//! lexicographically.
//!
//! `Ctx::plan_group` (a group of one or several functions, when neither `plan`, a list or integer
//! rule of `funcs.rs`, nor structural recursion applies): per function a tuple of components, of
//! one length across the group: integer distances (also over the fields of a parameter matched
//! by a constructor, and carried between the functions of the group through the calls'
//! arguments), the shape of a parameter (`KPrelude.Shape`, arity-indexed universe), a rank of the
//! function within the group (guarded by the facts at the calls into it when the group's calls
//! cycle), and a counter's distance to a bound before a component that decreases only beyond it.
//! The facts at the calls include lemmas about callees that this module derives from their
//! equations and the generated code proves (`@[k2l_fact]`): what a function returns, the range
//! of a total integer function, a bound on a result's shape.
//!
//! The checks are on linear integer forms, by Fourier–Motzkin elimination (sound for integers,
//! incomplete); they only choose: the proofs are Lean's (`k2l_decreasing`, `k2l_fn_facts`,
//! `omega`), so a wrong choice is a build error, never an unsound definition. When no measure is
//! found the generator leaves the measure to Lean.

use crate::lower::{L, Step};
use std::collections::{BTreeMap, BTreeSet};

/// A linear form over atoms (parameters or other variables, and rendered terms) plus a constant.
#[derive(Clone, Debug, PartialEq)]
struct Lin {
    terms: BTreeMap<String, i128>,
    c: i128,
}

impl Lin {
    fn konst(c: i128) -> Lin {
        Lin {
            terms: BTreeMap::new(),
            c,
        }
    }
    fn atom(a: &str) -> Lin {
        let mut terms = BTreeMap::new();
        terms.insert(a.to_string(), 1);
        Lin { terms, c: 0 }
    }
    fn add(&self, o: &Lin, k: i128) -> Lin {
        let mut r = self.clone();
        for (a, v) in &o.terms {
            *r.terms.entry(a.clone()).or_insert(0) += k * v;
        }
        r.terms.retain(|_, v| *v != 0);
        r.c += k * o.c;
        r
    }
    fn scale(&self, k: i128) -> Lin {
        Lin {
            terms: self
                .terms
                .iter()
                .map(|(a, v)| (a.clone(), v * k))
                .filter(|(_, v)| *v != 0)
                .collect(),
            c: self.c * k,
        }
    }
    fn plus(&self, c: i128) -> Lin {
        Lin {
            terms: self.terms.clone(),
            c: self.c + c,
        }
    }
    fn as_const(&self) -> Option<i128> {
        if self.terms.is_empty() {
            Some(self.c)
        } else {
            None
        }
    }
    /// A Lean `Int` expression.
    fn render(&self) -> String {
        let mut s = String::new();
        for (a, v) in &self.terms {
            let t = if a.contains(' ') {
                format!("({a})")
            } else {
                a.clone()
            };
            let (sign, mag) = if *v < 0 { ("-", -v) } else { ("+", *v) };
            let t = if mag == 1 { t } else { format!("{mag} * {t}") };
            if s.is_empty() {
                s = if sign == "-" { format!("-{t}") } else { t };
            } else {
                s.push_str(&format!(" {sign} {t}"));
            }
        }
        if self.c != 0 || s.is_empty() {
            let (sign, mag) = if self.c < 0 {
                ("-", -self.c)
            } else {
                ("+", self.c)
            };
            if s.is_empty() {
                s = format!("({} : Int)", self.c);
            } else {
                s.push_str(&format!(" {sign} ({mag} : Int)"));
            }
        }
        s
    }
}

/// A fact `lin ≥ 0`.
type Fact = Lin;

fn int_lit(r: &str) -> Option<i128> {
    let t = r.trim_start_matches('(').trim_end_matches(')');
    let v = t.strip_suffix(": Int")?.trim();
    v.parse().ok()
}

fn vars_of(l: &L, out: &mut BTreeSet<String>) {
    match l {
        L::Var(v) => {
            out.insert(v.clone());
        }
        L::App(_, args) => args.iter().for_each(|a| vars_of(a, out)),
        L::Typed(e, _) => vars_of(e, out),
        L::Raw(_) => {}
    }
}

thread_local! {
    /// The variables of each compound atom (a rendered term) met so far.
    static ATOM_VARS: std::cell::RefCell<BTreeMap<String, BTreeSet<String>>> = Default::default();
    /// The term of each compound atom met so far.
    static ATOM_TERMS: std::cell::RefCell<BTreeMap<String, L>> = Default::default();
}

fn compound_atom(l: &L) -> Lin {
    let a = l.render();
    let mut vs = BTreeSet::new();
    vars_of(l, &mut vs);
    ATOM_VARS.with(|m| m.borrow_mut().insert(a.clone(), vs));
    ATOM_TERMS.with(|m| m.borrow_mut().insert(a.clone(), l.clone()));
    Lin::atom(&a)
}

/// The term of an atom: a variable, or a compound atom met before.
fn atom_term(a: &str) -> L {
    ATOM_TERMS
        .with(|m| m.borrow().get(a).cloned())
        .unwrap_or_else(|| L::Var(a.to_string()))
}

/// The variables an atom mentions.
fn atom_vars(a: &str) -> BTreeSet<String> {
    ATOM_VARS
        .with(|m| m.borrow().get(a).cloned())
        .unwrap_or_else(|| [a.to_string()].into_iter().collect())
}

/// The linear form of an integer term (unknown subterms are atoms).
fn lin(l: &L) -> Option<Lin> {
    match l {
        L::Var(v) => Some(Lin::atom(v)),
        L::Raw(r) => int_lit(r).map(Lin::konst),
        L::App(h, args)
            if args.len() == 2 && (h == "KPrelude.IntHook.add" || h == "KPrelude.IntHook.sub") =>
        {
            let a = lin(&args[0])?;
            let b = lin(&args[1])?;
            Some(a.add(&b, if h.ends_with("add") { 1 } else { -1 }))
        }
        L::App(h, args) if args.len() == 2 && h == "KPrelude.IntHook.mul" => {
            let a = lin(&args[0])?;
            let b = lin(&args[1])?;
            match (a.as_const(), b.as_const()) {
                (Some(k), _) => Some(b.scale(k)),
                (_, Some(k)) => Some(a.scale(k)),
                _ => Some(compound_atom(l)),
            }
        }
        L::App(..) | L::Typed(..) => Some(compound_atom(l)),
    }
}

/// The facts a Boolean condition gives when it holds (`pos`) or fails.
fn cond_facts(c: &L, pos: bool) -> Vec<Fact> {
    let L::App(h, args) = c else { return vec![] };
    let h = h.as_str();
    match (h, args.len()) {
        ("KPrelude.BoolHook.not", 1) => cond_facts(&args[0], !pos),
        ("KPrelude.BoolHook.and", 2) if pos => {
            [cond_facts(&args[0], true), cond_facts(&args[1], true)].concat()
        }
        ("KPrelude.BoolHook.or", 2) if !pos => {
            [cond_facts(&args[0], false), cond_facts(&args[1], false)].concat()
        }
        (_, 2) if h.starts_with("KPrelude.IntHook.") => {
            let (Some(a), Some(b)) = (lin(&args[0]), lin(&args[1])) else {
                return vec![];
            };
            let ge = |x: &Lin, y: &Lin, off: i128| vec![x.add(y, -1).plus(-off)]; // x - y - off ≥ 0
            match (h.trim_start_matches("KPrelude.IntHook."), pos) {
                // a ≤ b, ¬(a > b): b - a ≥ 0; a < b, ¬(a ≥ b): b - a - 1 ≥ 0; and symmetrically
                ("le", true) | ("gt", false) => ge(&b, &a, 0),
                ("lt", true) | ("ge", false) => ge(&b, &a, 1),
                ("ge", true) | ("lt", false) => ge(&a, &b, 0),
                ("gt", true) | ("le", false) => ge(&a, &b, 1),
                ("eq", true) | ("ne", false) => [ge(&a, &b, 0), ge(&b, &a, 0)].concat(),
                _ => vec![],
            }
        }
        _ => vec![],
    }
}

/// `g ≥ 0` follows from one fact by adding a nonnegative constant.
fn implied(g: &Lin, facts: &[Fact]) -> bool {
    if let Some(c) = g.as_const() {
        return c >= 0;
    }
    facts
        .iter()
        .any(|f| g.add(f, -1).as_const().is_some_and(|c| c >= 0))
}

/// One recursive call: the facts that hold there, the parameters' head constructors known from
/// the equation's patterns, and the arguments.
struct Call {
    facts: Vec<Fact>,
    heads: BTreeMap<usize, String>,
    args: Vec<L>,
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Rel {
    Lt,
    Le,
    Unknown,
}

/// The equations of one function, lowered: steps, the number of left-hand-side steps, and
/// whether its cascade position may be named (a guard-only equation).
pub struct Eqn<'a> {
    pub steps: &'a [Step],
    pub lhs_len: usize,
}

pub struct Plan {
    /// `termination_by` term.
    pub measure: String,
    /// Rank functions (Lean declarations) to emit before the definition, and their names.
    pub rank_defs: String,
    pub rank_names: Vec<String>,
    /// Equations (indices into the list given to `plan`) whose cascade `match` gets a name, so
    /// that their failure is a hypothesis of the later recursive calls.
    pub named: BTreeSet<usize>,
}

/// A measure for a function that is the only member of its recursive group.
/// `ctors` maps each constructor's Lean path to its arity.
pub fn plan(
    fname: &str,
    params: &[String],
    arg_tys: &[String],
    eqs: &[Eqn],
    ctors: &BTreeMap<String, usize>,
) -> Option<Plan> {
    let pidx: BTreeMap<&str, usize> = params
        .iter()
        .enumerate()
        .map(|(i, p)| (p.as_str(), i))
        .collect();
    // the facts of each guard-only equation's failure
    let negated: Vec<Vec<Fact>> = eqs
        .iter()
        .map(|e| {
            let guard_only = e.steps.len() == e.lhs_len
                && e.lhs_len == 1
                && matches!(e.steps[0], Step::Cond { .. } | Step::CondEq { .. });
            if !guard_only {
                return vec![];
            }
            match &e.steps[0] {
                Step::Cond { cond, .. } => cond_facts(cond, false),
                Step::CondEq {
                    lhs,
                    rhs: L::Raw(r),
                    ..
                } if r == "false" => cond_facts(lhs, true),
                _ => vec![],
            }
        })
        .collect();
    let mut calls: Vec<Call> = Vec::new();
    let mut named: BTreeSet<usize> = BTreeSet::new();
    for (ei, e) in eqs.iter().enumerate() {
        let mut facts: Vec<Fact> = Vec::new();
        let mut earlier: Vec<Fact> = Vec::new();
        for (j, n) in negated.iter().enumerate().take(ei) {
            if !n.is_empty() {
                earlier.extend(n.iter().cloned());
                let _ = j;
            }
        }
        let mut alias: BTreeMap<String, L> = BTreeMap::new();
        let mut heads: BTreeMap<usize, String> = BTreeMap::new();
        for s in e.steps {
            match s {
                Step::Destruct { scrut, pat, .. } => {
                    if let Some(&k) = pidx.get(scrut.as_str()) {
                        match pat {
                            L::Var(y) => {
                                alias.insert(y.clone(), L::Var(scrut.clone()));
                            }
                            L::App(h, _) if ctors.contains_key(h) => {
                                heads.insert(k, h.clone());
                            }
                            _ => {}
                        }
                    }
                }
                Step::Cond { cond, .. } => facts.extend(cond_facts(&cond.subst(&alias), true)),
                Step::CondEq { lhs, rhs, .. } => {
                    let (l, r) = (lhs.subst(&alias), rhs.subst(&alias));
                    if let L::Raw(b) = &r {
                        if b == "false" {
                            facts.extend(cond_facts(&l, false));
                        } else if let (Some(a), Some(v)) = (lin(&l), lin(&r)) {
                            facts.push(a.add(&v, -1));
                            facts.push(v.add(&a, -1));
                        }
                    }
                }
                Step::Bind { expr, var, .. } => {
                    let expr = expr.subst(&alias);
                    if let L::App(h, args) = &expr {
                        if h == fname {
                            let mut f = facts.clone();
                            f.extend(earlier.iter().cloned());
                            calls.push(Call {
                                facts: f,
                                heads: heads.clone(),
                                args: args.clone(),
                            });
                            if !earlier.is_empty() {
                                for (j, n) in negated.iter().enumerate().take(ei) {
                                    if !n.is_empty() {
                                        named.insert(j);
                                    }
                                }
                            }
                        }
                        hook_facts(h, args, var, &mut facts);
                    }
                }
                _ => {}
            }
        }
    }
    if calls.is_empty() {
        return None;
    }
    // candidate integer measures: `f + 1` for each fact `f ≥ 0` over parameters
    let mut cands: Vec<Lin> = Vec::new();
    for c in &calls {
        for f in &c.facts {
            let m = f.plus(1);
            let over_params = m
                .terms
                .keys()
                .all(|a| atom_vars(a).iter().all(|v| pidx.contains_key(v.as_str())));
            if over_params && m.as_const().is_none() && !cands.contains(&m) {
                cands.push(m);
            }
        }
    }
    let int_rel = |m: &Lin, c: &Call| -> Rel {
        // the measure at the call's arguments
        let mut m2 = Lin::konst(m.c);
        for (a, k) in &m.terms {
            let t = if let Some(&i) = pidx.get(a.as_str()) {
                match lin(&c.args[i]) {
                    Some(l) => l,
                    None => return Rel::Unknown,
                }
            } else {
                // a rendered term over parameters: unchanged when they are
                let vs: Vec<usize> = atom_vars(a)
                    .iter()
                    .filter_map(|v| pidx.get(v.as_str()).copied())
                    .collect();
                if vs.iter().all(|&i| c.args[i] == L::Var(params[i].clone())) {
                    Lin::atom(a)
                } else {
                    return Rel::Unknown;
                }
            };
            m2 = m2.add(&t, *k);
        }
        let d = m.add(&m2, -1); // m - m2
        let pos = implied(&m.plus(-1), &c.facts);
        if pos && implied(&d.plus(-1), &c.facts) {
            Rel::Lt
        } else if implied(&d, &c.facts) {
            Rel::Le
        } else {
            Rel::Unknown
        }
    };
    // constructor ranks of a parameter over a set of calls
    let rank_of = |k: usize, idx: &[usize]| -> Option<(BTreeMap<String, usize>, Vec<Rel>)> {
        let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut any = false;
        for &ci in idx {
            let c = &calls[ci];
            let arg_head = match &c.args[k] {
                L::App(h, _) if ctors.contains_key(h) => Some(h.clone()),
                _ => None,
            };
            if let (Some(from), Some(to)) = (c.heads.get(&k), arg_head) {
                edges.entry(from.clone()).or_default().insert(to);
                any = true;
            }
        }
        if !any {
            return None;
        }
        // longest path from each node; a cycle rejects the candidate
        fn depth(
            n: &str,
            e: &BTreeMap<String, BTreeSet<String>>,
            memo: &mut BTreeMap<String, Option<usize>>,
        ) -> Option<usize> {
            if let Some(v) = memo.get(n) {
                return *v; // None while on the stack: a cycle
            }
            memo.insert(n.to_string(), None);
            let mut d = 0;
            for m in e.get(n).into_iter().flatten() {
                d = d.max(depth(m, e, memo)? + 1);
            }
            memo.insert(n.to_string(), Some(d));
            Some(d)
        }
        let mut memo = BTreeMap::new();
        let mut rank = BTreeMap::new();
        for n in edges.keys() {
            rank.insert(n.clone(), depth(n, &edges, &mut memo)?);
        }
        for (n, d) in memo {
            rank.insert(n, d?);
        }
        let rels = idx
            .iter()
            .map(|&ci| {
                let c = &calls[ci];
                let to = match &c.args[k] {
                    L::App(h, _) if ctors.contains_key(h) => {
                        Some(rank.get(h).copied().unwrap_or(0))
                    }
                    _ => None,
                };
                match (c.heads.get(&k), to) {
                    (Some(from), Some(t)) if rank.get(from).copied().unwrap_or(0) > t => Rel::Lt,
                    (_, Some(0)) => Rel::Le,
                    (_, None) if c.args[k] == L::Var(params[k].clone()) => Rel::Le,
                    _ => Rel::Unknown,
                }
            })
            .collect();
        Some((rank, rels))
    };
    // lexicographic search
    let mut remaining: Vec<usize> = (0..calls.len()).collect();
    let mut chosen: Vec<String> = Vec::new();
    let mut rank_defs = String::new();
    let mut rank_names = Vec::new();
    while !remaining.is_empty() {
        let mut step: Option<(String, Vec<Rel>)> = None;
        for m in &cands {
            let rels: Vec<Rel> = remaining.iter().map(|&ci| int_rel(m, &calls[ci])).collect();
            if rels.iter().all(|r| *r != Rel::Unknown) && rels.contains(&Rel::Lt) {
                step = Some((format!("({}).toNat", m.render()), rels));
                break;
            }
        }
        if step.is_none() {
            for k in 0..params.len() {
                let Some((rank, rels)) = rank_of(k, &remaining) else {
                    continue;
                };
                if !(rels.iter().all(|r| *r != Rel::Unknown) && rels.contains(&Rel::Lt)) {
                    continue;
                }
                let name = format!("{fname}.rank{k}");
                let mut d = format!(
                    "/-- The rank of `{}`'s constructors in `{fname}`'s chain of recursive calls (termination). -/\ndef {name} : {} → Nat\n",
                    params[k], arg_tys[k]
                );
                for (h, r) in &rank {
                    if *r > 0 {
                        let ar = ctors.get(h).copied().unwrap_or(0);
                        let wild = " _".repeat(ar);
                        d.push_str(&format!("  | {h}{wild} => {r}\n"));
                    }
                }
                d.push_str("  | _ => 0\n\n");
                rank_defs.push_str(&d);
                rank_names.push(name.clone());
                step = Some((format!("{name} {}", params[k]), rels));
                break;
            }
        }
        let (m, rels) = step?;
        chosen.push(m);
        remaining = remaining
            .iter()
            .zip(&rels)
            .filter(|(_, r)| **r != Rel::Lt)
            .map(|(c, _)| *c)
            .collect();
    }
    let measure = if chosen.len() == 1 {
        chosen[0].clone()
    } else {
        format!("({})", chosen.join(", "))
    };
    Some(Plan {
        measure,
        rank_defs,
        rank_names,
        named,
    })
}

/// Facts from a defined partial hook (`match hr : hook args with | some var => …`); the prelude
/// lemmas `k2l_facts` applies give the same facts to Lean.
fn hook_facts(h: &str, args: &[L], var: &str, facts: &mut Vec<Fact>) {
    let len = |b: &L| compound_atom(&L::app("KPrelude.BytesHook.length", vec![b.clone()]));
    match (h, args) {
        ("KPrelude.BytesHook.get", [b, i]) => {
            if let Some(i) = lin(i) {
                facts.push(i.clone());
                facts.push(len(b).add(&i, -1).plus(-1));
            }
        }
        ("KPrelude.BytesHook.substr", [b, i, j]) => {
            if let (Some(i), Some(j)) = (lin(i), lin(j)) {
                facts.push(i.clone());
                facts.push(j.add(&i, -1));
                facts.push(len(b).add(&j, -1));
                let r = len(&L::Var(var.to_string()));
                facts.push(r.add(&j, -1).add(&i, 1));
                facts.push(j.add(&i, -1).add(&r, -1));
            }
        }
        ("KPrelude.IntHook.tdiv", [a, L::Raw(c)]) => {
            if let (Some(a), Some(c)) = (lin(a), int_lit(c))
                && c >= 2
            {
                // r = a / c for a ≥ 0 (`IntHook.tdiv_facts`): 0 ≤ r, and r < a for a ≥ 1
                let r = Lin::atom(var);
                if implied(&a, facts) {
                    facts.push(r.clone());
                }
                if implied(&a.plus(-1), facts) {
                    facts.push(a.add(&r, -1).plus(-1));
                }
            }
        }
        ("KPrelude.IntHook.shr", [a, L::Raw(c)]) => {
            if let (Some(a), Some(c)) = (lin(a), int_lit(c))
                && c >= 1
            {
                // r = a >> c for a ≥ 0 (`IntHook.shr_facts`): 0 ≤ r ≤ a, and r < a for a ≥ 1
                let r = Lin::atom(var);
                if implied(&a, facts) {
                    facts.push(r.clone());
                    facts.push(a.add(&r, -1));
                }
                if implied(&a.plus(-1), facts) {
                    facts.push(a.add(&r, -1).plus(-1));
                }
            }
        }
        ("KPrelude.IntHook.emod", [_, L::Raw(c)]) => {
            if let Some(c) = int_lit(c)
                && c > 0
            {
                let r = Lin::atom(var);
                facts.push(r.clone());
                facts.push(Lin::konst(c - 1).add(&r, -1));
            } else if c
                .trim_start_matches('(')
                .split(' ')
                .next()
                .is_some_and(|d| !d.is_empty() && d.chars().all(|x| x.is_ascii_digit()) && d != "0")
            {
                // a modulus too large for these coefficients: the remainder is not negative
                facts.push(Lin::atom(var));
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------------------------
// Linear integer arithmetic: entailment by Fourier–Motzkin elimination.
//
// Every atom is an integer (a parameter, a bound variable, a rendered integer term such as
// `KPrelude.BytesHook.length x0`), and a fact is `lin ≥ 0`. Elimination over the rationals,
// with each fact divided by the gcd of its coefficients and its constant rounded down (sound for
// integers), derives only consequences of the facts; so `infeasible` is never wrong when it says
// yes, and an entailment it finds is one `omega` finds too. It is a heuristic for choosing
// measures and lemma statements: Lean proves both.

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// `lin ≥ 0` divided by the gcd of its coefficients, the constant rounded down.
fn tighten(l: &Lin) -> Lin {
    let g = l.terms.values().fold(0, |g, v| gcd(g, *v));
    if g <= 1 {
        return l.clone();
    }
    Lin {
        terms: l.terms.iter().map(|(a, v)| (a.clone(), v / g)).collect(),
        c: l.c.div_euclid(g),
    }
}

/// The largest system elimination may build; beyond it, `infeasible` gives up (answers no).
const FM_LIMIT: usize = 600;

/// Whether the facts (each `lin ≥ 0`) have no integer solution, as far as elimination finds.
fn infeasible(facts: &[Lin]) -> bool {
    infeasible_keep(facts, &BTreeSet::new()).is_none()
}

/// Eliminate every atom not in `keep`; `None` when the facts are contradictory, else the facts
/// left over the kept atoms (`Some(vec![])` when elimination gave up).
fn infeasible_keep(facts: &[Lin], keep: &BTreeSet<String>) -> Option<Vec<Lin>> {
    let mut sys: Vec<Lin> = facts.iter().map(tighten).collect();
    loop {
        if sys.iter().any(|f| f.terms.is_empty() && f.c < 0) {
            return None;
        }
        // the tightest fact per left-hand side
        let mut best: BTreeMap<Vec<(String, i128)>, i128> = BTreeMap::new();
        for f in &sys {
            if f.terms.is_empty() {
                continue;
            }
            let k: Vec<(String, i128)> = f.terms.iter().map(|(a, v)| (a.clone(), *v)).collect();
            let e = best.entry(k).or_insert(f.c);
            *e = (*e).min(f.c);
        }
        // `a + c ≥ 0` and `-a + d ≥ 0` with `c + d < 0`: contradiction
        for (k, c) in &best {
            let neg: Vec<(String, i128)> = k.iter().map(|(a, v)| (a.clone(), -v)).collect();
            if let Some(d) = best.get(&neg)
                && c + d < 0
            {
                return None;
            }
        }
        sys = best
            .into_iter()
            .map(|(k, c)| Lin {
                terms: k.into_iter().collect(),
                c,
            })
            .collect();
        // the atom to eliminate: fewest new facts
        let mut atoms: BTreeMap<&String, (usize, usize)> = BTreeMap::new();
        for f in &sys {
            for (a, v) in &f.terms {
                if keep.contains(a) {
                    continue;
                }
                let e = atoms.entry(a).or_insert((0, 0));
                if *v > 0 { e.0 += 1 } else { e.1 += 1 }
            }
        }
        let Some((x, _)) = atoms
            .iter()
            .min_by_key(|(_, (p, n))| (p * n) as i128 - (*p + *n) as i128)
            .map(|(a, pn)| ((*a).clone(), *pn))
        else {
            return Some(sys);
        };
        let (mut pos, mut neg, mut rest) = (Vec::new(), Vec::new(), Vec::new());
        for f in sys {
            match f.terms.get(&x).copied() {
                Some(v) if v > 0 => pos.push((v, f)),
                Some(v) => neg.push((-v, f)),
                None => rest.push(f),
            }
        }
        for (p, fp) in &pos {
            for (n, fn_) in &neg {
                // n·fp + p·fn eliminates x
                rest.push(tighten(&fp.scale(*n).add(fn_, *p)));
            }
        }
        if rest.len() > FM_LIMIT {
            return Some(vec![]);
        }
        sys = rest;
    }
}

/// `g ≥ 0` follows from the facts.
fn entails(facts: &[Lin], g: &Lin) -> bool {
    if let Some(c) = g.as_const() {
        return c >= 0;
    }
    let mut f = facts.to_vec();
    f.push(g.scale(-1).plus(-1));
    infeasible(&f)
}

/// The facts at a program point: a conjunction, and disjunctions (each a list of alternative
/// conjunctions) from conditions such as a failed `andBool` guard or a conditional hook fact.
#[derive(Clone, Debug, Default)]
pub(crate) struct Facts {
    base: Vec<Lin>,
    alts: Vec<Vec<Vec<Lin>>>,
}

/// The number of alternative combinations a check explores at most.
const ALT_LIMIT: usize = 256;

impl Facts {
    fn push(&mut self, f: Lin) {
        self.base.push(f);
    }
    fn extend(&mut self, fs: impl IntoIterator<Item = Lin>) {
        self.base.extend(fs);
    }
    /// A disjunction of conjunctions (a single alternative is a conjunction).
    fn push_dnf(&mut self, d: Vec<Vec<Lin>>) {
        match d.len() {
            0 => self.base.push(Lin::konst(-1)),
            1 => self.base.extend(d.into_iter().next().unwrap()),
            _ => self.alts.push(d),
        }
    }
    fn and(&self, o: &Facts) -> Facts {
        let mut r = self.clone();
        r.base.extend(o.base.iter().cloned());
        r.alts.extend(o.alts.iter().cloned());
        r
    }
    /// Every feasible combination of alternatives, as one conjunction each (`None` past
    /// `ALT_LIMIT`); combinations found contradictory on the way are dropped.
    fn cases(&self) -> Option<Vec<Vec<Lin>>> {
        let mut out = vec![self.base.clone()];
        for d in &self.alts {
            let mut next = Vec::new();
            for c in &out {
                for alt in d {
                    let mut c2 = c.clone();
                    c2.extend(alt.iter().cloned());
                    if alt.is_empty() || !infeasible(&c2) {
                        next.push(c2);
                    }
                }
            }
            if next.len() > ALT_LIMIT {
                return None;
            }
            out = next;
        }
        Some(out)
    }
    /// `g ≥ 0` in every case.
    fn entails(&self, g: &Lin) -> bool {
        match self.cases() {
            Some(cs) => cs.iter().all(|c| entails(c, g)),
            None => entails(&self.base, g),
        }
    }
    /// The facts with their atoms' variables substituted.
    fn subst(&self, m: &BTreeMap<String, L>) -> Option<Facts> {
        let sub =
            |c: &Vec<Lin>| -> Option<Vec<Lin>> { c.iter().map(|x| subst_lin(x, m)).collect() };
        Some(Facts {
            base: sub(&self.base)?,
            alts: self
                .alts
                .iter()
                .map(|d| d.iter().map(sub).collect::<Option<Vec<_>>>())
                .collect::<Option<Vec<_>>>()?,
        })
    }

    fn infeasible(&self) -> bool {
        match self.cases() {
            Some(cs) => cs.iter().all(|c| infeasible(c)),
            None => infeasible(&self.base),
        }
    }
}

/// What a set of conjunctions (alternatives) says about `dir`: its least value.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Bound {
    /// No alternative is feasible.
    Never,
    /// Unbounded below in some alternative.
    None,
    Lower(i128),
}

/// The least value of `dir` over the alternatives (each a conjunction of facts).
fn lower_bound(alts: &[Vec<Lin>], dir: &Lin) -> Bound {
    let t = "\u{1}t".to_string();
    let keep: BTreeSet<String> = [t.clone()].into_iter().collect();
    let mut best: Option<i128> = None;
    let mut any = false;
    for c in alts {
        let mut f = c.clone();
        let tl = Lin::atom(&t);
        f.push(tl.add(dir, -1));
        f.push(dir.add(&tl, -1));
        let Some(left) = infeasible_keep(&f, &keep) else {
            continue;
        };
        any = true;
        // k·t + c ≥ 0 with k > 0: t ≥ ⌈-c/k⌉
        let lb = left
            .iter()
            .filter_map(|l| {
                let k = *l.terms.get(&t)?;
                (k > 0 && l.terms.len() == 1).then(|| (-l.c + k - 1).div_euclid(k))
            })
            .max();
        match lb {
            Some(v) => best = Some(best.map_or(v, |b: i128| b.min(v))),
            None => return Bound::None,
        }
    }
    match (any, best) {
        (false, _) => Bound::Never,
        (true, Some(v)) => Bound::Lower(v),
        (true, None) => Bound::None,
    }
}

// ---------------------------------------------------------------------------------------------
// The definition as the planner sees it.

/// A generated function: its signature and lowered equations (`funcs::generate_with`).
#[derive(Clone, Debug)]
pub struct FnDef {
    pub lean: String,
    pub params: Vec<String>,
    pub arg_tys: Vec<String>,
    pub result: String,
    /// total (its result is not `Option`-valued)
    pub pure: bool,
    pub recursive: bool,
    /// the equations in cascade order: steps, number of left-hand-side steps, result
    pub eqs: Vec<(Vec<Step>, usize, L)>,
    /// the definitions to unfold (`unfold … at h`); empty for a recursive function (`f.eq_def`)
    pub unfold: Vec<String>,
    /// its `termination_by` measure, for a recursive function that has one
    pub measure: Option<String>,
    /// it uses a parameter of the library (`[Hooks]`), directly or through a callee
    pub hooks: bool,
}

/// What the planner knows of the definition, and the lemmas it has derived so far.
pub struct Ctx {
    pub fns: BTreeMap<String, FnDef>,
    /// constructor paths, with the Lean type of each argument
    pub ctors: BTreeMap<String, Vec<String>>,
    /// constructor paths that are the only value of their sort (a pattern of variables under
    /// them is irrefutable)
    pub sole: BTreeSet<String>,
    /// injection heads (`S.inj_L`), with whether the leaf `L` is a builtin sort
    pub injs: BTreeMap<String, bool>,
    /// the Lean types of builtin sorts
    pub builtin: BTreeSet<String>,
    /// the arity-indexed universe, where `KPrelude.Shape` is defined (`Term.shape`)
    pub arity: bool,
    /// the library has parameters (`variable [Hooks]`)
    pub has_hooks: bool,
    lemmas: std::cell::RefCell<Lemmas>,
}

/// A derived lemma about a generated function.
#[derive(Clone, Debug)]
struct Lemma {
    name: String,
    /// facts over the function's parameters `x0, x1, …`, the pattern's fields and `r`
    facts: Vec<Lin>,
    /// the result pattern (`r`, or a constructor pattern over fields `a0, a1, …`)
    pattern: L,
    /// the function, and the definitions its proof unfolds
    fname: String,
    unfolds: Vec<String>,
}

#[derive(Default)]
struct Lemmas {
    /// facts of a function's result: (function, rendered pattern) → lemma
    out: BTreeMap<(String, String), Option<Lemma>>,
    /// shape bounds: (function, parameter) → lemma
    shape: BTreeMap<(String, usize), Option<Lemma>>,
    /// derivations in progress (a cycle gives nothing)
    busy: BTreeSet<String>,
    /// the text of each lemma and the lemmas its proof uses
    text: BTreeMap<String, (String, Vec<String>)>,
    /// lemmas already written out
    emitted: BTreeSet<String>,
    /// whether `Term.shape` is needed
    shape_used: bool,
    /// the lemmas the group being planned has used
    used: BTreeSet<String>,
    /// the cache key of each result lemma, by name
    by_name: BTreeMap<String, (String, String)>,
}

impl Ctx {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        fns: BTreeMap<String, FnDef>,
        ctors: BTreeMap<String, Vec<String>>,
        sole: BTreeSet<String>,
        injs: BTreeMap<String, bool>,
        builtin: BTreeSet<String>,
        arity: bool,
        has_hooks: bool,
    ) -> Ctx {
        Ctx {
            fns,
            ctors,
            sole,
            injs,
            builtin,
            arity,
            has_hooks,
            lemmas: Default::default(),
        }
    }

    /// Record a function as it is generated (callees first).
    pub fn add(&mut self, f: FnDef) {
        self.fns.insert(f.lean.clone(), f);
    }

    /// Whether some lemma or measure uses `KPrelude.Shape` (the caller emits `Term.shape`).
    pub fn shape_used(&self) -> bool {
        self.lemmas.borrow().shape_used
    }

    /// The text of lemmas `names` and of the lemmas their proofs use, not written before, in an
    /// order where each comes after the lemmas it uses.
    fn take(&self, names: &[String]) -> String {
        let mut lm = self.lemmas.borrow_mut();
        let mut out = String::new();
        fn go(n: &str, lm: &mut Lemmas, out: &mut String) {
            if lm.emitted.contains(n) {
                return;
            }
            lm.emitted.insert(n.to_string());
            let Some((t, deps)) = lm.text.get(n).cloned() else {
                return;
            };
            for d in &deps {
                go(d, lm, out);
            }
            out.push_str(&t);
            out.push('\n');
        }
        for n in names {
            go(n, &mut lm, &mut out);
        }
        out
    }

    fn is_int(&self, ty: &str) -> bool {
        ty == "SortInt" || ty == "Int"
    }
}

/// Simultaneous substitution of variables.
fn subst_sim(l: &L, s: &BTreeMap<String, L>) -> L {
    match l {
        L::Var(v) => s.get(v).cloned().unwrap_or_else(|| l.clone()),
        L::Raw(_) => l.clone(),
        L::Typed(e, t) => L::Typed(Box::new(subst_sim(e, s)), t.clone()),
        L::App(h, args) => L::App(h.clone(), args.iter().map(|a| subst_sim(a, s)).collect()),
    }
}

/// A linear form with its atoms' variables substituted (`None` when an atom's term is no
/// longer linear).
fn subst_lin(f: &Lin, s: &BTreeMap<String, L>) -> Option<Lin> {
    let mut out = Lin::konst(f.c);
    for (a, k) in &f.terms {
        let t = subst_sim(&atom_term(a), s);
        out = out.add(&lin(&t)?, *k);
    }
    Some(out)
}

/// The atoms of a set of facts.
fn atoms_of(fs: &[Lin]) -> BTreeSet<String> {
    fs.iter().flat_map(|f| f.terms.keys().cloned()).collect()
}

/// The facts a Boolean condition gives when it holds (`pos`) or fails, as a disjunction of
/// conjunctions (`[[]]`: nothing known; `[]`: impossible).
fn cond_dnf(c: &L, pos: bool) -> Vec<Vec<Lin>> {
    let L::App(h, args) = c else {
        return vec![vec![]];
    };
    match (h.as_str(), args.len(), pos) {
        ("KPrelude.BoolHook.not", 1, _) => cond_dnf(&args[0], !pos),
        ("KPrelude.BoolHook.and", 2, true) | ("KPrelude.BoolHook.or", 2, false) => {
            let (a, b) = (cond_dnf(&args[0], pos), cond_dnf(&args[1], pos));
            let mut out = Vec::new();
            for x in &a {
                for y in &b {
                    out.push([x.clone(), y.clone()].concat());
                }
            }
            out
        }
        ("KPrelude.BoolHook.and", 2, false) | ("KPrelude.BoolHook.or", 2, true) => {
            [cond_dnf(&args[0], pos), cond_dnf(&args[1], pos)].concat()
        }
        _ => {
            let f = cond_facts(c, pos);
            // `=/=Int` holding, `==Int` failing: a disequality
            if f.is_empty()
                && let ("KPrelude.IntHook.ne", true) | ("KPrelude.IntHook.eq", false) =
                    (h.as_str(), pos)
                && let (Some(a), Some(b)) = (lin(&args[0]), lin(&args[1]))
            {
                return vec![vec![a.add(&b, -1).plus(-1)], vec![b.add(&a, -1).plus(-1)]];
            }
            vec![f]
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Facts about generated functions, derived from their equations and proved by Lean.

/// The outcome of matching a pattern against a term.
enum Unif {
    /// the pattern's variables are bound to subterms (in the map given to `unify`)
    Match,
    /// different constructors: the term never matches
    Clash,
    /// not known (a variable, a call)
    Unknown,
}

/// A `Lean` fact `lin ≥ 0`, written with an integer literal first (so that the relation is at
/// `Int`, whatever the sort abbreviations of its atoms).
fn render_fact(f: &Lin) -> String {
    let neg = f.terms.values().all(|v| *v < 0);
    if neg {
        // -e + c ≥ 0: c ≥ e
        let e = Lin {
            terms: f.terms.clone(),
            c: 0,
        }
        .scale(-1);
        format!("({} : Int) ≥ {}", f.c, e.render())
    } else {
        let e = Lin {
            terms: f.terms.clone(),
            c: 0,
        };
        format!("({} : Int) ≤ {}", -f.c, e.render())
    }
}

/// The directions of the template facts over `targets`: every sum of one to three distinct
/// targets with coefficients ±1 (two at most past seven targets).
fn directions(targets: &[String]) -> Vec<Lin> {
    let n = targets.len();
    let max = if n > 7 { 2 } else { 3 };
    let mut out = Vec::new();
    for mask in 1u32..(1 << n.min(16)) {
        let k = mask.count_ones() as usize;
        if k > max {
            continue;
        }
        let idx: Vec<usize> = (0..n).filter(|i| mask & (1 << i) != 0).collect();
        for signs in 0u32..(1 << k) {
            let mut l = Lin::konst(0);
            for (j, i) in idx.iter().enumerate() {
                let s = if signs & (1 << j) != 0 { -1 } else { 1 };
                l = l.add(&Lin::atom(&targets[*i]), s);
            }
            out.push(l);
        }
    }
    out
}

/// The facts of `dirs` that hold in every case, each with its best constant, without those the
/// others imply.
fn template_facts(cases: &[Vec<Lin>], dirs: &[Lin]) -> Vec<Lin> {
    let mut found: Vec<Lin> = Vec::new();
    for d in dirs {
        if let Bound::Lower(v) = lower_bound(cases, d) {
            found.push(d.plus(-v));
        }
    }
    found.sort_by_key(|f| f.terms.len());
    let mut kept: Vec<Lin> = Vec::new();
    for f in found {
        if !entails(&kept, &f) {
            kept.push(f);
        }
    }
    // drop those the later ones made redundant
    let mut i = 0;
    while i < kept.len() {
        let others: Vec<Lin> = kept
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != i)
            .map(|(_, f)| f.clone())
            .collect();
        if entails(&others, &kept[i]) {
            kept.remove(i);
        } else {
            i += 1;
        }
    }
    kept
}

/// The facts of a hook application that hold under a condition (as a disjunction), for
/// `KPrelude.IntHook.tdiv_mul_facts` and `tdiv_mul_divisor_facts`: `a * n / m` is smaller than
/// `a` in absolute value when `n` is smaller than `m` (or `a` is zero), and `|i| ≤ |d * i|`.
fn hook_dnf(h: &str, args: &[L], var: &str, facts: &mut Facts) {
    if h != "KPrelude.IntHook.tdiv" || args.len() != 2 {
        return;
    }
    let abs = abs_atom;
    let r = L::Var(var.to_string());
    if let L::App(m, ma) = &args[0]
        && m == "KPrelude.IntHook.mul"
        && ma.len() == 2
    {
        let (a, n, m) = (&ma[0], &ma[1], &args[1]);
        // ¬(|n| < |m|) ∨ |r| < |a| ∨ a = 0
        let mut d = vec![
            vec![abs(n).add(&abs(m), -1)],
            vec![abs(a).add(&abs(&r), -1).plus(-1)],
        ];
        if let Some(al) = lin(a) {
            d.push(vec![al.clone(), al.scale(-1)]);
        }
        facts.push_dnf(d);
    }
    if let L::App(m, ma) = &args[1]
        && m == "KPrelude.IntHook.mul"
        && ma.len() == 2
    {
        facts.push(abs(&args[1]).add(&abs(&ma[1]), -1));
        facts.push(abs(&args[1]).add(&abs(&ma[0]), -1));
    }
}

/// `|e|` as an integer atom.
fn abs_atom(l: &L) -> Lin {
    compound_atom(&L::Typed(
        Box::new(L::app("Int.natAbs", vec![l.clone()])),
        "Int".into(),
    ))
}

/// `|e| ≥ e`, `|e| ≥ -e` for each absolute-value atom of the facts, and `|e| = e ∨ |e| = -e`.
fn abs_facts(atoms: &BTreeSet<String>, facts: &mut Facts) {
    for a in atoms {
        let L::Typed(inner, ty) = atom_term(a) else {
            continue;
        };
        let L::App(h, args) = *inner else { continue };
        if ty != "Int" || h != "Int.natAbs" || args.len() != 1 {
            continue;
        }
        let x = Lin::atom(a);
        facts.push(x.clone());
        if let Some(e) = lin(&args[0]) {
            facts.push(x.add(&e, -1));
            facts.push(x.add(&e, 1));
            facts.push_dnf(vec![vec![e.add(&x, -1)], vec![e.scale(-1).add(&x, -1)]]);
        }
    }
}

impl Ctx {
    /// Match a pattern against a term (`Unknown` when the term is a variable).
    fn unify(&self, pat: &L, t: &L, out: &mut BTreeMap<String, L>) -> Unif {
        if matches!(t, L::Var(_)) && !matches!(pat, L::Var(_)) {
            return Unif::Unknown;
        }
        self.unify_in(pat, t, out)
    }

    fn unify_in(&self, pat: &L, t: &L, out: &mut BTreeMap<String, L>) -> Unif {
        match (pat, t) {
            (L::Var(v), _) => {
                out.insert(v.clone(), t.clone());
                Unif::Match
            }
            (L::App(h, ps), L::App(g, ts)) => {
                if h != g {
                    if self.ctors.contains_key(h) && self.ctors.contains_key(g) {
                        return Unif::Clash;
                    }
                    return Unif::Unknown;
                }
                if ps.len() != ts.len() {
                    return Unif::Unknown;
                }
                for (p, a) in ps.iter().zip(ts) {
                    match self.unify_in(p, a, out) {
                        Unif::Match => {}
                        other => return other,
                    }
                }
                Unif::Match
            }
            (L::Raw(a), L::Raw(b)) if a == b => Unif::Match,
            // a pattern part against a variable of the term: it may match, and the pattern's
            // variables under it are not bound (nothing is known of them)
            (L::App(..), L::Var(_)) => Unif::Match,
            _ => Unif::Unknown,
        }
    }

    /// The field types of a pattern's variables (by the constructor argument they stand at).
    fn field_types(&self, pat: &L, out: &mut BTreeMap<String, String>) {
        if let L::App(h, args) = pat {
            let tys = self.ctors.get(h);
            for (i, a) in args.iter().enumerate() {
                match a {
                    L::Var(v) => {
                        if let Some(t) = tys.and_then(|t| t.get(i)) {
                            out.insert(v.clone(), t.clone());
                        }
                    }
                    _ => self.field_types(a, out),
                }
            }
        }
    }

    /// Each way `f` returns a value: the facts on the way (over its parameters and the variables
    /// it binds), the value, and the variables bound to calls of other functions.
    #[allow(clippy::type_complexity)]
    fn paths(
        &self,
        f: &FnDef,
        deps: &mut Vec<String>,
    ) -> Vec<(Facts, L, BTreeMap<String, (String, Vec<L>)>)> {
        let mut out = Vec::new();
        let mut negs: Vec<Vec<Vec<Lin>>> = Vec::new();
        for (steps, lhs_len, rhs) in &f.eqs {
            let mut facts = Facts::default();
            for d in &negs {
                facts.push_dnf(d.clone());
            }
            let mut alias: BTreeMap<String, L> = BTreeMap::new();
            let mut binds: BTreeMap<String, (String, Vec<L>)> = BTreeMap::new();
            for s in steps {
                match s {
                    Step::Cond { cond, .. } => {
                        facts.push_dnf(cond_dnf(&subst_sim(cond, &alias), true))
                    }
                    Step::CondEq { lhs, rhs, .. } => {
                        let (l, r) = (subst_sim(lhs, &alias), subst_sim(rhs, &alias));
                        match &r {
                            L::Raw(b) if b == "true" || b == "false" => {
                                facts.push_dnf(cond_dnf(&l, b == "true"))
                            }
                            _ => {
                                if let (Some(a), Some(b)) = (lin(&l), lin(&r)) {
                                    facts.push(a.add(&b, -1));
                                    facts.push(b.add(&a, -1));
                                }
                            }
                        }
                    }
                    Step::Destruct {
                        scrut,
                        pat: L::Var(y),
                        ..
                    } => {
                        let t = alias.get(scrut).cloned().unwrap_or(L::Var(scrut.clone()));
                        alias.insert(y.clone(), t);
                    }
                    Step::Bind { expr, var, .. } => {
                        let e = subst_sim(expr, &alias);
                        if let L::App(h, args) = &e {
                            // the facts so far, for the hook's conditional facts
                            let mut v = facts.base.clone();
                            let n0 = v.len();
                            hook_facts(h, args, var, &mut v);
                            facts.extend(v.split_off(n0));
                            hook_dnf(h, args, var, &mut facts);
                            if let Some(g) = self.fns.get(h)
                                && !g.recursive
                                && *h != f.lean
                                && let Some(lm) = self.out_lemma(h, &L::Var("r".into()))
                            {
                                let mut m: BTreeMap<String, L> =
                                    g.params.iter().cloned().zip(args.iter().cloned()).collect();
                                m.insert("r".into(), L::Var(var.clone()));
                                if let Some(fs) = lm
                                    .facts
                                    .iter()
                                    .map(|x| subst_lin(x, &m))
                                    .collect::<Option<Vec<_>>>()
                                {
                                    facts.extend(fs);
                                    deps.push(lm.name.clone());
                                }
                            }
                            binds.insert(var.clone(), (h.clone(), args.clone()));
                        }
                    }
                    _ => {}
                }
            }
            out.push((facts, subst_sim(rhs, &alias), binds));
            let guard_only = *lhs_len > 0
                && steps[..*lhs_len]
                    .iter()
                    .all(|s| matches!(s, Step::Cond { .. } | Step::CondEq { .. }));
            if guard_only {
                let mut d: Vec<Vec<Lin>> = Vec::new();
                for s in &steps[..*lhs_len] {
                    match s {
                        Step::Cond { cond, .. } => d.extend(cond_dnf(cond, false)),
                        Step::CondEq {
                            lhs,
                            rhs: L::Raw(b),
                            ..
                        } if b == "true" || b == "false" => d.extend(cond_dnf(lhs, b != "true")),
                        _ => d.push(vec![]),
                    }
                }
                negs.push(d);
            }
            if *lhs_len == 0 {
                break;
            }
        }
        out
    }

    /// A value, with the calls of total non-recursive functions at its head replaced by their
    /// own values (their variables renamed apart): each way, with the facts on it.
    #[allow(clippy::type_complexity)]
    fn expand(
        &self,
        t: &L,
        depth: usize,
        unfolds: &mut Vec<String>,
        deps: &mut Vec<String>,
    ) -> Option<Vec<(Facts, L, BTreeMap<String, (String, Vec<L>)>)>> {
        let none = || Some(vec![(Facts::default(), t.clone(), BTreeMap::new())]);
        let L::App(h, args) = t else { return none() };
        let Some(g) = self.fns.get(h) else {
            return none();
        };
        if !g.pure || g.recursive || depth == 0 || args.len() != g.params.len() {
            return none();
        }
        let g = g.clone();
        unfolds.extend(g.unfold.iter().cloned());
        let tag = format!("{}_", names_tag(&g.lean));
        let mut out = Vec::new();
        for (facts, v, binds) in self.paths(&g, deps) {
            // the callee's own variables, renamed apart; its parameters, the arguments
            let mut vars = BTreeSet::new();
            for c in std::iter::once(&facts.base).chain(facts.alts.iter().flatten()) {
                for a in atoms_of(c) {
                    vars.extend(atom_vars(&a));
                }
            }
            vars_of(&v, &mut vars);
            vars.extend(binds.keys().cloned());
            let mut m: BTreeMap<String, L> = BTreeMap::new();
            for x in vars {
                if !g.params.contains(&x) {
                    m.insert(x.clone(), L::Var(format!("{tag}{x}")));
                }
            }
            for (p, a) in g.params.iter().zip(args) {
                m.insert(p.clone(), a.clone());
            }
            let facts = facts.subst(&m)?;
            let v = subst_sim(&v, &m);
            let binds: BTreeMap<String, (String, Vec<L>)> = binds
                .into_iter()
                .map(|(k, (h, a))| {
                    (
                        format!("{tag}{k}"),
                        (h, a.iter().map(|x| subst_sim(x, &m)).collect()),
                    )
                })
                .collect();
            for (f2, v2, b2) in self.expand(&v, depth - 1, unfolds, deps)? {
                let mut b = binds.clone();
                b.extend(b2);
                out.push((facts.and(&f2), v2, b));
            }
        }
        Some(out)
    }

    /// The facts at each way `f` returns a value matching `pat` (`r`, or a constructor pattern
    /// over variables): one `Facts` per path; `None` when a path's value is not understood.
    fn leaves(
        &self,
        f: &FnDef,
        pat: &L,
        deps: &mut Vec<String>,
        unfolds: &mut Vec<String>,
    ) -> Option<Vec<Facts>> {
        let mut out = Vec::new();
        let res_int = self.is_int(&f.result);
        let mut ftys = BTreeMap::new();
        self.field_types(pat, &mut ftys);
        for (facts0, rhs0, binds0) in self.paths(f, deps) {
            for (fx, rhs, bx) in self.expand(&rhs0, 3, unfolds, deps)? {
                let mut facts = facts0.and(&fx);
                let mut binds = binds0.clone();
                binds.extend(bx);
                match pat {
                    L::Var(r) => {
                        if res_int {
                            let l = lin(&rhs)?;
                            let rl = Lin::atom(r);
                            facts.push(rl.add(&l, -1));
                            facts.push(l.add(&rl, -1));
                        }
                    }
                    _ => {
                        let mut m = BTreeMap::new();
                        match self.unify(pat, &rhs, &mut m) {
                            Unif::Match => {
                                for (v, t) in &m {
                                    if ftys.get(v).is_some_and(|ty| self.is_int(ty)) {
                                        let l = lin(t)?;
                                        let vl = Lin::atom(v);
                                        facts.push(vl.add(&l, -1));
                                        facts.push(l.add(&vl, -1));
                                    }
                                }
                            }
                            Unif::Clash => continue,
                            Unif::Unknown => {
                                // the value of a callee
                                let L::Var(v) = &rhs else { return None };
                                let (h, args) = binds.get(v)?;
                                let g = self.fns.get(h)?;
                                if g.recursive {
                                    return None;
                                }
                                let lm = self.out_lemma(h, pat)?;
                                let mut m: BTreeMap<String, L> =
                                    g.params.iter().cloned().zip(args.iter().cloned()).collect();
                                for v in ftys.keys() {
                                    m.insert(v.clone(), L::Var(v.clone()));
                                }
                                let fs = lm
                                    .facts
                                    .iter()
                                    .map(|x| subst_lin(x, &m))
                                    .collect::<Option<Vec<_>>>()?;
                                facts.extend(fs);
                                deps.push(lm.name.clone());
                            }
                        }
                    }
                }
                out.push(self.close_deps(&facts, &[], deps));
            }
        }
        Some(out)
    }

    /// The facts `f`'s result satisfies when it matches `pat` (`r`: facts of its arguments, and of
    /// `r` when `f` is integer-valued; a constructor pattern over `a0, a1, …`: facts of its
    /// integer fields), as a lemma `@[k2l_fact]` proved by unfolding `f`. `None` when nothing
    /// is known.
    fn out_lemma(&self, fname: &str, pat: &L) -> Option<Lemma> {
        let key = (fname.to_string(), pat.render());
        if let Some(l) = self.lemmas.borrow().out.get(&key) {
            return l.clone();
        }
        let busy = format!("out {fname} {}", key.1);
        if !self.lemmas.borrow_mut().busy.insert(busy.clone()) {
            return None;
        }
        let r = self.derive_out(fname, pat);
        if std::env::var_os("K2LEAN_TERM_DEBUG").is_some() {
            eprintln!(
                "  out_lemma {fname} {}: {:?}",
                pat.render(),
                r.as_ref()
                    .map(|l| l.facts.iter().map(render_fact).collect::<Vec<_>>())
            );
        }
        let mut lm = self.lemmas.borrow_mut();
        lm.busy.remove(&busy);
        lm.out.insert(key, r.clone());
        r
    }

    fn derive_out(&self, fname: &str, pat: &L) -> Option<Lemma> {
        let f = self.fns.get(fname)?.clone();
        if f.recursive {
            return None;
        }
        let mut deps = Vec::new();
        let mut unfolds = Vec::new();
        let leaves = self.leaves(&f, pat, &mut deps, &mut unfolds)?;
        let mut cases = Vec::new();
        for l in &leaves {
            cases.extend(l.cases()?);
        }
        if cases.is_empty() {
            return None;
        }
        // the atoms facts may be stated over: integer parameters, terms over parameters, the
        // integer fields (or `r`)
        let params: BTreeSet<&str> = f.params.iter().map(|p| p.as_str()).collect();
        let mut targets: Vec<String> = Vec::new();
        for (p, t) in f.params.iter().zip(&f.arg_tys) {
            if self.is_int(t) {
                targets.push(p.clone());
            }
        }
        let mut ftys = BTreeMap::new();
        self.field_types(pat, &mut ftys);
        match pat {
            L::Var(r) if self.is_int(&f.result) => targets.push(r.clone()),
            _ => {
                for (v, t) in &ftys {
                    if self.is_int(t) {
                        targets.push(v.clone());
                    }
                }
            }
        }
        for c in &cases {
            for a in atoms_of(c) {
                if !targets.contains(&a)
                    && a.contains(' ')
                    && atom_vars(&a).iter().all(|v| params.contains(v.as_str()))
                    && !atom_vars(&a).is_empty()
                {
                    targets.push(a);
                }
            }
        }
        let facts = template_facts(&cases, &directions(&targets));
        if facts.is_empty() {
            return None;
        }
        let n = {
            let lm = self.lemmas.borrow();
            lm.by_name
                .values()
                .filter(|(g, p)| g == fname && !p.starts_with(|c: char| c.is_lowercase()))
                .count()
        };
        let name = match pat {
            L::Var(_) if f.pure => format!("{fname}.k2l_range"),
            L::Var(_) => format!("{fname}.k2l_out"),
            _ => format!("{fname}.k2l_out_{}", n + 1),
        };
        let mut f2 = f.clone();
        for u in unfolds {
            if !f2.unfold.contains(&u) {
                f2.unfold.push(u);
            }
        }
        let lm = Lemma {
            name: name.clone(),
            facts,
            pattern: pat.clone(),
            fname: fname.to_string(),
            unfolds: f2.unfold.clone(),
        };
        let text = self.out_text(&f2, &lm, &ftys);
        self.lemmas
            .borrow_mut()
            .by_name
            .insert(name.clone(), (fname.to_string(), pat.render()));
        deps.sort();
        deps.dedup();
        self.lemmas.borrow_mut().text.insert(name, (text, deps));
        Some(lm)
    }

    /// The constructor and injection names of terms, for `simp` to unfold.
    fn ctor_names(&self, l: &L, out: &mut BTreeSet<String>) {
        if let L::App(h, args) = l {
            if self.ctors.contains_key(h) || self.injs.contains_key(h) {
                out.insert(h.clone());
            }
            for a in args {
                self.ctor_names(a, out);
            }
        }
    }

    fn fn_ctor_names(&self, f: &FnDef, out: &mut BTreeSet<String>) {
        for (steps, _, rhs) in &f.eqs {
            self.ctor_names(rhs, out);
            for s in steps {
                match s {
                    Step::Destruct { pat, .. } => self.ctor_names(pat, out),
                    Step::Bind { expr, .. } => self.ctor_names(expr, out),
                    Step::CondEq { lhs, rhs, .. } => {
                        self.ctor_names(lhs, out);
                        self.ctor_names(rhs, out);
                    }
                    _ => {}
                }
            }
        }
    }

    /// The `simp` names of constructors: the reducible definitions of the arity-indexed universe
    /// and the injectivity lemmas of the family's constructors they use, the constructors'
    /// injectivity lemmas otherwise.
    fn simp_names(&self, names: BTreeSet<String>) -> Vec<String> {
        if self.arity {
            let mut inj: BTreeSet<String> = BTreeSet::new();
            for n in &names {
                if let Some(tys) = self.ctors.get(n) {
                    inj.insert(format!("Term.c{}.injEq", tys.len()));
                    for t in tys {
                        if self.builtin.contains(t) {
                            inj.insert(format!("Term.«b_{t}».injEq"));
                        }
                    }
                } else if self.injs.contains_key(n) {
                    inj.insert("Term.inj.injEq".into());
                }
            }
            let mut out: Vec<String> = names.into_iter().collect();
            if !inj.is_empty() {
                out.extend(inj);
                out.push("heq_eq_eq".into());
            }
            return out;
        }
        names
            .into_iter()
            .filter(|n| {
                self.injs.contains_key(n) || self.ctors.get(n).is_some_and(|a| !a.is_empty())
            })
            .map(|n| format!("{n}.injEq"))
            .collect()
    }

    /// `omit [Hooks] in` before a declaration that does not use the library's parameters.
    fn omit(&self, uses: bool) -> &'static str {
        if self.has_hooks && !uses {
            "omit [Hooks] in\n"
        } else {
            ""
        }
    }

    fn unfold_text(&self, f: &FnDef, h: &str) -> String {
        if f.recursive {
            format!("rw [{}.eq_def] at {h}", f.lean)
        } else {
            format!("unfold {} at {h}", f.unfold.join(" "))
        }
    }

    fn out_text(&self, f: &FnDef, lm: &Lemma, ftys: &BTreeMap<String, String>) -> String {
        let mut simps: BTreeSet<String> = BTreeSet::new();
        self.fn_ctor_names(f, &mut simps);
        self.ctor_names(&lm.pattern, &mut simps);
        let simps: Vec<String> = self.simp_names(simps);
        let xs = f.params.join(" ");
        let facts: Vec<String> = lm.facts.iter().map(render_fact).collect();
        let doc = format!(
            "/-- What `{}` returns (generated: termination of a recursive function). -/\n",
            f.lean.trim_start_matches("K.")
        );
        if f.pure {
            let bs: Vec<String> = f
                .params
                .iter()
                .zip(&f.arg_tys)
                .map(|(p, t)| format!("({p} : {t})"))
                .collect();
            let app = L::app(
                f.lean.clone(),
                f.params.iter().map(|p| L::Var(p.clone())).collect(),
            );
            let facts: Vec<String> = lm
                .facts
                .iter()
                .map(|x| {
                    let m: BTreeMap<String, L> = [("r".to_string(), app.clone())].into();
                    render_fact(&subst_lin(x, &m).unwrap_or_else(|| x.clone()))
                })
                .collect();
            format!(
                "{}{doc}@[k2l_fact] theorem {} {} :\n    {} := by\n  generalize hr : {} {xs} = r\n  {}\n  k2l_fn_facts [{}]\n",
                self.omit(f.hooks),
                lm.name,
                bs.join(" "),
                facts.join(" ∧ "),
                f.lean,
                self.unfold_text(f, "hr"),
                simps.join(", ")
            )
        } else {
            let mut bs: Vec<String> = f
                .params
                .iter()
                .zip(&f.arg_tys)
                .map(|(p, t)| format!("{{{p} : {t}}}"))
                .collect();
            let res = match &lm.pattern {
                L::Var(r) => {
                    bs.push(format!("{{{r} : {}}}", f.result));
                    r.clone()
                }
                p => {
                    for (v, t) in ftys {
                        bs.push(format!("{{{v} : {t}}}"));
                    }
                    p.render_arg()
                }
            };
            format!(
                "{}{doc}@[k2l_fact] theorem {} {} (h : {} {xs} = some {res}) :\n    {} := by\n  {}\n  k2l_fn_facts [{}]\n",
                self.omit(f.hooks),
                lm.name,
                bs.join(" "),
                f.lean,
                facts.join(" ∧ "),
                self.unfold_text(f, "h"),
                simps.join(", ")
            )
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Shapes: `KPrelude.Shape.shape` of terms (arity-indexed universe), symbolically.

const SHAPE: &str = "KPrelude.Shape.shape";

fn shape_atom(v: &str) -> Lin {
    Lin::atom(&format!("{SHAPE} {v}"))
}

impl Ctx {
    /// The shape of a term as a linear form over the shapes of its variables (`None` when it
    /// contains a call or a literal of a non-builtin sort).
    fn shape_of(&self, l: &L) -> Option<Lin> {
        match l {
            L::Var(v) => Some(shape_atom(v)),
            L::Typed(e, _) => self.shape_of(e),
            L::Raw(r) if r == "KPrelude.ListHook.unit" => Some(Lin::konst(0)),
            L::Raw(_) => None,
            L::App(h, args) => match (h.as_str(), args.len()) {
                ("KPrelude.ListHook.unit", 0) => Some(Lin::konst(0)),
                ("KPrelude.ListHook.element", 1) => Some(self.shape_of(&args[0])?.plus(1)),
                ("KPrelude.ListHook.concat", 2) => {
                    Some(self.shape_of(&args[0])?.add(&self.shape_of(&args[1])?, 1))
                }
                _ => {
                    if let Some(tys) = self.ctors.get(h) {
                        let mut s = Lin::konst(1);
                        for (a, t) in args.iter().zip(tys) {
                            s = if self.builtin.contains(t) {
                                s.plus(1)
                            } else {
                                s.add(&self.shape_of(a)?, 1)
                            };
                        }
                        Some(s)
                    } else if let Some(b) = self.injs.get(h) {
                        if *b {
                            Some(Lin::konst(2))
                        } else {
                            Some(self.shape_of(args.first()?)?.plus(1))
                        }
                    } else {
                        None
                    }
                }
            },
        }
    }

    /// Facts about shapes at one step of an equation (destructured terms, list patterns).
    fn shape_step(&self, s: &Step, alias: &BTreeMap<String, L>, out: &mut Vec<Lin>) {
        let sh = |v: &str| -> Option<Lin> {
            self.shape_of(&alias.get(v).cloned().unwrap_or(L::Var(v.to_string())))
        };
        match s {
            Step::Destruct { scrut, pat, .. } if !matches!(pat, L::Var(_)) => {
                if let (Some(a), Some(b)) = (sh(scrut), self.shape_of(&subst_sim(pat, alias))) {
                    out.push(a.add(&b, -1));
                    out.push(b.add(&a, -1));
                }
            }
            Step::ListElem {
                list, head, tail, ..
            } => {
                if let (Some(l), Some(h), Some(t)) = (sh(list), sh(head), sh(tail)) {
                    let e = h.add(&t, 1).plus(1);
                    out.push(l.add(&e, -1));
                    out.push(e.add(&l, -1));
                }
            }
            Step::CondEq {
                lhs: L::Var(x),
                rhs,
                ..
            } if matches!(rhs, L::Raw(r) if r == "KPrelude.ListHook.unit")
                || matches!(rhs, L::App(h, a) if h == "KPrelude.ListHook.unit" && a.is_empty()) =>
            {
                if let Some(a) = sh(x) {
                    out.push(a.scale(-1));
                }
            }
            _ => {}
        }
    }

    /// `shape r ≤ shape x_j` for `f x̄ = some r`, when every equation of `f` builds its result
    /// from pieces of `x_j` (and recursive calls on pieces of it), as a lemma `@[k2l_fact]`.
    fn shape_lemma(&self, fname: &str, j: usize) -> Option<Lemma> {
        if !self.arity {
            return None;
        }
        let key = (fname.to_string(), j);
        if let Some(l) = self.lemmas.borrow().shape.get(&key) {
            return l.clone();
        }
        let busy = format!("shape {fname} {j}");
        if !self.lemmas.borrow_mut().busy.insert(busy.clone()) {
            return None;
        }
        let r = self.derive_shape(fname, j);
        let mut lm = self.lemmas.borrow_mut();
        lm.busy.remove(&busy);
        lm.shape.insert(key, r.clone());
        if r.is_some() {
            lm.shape_used = true;
        }
        r
    }

    fn derive_shape(&self, fname: &str, j: usize) -> Option<Lemma> {
        let f = self.fns.get(fname)?.clone();
        if f.pure || self.builtin.contains(&f.result) || self.builtin.contains(f.arg_tys.get(j)?) {
            return None;
        }
        let xj = shape_atom(&f.params[j]);
        let mut deps = Vec::new();
        // every recursive call is on an argument of smaller shape
        let mut rec_shape = true;
        for (steps, _, rhs) in &f.eqs {
            let mut facts: Vec<Lin> = Vec::new();
            let mut alias: BTreeMap<String, L> = BTreeMap::new();
            let mut fail = false;
            for s in steps {
                if let Step::Destruct {
                    scrut,
                    pat: L::Var(y),
                    ..
                } = s
                {
                    let t = alias.get(scrut).cloned().unwrap_or(L::Var(scrut.clone()));
                    alias.insert(y.clone(), t);
                    continue;
                }
                self.shape_step(s, &alias, &mut facts);
                if let Step::Bind { expr, var, .. } = s {
                    let e = subst_sim(expr, &alias);
                    let L::App(h, args) = &e else { continue };
                    if h == fname {
                        // the recursive call: the lemma itself, on the call's argument, whose
                        // shape is smaller (the lemma's own measure, when `f` has none)
                        if let Some(a) = self.shape_of(&args[j]) {
                            facts.push(a.add(&shape_atom(var), -1));
                            let mut all = facts.clone();
                            for x in atoms_of(&[a.clone(), xj.clone()]).union(&atoms_of(&facts)) {
                                if x.starts_with(SHAPE) {
                                    all.push(Lin::atom(x));
                                }
                            }
                            rec_shape &= entails(&all, &xj.add(&a, -1).plus(-1));
                        } else {
                            rec_shape = false;
                        }
                    } else if self.fns.contains_key(h)
                        && !self.builtin.contains(&self.fns[h].result)
                    {
                        // a callee building a term: its own bound, on some argument
                        let g = self.fns[h].clone();
                        for (k, t) in g.arg_tys.iter().enumerate() {
                            if self.builtin.contains(t) {
                                continue;
                            }
                            if let Some(lm) = self.shape_lemma(h, k)
                                && let Some(a) = self.shape_of(&args[k])
                            {
                                facts.push(a.add(&shape_atom(var), -1));
                                deps.push(lm.name.clone());
                            }
                        }
                    }
                    let _ = &mut fail;
                }
            }
            let v = self.shape_of(&subst_sim(rhs, &alias))?;
            let mut all = facts.clone();
            for a in atoms_of(&[v.clone(), xj.clone()]).union(&atoms_of(&facts)) {
                if a.starts_with(SHAPE) {
                    all.push(Lin::atom(a));
                }
            }
            if !entails(&all, &xj.add(&v, -1)) {
                return None;
            }
        }
        let name = format!("{fname}.k2l_shape");
        let name = if j == f.params.len() - 1 || f.params.len() == 1 {
            name
        } else {
            format!("{name}{j}")
        };
        let mut simps: BTreeSet<String> = BTreeSet::new();
        self.fn_ctor_names(&f, &mut simps);
        let simps: Vec<String> = ["Term.shape_eq".to_string(), "Term.shape".to_string()]
            .into_iter()
            .chain(self.simp_names(simps))
            .collect();
        let bs: Vec<String> = f
            .params
            .iter()
            .zip(&f.arg_tys)
            .map(|(p, t)| format!("{{{p} : {t}}}"))
            .collect();
        let mut text = format!(
            "{}/-- `{}` builds its result from pieces of its argument (generated: termination of a recursive function). -/\n@[k2l_fact] theorem {name} {} {{r : {}}} (h : {} {} = some r) :\n    {SHAPE} r ≤ {SHAPE} {} := by\n  {}\n  k2l_fn_facts [{}]{}\n",
            self.omit(f.hooks),
            f.lean.trim_start_matches("K."),
            bs.join(" "),
            f.result,
            f.lean,
            f.params.join(" "),
            f.params[j],
            self.unfold_text(&f, "h"),
            simps.join(", "),
            if f.recursive {
                format!(" using {name}")
            } else {
                String::new()
            }
        );
        if f.recursive {
            match &f.measure {
                Some(m) => {
                    text.push_str(&format!("termination_by {m}\n"));
                    text.push_str(
                        "decreasing_by all_goals first | k2l_decreasing | (simp_wf; (try subst_vars); simp_all; omega)\n",
                    );
                }
                // structural recursion of `f`: the shape of the argument decreases too
                None if rec_shape => {
                    text.push_str(&format!(
                        "termination_by {SHAPE} {}\ndecreasing_by all_goals k2l_decreasing [] using [{}]\n",
                        f.params[j],
                        simps.join(", ")
                    ));
                }
                None => text.push_str(
                    "decreasing_by all_goals first | k2l_decreasing | (simp_wf; (try subst_vars); simp_all; omega)\n",
                ),
            }
        }
        deps.sort();
        deps.dedup();
        self.lemmas
            .borrow_mut()
            .text
            .insert(name.clone(), (text, deps));
        Some(Lemma {
            name,
            facts: vec![],
            pattern: L::Var("r".into()),
            fname: fname.to_string(),
            unfolds: vec![],
        })
    }
}

// ---------------------------------------------------------------------------------------------
// Measures for a recursive group (one function, or several calling each other).
//
// Each function gets a tuple of components, all of the same length, compared lexicographically
// (`Prod.Lex`): an integer distance `(e).toNat` (from the facts at its recursive calls, or
// carried back from a callee's distance through the call's arguments), the shape of a parameter
// (`KPrelude.Shape.shape`), and a rank of the function in the group, possibly guarded by a fact
// that holds at every call into it within the group (when the fact fails, the rank is above every
// other). A distance may read a field of a parameter matched by a constructor pattern (then the
// measure is a definition by cases on that parameter). The search is lexicographic as Lean's own
// (`GuessLex`): pick a component per function that does not increase on any remaining call and
// decreases on some, drop those calls, repeat. Facts about callees (the result of a function, the
// range of an integer function, a bound on a result's shape) are lemmas derived from their
// equations and proved before the group.

/// A parameter matched by a constructor pattern, whose fields a component reads.
type View = Option<(usize, L)>;

/// One component of a function's measure.
#[derive(Clone, Debug, PartialEq)]
enum Comp {
    Zero,
    /// `(e).toNat`
    Dist(Lin, View),
    /// `KPrelude.Shape.shape x_k`
    Shape(usize),
    Rank(i128),
    /// `if guard then rank else top`
    GRank(Vec<Lin>, i128, View),
}

/// A component's value at a call: an integer `(e).toNat`, a natural number `e`, or a constant.
#[derive(Clone, Debug)]
enum Val {
    ToNat(Lin),
    Nat(Lin),
    K(i128),
}

/// One recursive call within the group.
#[derive(Clone, Debug)]
struct Edge {
    from: usize,
    to: usize,
    args: Vec<L>,
    facts: Facts,
    /// the caller's parameters matched by a constructor pattern (with canonical field names)
    views: BTreeMap<usize, L>,
    /// variables bound to calls of functions outside the group
    binds: BTreeMap<String, (String, Vec<L>)>,
}

/// The measure of a recursive group: per function, its `termination_by`, its `decreasing_by`,
/// and the declarations to emit before the group (lemmas, measure definitions).
pub struct GroupPlan {
    pub measures: Vec<String>,
    pub decreasing: String,
    pub pre: String,
}

/// A pattern with its variables named by their position under the parameter (`x2_1`, `x2_0_1`),
/// so that two patterns of one parameter name a field alike; and the renaming.
fn canon(pat: &L, prefix: &str, ren: &mut BTreeMap<String, L>) -> L {
    match pat {
        L::Var(v) => {
            ren.insert(v.clone(), L::Var(prefix.to_string()));
            L::Var(prefix.to_string())
        }
        L::App(h, args) => L::App(
            h.clone(),
            args.iter()
                .enumerate()
                .map(|(i, a)| canon(a, &format!("{prefix}_{i}"), ren))
                .collect(),
        ),
        other => other.clone(),
    }
}

fn pattern_vars(p: &L, out: &mut Vec<String>) {
    match p {
        L::Var(v) => out.push(v.clone()),
        L::App(_, a) => a.iter().for_each(|x| pattern_vars(x, out)),
        L::Typed(e, _) => pattern_vars(e, out),
        L::Raw(_) => {}
    }
}

impl Ctx {
    /// The recursive calls of the group, with the facts at each.
    fn edges(&self, group: &[FnDef]) -> Vec<Edge> {
        let idx: BTreeMap<&str, usize> = group
            .iter()
            .enumerate()
            .map(|(i, f)| (f.lean.as_str(), i))
            .collect();
        let mut out = Vec::new();
        for (fi, f) in group.iter().enumerate() {
            let pidx: BTreeMap<&str, usize> = f
                .params
                .iter()
                .enumerate()
                .map(|(i, p)| (p.as_str(), i))
                .collect();
            let mut negs: Vec<Vec<Vec<Lin>>> = Vec::new();
            for (steps, lhs_len, _) in &f.eqs {
                let mut facts = Facts::default();
                for d in &negs {
                    facts.push_dnf(d.clone());
                }
                let mut alias: BTreeMap<String, L> = BTreeMap::new();
                let mut views: BTreeMap<usize, L> = BTreeMap::new();
                let mut binds: BTreeMap<String, (String, Vec<L>)> = BTreeMap::new();
                for s in steps {
                    match s {
                        Step::Destruct { scrut, pat, .. } => {
                            if let L::Var(y) = pat {
                                let t = alias.get(scrut).cloned().unwrap_or(L::Var(scrut.clone()));
                                alias.insert(y.clone(), t);
                                continue;
                            }
                            if let Some(&k) = pidx.get(scrut.as_str())
                                && !alias.contains_key(scrut)
                            {
                                let mut ren = BTreeMap::new();
                                let c = canon(pat, &format!("x{k}"), &mut ren);
                                // a field of an integer sort is an atom under its canonical name
                                for (v, t) in ren {
                                    alias.insert(v, t);
                                }
                                let mut sf = Vec::new();
                                self.shape_step(s, &alias, &mut sf);
                                facts.extend(sf);
                                views.insert(k, c);
                                continue;
                            }
                            let mut sf = Vec::new();
                            self.shape_step(s, &alias, &mut sf);
                            facts.extend(sf);
                        }
                        Step::Cond { cond, .. } => {
                            facts.push_dnf(cond_dnf(&subst_sim(cond, &alias), true))
                        }
                        Step::CondEq { lhs, rhs, .. } => {
                            let (l, r) = (subst_sim(lhs, &alias), subst_sim(rhs, &alias));
                            match &r {
                                L::Raw(b) if b == "true" || b == "false" => {
                                    facts.push_dnf(cond_dnf(&l, b == "true"))
                                }
                                _ => {
                                    if let (Some(a), Some(b)) = (lin(&l), lin(&r)) {
                                        facts.push(a.add(&b, -1));
                                        facts.push(b.add(&a, -1));
                                    }
                                }
                            }
                            let mut sf = Vec::new();
                            self.shape_step(s, &alias, &mut sf);
                            facts.extend(sf);
                        }
                        Step::ListElem { .. } => {
                            let mut sf = Vec::new();
                            self.shape_step(s, &alias, &mut sf);
                            facts.extend(sf);
                        }
                        Step::Bind { expr, var, .. } => {
                            let e = subst_sim(expr, &alias);
                            let L::App(h, args) = &e else { continue };
                            if let Some(&gi) = idx.get(h.as_str()) {
                                out.push(Edge {
                                    from: fi,
                                    to: gi,
                                    args: args.clone(),
                                    facts: facts.clone(),
                                    views: views.clone(),
                                    binds: binds.clone(),
                                });
                                continue;
                            }
                            // the facts so far, for the hook's conditional facts
                            let mut v = facts.base.clone();
                            let n0 = v.len();
                            hook_facts(h, args, var, &mut v);
                            facts.extend(v.split_off(n0));
                            hook_dnf(h, args, var, &mut facts);
                            if let Some(g) = self.fns.get(h)
                                && !g.recursive
                                && let Some(lm) = self.out_lemma(h, &L::Var("r".into()))
                            {
                                let mut m: BTreeMap<String, L> =
                                    g.params.iter().cloned().zip(args.iter().cloned()).collect();
                                m.insert("r".into(), L::Var(var.clone()));
                                if let Some(fs) = lm
                                    .facts
                                    .iter()
                                    .map(|x| subst_lin(x, &m))
                                    .collect::<Option<Vec<_>>>()
                                {
                                    facts.extend(fs);
                                    self.lemmas.borrow_mut().used.insert(lm.name.clone());
                                }
                            }
                            binds.insert(var.clone(), (h.clone(), args.clone()));
                        }
                        _ => {}
                    }
                }
                let guard_only = *lhs_len > 0
                    && steps[..*lhs_len]
                        .iter()
                        .all(|s| matches!(s, Step::Cond { .. } | Step::CondEq { .. }));
                if guard_only {
                    let mut d: Vec<Vec<Lin>> = Vec::new();
                    for s in &steps[..*lhs_len] {
                        match s {
                            Step::Cond { cond, .. } => d.extend(cond_dnf(cond, false)),
                            Step::CondEq {
                                lhs,
                                rhs: L::Raw(b),
                                ..
                            } if b == "true" || b == "false" => {
                                d.extend(cond_dnf(lhs, b != "true"))
                            }
                            _ => d.push(vec![]),
                        }
                    }
                    negs.push(d);
                }
            }
        }
        out
    }

    /// Facts every check adds: absolute values, the range of total integer functions applied in
    /// the facts, shapes are natural numbers.
    fn close(&self, f: &Facts, extra: &[Lin]) -> Facts {
        self.close_deps(f, extra, &mut Vec::new())
    }

    fn close_deps(&self, f: &Facts, extra: &[Lin], deps: &mut Vec<String>) -> Facts {
        let mut f = f.clone();
        let mut atoms = atoms_of(&f.base);
        for d in &f.alts {
            for c in d {
                atoms.extend(atoms_of(c));
            }
        }
        atoms.extend(atoms_of(extra));
        abs_facts(&atoms, &mut f);
        let mut add = Vec::new();
        for a in &atoms {
            if a.starts_with(SHAPE) {
                add.push(Lin::atom(a));
            }
            if let L::App(h, args) = atom_term(a)
                && let Some(g) = self.fns.get(&h)
                && g.pure
                && !g.recursive
                && self.is_int(&g.result)
                && args.len() == g.params.len()
                && let Some(lm) = self.out_lemma(&h, &L::Var("r".into()))
            {
                let mut m: BTreeMap<String, L> = g.params.iter().cloned().zip(args).collect();
                m.insert("r".into(), atom_term(a));
                for x in &lm.facts {
                    if let Some(y) = subst_lin(x, &m) {
                        add.push(y);
                    }
                }
                self.lemmas.borrow_mut().used.insert(lm.name.clone());
                deps.push(lm.name.clone());
            }
        }
        f.extend(add);
        f
    }
}

/// A case of a component's view at a call: its facts, and the fields read (`None`: the
/// argument does not match, the measure's default arm).
type ViewCase = (Facts, Option<BTreeMap<String, L>>);

/// Whether a pattern matches every value of its sort (its constructor is the sort's only value,
/// and its arguments are variables or such patterns).
impl Ctx {
    fn irrefutable(&self, p: &L) -> bool {
        match p {
            L::Var(_) => true,
            L::App(h, args) => self.sole.contains(h) && args.iter().all(|a| self.irrefutable(a)),
            _ => false,
        }
    }

    /// The fields a component reads, renamed in the substitution `m` from the argument `arg` of
    /// the call at view `(k, P)`: cases with their facts (`None` in a case: the default arm).
    fn view_cases(&self, pat: &L, arg: &L, e: &Edge, caller: &FnDef) -> Option<Vec<ViewCase>> {
        let mut m = BTreeMap::new();
        match self.unify(pat, arg, &mut m) {
            Unif::Match => return Some(vec![(Facts::default(), Some(m))]),
            Unif::Clash => return Some(vec![(Facts::default(), None)]),
            Unif::Unknown => {}
        }
        let L::Var(v) = arg else { return None };
        // the caller's own parameter, matched by a pattern of its own
        if let Some(j) = caller.params.iter().position(|p| p == v)
            && let Some(q) = e.views.get(&j)
        {
            let mut m = BTreeMap::new();
            return match self.unify(pat, q, &mut m) {
                Unif::Match => Some(vec![(Facts::default(), Some(m))]),
                Unif::Clash => Some(vec![(Facts::default(), None)]),
                Unif::Unknown => None,
            };
        }
        // the result of a callee: its result facts for the pattern
        let (h, hargs) = e.binds.get(v)?;
        let g = self.fns.get(h)?;
        let mut vars = Vec::new();
        pattern_vars(pat, &mut vars);
        let lren: BTreeMap<String, L> = vars
            .iter()
            .enumerate()
            .map(|(i, x)| (x.clone(), L::Var(format!("a{i}"))))
            .collect();
        let lpat = subst_sim(pat, &lren);
        let mut facts = Facts::default();
        let mut m: BTreeMap<String, L> = BTreeMap::new();
        for (i, x) in vars.iter().enumerate() {
            m.insert(x.clone(), L::Var(format!("{v}_a{i}")));
        }
        if !g.recursive
            && let Some(lm) = self.out_lemma(h, &lpat)
        {
            let mut im: BTreeMap<String, L> = g
                .params
                .iter()
                .cloned()
                .zip(hargs.iter().cloned())
                .collect();
            for i in 0..vars.len() {
                im.insert(format!("a{i}"), L::Var(format!("{v}_a{i}")));
            }
            for x in &lm.facts {
                if let Some(y) = subst_lin(x, &im) {
                    facts.push(y);
                }
            }
            self.lemmas.borrow_mut().used.insert(lm.name.clone());
        }
        let mut out = vec![(facts, Some(m))];
        if !self.irrefutable(pat) {
            out.push((Facts::default(), None));
        }
        Some(out)
    }

    /// The value of a component of the callee `g` at the call `e` (from `f`): cases.
    fn eval_callee(
        &self,
        group: &[FnDef],
        c: &Comp,
        e: &Edge,
        top: i128,
    ) -> Option<Vec<(Facts, Val)>> {
        let (f, g) = (&group[e.from], &group[e.to]);
        let base: BTreeMap<String, L> = g
            .params
            .iter()
            .cloned()
            .zip(e.args.iter().cloned())
            .collect();
        match c {
            Comp::Zero => Some(vec![(Facts::default(), Val::K(0))]),
            Comp::Rank(n) => Some(vec![(Facts::default(), Val::K(*n))]),
            Comp::Shape(k) => {
                let v = self.shape_of(&e.args[*k])?;
                let mut facts = Facts::default();
                // the shapes of results of callees: their shape lemmas
                for a in atoms_of(std::slice::from_ref(&v)) {
                    let Some(x) = a.strip_prefix(&format!("{SHAPE} ")) else {
                        continue;
                    };
                    let Some((h, hargs)) = e.binds.get(x) else {
                        continue;
                    };
                    let Some(hd) = self.fns.get(h) else { continue };
                    for (j, t) in hd.arg_tys.iter().enumerate() {
                        if self.builtin.contains(t) {
                            continue;
                        }
                        if let Some(lm) = self.shape_lemma(h, j)
                            && let Some(s) = self.shape_of(&hargs[j])
                        {
                            facts.push(s.add(&Lin::atom(&a), -1));
                            self.lemmas.borrow_mut().used.insert(lm.name.clone());
                        }
                    }
                }
                Some(vec![(facts, Val::Nat(v))])
            }
            Comp::Dist(_, view) | Comp::GRank(_, _, view) => {
                let cases = match view {
                    None => vec![(Facts::default(), Some(BTreeMap::new()))],
                    Some((k, p)) => self.view_cases(p, &e.args[*k], e, f)?,
                };
                let mut out = Vec::new();
                for (facts, m) in cases {
                    let Some(m) = m else {
                        out.push((
                            facts,
                            match c {
                                Comp::GRank(..) => Val::K(top),
                                _ => Val::K(0),
                            },
                        ));
                        continue;
                    };
                    let mut sm = base.clone();
                    sm.extend(m);
                    match c {
                        Comp::Dist(l, _) => out.push((facts, Val::ToNat(subst_lin(l, &sm)?))),
                        Comp::GRank(gd, n, _) => {
                            let gs: Vec<Lin> = gd
                                .iter()
                                .map(|x| subst_lin(x, &sm))
                                .collect::<Option<_>>()?;
                            out.extend(self.guard_cases(
                                &e.facts.and(&facts),
                                &gs,
                                *n,
                                top,
                                &facts,
                            ));
                        }
                        _ => unreachable!(),
                    }
                }
                Some(out)
            }
        }
    }

    /// `if guard then n else top`, as cases (one when the facts decide the guard).
    fn guard_cases(
        &self,
        at: &Facts,
        guard: &[Lin],
        n: i128,
        top: i128,
        extra: &Facts,
    ) -> Vec<(Facts, Val)> {
        let at = self.close(at, guard);
        if guard.iter().all(|g| at.entails(g)) {
            return vec![(extra.clone(), Val::K(n))];
        }
        let mut yes = extra.clone();
        yes.extend(guard.iter().cloned());
        let mut no = extra.clone();
        no.push_dnf(guard.iter().map(|g| vec![g.scale(-1).plus(-1)]).collect());
        vec![(yes, Val::K(n)), (no, Val::K(top))]
    }

    /// The value of a component of the caller at its own parameters, at the call `e`: cases.
    fn eval_caller(
        &self,
        group: &[FnDef],
        c: &Comp,
        e: &Edge,
        top: i128,
    ) -> Option<Vec<(Facts, Val)>> {
        let f = &group[e.from];
        match c {
            Comp::Zero => Some(vec![(Facts::default(), Val::K(0))]),
            Comp::Rank(n) => Some(vec![(Facts::default(), Val::K(*n))]),
            Comp::Shape(k) => Some(vec![(
                Facts::default(),
                Val::Nat(shape_atom(&f.params[*k])),
            )]),
            Comp::Dist(_, view) | Comp::GRank(_, _, view) => {
                let m = match view {
                    None => Some(BTreeMap::new()),
                    Some((k, p)) => {
                        let q = e.views.get(k)?;
                        let mut m = BTreeMap::new();
                        match self.unify(p, q, &mut m) {
                            Unif::Match => Some(m),
                            Unif::Clash => None,
                            Unif::Unknown => return None,
                        }
                    }
                };
                let Some(m) = m else {
                    return Some(vec![(
                        Facts::default(),
                        match c {
                            Comp::GRank(..) => Val::K(top),
                            _ => Val::K(0),
                        },
                    )]);
                };
                match c {
                    Comp::Dist(l, _) => {
                        Some(vec![(Facts::default(), Val::ToNat(subst_lin(l, &m)?))])
                    }
                    Comp::GRank(gd, n, _) => {
                        let gs: Vec<Lin> =
                            gd.iter().map(|x| subst_lin(x, &m)).collect::<Option<_>>()?;
                        Some(self.guard_cases(&e.facts, &gs, *n, top, &Facts::default()))
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    /// How the callee's value compares with the caller's under the facts.
    fn cmp(&self, facts: &Facts, callee: &Val, caller: &Val) -> Rel {
        use Val::*;
        let ent = |g: &Lin| -> bool {
            let f = self.close(facts, std::slice::from_ref(g));
            f.infeasible() || f.entails(g)
        };
        match (callee, caller) {
            (K(a), K(b)) => {
                if a < b {
                    Rel::Lt
                } else if a <= b {
                    Rel::Le
                } else {
                    Rel::Unknown
                }
            }
            (ToNat(g), ToNat(h)) => {
                if ent(&h.plus(-1)) && ent(&h.add(g, -1).plus(-1)) {
                    Rel::Lt
                } else if ent(&h.add(g, -1)) || ent(&g.scale(-1)) {
                    Rel::Le
                } else {
                    Rel::Unknown
                }
            }
            (ToNat(g), K(c)) => {
                if *c >= 1 && (ent(&g.scale(-1).plus(c - 1))) {
                    Rel::Lt
                } else if ent(&g.scale(-1).plus(*c)) {
                    Rel::Le
                } else {
                    Rel::Unknown
                }
            }
            (K(c), ToNat(h)) => {
                if ent(&h.plus(-c - 1)) {
                    Rel::Lt
                } else if *c <= 0 || ent(&h.plus(-c)) {
                    Rel::Le
                } else {
                    Rel::Unknown
                }
            }
            (Nat(g), Nat(h)) => {
                if ent(&h.add(g, -1).plus(-1)) {
                    Rel::Lt
                } else if ent(&h.add(g, -1)) {
                    Rel::Le
                } else {
                    Rel::Unknown
                }
            }
            (Nat(g), K(c)) => {
                if ent(&g.scale(-1).plus(c - 1)) {
                    Rel::Lt
                } else if ent(&g.scale(-1).plus(*c)) {
                    Rel::Le
                } else {
                    Rel::Unknown
                }
            }
            (K(c), Nat(h)) => {
                if ent(&h.plus(-c - 1)) {
                    Rel::Lt
                } else if *c <= 0 || ent(&h.plus(-c)) {
                    Rel::Le
                } else {
                    Rel::Unknown
                }
            }
            (ToNat(g), Nat(h)) => {
                if ent(&h.add(g, -1).plus(-1)) || (ent(&h.plus(-1)) && ent(&g.scale(-1))) {
                    Rel::Lt
                } else if ent(&h.add(g, -1)) || ent(&g.scale(-1)) {
                    Rel::Le
                } else {
                    Rel::Unknown
                }
            }
            (Nat(g), ToNat(h)) => {
                if ent(&h.plus(-1)) && ent(&h.add(g, -1).plus(-1)) {
                    Rel::Lt
                } else if ent(&h.add(g, -1)) {
                    Rel::Le
                } else {
                    Rel::Unknown
                }
            }
        }
    }

    /// The relation of one component at a call, and the facts its equality gives (for the next
    /// components), when it is `≤`.
    fn rel_at(
        &self,
        group: &[FnDef],
        cf: &Comp,
        cg: &Comp,
        e: &Edge,
        extra: &Facts,
        top: i128,
    ) -> (Rel, Vec<Vec<Lin>>) {
        let (Some(a), Some(b)) = (
            self.eval_caller(group, cf, e, top),
            self.eval_callee(group, cg, e, top),
        ) else {
            return (Rel::Unknown, vec![]);
        };
        let mut worst = Rel::Lt;
        for (fa, va) in &a {
            for (fb, vb) in &b {
                let facts = e.facts.and(extra).and(fa).and(fb);
                let r = self.cmp(&facts, vb, va);

                worst = match (worst, r) {
                    (_, Rel::Unknown) | (Rel::Unknown, _) => Rel::Unknown,
                    (Rel::Le, _) | (_, Rel::Le) => Rel::Le,
                    _ => Rel::Lt,
                };
                if worst == Rel::Unknown {
                    return (worst, vec![]);
                }
            }
        }
        // the equality of a single value: facts for the next components
        let mut eq = vec![];
        if worst == Rel::Le && a.len() == 1 && b.len() == 1 {
            match (&a[0].1, &b[0].1) {
                (Val::ToNat(h), Val::ToNat(g)) => {
                    eq = vec![
                        vec![h.add(g, -1), g.add(h, -1)],
                        vec![h.scale(-1), g.scale(-1)],
                    ];
                }
                (Val::Nat(h), Val::Nat(g)) => eq = vec![vec![h.add(g, -1), g.add(h, -1)]],
                (Val::ToNat(h), Val::K(0)) | (Val::Nat(h), Val::K(0)) => {
                    eq = vec![vec![h.scale(-1)]]
                }
                _ => {}
            }
        }
        (worst, eq)
    }
}

/// The state of a remaining call during the search: its index and the facts the equal earlier
/// components give.
type Remaining = Vec<(usize, Facts)>;

impl Ctx {
    /// The canonical field names of the views of `f`'s calls, by parameter.
    fn field_names(&self, edges: &[Edge], f: usize) -> BTreeMap<String, (usize, L)> {
        let mut out = BTreeMap::new();
        for e in edges.iter().filter(|e| e.from == f) {
            for (k, p) in &e.views {
                let mut vs = Vec::new();
                pattern_vars(p, &mut vs);
                for v in vs {
                    out.entry(v).or_insert((*k, p.clone()));
                }
            }
        }
        out
    }

    /// The view a linear form needs: the parameter whose fields it reads (`Err` when it reads
    /// fields of two parameters, or of no known view).
    fn view_of(
        &self,
        l: &[Lin],
        fields: &BTreeMap<String, (usize, L)>,
        e: Option<&Edge>,
    ) -> Result<View, ()> {
        let mut view: View = None;
        for a in atoms_of(l) {
            for v in atom_vars(&a) {
                let Some((k, p)) = fields.get(&v) else {
                    continue;
                };
                let p = e.and_then(|e| e.views.get(k)).cloned().unwrap_or(p.clone());
                match &view {
                    None => view = Some((*k, p)),
                    Some((k2, _)) if k2 == k => {}
                    Some(_) => return Err(()),
                }
            }
        }
        Ok(view)
    }

    /// Whether the atoms of `l` are all over `f`'s parameters and fields.
    fn own(&self, f: &FnDef, l: &Lin, fields: &BTreeMap<String, (usize, L)>) -> bool {
        atoms_of(std::slice::from_ref(l)).iter().all(|a| {
            let vs = atom_vars(a);
            !vs.is_empty()
                && vs
                    .iter()
                    .all(|v| f.params.contains(v) || fields.contains_key(v))
                && (!a.starts_with(SHAPE))
        })
    }

    /// Candidate distances of each function.
    fn candidates(&self, group: &[FnDef], edges: &[Edge]) -> Vec<Vec<Comp>> {
        let n = group.len();
        let fields: Vec<BTreeMap<String, (usize, L)>> =
            (0..n).map(|f| self.field_names(edges, f)).collect();
        let mut cands: Vec<Vec<Comp>> = vec![vec![]; n];
        let push = |cands: &mut Vec<Vec<Comp>>, f: usize, c: Comp| {
            if !cands[f].contains(&c) && cands[f].len() < 12 {
                cands[f].push(c);
            }
        };
        for e in edges {
            let f = &group[e.from];
            for fact in &e.facts.base {
                if fact.as_const().is_none() && self.own(f, fact, &fields[e.from]) {
                    let m = fact.plus(1);
                    if let Ok(v) = self.view_of(std::slice::from_ref(&m), &fields[e.from], Some(e))
                    {
                        push(&mut cands, e.from, Comp::Dist(m, v));
                    }
                }
            }
        }
        // the distance to a bound under which a conditional decrease holds: a fact `g ≥ 0` that
        // one alternative of a disjunction needs, bounded above by replacing `-|p|` with `-p`
        for e in edges {
            let f = &group[e.from];
            for d in &e.facts.alts {
                for alt in d {
                    let [g] = alt.as_slice() else { continue };
                    let mut g2 = Lin::konst(g.c);
                    for (a, k) in &g.terms {
                        let t = atom_term(a);
                        let repl = match (&t, *k < 0) {
                            (L::Typed(inner, ty), true) if ty == "Int" => match &**inner {
                                L::App(h, args) if h == "Int.natAbs" && args.len() == 1 => {
                                    lin(&args[0])
                                }
                                _ => None,
                            },
                            _ => None,
                        };
                        g2 = g2.add(&repl.unwrap_or_else(|| Lin::atom(a)), *k);
                    }
                    let q = g2.plus(1);
                    if q.as_const().is_none() && self.own(f, &q, &fields[e.from]) {
                        push(&mut cands, e.from, Comp::Dist(q, None));
                    }
                    // or: the parameter terms of `g` with a positive coefficient, less a counter
                    // the call increments, when the facts bound `g` by it
                    let pos = Lin {
                        terms: g
                            .terms
                            .iter()
                            .filter(|(a, k)| **k > 0 && self.own(f, &Lin::atom(a), &fields[e.from]))
                            .map(|(a, k)| (a.clone(), *k))
                            .collect(),
                        c: 0,
                    };
                    for (k, p) in f.params.iter().enumerate() {
                        if !self.is_int(&f.arg_tys[k]) {
                            continue;
                        }
                        let Some(a) = lin(&e.args[k]) else { continue };
                        let step = a.add(&Lin::atom(p), -1);
                        if !step.as_const().is_some_and(|c| c > 0) {
                            continue;
                        }
                        let bound = pos.add(&Lin::atom(p), -1);
                        let facts = self.close(&e.facts, &[bound.clone(), g.clone()]);
                        if facts.entails(&bound.add(g, -1)) {
                            push(&mut cands, e.from, Comp::Dist(bound.plus(1), None));
                        }
                    }
                }
            }
        }
        // carried forward to a callee whose arguments are the caller's parameters
        for e in edges {
            let (f, g) = (&group[e.from], &group[e.to]);
            let mut inv: BTreeMap<String, L> = BTreeMap::new();
            for (k, a) in e.args.iter().enumerate() {
                if let L::Var(v) = a
                    && f.params.contains(v)
                {
                    inv.insert(v.clone(), L::Var(g.params[k].clone()));
                }
            }
            for c in cands[e.from].clone() {
                let Comp::Dist(l, None) = &c else { continue };
                let all = atoms_of(std::slice::from_ref(l))
                    .iter()
                    .all(|a| atom_vars(a).iter().all(|v| inv.contains_key(v)));
                if all && let Some(l2) = subst_lin(l, &inv) {
                    push(&mut cands, e.to, Comp::Dist(l2, None));
                }
            }
        }
        // carried back from callees through the call's arguments
        for _ in 0..2 {
            for e in edges {
                let f = &group[e.from];
                for c in cands[e.to].clone() {
                    if !matches!(c, Comp::Dist(..)) {
                        continue;
                    }
                    let Some(vs) = self.eval_callee(group, &c, e, 0) else {
                        continue;
                    };
                    let [(fx, Val::ToNat(l))] = vs.as_slice() else {
                        continue;
                    };
                    if !fx.base.is_empty() || !fx.alts.is_empty() {
                        continue;
                    }
                    if l.as_const().is_none()
                        && self.own(f, l, &fields[e.from])
                        && let Ok(v) =
                            self.view_of(std::slice::from_ref(l), &fields[e.from], Some(e))
                    {
                        push(&mut cands, e.from, Comp::Dist(l.clone(), v));
                    }
                }
            }
        }
        cands
    }

    /// A component per function that no remaining call increases and some decreases: the
    /// assignment with the most decreases, among `options` (per function).
    #[allow(clippy::type_complexity)]
    fn step(
        &self,
        group: &[FnDef],
        edges: &[Edge],
        rem: &Remaining,
        options: &[Vec<Comp>],
        chosen: &[Vec<Comp>],
        need_lt: bool,
    ) -> Option<(Vec<Comp>, Vec<(Rel, Vec<Vec<Lin>>)>)> {
        let n = group.len();
        let top = n as i128 + 1;
        let mut memo: BTreeMap<(usize, usize, usize), (Rel, Vec<Vec<Lin>>)> = BTreeMap::new();
        let mut best: Option<(usize, usize, Vec<usize>)> = None;
        let mut cur: Vec<usize> = vec![0; n];
        // depth-first over functions; a call is checked once both its ends are chosen
        #[allow(clippy::too_many_arguments)]
        fn go(
            ctx: &Ctx,
            i: usize,
            group: &[FnDef],
            edges: &[Edge],
            rem: &Remaining,
            options: &[Vec<Comp>],
            chosen: &[Vec<Comp>],
            cur: &mut Vec<usize>,
            memo: &mut BTreeMap<(usize, usize, usize), (Rel, Vec<Vec<Lin>>)>,
            best: &mut Option<(usize, usize, Vec<usize>)>,
            top: i128,
            need_lt: bool,
        ) {
            let n = group.len();
            if i == n {
                let mut lt = 0;
                for (ri, (ei, _)) in rem.iter().enumerate() {
                    let e = &edges[*ei];
                    let r = &memo[&(ri, cur[e.from], cur[e.to])];
                    if r.0 == Rel::Lt {
                        lt += 1;
                    }
                }
                if need_lt && lt == 0 {
                    return;
                }
                let nonzero = (0..n)
                    .filter(|f| options[*f][cur[*f]] != Comp::Zero)
                    .count();
                let better = match best {
                    None => true,
                    Some((bl, bn, _)) => lt > *bl || (lt == *bl && nonzero < *bn),
                };
                if better {
                    *best = Some((lt, nonzero, cur.clone()));
                }
                return;
            }
            'opt: for o in 0..options[i].len() {
                // one view per function
                if let Comp::Dist(_, Some((k, _))) | Comp::GRank(_, _, Some((k, _))) =
                    &options[i][o]
                {
                    for c in &chosen[i] {
                        if let Comp::Dist(_, Some((k2, _))) | Comp::GRank(_, _, Some((k2, _))) = c
                            && k2 != k
                        {
                            continue 'opt;
                        }
                    }
                }
                cur[i] = o;
                for (ri, (ei, extra)) in rem.iter().enumerate() {
                    let e = &edges[*ei];
                    if e.from.max(e.to) != i {
                        continue;
                    }
                    let key = (ri, cur[e.from], cur[e.to]);
                    memo.entry(key).or_insert_with(|| {
                        ctx.rel_at(
                            group,
                            &options[e.from][cur[e.from]],
                            &options[e.to][cur[e.to]],
                            e,
                            extra,
                            top,
                        )
                    });
                    if memo[&key].0 == Rel::Unknown {
                        continue 'opt;
                    }
                }
                go(
                    ctx,
                    i + 1,
                    group,
                    edges,
                    rem,
                    options,
                    chosen,
                    cur,
                    memo,
                    best,
                    top,
                    need_lt,
                );
            }
        }
        go(
            self, 0, group, edges, rem, options, chosen, &mut cur, &mut memo, &mut best, top,
            need_lt,
        );
        let (_, _, a) = best?;
        let choice: Vec<Comp> = (0..n).map(|f| options[f][a[f]].clone()).collect();
        let rels = rem
            .iter()
            .enumerate()
            .map(|(ri, (ei, _))| {
                let e = &edges[*ei];
                memo[&(ri, a[e.from], a[e.to])].clone()
            })
            .collect();
        Some((choice, rels))
    }

    /// Ranks of the functions along the remaining calls between different functions, when they
    /// form no cycle.
    fn ranks(&self, n: usize, edges: &[Edge], rem: &Remaining) -> Option<Vec<i128>> {
        let mut succ: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n];
        let mut any = false;
        for (ei, _) in rem {
            let e = &edges[*ei];
            if e.from != e.to {
                succ[e.from].insert(e.to);
                any = true;
            }
        }
        if !any {
            return None;
        }
        fn depth(
            f: usize,
            succ: &[BTreeSet<usize>],
            memo: &mut Vec<Option<Option<i128>>>,
        ) -> Option<i128> {
            if let Some(v) = memo[f] {
                return v;
            }
            memo[f] = Some(None);
            let mut d = 0;
            for &g in &succ[f] {
                d = d.max(depth(g, succ, memo)? + 1);
            }
            memo[f] = Some(Some(d));
            Some(d)
        }
        let mut memo = vec![None; n];
        (0..n).map(|f| depth(f, &succ, &mut memo)).collect()
    }

    /// Facts that hold at every call into each function from within the group, over its own
    /// parameters and the fields of its view.
    fn invariants(&self, group: &[FnDef], edges: &[Edge]) -> Vec<Vec<Lin>> {
        let n = group.len();
        let mut out = vec![vec![]; n];
        for (g, gd) in group.iter().enumerate() {
            let fields = self.field_names(edges, g);
            // targets: integer parameters, terms over them, integer fields of one view
            let mut targets: Vec<L> = Vec::new();
            for (p, t) in gd.params.iter().zip(&gd.arg_tys) {
                if self.is_int(t) {
                    targets.push(L::Var(p.clone()));
                }
            }
            for e in edges.iter().filter(|e| e.from == g) {
                for a in atoms_of(&e.facts.base) {
                    let vs = atom_vars(&a);
                    if a.contains(' ')
                        && !a.starts_with(SHAPE)
                        && !vs.is_empty()
                        && vs.iter().all(|v| gd.params.contains(v))
                        && !targets.contains(&atom_term(&a))
                    {
                        targets.push(atom_term(&a));
                    }
                }
            }
            let mut view: View = None;
            for (v, (k, p)) in &fields {
                let mut tys = BTreeMap::new();
                self.field_types(p, &mut tys);
                if tys.get(v).is_some_and(|t| self.is_int(t))
                    && view.as_ref().is_none_or(|(k2, _)| k2 == k)
                {
                    view = Some((*k, p.clone()));
                    targets.push(L::Var(v.clone()));
                }
            }
            let base: Vec<String> = targets
                .iter()
                .map(|t| format!("\u{2}{}", t.render()))
                .collect();
            let mut cases: Vec<Vec<Lin>> = Vec::new();
            let mut ok = false;
            for e in edges.iter().filter(|e| e.to == g) {
                let sub: BTreeMap<String, L> = gd
                    .params
                    .iter()
                    .cloned()
                    .zip(e.args.iter().cloned())
                    .collect();
                let vcases = match &view {
                    None => vec![(Facts::default(), Some(BTreeMap::new()))],
                    Some((k, p)) => match self.view_cases(p, &e.args[*k], e, &group[e.from]) {
                        Some(c) => c,
                        None => return out,
                    },
                };
                for (fx, m) in vcases {
                    let Some(m) = m else { continue };
                    let mut sm = sub.clone();
                    sm.extend(m);
                    let mut facts = e.facts.and(&fx);
                    for (t, b) in targets.iter().zip(&base) {
                        let Some(l) = lin(&subst_sim(t, &sm)) else {
                            continue;
                        };
                        let bl = Lin::atom(b);
                        facts.push(bl.add(&l, -1));
                        facts.push(l.add(&bl, -1));
                    }
                    let facts = self.close(&facts, &[]);
                    let Some(cs) = facts.cases() else { return out };
                    cases.extend(cs);
                    ok = true;
                }
            }
            if !ok {
                continue;
            }
            let back: BTreeMap<String, L> =
                base.iter().cloned().zip(targets.iter().cloned()).collect();
            out[g] = template_facts(&cases, &directions(&base))
                .iter()
                .filter_map(|f| subst_lin(f, &back))
                .collect();
        }
        out
    }

    /// Whether the measures decrease at a call, lexicographically, in every case of the caller's
    /// guards.
    fn verify(&self, group: &[FnDef], comps: &[Vec<Comp>], e: &Edge) -> bool {
        let top = group.len() as i128 + 1;
        let mut caller_cases = vec![Facts::default()];
        for c in &comps[e.from] {
            if let Comp::GRank(gd, _, view) = c {
                let gs: Option<Vec<Lin>> = match view {
                    None => Some(gd.clone()),
                    Some((k, p)) => e.views.get(k).and_then(|q| {
                        let mut m = BTreeMap::new();
                        match self.unify(p, q, &mut m) {
                            Unif::Match => gd.iter().map(|x| subst_lin(x, &m)).collect(),
                            _ => None,
                        }
                    }),
                };
                if let Some(gs) = gs {
                    let mut yes = Facts::default();
                    yes.extend(gs.iter().cloned());
                    let mut no = Facts::default();
                    no.push_dnf(gs.iter().map(|g| vec![g.scale(-1).plus(-1)]).collect());
                    caller_cases = vec![yes, no];
                }
            }
        }
        'case: for case in caller_cases {
            let mut e2 = e.clone();
            e2.facts = e.facts.and(&case);
            let mut extra = Facts::default();
            for (cf, cg) in comps[e.from].iter().zip(&comps[e.to]) {
                let (r, eq) = self.rel_at(group, cf, cg, &e2, &extra, top);
                match r {
                    Rel::Lt => continue 'case,
                    Rel::Le => {
                        if !eq.is_empty() {
                            extra.push_dnf(eq);
                        }
                    }
                    Rel::Unknown => return false,
                }
            }
            return false;
        }
        true
    }

    /// The lexicographic search (with `inv`, the facts at every call into a function are
    /// assumed in its own calls, and its rank is guarded by them).
    fn search(&self, group: &[FnDef], edges0: &[Edge], inv: bool) -> Option<Vec<Vec<Comp>>> {
        let n = group.len();
        let mut edges = edges0.to_vec();
        let invs = if inv {
            let v = self.invariants(group, &edges);
            if v.iter().all(|x| x.is_empty()) {
                return None;
            }
            for e in &mut edges {
                e.facts.extend(v[e.from].iter().cloned());
            }
            v
        } else {
            vec![vec![]; n]
        };
        let cands = self.candidates(group, &edges);
        let mut comps: Vec<Vec<Comp>> = vec![vec![]; n];
        let mut rem: Remaining = (0..edges.len()).map(|i| (i, Facts::default())).collect();
        let apply = |rem: Remaining, rels: Vec<(Rel, Vec<Vec<Lin>>)>| -> Remaining {
            rem.into_iter()
                .zip(rels)
                .filter(|(_, (r, _))| *r != Rel::Lt)
                .map(|((i, mut f), (_, eq))| {
                    if !eq.is_empty() {
                        f.push_dnf(eq);
                    }
                    (i, f)
                })
                .collect()
        };
        let involved = |rem: &Remaining| -> BTreeSet<usize> {
            rem.iter()
                .flat_map(|(i, _)| [edges[*i].from, edges[*i].to])
                .collect()
        };
        while !rem.is_empty() {
            if comps[0].len() >= 5 {
                return None;
            }
            let inv_fns = involved(&rem);
            let dist_opts: Vec<Vec<Comp>> = (0..n)
                .map(|f| {
                    let mut o = if inv_fns.contains(&f) {
                        cands[f].clone()
                    } else {
                        vec![]
                    };
                    o.push(Comp::Zero);
                    o
                })
                .collect();
            let shape_opts: Vec<Vec<Comp>> = (0..n)
                .map(|f| {
                    let mut o = Vec::new();
                    if self.arity && inv_fns.contains(&f) {
                        for (k, t) in group[f].arg_tys.iter().enumerate() {
                            if !self.builtin.contains(t) {
                                o.push(Comp::Shape(k));
                            }
                        }
                    }
                    o.push(Comp::Zero);
                    o
                })
                .collect();
            let mut found = None;
            if let Some(r) = self.ranks(n, &edges, &rem) {
                let rels: Vec<(Rel, Vec<Vec<Lin>>)> = rem
                    .iter()
                    .map(|(i, _)| {
                        let e = &edges[*i];
                        (
                            if r[e.to] < r[e.from] {
                                Rel::Lt
                            } else {
                                Rel::Le
                            },
                            vec![],
                        )
                    })
                    .collect();
                found = Some((r.into_iter().map(Comp::Rank).collect(), rels));
            }
            if found.is_none() {
                found = self.step(group, &edges, &rem, &dist_opts, &comps, true);
            }
            if found.is_none() {
                found = self.step(group, &edges, &rem, &shape_opts, &comps, true);
            }
            if found.is_none() {
                // a component that only does not increase, whose equality makes a next one
                // decrease (a counter's distance to a bound, then what decreases beyond it)
                'look: for f in 0..n {
                    for c in &dist_opts[f] {
                        if *c == Comp::Zero {
                            continue;
                        }
                        let one: Vec<Vec<Comp>> = (0..n)
                            .map(|g| {
                                if g == f {
                                    vec![c.clone()]
                                } else {
                                    vec![Comp::Zero]
                                }
                            })
                            .collect();
                        let Some((c1, r1)) = self.step(group, &edges, &rem, &one, &comps, false)
                        else {
                            continue;
                        };
                        if r1.iter().all(|(_, eq)| eq.is_empty()) {
                            continue;
                        }
                        let rem2 = apply(rem.clone(), r1.clone());
                        let mut comps2 = comps.clone();
                        for g in 0..n {
                            comps2[g].push(c1[g].clone());
                        }
                        if let Some((c2, r2)) =
                            self.step(group, &edges, &rem2, &dist_opts, &comps2, true)
                        {
                            comps = comps2;
                            rem = rem2;
                            found = Some((c2, r2));
                            break 'look;
                        }
                    }
                }
            }
                let (choice, rels) = found?;
            for f in 0..n {
                comps[f].push(choice[f].clone());
            }
            rem = apply(rem, rels);
        }
        if inv {
            // the rank, guarded by the facts at the calls into the function
            if !comps[0].iter().any(|c| matches!(c, Comp::Rank(_))) {
                for c in comps.iter_mut() {
                    c.push(Comp::Rank(0));
                }
            }
            for f in 0..n {
                if invs[f].is_empty() {
                    continue;
                }
                let fields = self.field_names(&edges, f);
                let view = self.view_of(&invs[f], &fields, None).ok()?;
                if let Some((k, _)) = &view
                    && comps[f]
                        .iter()
                        .any(|c| matches!(c, Comp::Dist(_, Some((k2, _))) if k2 != k))
                {
                    return None;
                }
                let pos = comps[f].iter().rposition(|c| matches!(c, Comp::Rank(_)))?;
                let Comp::Rank(r) = comps[f][pos] else {
                    unreachable!()
                };
                comps[f][pos] = Comp::GRank(invs[f].clone(), r, view);
            }
        }
        // the whole measure, checked again at every call (without the assumed facts)
        if edges0.iter().all(|e| self.verify(group, &comps, e)) {
            Some(comps)
        } else {
            None
        }
    }
}

impl Ctx {
    /// Plan the measures of a recursive group whose functions Lean's own search does not cover
    /// (`None`: no plan found; Lean then searches as before).
    pub fn plan_group(&self, group: &[FnDef]) -> Option<GroupPlan> {
        self.lemmas.borrow_mut().used.clear();
        let edges = self.edges(group);
        if edges.is_empty() {
            return None;
        }
        let debug = std::env::var_os("K2LEAN_TERM_DEBUG").is_some();
        if debug {
            eprintln!(
                "plan_group {:?}",
                group.iter().map(|f| &f.lean).collect::<Vec<_>>()
            );
            for e in &edges {
                eprintln!(
                    "  edge {} -> {} args {:?}\n    facts {:?}\n    alts {:?}\n    views {:?}",
                    group[e.from].lean,
                    group[e.to].lean,
                    e.args.iter().map(|a| a.render()).collect::<Vec<_>>(),
                    e.facts.base.iter().map(render_fact).collect::<Vec<_>>(),
                    e.facts
                        .alts
                        .iter()
                        .map(|d| d
                            .iter()
                            .map(|c| c.iter().map(render_fact).collect::<Vec<_>>())
                            .collect::<Vec<_>>())
                        .collect::<Vec<_>>(),
                    e.views
                        .iter()
                        .map(|(k, p)| (k, p.render()))
                        .collect::<Vec<_>>()
                );
            }
            for (i, c) in self.candidates(group, &edges).iter().enumerate() {
                eprintln!(
                    "  cands {}: {:?}",
                    group[i].lean,
                    c.iter()
                        .map(|c| self.render_comp(c, 9, false))
                        .collect::<Vec<_>>()
                );
            }
        }
        let comps = self.search(group, &edges, false);
        if debug {
            eprintln!(
                "  plain search: {:?}",
                comps.as_ref().map(|c| c
                    .iter()
                    .map(|x| x
                        .iter()
                        .map(|y| self.render_comp(y, 9, false))
                        .collect::<Vec<_>>())
                    .collect::<Vec<_>>())
            );
        }
        let comps = comps.or_else(|| {
            if debug {
                for (i, v) in self.invariants(group, &edges).iter().enumerate() {
                    eprintln!(
                        "  invariant {}: {:?}",
                        group[i].lean,
                        v.iter().map(render_fact).collect::<Vec<_>>()
                    );
                }
            }
            self.search(group, &edges, true)
        })?;
        self.prune(group, &comps);
        Some(self.render_plan(group, &edges, &comps))
    }

    /// Drop the facts of the result lemmas the plan uses that it does not need (each checked by
    /// verifying the plan again without it), then those of the lemmas their proofs use that the
    /// remaining facts do not need; rewrite the texts of the lemmas that changed.
    fn prune(&self, group: &[FnDef], comps: &[Vec<Comp>]) {
        let ok_plan = || {
            let edges = self.edges(group);
            edges.iter().all(|e| self.verify(group, comps, e))
        };
        // the lemmas, top down: those the plan uses, then the lemmas their proofs use
        let mut order: Vec<String> = Vec::new();
        let mut todo: Vec<String> = self.lemmas.borrow().used.iter().cloned().collect();
        while let Some(n) = todo.pop() {
            if order.contains(&n) {
                continue;
            }
            order.push(n.clone());
            if let Some((_, deps)) = self.lemmas.borrow().text.get(&n) {
                todo.extend(deps.iter().cloned());
            }
        }
        let direct: BTreeSet<String> = self.lemmas.borrow().used.clone();
        let mut changed: BTreeSet<String> = BTreeSet::new();
        for n in &order {
            let Some(key) = self.lemmas.borrow().by_name.get(n).cloned() else {
                continue;
            };
            if self.lemmas.borrow().emitted.contains(n) {
                continue;
            }
            let Some(Some(lm)) = self.lemmas.borrow().out.get(&key).cloned() else {
                continue;
            };
            // the lemmas whose proofs use this one
            let users: Vec<String> = self
                .lemmas
                .borrow()
                .text
                .iter()
                .filter(|(_, (_, d))| d.contains(n))
                .map(|(k, _)| k.clone())
                .collect();
            let mut facts = lm.facts.clone();
            for i in (0..facts.len()).rev() {
                let mut trial = facts.clone();
                trial.remove(i);
                self.lemmas.borrow_mut().out.insert(
                    key.clone(),
                    Some(Lemma {
                        facts: trial.clone(),
                        ..lm.clone()
                    }),
                );
                let users_ok = users.iter().all(|u| self.lemma_holds(u));
                if users_ok && (!direct.contains(n) || ok_plan()) {
                    facts = trial;
                } else {
                    self.lemmas.borrow_mut().out.insert(
                        key.clone(),
                        Some(Lemma {
                            facts: facts.clone(),
                            ..lm.clone()
                        }),
                    );
                }
            }
            if facts.len() != lm.facts.len() {
                changed.insert(n.clone());
            }
        }
        for n in changed {
            let Some(key) = self.lemmas.borrow().by_name.get(&n).cloned() else {
                continue;
            };
            let Some(Some(lm)) = self.lemmas.borrow().out.get(&key).cloned() else {
                continue;
            };
            let Some(f) = self.fns.get(&lm.fname).cloned() else {
                continue;
            };
            if lm.facts.is_empty() {
                self.lemmas.borrow_mut().text.remove(&n);
                continue;
            }
            let mut ftys = BTreeMap::new();
            self.field_types(&lm.pattern, &mut ftys);
            let f2 = FnDef {
                unfold: lm.unfolds.clone(),
                ..f
            };
            let text = self.out_text(&f2, &lm, &ftys);
            if let Some(e) = self.lemmas.borrow_mut().text.get_mut(&n) {
                e.0 = text;
            }
        }
    }

    /// Whether a result lemma's facts still follow from its function's equations (with the
    /// lemmas its proof uses, as they now are).
    fn lemma_holds(&self, name: &str) -> bool {
        let Some(key) = self.lemmas.borrow().by_name.get(name).cloned() else {
            return true;
        };
        let Some(Some(lm)) = self.lemmas.borrow().out.get(&key).cloned() else {
            return true;
        };
        let Some(f) = self.fns.get(&lm.fname).cloned() else {
            return false;
        };
        let (mut d, mut u) = (Vec::new(), Vec::new());
        let Some(leaves) = self.leaves(&f, &lm.pattern, &mut d, &mut u) else {
            return false;
        };
        leaves
            .iter()
            .all(|l| lm.facts.iter().all(|g| l.infeasible() || l.entails(g)))
    }

    fn render_comp(&self, c: &Comp, top: i128, default: bool) -> String {
        match c {
            Comp::Zero => "0".into(),
            Comp::Rank(n) => n.to_string(),
            Comp::Dist(_, Some(_)) if default => "0".into(),
            Comp::Dist(l, _) => format!("({}).toNat", l.render()),
            Comp::Shape(k) => format!("{SHAPE} x{k}"),
            Comp::GRank(_, _, Some(_)) if default => top.to_string(),
            Comp::GRank(g, n, _) => {
                let gs: Vec<String> = g.iter().map(render_fact).collect();
                format!("if {} then {n} else {top}", gs.join(" ∧ "))
            }
        }
    }

    fn render_plan(&self, group: &[FnDef], edges: &[Edge], comps: &[Vec<Comp>]) -> GroupPlan {
        let n = group.len();
        let top = n as i128 + 1;
        let mut defs = String::new();
        let mut def_names = Vec::new();
        let mut measures = Vec::new();
        let mut shape = false;
        for (fi, f) in group.iter().enumerate() {
            let cs = &comps[fi];
            shape |= cs.iter().any(|c| matches!(c, Comp::Shape(_)));
            let view = cs.iter().find_map(|c| match c {
                Comp::Dist(_, Some(v)) | Comp::GRank(_, _, Some(v)) => Some(v.clone()),
                _ => None,
            });
            let tuple = |default: bool| -> String {
                let r: Vec<String> = cs
                    .iter()
                    .map(|c| self.render_comp(c, top, default))
                    .collect();
                if r.len() == 1 {
                    r[0].clone()
                } else {
                    format!("({})", r.join(", "))
                }
            };
            match view {
                None => measures.push(tuple(false)),
                Some((k, p)) => {
                    let name = format!("{}.k2l_measure", f.lean);
                    let ty = vec!["Nat"; cs.len()].join(" × ");
                    let ps: Vec<String> = f
                        .params
                        .iter()
                        .zip(&f.arg_tys)
                        .map(|(x, t)| format!("({x} : {t})"))
                        .collect();
                    let mut d = format!(
                        "{}/-- `{}`'s termination measure (generated). -/\ndef {name} {} : {ty} :=\n  match x{k} with\n  | {} => {}\n",
                        self.omit(false),
                        f.lean.trim_start_matches("K."),
                        ps.join(" "),
                        p.render(),
                        tuple(false)
                    );
                    if !self.irrefutable(&p) {
                        d.push_str(&format!("  | _ => {}\n", tuple(true)));
                    }
                    defs.push_str(&d);
                    defs.push('\n');
                    measures.push(format!("{name} {}", f.params.join(" ")));
                    def_names.push(name);
                }
            }
        }
        let _ = edges;
        let used: Vec<String> = self.lemmas.borrow().used.iter().cloned().collect();
        if shape
            || used
                .iter()
                .any(|u| u.ends_with("k2l_shape") || u.contains(".k2l_shape"))
        {
            self.lemmas.borrow_mut().shape_used = true;
        }
        let lemmas = self.take(&used);
        let mut simps: BTreeSet<String> = BTreeSet::new();
        for f in group {
            self.fn_ctor_names(f, &mut simps);
        }
        let mut simps: Vec<String> = self.simp_names(simps);
        if shape || used.iter().any(|u| u.contains(".k2l_shape")) {
            simps.insert(0, "Term.shape".into());
            simps.insert(0, "Term.shape_eq".into());
        }
        GroupPlan {
            measures,
            decreasing: format!(
                "all_goals k2l_decreasing_m [{}] using [{}]",
                def_names.join(", "),
                simps.join(", ")
            ),
            pre: format!("{lemmas}{defs}"),
        }
    }
}

/// A short tag of a function's Lean name, for renaming its variables apart.
fn names_tag(lean: &str) -> String {
    let t: String = lean
        .trim_start_matches("K.")
        .chars()
        .filter(|c| c.is_ascii_alphanumeric())
        .take(12)
        .collect();
    format!("v{t}")
}

/// The heads of the applications in a term.
fn heads(l: &L, out: &mut BTreeSet<String>) {
    match l {
        L::App(h, args) => {
            out.insert(h.clone());
            args.iter().for_each(|a| heads(a, out));
        }
        L::Typed(e, _) => heads(e, out),
        _ => {}
    }
}

impl Ctx {
    /// Whether a function uses a parameter of the library (`Hooks`), directly or through a callee
    /// already recorded.
    pub fn uses_hooks(&self, f: &FnDef) -> bool {
        let mut hs = BTreeSet::new();
        for (steps, _, rhs) in &f.eqs {
            heads(rhs, &mut hs);
            for s in steps {
                match s {
                    Step::Bind { expr, .. } => heads(expr, &mut hs),
                    Step::Cond { cond, .. } => heads(cond, &mut hs),
                    Step::CondEq { lhs, rhs, .. } => {
                        heads(lhs, &mut hs);
                        heads(rhs, &mut hs);
                    }
                    Step::MapElem { key, .. } => heads(key, &mut hs),
                    _ => {}
                }
            }
        }
        hs.iter()
            .any(|h| h.starts_with("Hooks.") || self.fns.get(h).is_some_and(|g| g.hooks))
    }
}

impl Ctx {
    /// Whether every recursive call of the group passes a piece of one of the caller's parameters
    /// (a variable of a constructor or list pattern on it, or constructors over such pieces):
    /// structural recursion, which Lean's own search (`sizeOf`) proves.
    pub fn structural(&self, group: &[FnDef]) -> bool {
        let names: BTreeSet<&str> = group.iter().map(|f| f.lean.as_str()).collect();
        fn piece(ctx: &Ctx, t: &L, sub: &BTreeSet<String>, some: &mut bool) -> bool {
            match t {
                L::Var(v) => {
                    *some |= sub.contains(v);
                    sub.contains(v)
                }
                L::App(h, args) if ctx.ctors.contains_key(h) || ctx.injs.contains_key(h) => {
                    args.iter().all(|a| piece(ctx, a, sub, some))
                }
                _ => false,
            }
        }
        for f in group {
            for (steps, _, _) in &f.eqs {
                let mut whole: BTreeSet<String> = f.params.iter().cloned().collect();
                let mut sub: BTreeSet<String> = BTreeSet::new();
                for s in steps {
                    match s {
                        Step::Destruct { scrut, pat, .. } => {
                            if whole.contains(scrut) || sub.contains(scrut) {
                                let mut vs = Vec::new();
                                pattern_vars(pat, &mut vs);
                                if matches!(pat, L::Var(_)) && !sub.contains(scrut) {
                                    whole.extend(vs);
                                } else {
                                    sub.extend(vs);
                                }
                            }
                        }
                        Step::ListElem {
                            list, head, tail, ..
                        } if whole.contains(list) || sub.contains(list) => {
                            sub.insert(head.clone());
                            sub.insert(tail.clone());
                        }
                        Step::Bind {
                            expr: L::App(h, args),
                            ..
                        } if names.contains(h.as_str()) => {
                            let ok = args.iter().any(|a| {
                                let mut some = false;
                                piece(self, a, &sub, &mut some) && some
                            });
                            if !ok {
                                return false;
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    //! The linear-arithmetic core of the measure synthesis.
    use super::*;

    fn v(a: &str) -> Lin {
        Lin::atom(a)
    }

    #[test]
    fn entailment_by_elimination() {
        // x ≥ 1, y ≥ x + 2 ⊢ y ≥ 3, but not y ≥ 4
        let facts = vec![v("x").plus(-1), v("y").add(&v("x"), -1).plus(-2)];
        assert!(entails(&facts, &v("y").plus(-3)));
        assert!(!entails(&facts, &v("y").plus(-4)));
        // integers: 2x ≥ 1 ⊢ x ≥ 1
        assert!(entails(&[v("x").scale(2).plus(-1)], &v("x").plus(-1)));
        // a contradiction entails anything
        assert!(entails(&[v("x").plus(-1), v("x").scale(-1)], &v("z")));
    }

    #[test]
    fn lower_bound_over_alternatives() {
        // r = 1 (one way) or r = x - 90 with 92 ≤ x ≤ 99 (the other): r ≥ 1
        let a = vec![v("r").plus(-1), v("r").scale(-1).plus(1)];
        let b = vec![
            v("r").add(&v("x"), -1).plus(90),
            v("x").add(&v("r"), -1).plus(-90),
            v("x").plus(-92),
            v("x").scale(-1).plus(99),
        ];
        assert_eq!(
            lower_bound(&[a.clone(), b.clone()], &v("r")),
            Bound::Lower(1)
        );
        assert_eq!(lower_bound(&[a, b], &v("r").scale(-1)), Bound::Lower(-9));
        assert_eq!(lower_bound(&[vec![]], &v("r")), Bound::None);
        assert_eq!(lower_bound(&[vec![Lin::konst(-1)]], &v("r")), Bound::Never);
    }

    #[test]
    fn a_failed_conjunction_is_a_disjunction() {
        let c = L::app(
            "KPrelude.BoolHook.and",
            vec![
                L::app(
                    "KPrelude.IntHook.ge",
                    vec![L::Var("x".into()), L::Raw("(192 : Int)".into())],
                ),
                L::app(
                    "KPrelude.IntHook.lt",
                    vec![L::Var("x".into()), L::Raw("(248 : Int)".into())],
                ),
            ],
        );
        let d = cond_dnf(&c, false);
        assert_eq!(d.len(), 2);
        // with x ≥ 192 known, the failure leaves x ≥ 248
        let mut f = Facts::default();
        f.push(v("x").plus(-192));
        f.push_dnf(d);
        assert!(f.entails(&v("x").plus(-248)));
    }

    #[test]
    fn template_facts_find_sums() {
        // two ways a header is built: (L, P) = (1, s), or (X - 192, s + 1) with X ≥ 192
        let a = vec![
            v("L").plus(-1),
            v("L").scale(-1).plus(1),
            v("P").add(&v("s"), -1),
            v("s").add(&v("P"), -1),
        ];
        let b = vec![
            v("L").add(&v("X"), -1).plus(192),
            v("X").add(&v("L"), -1).plus(-192),
            v("P").add(&v("s"), -1).plus(-1),
            v("s").add(&v("P"), -1).plus(1),
            v("X").plus(-192),
        ];
        let targets: Vec<String> = ["s", "L", "P"].iter().map(|x| x.to_string()).collect();
        let facts = template_facts(&[a, b], &directions(&targets));
        // the item ends after its start: L + P - s ≥ 1
        assert!(entails(
            &facts,
            &v("L").add(&v("P"), 1).add(&v("s"), -1).plus(-1)
        ));
    }
}
