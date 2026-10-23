//! Termination measures for recursive functions.
//!
//! A recursive K function is a well-founded Lean definition. Lean's own measure search
//! (`GuessLex`) only tries `sizeOf` of each parameter; this module adds the measures that K
//! definitions count with, computed from the lowered equations:
//!
//! * integer distances `(u - t).toNat`, from a bound `t < u` or `t ≤ u` that holds at a recursive
//!   call: the call's own requires, a failed earlier equation whose guard is a single comparison
//!   (an `owise` equation after `requires N <=Int 0`), or the range of a defined partial hook
//!   (`B[I]` defined: `I < lengthBytes(B)`);
//! * constructor ranks: a parameter matched by a constructor and passed a different constructor
//!   at the call (a hard fork's schedule falling back to the previous one), ranked by the longest
//!   chain of such calls, which must be acyclic.
//!
//! For each recursive call and each candidate measure, a symbolic check on linear forms says
//! whether the measure decreases (`<`), does not increase (`≤`), or is not known (`?`); a
//! lexicographic combination is then searched as `GuessLex` does (pick a measure that is `≤` on
//! every remaining call and `<` on at least one, drop the `<` calls, repeat). The check is only
//! a heuristic for choosing the measure: the proof is Lean's (`k2l_decreasing`, `omega`), so a
//! wrong choice is a build error, never an unsound definition. When no combination is found the
//! generator leaves the measure to Lean.

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
}

fn compound_atom(l: &L) -> Lin {
    let a = l.render();
    let mut vs = BTreeSet::new();
    vars_of(l, &mut vs);
    ATOM_VARS.with(|m| m.borrow_mut().insert(a.clone(), vs));
    Lin::atom(&a)
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
        ("KPrelude.IntHook.emod", [_, L::Raw(c)]) => {
            if let Some(c) = int_lit(c)
                && c > 0
            {
                let r = Lin::atom(var);
                facts.push(r.clone());
                facts.push(Lin::konst(c - 1).add(&r, -1));
            }
        }
        _ => {}
    }
}
