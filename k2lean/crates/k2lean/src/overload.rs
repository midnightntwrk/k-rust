//! Matching modulo overload axioms.
//!
//! An overload axiom `f(inj{A1,S1}(x1), …) = inj{Sub,S}(g(x1, …))` (`symbol-overload`) makes the
//! term `f(…)` of the super symbol equal to the injected sub symbol's term. Values are kept in
//! normal form (the generated normalizer `K.f` rewrites `f` to `g` whenever its arguments allow),
//! so in the model a value equal to `f(p1, …, pn)` is either built with `f` itself, or is
//! `inj(g(q1, …, qn))` with each `pi` equal to `inj(qi)`. A left-hand side that mentions `f` is
//! therefore the union of its variants: the pattern with `f`, and one pattern per overload axiom
//! with `inj(g(…))` in its place (a variable `pi` of the super sort becomes `inj(xi)` for a fresh
//! variable `xi` of the sub sort, everywhere in the rule). Matching logic reads the pattern modulo
//! the axioms; the variants, matched syntactically against normal forms, have exactly the same
//! instances.

use crate::ir::{Def, P, S};
use crate::model::Model;
use std::collections::BTreeMap;

/// One overload axiom: argument sorts of the super symbol's injected arguments, the sub symbol.
struct Ov {
    /// (sub argument sort A_i, super argument sort S_i)
    args: Vec<(String, String)>,
    sub_sym: String,
    sub_sort: String,
    super_sort: String,
}

fn overloads(def: &Def, f: &str) -> Vec<Ov> {
    let mut out = Vec::new();
    for a in &def.axioms {
        if !a.attrs.has("symbol-overload") {
            continue;
        }
        let P::Equals(_, _, l, r) = &a.pattern else {
            continue;
        };
        let P::App(g, _, largs) = &**l else { continue };
        if g != f {
            continue;
        }
        let mut args = Vec::new();
        let mut ok = true;
        for x in largs {
            match x {
                P::App(i, ps, _) if i == "inj" => match (ps[0].name(), ps[1].name()) {
                    (Some(a), Some(b)) => args.push((a.to_string(), b.to_string())),
                    _ => ok = false,
                },
                _ => ok = false,
            }
        }
        let P::App(i, ps, inner) = &**r else { continue };
        if !ok || i != "inj" || inner.len() != 1 {
            continue;
        }
        let Some(P::App(sub_sym, _, _)) = inner.first() else {
            continue;
        };
        let (Some(sub_sort), Some(super_sort)) = (ps[0].name(), ps[1].name()) else {
            continue;
        };
        out.push(Ov {
            args,
            sub_sym: sub_sym.clone(),
            sub_sort: sub_sort.to_string(),
            super_sort: super_sort.to_string(),
        });
    }
    out
}

type Subst = Vec<(String, P)>;

/// An overload axiom as the expander caches it: (argument sort pairs, sub symbol, sub sort, super sort).
type OvEntry = (Vec<(String, String)>, String, String, String);

pub struct Expander<'a> {
    def: &'a Def,
    m: &'a Model,
    counter: usize,
    /// super symbol → its overload axioms (cached)
    ovs: BTreeMap<String, Vec<OvEntry>>,
}

fn sort_p(n: &str) -> S {
    S::App(n.to_string(), vec![])
}

impl<'a> Expander<'a> {
    pub fn new(def: &'a Def, m: &'a Model) -> Self {
        Expander {
            def,
            m,
            counter: 0,
            ovs: BTreeMap::new(),
        }
    }

    fn ovs_of(&mut self, f: &str) -> Vec<OvEntry> {
        if !self.ovs.contains_key(f) {
            let v = overloads(self.def, f)
                .into_iter()
                .filter(|o| {
                    o.args
                        .iter()
                        .all(|(a, b)| self.m.sorts.contains_key(a) && self.m.sorts.contains_key(b))
                        && self.m.sorts.contains_key(&o.sub_sort)
                })
                .map(|o| (o.args, o.sub_sym, o.sub_sort, o.super_sort))
                .collect();
            self.ovs.insert(f.to_string(), v);
        }
        self.ovs[f].clone()
    }

    /// The variants of pattern `p`: (pattern, substitution of the rule's variables).
    pub fn expand(&mut self, p: &P) -> Vec<(P, Subst)> {
        match p {
            P::App(f, ps, args) => {
                // the variants of the arguments, combined
                let mut combos: Vec<(Vec<P>, Subst)> = vec![(vec![], vec![])];
                for a in args {
                    let va = self.expand(a);
                    let mut next = Vec::new();
                    for (prefix, s) in &combos {
                        for (q, s2) in &va {
                            let mut pre = prefix.clone();
                            pre.push(q.clone());
                            let mut ss = s.clone();
                            ss.extend(s2.iter().cloned());
                            next.push((pre, ss));
                        }
                    }
                    combos = next;
                }
                let mut out: Vec<(P, Subst)> = combos
                    .iter()
                    .map(|(a, s)| (P::App(f.clone(), ps.clone(), a.clone()), s.clone()))
                    .collect();
                if f != "inj"
                    && self.m.anywhere.contains(f)
                    && !self.def.symbols.get(f).is_some_and(|d| d.is_function())
                {
                    for (oargs, sub_sym, sub_sort, super_sort) in self.ovs_of(f) {
                        // each argument must equal `inj{A_i,S_i}(q_i)`
                        let mut acombos: Vec<(Vec<P>, Subst)> = vec![(vec![], vec![])];
                        for (a, (asub, asup)) in args.iter().zip(&oargs) {
                            let ra = self.restrict(a, asub, asup);
                            let mut next = Vec::new();
                            for (prefix, s) in &acombos {
                                for (q, s2) in &ra {
                                    let mut pre = prefix.clone();
                                    pre.push(q.clone());
                                    let mut ss = s.clone();
                                    ss.extend(s2.iter().cloned());
                                    next.push((pre, ss));
                                }
                            }
                            acombos = next;
                        }
                        for (qs, s) in acombos {
                            let inner = P::App(sub_sym.clone(), vec![], qs);
                            out.push((
                                P::App(
                                    "inj".into(),
                                    vec![sort_p(&sub_sort), sort_p(&super_sort)],
                                    vec![inner],
                                ),
                                s,
                            ));
                        }
                    }
                }
                out
            }
            P::And(s, ps) => {
                // conjuncts are matched against the same value; expand the non-variables
                let mut combos: Vec<(Vec<P>, Subst)> = vec![(vec![], vec![])];
                for a in ps {
                    let va = self.expand(a);
                    let mut next = Vec::new();
                    for (prefix, sb) in &combos {
                        for (q, s2) in &va {
                            let mut pre = prefix.clone();
                            pre.push(q.clone());
                            let mut ss = sb.clone();
                            ss.extend(s2.iter().cloned());
                            next.push((pre, ss));
                        }
                    }
                    combos = next;
                }
                combos
                    .into_iter()
                    .map(|(a, sb)| (P::And(s.clone(), a), sb))
                    .collect()
            }
            other => vec![(other.clone(), vec![])],
        }
    }

    /// The ways `p` (of sort `sup`) can equal `inj{sub,sup}(q)`: the patterns `q` at `sub`.
    fn restrict(&mut self, p: &P, sub: &str, sup: &str) -> Vec<(P, Subst)> {
        match p {
            P::Var(v, _) => {
                self.counter += 1;
                let x = format!("{v}'Ov{}", self.counter);
                let xs = sort_p(sub);
                vec![(
                    P::Var(x.clone(), xs.clone()),
                    vec![(
                        v.clone(),
                        P::App(
                            "inj".into(),
                            vec![xs, sort_p(sup)],
                            vec![P::Var(x, sort_p(sub))],
                        ),
                    )],
                )]
            }
            P::App(i, ps, inner) if i == "inj" => {
                let b = ps[0].name().unwrap_or_default().to_string();
                if b == sub {
                    self.expand(&inner[0])
                } else if self.m.subsort_closure(&b, sub) {
                    self.expand(&inner[0])
                        .into_iter()
                        .map(|(q, s)| {
                            (
                                P::App("inj".into(), vec![sort_p(&b), sort_p(sub)], vec![q]),
                                s,
                            )
                        })
                        .collect()
                } else {
                    vec![]
                }
            }
            P::App(..) => {
                // a constructor of the super sort equals an injection only through an overload
                self.expand(p)
                    .into_iter()
                    .filter_map(|(q, s)| match &q {
                        P::App(i, ps, inner) if i == "inj" => {
                            let b = ps[0].name().unwrap_or_default().to_string();
                            if b == sub {
                                Some((inner[0].clone(), s))
                            } else if self.m.subsort_closure(&b, sub) {
                                Some((
                                    P::App(
                                        "inj".into(),
                                        vec![sort_p(&b), sort_p(sub)],
                                        inner.clone(),
                                    ),
                                    s,
                                ))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    })
                    .collect()
            }
            _ => vec![],
        }
    }
}

/// Apply a variable substitution to a pattern.
pub fn subst(p: &P, s: &Subst) -> P {
    if s.is_empty() {
        return p.clone();
    }
    match p {
        P::Var(v, _) => s
            .iter()
            .find(|(n, _)| n == v)
            .map(|(_, t)| t.clone())
            .unwrap_or_else(|| p.clone()),
        P::App(f, ps, args) => P::App(
            f.clone(),
            ps.clone(),
            args.iter().map(|a| subst(a, s)).collect(),
        ),
        P::And(x, ps) => P::And(x.clone(), ps.iter().map(|a| subst(a, s)).collect()),
        P::Or(x, ps) => P::Or(x.clone(), ps.iter().map(|a| subst(a, s)).collect()),
        P::Not(x, a) => P::Not(x.clone(), Box::new(subst(a, s))),
        P::Equals(a, b, l, r) => P::Equals(
            a.clone(),
            b.clone(),
            Box::new(subst(l, s)),
            Box::new(subst(r, s)),
        ),
        P::In(a, b, l, r) => P::In(
            a.clone(),
            b.clone(),
            Box::new(subst(l, s)),
            Box::new(subst(r, s)),
        ),
        P::Ceil(a, b, x) => P::Ceil(a.clone(), b.clone(), Box::new(subst(x, s))),
        other => other.clone(),
    }
}
