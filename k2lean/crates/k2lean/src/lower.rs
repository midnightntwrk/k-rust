//! Lowering KORE patterns to Lean: left-hand sides become a sequence of match steps (rendered
//! as an executable matcher and, by substitution, as the indices and hypotheses of a relation
//! constructor); terms become Lean expressions, with every partial function application bound
//! to a variable first (matching logic is strict in `⊥`: an application with an undefined
//! argument is undefined).

use crate::ir::{P, S};
use crate::model::{Builtin, Coll, Kind, Model};
use crate::names;
use std::collections::{BTreeMap, BTreeSet};

/// A small Lean term AST.
#[derive(Clone, Debug, PartialEq)]
pub enum L {
    Var(String),
    App(String, Vec<L>),
    Raw(String),
}

impl L {
    pub fn app(h: impl Into<String>, args: Vec<L>) -> L {
        L::App(h.into(), args)
    }
    pub fn render(&self) -> String {
        match self {
            L::Var(v) => v.clone(),
            L::Raw(r) => r.clone(),
            L::App(h, args) => {
                if args.is_empty() {
                    h.clone()
                } else {
                    let mut s = h.clone();
                    for a in args {
                        s.push(' ');
                        s.push_str(&a.render_arg());
                    }
                    s
                }
            }
        }
    }
    pub fn render_arg(&self) -> String {
        match self {
            L::App(_, args) if !args.is_empty() => format!("({})", self.render()),
            L::Raw(r) if r.contains(' ') && !(r.starts_with('(') && r.ends_with(')')) => {
                format!("({r})")
            }
            _ => self.render(),
        }
    }
    pub fn subst(&self, s: &BTreeMap<String, L>) -> L {
        match self {
            L::Var(v) => match s.get(v) {
                Some(t) => t.subst(s),
                None => self.clone(),
            },
            L::Raw(_) => self.clone(),
            L::App(h, args) => L::App(h.clone(), args.iter().map(|a| a.subst(s)).collect()),
        }
    }
}

/// A function the generated code can call.
#[derive(Clone, Debug)]
pub struct FnSig {
    pub lean: String,
    pub partial: bool,
    pub args: Vec<String>,
    pub result: String,
}

pub type Fns = BTreeMap<String, FnSig>;

#[derive(Clone, Debug)]
pub enum Step {
    /// `match [h :] scrut with | pat => … | _ => fail` (no fallback when `pat` is irrefutable)
    Destruct {
        scrut: String,
        pat: L,
        hyp: Option<String>,
        refutable: bool,
    },
    /// `match hyp : expr with | some var => … | none => fail`; relation: `expr = some var`
    Bind { expr: L, var: String, hyp: String },
    /// `if hyp : cond = true then … else fail`; relation: `cond = true`
    Cond { cond: L, hyp: String },
    /// `if hyp : lhs = rhs then … else fail`; relation: `lhs = rhs`
    CondEq { lhs: L, rhs: L, hyp: String },
    /// `if hyp : b = a then … else fail`; relation: `b` is `a`
    EqVar { a: String, b: String, hyp: String },
    /// The map pattern `key |-> val rest` at `map`, `key` bound.
    /// Executable: `MapHook.wfb map`, `MapHook.lookup map key = some val`, `rest := remove map key`.
    /// Relation: `MapHook.concat (MapHook.element key val) rest = some map`.
    MapElem {
        map: String,
        key: L,
        val: String,
        rest: String,
        wf_hyp: String,
        lookup_hyp: String,
        hyp: String,
    },
    /// The map pattern `key |-> val rest` at `map` with a free key: every binding is a match.
    /// Executable: `MapHook.wfb map`, then `MapHook.choose` over the bindings (`cert` names the
    /// certificate it passes, `rest := remove map key`). Relation: as `MapElem`.
    MapChoose {
        map: String,
        key: String,
        val: String,
        rest: String,
        wf_hyp: String,
        cert: String,
        hyp: String,
    },
    /// The list pattern `ListItem(head) tail` (`front`) or `tail ListItem(head)` at `list`.
    /// Executable: `ListHook.uncons` / `ListHook.unsnoc`. Relation: `list` is the concatenation.
    ListElem {
        list: String,
        head: String,
        tail: String,
        front: bool,
        hyp: String,
    },
}

pub struct Lower<'a> {
    pub m: &'a Model,
    pub fns: &'a Fns,
    /// KORE variable name → Lean variable.
    pub vars: BTreeMap<String, String>,
    /// Lean variable → Lean type.
    pub ty: BTreeMap<String, String>,
    pub steps: Vec<Step>,
    used: BTreeSet<String>,
    counter: usize,
    late: Vec<(P, String, String)>,
    refutable: bool,
}

enum Deferred {
    Pat(P, String, String),
    /// `inj{A,B}(p)` with `A` a sum sort: project the `B` value `y` to `A`, then match `p`.
    Proj {
        y: String,
        from: String,
        to: String,
        pat: P,
    },
}

pub type R<T> = Result<T, String>;

fn sanitize(kore_var: &str) -> String {
    let d = names::demangle(kore_var);
    let d = d.strip_prefix("Var").unwrap_or(&d).to_string();
    let mut s: String = d
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    s = s.trim_matches('_').to_string();
    if s.is_empty() || s.chars().next().unwrap().is_ascii_digit() {
        s = format!("v{s}");
    }
    s
}

impl<'a> Lower<'a> {
    pub fn new(m: &'a Model, fns: &'a Fns, reserved: &[&str]) -> Self {
        let mut used: BTreeSet<String> = reserved.iter().map(|s| s.to_string()).collect();
        for k in [
            "K", "R", "Eqn", "Simp", "Rules", "KPrelude", "c", "c'", "h", "fun", "match", "with",
            "if", "then", "else", "let", "in", "at", "by", "do",
        ] {
            used.insert(k.to_string());
        }
        Lower {
            m,
            fns,
            vars: BTreeMap::new(),
            ty: BTreeMap::new(),
            steps: vec![],
            used,
            counter: 0,
            late: vec![],
            refutable: false,
        }
    }

    pub fn fresh(&mut self, base: &str, ty: &str) -> String {
        let mut name = base.to_string();
        while self.used.contains(&name) || names::ident(&name) != name {
            self.counter += 1;
            name = format!("{base}_{}", self.counter);
        }
        self.used.insert(name.clone());
        self.ty.insert(name.clone(), ty.to_string());
        name
    }

    fn hyp(&mut self, base: &str) -> String {
        let n = self.fresh(base, "");
        self.ty.remove(&n);
        n
    }

    /// Declare a Lean variable (e.g. a function parameter) of a given type.
    pub fn param(&mut self, name: &str, ty: &str) -> String {
        self.fresh(name, ty)
    }

    fn bind_kore(&mut self, v: &str, ty: &str) -> String {
        let n = self.fresh(&sanitize(v), ty);
        self.vars.insert(v.to_string(), n.clone());
        n
    }

    // ---------------------------------------------------------------- patterns

    /// Compile pattern `p` of sort `sort` against the Lean variable `scrut`.
    pub fn pat(&mut self, p: &P, scrut: &str, sort: &str, top: bool) -> R<()> {
        match p {
            P::Var(v, _) => {
                if let Some(a) = self.vars.get(v).cloned() {
                    let h = self.hyp("heq");
                    self.steps.push(Step::EqVar {
                        a,
                        b: scrut.to_string(),
                        hyp: h,
                    });
                } else {
                    self.vars.insert(v.clone(), scrut.to_string());
                }
                Ok(())
            }
            P::And(_, ps) => {
                // `#as`: every conjunct matches the same value; variables first so they alias.
                let (vs, others): (Vec<&P>, Vec<&P>) =
                    ps.iter().partition(|q| matches!(q, P::Var(..)));
                for q in vs.into_iter().chain(others) {
                    self.pat(q, scrut, sort, top)?;
                }
                Ok(())
            }
            P::App(f, _, _) if self.is_map_fn(f) => {
                self.late
                    .push((p.clone(), scrut.to_string(), sort.to_string()));
                Ok(())
            }
            P::App(f, _, _) if self.is_list_fn(f) => self.list_pat(p, scrut, sort),
            P::Other(s) if s.starts_with("__lit ") => {
                self.lit_step(scrut, &s[6..]);
                Ok(())
            }
            _ => {
                let mut deferred = Vec::new();
                self.refutable = false;
                let lp = self.deep(p, sort, &mut deferred)?;
                let refutable = self.refutable;
                let hyp = if top { None } else { Some(self.hyp("hd")) };
                self.steps.push(Step::Destruct {
                    scrut: scrut.to_string(),
                    pat: lp,
                    hyp,
                    refutable,
                });
                for d in deferred {
                    match d {
                        Deferred::Pat(q, y, s) => self.pat(&q, &y, &s, false)?,
                        Deferred::Proj { y, from, to, pat } => {
                            let unbound_var = match &pat {
                                P::Var(v, _) if !self.vars.contains_key(v) => Some(v.clone()),
                                _ => None,
                            };
                            let z = match &unbound_var {
                                Some(v) => self.bind_kore(v, &to),
                                None => self.fresh("z", &to),
                            };
                            let h = self.hyp("hp");
                            let expr = L::app(
                                format!(
                                    "proj_{}_{}",
                                    names::short_sort(&from),
                                    names::short_sort(&to)
                                ),
                                vec![L::Var(y.clone())],
                            );
                            self.steps.push(Step::Bind {
                                expr,
                                var: z.clone(),
                                hyp: h,
                            });
                            if unbound_var.is_none() {
                                self.pat(&pat, &z, &to, false)?;
                            }
                        }
                    }
                }
                Ok(())
            }
        }
    }

    /// After the whole left-hand side: the map and set patterns. Elements whose key is bound
    /// by then are looked up; when no pending element has a bound key, the first one is
    /// enumerated (`MapChoose`), which binds its key and may bind the keys of others.
    pub fn finish_lhs(&mut self) -> R<()> {
        struct Pending {
            scrut: String,
            sort: String,
            elems: Vec<P>,
            rests: Vec<P>,
        }
        let mut pending: Vec<Pending> = Vec::new();
        loop {
            for (p, scrut, sort) in std::mem::take(&mut self.late) {
                let mut items = Vec::new();
                self.flat_coll(&p, &mut items);
                let (elems, rests): (Vec<P>, Vec<P>) = items.into_iter().partition(|q| {
                    matches!(q, P::App(f, _, _) if matches!(self.hook_of(f).as_deref(), Some("MAP.element" | "SET.element")))
                });
                if rests.len() > 1 {
                    return Err("map pattern with two map variables (AC matching with free split) is not supported".into());
                }
                pending.push(Pending {
                    scrut,
                    sort,
                    elems,
                    rests,
                });
            }
            // the bound elements first, in order
            let mut progressed = false;
            for i in 0..pending.len() {
                let pos = pending[i].elems.iter().position(|e| {
                    let P::App(_, _, kv) = e else { return false };
                    self.ground(&kv[0])
                });
                if let Some(j) = pos {
                    let e = pending[i].elems.remove(j);
                    let (scrut, sort) = (pending[i].scrut.clone(), pending[i].sort.clone());
                    let last = pending[i].elems.is_empty();
                    let rest_pat = if last {
                        pending[i].rests.first().cloned()
                    } else {
                        None
                    };
                    let rest = self.map_elem(&e, &scrut, &sort, false, last, rest_pat.as_ref())?;
                    pending[i].scrut = rest;
                    if last {
                        pending.remove(i);
                    }
                    progressed = true;
                    break;
                }
            }
            if progressed {
                continue;
            }
            if !self.late.is_empty() {
                continue;
            }
            // finished maps: match the rest
            if let Some(i) = pending.iter().position(|p| p.elems.is_empty()) {
                let pd = pending.remove(i);
                match pd.rests.first() {
                    None => {
                        let h = self.hyp("hu");
                        self.steps.push(Step::CondEq {
                            lhs: L::Var(pd.scrut.clone()),
                            rhs: L::Raw(unit_of(self.m, &pd.sort)),
                            hyp: h,
                        });
                    }
                    Some(P::Var(v, _)) if self.vars.get(v) == Some(&pd.scrut) => {}
                    Some(r) => {
                        let r = r.clone();
                        self.pat(&r, &pd.scrut, &pd.sort, false)?;
                    }
                }
                continue;
            }
            // no bound key anywhere: enumerate the first pending element
            let Some(i) = pending.iter().position(|p| !p.elems.is_empty()) else {
                break;
            };
            let e = pending[i].elems.remove(0);
            let (scrut, sort) = (pending[i].scrut.clone(), pending[i].sort.clone());
            let last = pending[i].elems.is_empty();
            let rest_pat = if last {
                pending[i].rests.first().cloned()
            } else {
                None
            };
            let rest = self.map_elem(&e, &scrut, &sort, true, last, rest_pat.as_ref())?;
            pending[i].scrut = rest;
            if last {
                pending.remove(i);
            }
        }
        Ok(())
    }

    /// Whether `p` can be computed from the variables bound so far.
    fn ground(&self, p: &P) -> bool {
        match p {
            P::Var(v, _) => self.vars.contains_key(v),
            P::App(_, _, args) => args.iter().all(|a| self.ground(a)),
            P::Dv(..) => true,
            _ => false,
        }
    }

    fn flat_coll(&self, p: &P, out: &mut Vec<P>) {
        if let P::App(f, _, args) = p {
            match self.hook_of(f).as_deref() {
                Some("MAP.concat" | "SET.concat") => {
                    for a in args {
                        self.flat_coll(a, out);
                    }
                    return;
                }
                Some("MAP.unit" | "SET.unit") => return,
                _ => {}
            }
        }
        out.push(p.clone());
    }

    fn is_map_fn(&self, f: &str) -> bool {
        matches!(
            self.hook_of(f).as_deref(),
            Some(
                "MAP.concat"
                    | "MAP.element"
                    | "MAP.unit"
                    | "SET.concat"
                    | "SET.element"
                    | "SET.unit"
            )
        )
    }

    fn is_list_fn(&self, f: &str) -> bool {
        matches!(
            self.hook_of(f).as_deref(),
            Some("LIST.concat" | "LIST.element" | "LIST.unit")
        )
    }

    fn hook_of(&self, f: &str) -> Option<String> {
        self.m_hooks().get(f).cloned()
    }

    fn m_hooks(&self) -> &BTreeMap<String, String> {
        &self.m.hooks
    }

    /// One element `K |-> V` (or `SetItem(K)`) of a map (set) pattern at `scrut`; returns the
    /// variable holding the rest. With `rest_pat`, the element is the last one and the rest is
    /// matched against it (a fresh variable is bound directly).
    fn map_elem(
        &mut self,
        e: &P,
        scrut: &str,
        sort: &str,
        choose: bool,
        last: bool,
        rest_pat: Option<&P>,
    ) -> R<String> {
        let P::App(_, _, kv) = e else { unreachable!() };
        let elems = self.m.elems(sort).to_vec();
        let is_set = self.m.sort(sort).kind == Kind::Coll(Coll::Set);
        let (key_sort, val_sort) = if is_set {
            (elems[0].clone(), "Unit".to_string())
        } else {
            (elems[0].clone(), elems[1].clone())
        };
        if !choose {
            let key = self
                .expr(&kv[0], &key_sort)
                .map_err(|e| format!("map key must be bound: {e}"))?;
            let val = self.fresh("v", &val_sort);
            let rest = match rest_pat {
                Some(P::Var(v, _)) if !self.vars.contains_key(v) => self.bind_kore(v, sort),
                _ => self.fresh("rest", sort),
            };
            let wf_hyp = self.hyp("hwf");
            let lookup_hyp = self.hyp("hl");
            let hyp = self.hyp("hm");
            self.steps.push(Step::MapElem {
                map: scrut.to_string(),
                key,
                val: val.clone(),
                rest: rest.clone(),
                wf_hyp,
                lookup_hyp,
                hyp,
            });
            if !is_set {
                self.pat(&kv[1], &val, &val_sort, false)?;
            }
            self.finish_rest(&rest, sort, last, rest_pat)?;
            return Ok(rest);
        }
        let key = self.fresh("k", &key_sort);
        let val = self.fresh("v", &val_sort);
        let rest = match rest_pat {
            Some(P::Var(v, _)) if !self.vars.contains_key(v) => self.bind_kore(v, sort),
            _ => self.fresh("rest", sort),
        };
        let wf_hyp = self.hyp("hwf");
        let cert = self.hyp("hc");
        let hyp = self.hyp("hm");
        self.steps.push(Step::MapChoose {
            map: scrut.to_string(),
            key: key.clone(),
            val: val.clone(),
            rest: rest.clone(),
            wf_hyp,
            cert,
            hyp,
        });
        self.pat(&kv[0], &key, &key_sort, false)?;
        if !is_set {
            self.pat(&kv[1], &val, &val_sort, false)?;
        }
        self.finish_rest(&rest, sort, last, rest_pat)?;
        Ok(rest)
    }

    fn finish_rest(&mut self, rest: &str, sort: &str, last: bool, rest_pat: Option<&P>) -> R<()> {
        match rest_pat {
            None if last => {
                let h = self.hyp("hu");
                self.steps.push(Step::CondEq {
                    lhs: L::Var(rest.to_string()),
                    rhs: L::Raw(unit_of(self.m, sort)),
                    hyp: h,
                });
                Ok(())
            }
            None => Ok(()),
            Some(P::Var(v, _)) if self.vars.get(v).map(|s| s.as_str()) == Some(rest) => Ok(()),
            Some(r) => {
                let r = r.clone();
                self.pat(&r, rest, sort, false)
            }
        }
    }

    /// A list pattern: elements at the front and at the back, at most one list variable.
    fn list_pat(&mut self, p: &P, scrut: &str, sort: &str) -> R<()> {
        fn flat(l: &Lower, p: &P, out: &mut Vec<P>) {
            if let P::App(f, _, args) = p {
                match l.hook_of(f).as_deref() {
                    Some("LIST.concat") => {
                        for a in args {
                            flat(l, a, out);
                        }
                        return;
                    }
                    Some("LIST.unit") => return,
                    _ => {}
                }
            }
            out.push(p.clone());
        }
        let mut items = Vec::new();
        flat(self, p, &mut items);
        let is_elem = |l: &Lower, q: &P| matches!(q, P::App(f, _, _) if l.hook_of(f).as_deref() == Some("LIST.element"));
        let vars: Vec<usize> = (0..items.len())
            .filter(|&i| !is_elem(self, &items[i]))
            .collect();
        if vars.len() > 1 {
            return Err("list pattern with two list variables is not supported".into());
        }
        let split = vars.first().copied().unwrap_or(items.len());
        let elem_sort = self.m.elems(sort)[0].clone();
        let mut cur = scrut.to_string();
        let mut patterns: Vec<(P, String)> = Vec::new();
        for item in &items[..split] {
            let P::App(_, _, a) = item else {
                unreachable!()
            };
            let head = self.fresh("x", &elem_sort);
            let tail = self.fresh("l", sort);
            let hyp = self.hyp("hli");
            self.steps.push(Step::ListElem {
                list: cur.clone(),
                head: head.clone(),
                tail: tail.clone(),
                front: true,
                hyp,
            });
            patterns.push((a[0].clone(), head));
            cur = tail;
        }
        let back: Vec<&P> = items[(split + 1).min(items.len())..].iter().collect();
        for item in back.iter().rev() {
            let P::App(_, _, a) = item else {
                unreachable!()
            };
            let head = self.fresh("x", &elem_sort);
            let tail = self.fresh("l", sort);
            let hyp = self.hyp("hli");
            self.steps.push(Step::ListElem {
                list: cur.clone(),
                head: head.clone(),
                tail: tail.clone(),
                front: false,
                hyp,
            });
            patterns.push((a[0].clone(), head));
            cur = tail;
        }
        for (q, v) in patterns {
            self.pat(&q, &v, &elem_sort, false)?;
        }
        match vars.first() {
            Some(&i) => {
                let q = items[i].clone();
                self.pat(&q, &cur, sort, false)
            }
            None => {
                let h = self.hyp("hu");
                self.steps.push(Step::CondEq {
                    lhs: L::Var(cur),
                    rhs: L::Raw(unit_of(self.m, sort)),
                    hyp: h,
                });
                Ok(())
            }
        }
    }

    /// The Lean pattern for `p` at `sort`; positions needing more than constructor matching get
    /// a fresh variable and are processed after the enclosing `match`.
    fn deep(&mut self, p: &P, sort: &str, d: &mut Vec<Deferred>) -> R<L> {
        match p {
            P::Var(v, _) => {
                if self.vars.contains_key(v) {
                    let y = self.fresh("y", sort);
                    d.push(Deferred::Pat(p.clone(), y.clone(), sort.to_string()));
                    Ok(L::Var(y))
                } else {
                    Ok(L::Var(self.bind_kore(v, sort)))
                }
            }
            P::Dv(s, val) => {
                let sn = s.name().unwrap_or_default().to_string();
                if self.m.sorts.get(&sn).map(|i| &i.kind) == Some(&Kind::Builtin(Builtin::Bool)) {
                    self.refutable = true;
                    return Ok(L::Raw(val.clone()));
                }
                let y = self.fresh("y", sort);
                let lit = self.literal(&sn, val)?;
                d.push(Deferred::Pat(
                    P::Other(format!("__lit {}", lit.render())),
                    y.clone(),
                    sort.to_string(),
                ));
                Ok(L::Var(y))
            }
            P::App(f, params, args) if f == "inj" => {
                let (a, b) = inj_sorts(params)?;
                if b != sort {
                    return Err(format!("injection into {b} at sort {sort}"));
                }
                // `B.inj_A …` is refutable (a sum has at least two leaves), unless it is a
                // projection, which binds a variable of `B`
                let saved = self.refutable;
                self.refutable = true;
                match &args[0] {
                    P::App(g, gp, gargs) if g == "inj" => {
                        let (c, _) = inj_sorts(gp)?;
                        let collapsed = P::App(
                            "inj".into(),
                            vec![S::App(c, vec![]), S::App(b.clone(), vec![])],
                            gargs.clone(),
                        );
                        self.deep(&collapsed, sort, d)
                    }
                    P::App(g, _, gargs) if self.m.ctors.contains_key(g) => {
                        let own = self.ctor_pat(g, gargs, d)?;
                        Ok(L::app(self.m.leaf_ctor(&b, &a), vec![own]))
                    }
                    P::Dv(_, val) => {
                        let ai = self.m.sort(&a);
                        if ai.kind == Kind::Builtin(Builtin::Bool) {
                            return Ok(L::app(self.m.leaf_ctor(&b, &a), vec![L::Raw(val.clone())]));
                        }
                        let y = self.fresh("y", &a);
                        let lit = self.literal(&a, val)?;
                        d.push(Deferred::Pat(
                            P::Other(format!("__lit {}", lit.render())),
                            y.clone(),
                            a.clone(),
                        ));
                        Ok(L::app(self.m.leaf_ctor(&b, &a), vec![L::Var(y)]))
                    }
                    P::Var(..) | P::And(..) => {
                        if self.m.sort(&a).is_simple() {
                            let inner = self.deep(&args[0], &a, d)?;
                            Ok(L::app(self.m.leaf_ctor(&b, &a), vec![inner]))
                        } else {
                            self.refutable = saved;
                            let y = self.fresh("y", &b);
                            d.push(Deferred::Proj {
                                y: y.clone(),
                                from: b.clone(),
                                to: a.clone(),
                                pat: args[0].clone(),
                            });
                            Ok(L::Var(y))
                        }
                    }
                    // a collection pattern under an injection (`inj{List, KItem}(ListItem(X) REST)`):
                    // the collection sort is a leaf; its value is matched after the enclosing match
                    P::App(g, _, _)
                        if (self.is_list_fn(g) || self.is_map_fn(g))
                            && self.m.sort(&a).is_simple() =>
                    {
                        let y = self.fresh("l", &a);
                        if self.is_map_fn(g) {
                            self.late.push((args[0].clone(), y.clone(), a.clone()));
                        } else {
                            d.push(Deferred::Pat(args[0].clone(), y.clone(), a.clone()));
                        }
                        Ok(L::app(self.m.leaf_ctor(&b, &a), vec![L::Var(y)]))
                    }
                    other => Err(format!("unsupported pattern under injection: {other:?}")),
                }
            }
            P::App(f, _, args) if self.m.ctors.contains_key(f) => {
                let ci = &self.m.ctors[f];
                if ci.sort != sort {
                    return Err(format!(
                        "constructor {f} of sort {} at sort {sort}",
                        ci.sort
                    ));
                }
                let si = self.m.sort(sort);
                if !si.is_simple() || si.own.len() > 1 {
                    self.refutable = true;
                }
                let own = self.ctor_pat(f, args, d)?;
                if self.m.sort(sort).is_simple() {
                    Ok(own)
                } else {
                    Ok(L::app(self.m.leaf_ctor(sort, sort), vec![own]))
                }
            }
            P::And(..) => {
                let y = self.fresh("y", sort);
                d.push(Deferred::Pat(p.clone(), y.clone(), sort.to_string()));
                Ok(L::Var(y))
            }
            P::App(f, _, _) if self.is_map_fn(f) => {
                let y = self.fresh("m", sort);
                self.late.push((p.clone(), y.clone(), sort.to_string()));
                Ok(L::Var(y))
            }
            P::App(f, _, _) if self.is_list_fn(f) => {
                let y = self.fresh("l", sort);
                d.push(Deferred::Pat(p.clone(), y.clone(), sort.to_string()));
                Ok(L::Var(y))
            }
            other => Err(format!(
                "unsupported left-hand-side pattern: {}",
                short_dbg(other)
            )),
        }
    }

    fn ctor_pat(&mut self, f: &str, args: &[P], d: &mut Vec<Deferred>) -> R<L> {
        let ci = self.m.ctors[f].clone();
        let mut largs = Vec::new();
        for (a, s) in args.iter().zip(&ci.args) {
            largs.push(self.deep(a, s, d)?);
        }
        Ok(L::app(self.m.ctor_path(f), largs))
    }

    /// A literal of a builtin or token sort.
    pub fn literal(&self, sort: &str, val: &str) -> R<L> {
        let info = self
            .m
            .sorts
            .get(sort)
            .ok_or(format!("literal of unknown sort {sort}"))?;
        Ok(match &info.kind {
            Kind::Builtin(Builtin::Int) => {
                let digits = val.strip_prefix('-').unwrap_or(val);
                if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
                    return Err(format!("bad Int literal {val}"));
                }
                L::Raw(format!("({val} : Int)"))
            }
            Kind::Builtin(Builtin::Bool) => L::Raw(val.to_string()),
            Kind::Builtin(Builtin::String) => L::Raw(names::string_lit(val)),
            Kind::Builtin(Builtin::Bytes) => L::Raw(format!(
                "(KPrelude.BytesHook.ofString {})",
                names::string_lit(val)
            )),
            Kind::Token => L::Raw(format!("({sort}.mk {})", names::string_lit(val))),
            _ => return Err(format!("domain value of sort {sort}")),
        })
    }

    // ---------------------------------------------------------------- expressions

    /// The Lean expression for term `p`; partial applications are bound first. `sort` is the sort
    /// the caller expects; the translation follows the sorts `p` carries, so it is not read.
    #[expect(
        clippy::only_used_in_recursion,
        reason = "the expected sort documents each call site"
    )]
    pub fn expr(&mut self, p: &P, sort: &str) -> R<L> {
        match p {
            P::Var(v, _) => self.vars.get(v).map(|n| L::Var(n.clone())).ok_or(format!(
                "unbound variable {v} (existential ?X is not supported)"
            )),
            P::Dv(s, val) => self.literal(s.name().unwrap_or_default(), val),
            P::App(f, params, args) if f == "inj" => {
                let (a, b) = inj_sorts(params)?;
                match &args[0] {
                    P::App(g, gp, gargs) if g == "inj" => {
                        let (c, _) = inj_sorts(gp)?;
                        let collapsed = P::App(
                            "inj".into(),
                            vec![S::App(c, vec![]), S::App(b.clone(), vec![])],
                            gargs.clone(),
                        );
                        self.expr(&collapsed, sort)
                    }
                    P::App(g, _, gargs)
                        if self.m.ctors.contains_key(g) && !self.m.anywhere.contains(g) =>
                    {
                        let own = self.ctor_expr(g, gargs)?;
                        Ok(L::app(self.m.leaf_ctor(&b, &a), vec![own]))
                    }
                    P::Dv(s, val) => {
                        let lit = self.literal(s.name().unwrap_or_default(), val)?;
                        Ok(L::app(self.m.leaf_ctor(&b, &a), vec![lit]))
                    }
                    t => {
                        let e = self.expr(t, &a)?;
                        if self.m.sort(&a).is_simple() {
                            Ok(L::app(self.m.leaf_ctor(&b, &a), vec![e]))
                        } else {
                            Ok(L::app(
                                format!("inj_{}_{}", names::short_sort(&a), names::short_sort(&b)),
                                vec![e],
                            ))
                        }
                    }
                }
            }
            P::App(f, _, args) if self.m.ctors.contains_key(f) && !self.m.anywhere.contains(f) => {
                let ci = &self.m.ctors[f];
                let s = ci.sort.clone();
                let own = self.ctor_expr(f, args)?;
                if self.m.sort(&s).is_simple() {
                    Ok(own)
                } else {
                    Ok(L::app(self.m.leaf_ctor(&s, &s), vec![own]))
                }
            }
            P::App(f, _, args) => {
                let sig = self
                    .fns
                    .get(f)
                    .cloned()
                    .ok_or(format!("no implementation for function {f}"))?;
                let mut largs = Vec::new();
                for (a, s) in args.iter().zip(&sig.args) {
                    largs.push(self.expr(a, s)?);
                }
                let call = L::app(sig.lean.clone(), largs);
                if sig.partial {
                    // a `match` scrutinee has no expected type: ascribe polymorphic results
                    let call = if crate::hooks::needs_ascription(&sig.lean) {
                        L::Raw(format!("({} : Option {})", call.render(), sig.result))
                    } else {
                        call
                    };
                    let r = self.fresh("r", &sig.result);
                    let h = self.hyp("hr");
                    self.steps.push(Step::Bind {
                        expr: call,
                        var: r.clone(),
                        hyp: h,
                    });
                    Ok(L::Var(r))
                } else {
                    Ok(call)
                }
            }
            other => Err(format!("unsupported term: {}", short_dbg(other))),
        }
    }

    fn ctor_expr(&mut self, f: &str, args: &[P]) -> R<L> {
        let ci = self.m.ctors[f].clone();
        let mut largs = Vec::new();
        for (a, s) in args.iter().zip(&ci.args) {
            largs.push(self.expr(a, s)?);
        }
        Ok(L::app(self.m.ctor_path(f), largs))
    }

    /// A requires clause: conjunctions of `\equals{Bool,_}(e, \dv{Bool}(b))`.
    pub fn cond(&mut self, p: &P) -> R<()> {
        match p {
            P::Top(_) => Ok(()),
            P::And(_, ps) => {
                for q in ps {
                    self.cond(q)?;
                }
                Ok(())
            }
            P::Equals(_, _, l, r) => {
                let (e, b) = match (&**l, &**r) {
                    (e, P::Dv(_, b)) | (P::Dv(_, b), e) => (e, b.clone()),
                    _ => return Err("requires clause that is not `e = true|false`".into()),
                };
                let le = self.expr(e, "SortBool")?;
                let h = self.hyp("hreq");
                if b == "true" {
                    self.steps.push(Step::Cond { cond: le, hyp: h });
                } else {
                    self.steps.push(Step::CondEq {
                        lhs: le,
                        rhs: L::Raw("false".into()),
                        hyp: h,
                    });
                }
                Ok(())
            }
            other => Err(format!("unsupported requires clause: {}", short_dbg(other))),
        }
    }

    /// Steps of the literal checks queued by `deep` (`__lit` markers).
    pub fn lit_step(&mut self, scrut: &str, lit: &str) {
        let h = self.hyp("hlit");
        self.steps.push(Step::CondEq {
            lhs: L::Var(scrut.to_string()),
            rhs: L::Raw(lit.to_string()),
            hyp: h,
        });
    }
}

/// The unit of a collection sort, typed.
pub fn unit_of(m: &Model, sort: &str) -> String {
    match m.sorts.get(sort).map(|s| &s.kind) {
        Some(Kind::Coll(Coll::List)) => "KPrelude.ListHook.unit".into(),
        _ => "KPrelude.MapHook.unit".into(),
    }
}

pub fn inj_sorts(params: &[S]) -> R<(String, String)> {
    match params {
        [a, b] => Ok((
            a.name().ok_or("parametric injection")?.to_string(),
            b.name().ok_or("parametric injection")?.to_string(),
        )),
        _ => Err("malformed injection".into()),
    }
}

pub fn short_dbg(p: &P) -> String {
    let s = format!("{p:?}");
    if s.len() > 300 {
        format!("{}…", &s[..300])
    } else {
        s
    }
}
