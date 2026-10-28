//! `k2lean pairs` (read-only), and the classification behind `gen --det2`: classify the pairs of
//! rewrite rules that a determinism proof has to consider.
//!
//! A pair is classified on the rules' KORE left-hand sides, requires clauses and right-hand
//! sides (the same variants the generator emits), not on the generated Lean:
//!
//! - `clash`: the left-hand sides do not unify; the first conflict is on two different
//!   constructors (`ctor`), two different literals (`lit`), a leaf sort outside a variable's
//!   sort (`sort`), a collection size (`coll`), or an occurs check (`occurs`); its depth counts
//!   constructor levels from the top cell;
//! - `priority`: the left-hand sides unify and the rules are in different priority ranks (only
//!   for pairs of different ranks, which the stratified `Step` already separates);
//! - `exclusive`: they unify in the same rank, and under the unifier the two requires clauses
//!   cannot both be `true`: one of them evaluates to `false` (`eval`, by the definition's own
//!   equations and the builtin hooks), they contain one atom with opposite polarities
//!   (`complement`), or z3 finds the conjunction unsatisfiable over integers and booleans with
//!   every other subterm abstracted (`smt`);
//! - `joinable`: they unify, and the right-hand sides are equal under the unifier (after the
//!   same evaluation);
//! - `overlap`: none of the above; the reason says what was not decided.
//!
//! Every step is conservative: a collection pattern that cannot be unified exactly, a function
//! call that cannot be evaluated, or an atom z3 cannot see make the pair less decided, never
//! more. Equal right-hand sides are a syntactic comparison.

use crate::funcs::Equation;
use crate::index::Tree;
use crate::ir::{Def, P};
use crate::model::Model;
use crate::rules::Rule;
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::rc::Rc;

type Leaves = Rc<BTreeSet<String>>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum T {
    /// A rule variable (global id) or a variable made by the unifier.
    Var(usize),
    /// A pattern variable of an equation template (local id).
    PVar(usize),
    Ctor(String, Vec<T>),
    Lit(String, String),
    Fn(String, Vec<T>),
    /// A pattern this analysis does not model (opaque, compares equal only to itself).
    Unk(String),
}

#[derive(Clone, Debug)]
pub struct Clash {
    pub depth: usize,
    pub kind: &'static str,
    pub at: String,
}

/// One rule, converted once with globally unique variable ids.
struct CRule {
    lhs: T,
    aliases: Vec<(T, T)>,
    req: Vec<(T, bool)>,
    rhs: T,
    /// the Boolean connectives that split the requires clause into `req`
    conns: BTreeSet<String>,
}

/// An equation template: patterns over `PVar`s.
struct Tmpl {
    args: Vec<T>,
    req: Vec<(T, bool)>,
    rhs: T,
    pleaves: Vec<Leaves>,
    /// `#as` patterns (`X #as P`): after the arguments match, `X` matches the value of `P`.
    aliases: Vec<(T, T)>,
}

pub struct Cx<'a> {
    def: &'a Def,
    m: &'a Model,
    hooks: BTreeMap<String, String>,
    /// (hook, result sort) → symbol, for rebuilding collection terms.
    coll_sym: BTreeMap<(String, String), String>,
    eqs: BTreeMap<String, Vec<Tmpl>>,
    raw_eqs: &'a BTreeMap<String, Vec<Equation>>,
    /// The values of calls on ground arguments, once evaluated by the equations (the witness
    /// search only, which evaluates calls on long lists repeatedly).
    memo: std::collections::HashMap<(String, Vec<T>), T>,
    use_memo: bool,
    /// The functions and hooks `eval` has applied since the last `classify0` began.
    used: BTreeSet<String>,
    vleaves: Vec<Leaves>,
    vnames: Vec<String>,
    unk: usize,
    /// `--same-binding`: two free-key map elements are unified as the same binding (what a
    /// determinism proof per binding, e.g. per thread, would need).
    pub same_binding: bool,
    /// Print the unified form of the pair being classified (`--explain R1 R2`).
    pub explain: bool,
}

fn sort_of(s: &crate::ir::S) -> String {
    s.name()
        .map(|n| n.to_string())
        .unwrap_or_else(|| s.to_string())
}

impl<'a> Cx<'a> {
    pub fn new(def: &'a Def, m: &'a Model, raw_eqs: &'a BTreeMap<String, Vec<Equation>>) -> Self {
        let mut hooks = BTreeMap::new();
        let mut coll_sym = BTreeMap::new();
        for (n, d) in &def.symbols {
            if let Some(h) = d.hook() {
                if let Some(r) = d.result.name() {
                    coll_sym
                        .entry((h.clone(), r.to_string()))
                        .or_insert_with(|| n.clone());
                }
                hooks.insert(n.clone(), h);
            }
        }
        Cx {
            def,
            m,
            hooks,
            coll_sym,
            eqs: BTreeMap::new(),
            raw_eqs,
            memo: std::collections::HashMap::new(),
            use_memo: false,
            used: BTreeSet::new(),
            vleaves: vec![],
            vnames: vec![],
            unk: 0,
            same_binding: false,
            explain: false,
        }
    }

    fn leaves_of_sort(&self, s: &str) -> Leaves {
        match self.m.sorts.get(s) {
            Some(i) if !i.leaves.is_empty() => Rc::new(i.leaves.iter().cloned().collect()),
            _ => Rc::new([s.to_string()].into_iter().collect()),
        }
    }

    fn hook(&self, f: &str) -> Option<&str> {
        self.hooks.get(f).map(|s| s.as_str())
    }

    fn result_sort(&self, f: &str) -> Option<String> {
        self.def
            .symbols
            .get(f)
            .and_then(|d| d.result.name().map(|s| s.to_string()))
    }

    /// The leaf sort of a term built by a constructor or a literal, or the leaves of the result
    /// sort of a function.
    fn term_leaves(&self, t: &T, ext: &[Leaves]) -> Option<Leaves> {
        match t {
            T::Ctor(f, _) => self
                .m
                .ctors
                .get(f)
                .map(|c| Rc::new([c.sort.clone()].into_iter().collect())),
            T::Lit(s, _) => Some(Rc::new([s.clone()].into_iter().collect())),
            T::Fn(f, _) => self.result_sort(f).map(|s| self.leaves_of_sort(&s)),
            T::Var(i) => Some(self.var_leaves(*i, ext)),
            _ => None,
        }
    }

    fn var_leaves(&self, i: usize, ext: &[Leaves]) -> Leaves {
        if i < self.vleaves.len() {
            self.vleaves[i].clone()
        } else {
            ext[i - self.vleaves.len()].clone()
        }
    }

    fn unk(&mut self, what: &str) -> T {
        self.unk += 1;
        T::Unk(format!("{what}#{}", self.unk))
    }

    // ------------------------------------------------------------ conversion

    fn conv(
        &mut self,
        p: &P,
        names: &mut BTreeMap<String, T>,
        aliases: &mut Vec<(T, T)>,
        pv: Option<&mut Vec<Leaves>>,
    ) -> T {
        let mut pv = pv;
        match p {
            P::Var(n, s) => {
                if let Some(t) = names.get(n) {
                    return t.clone();
                }
                let leaves = self.leaves_of_sort(&sort_of(s));
                let t = match pv.as_deref_mut() {
                    Some(v) => {
                        v.push(leaves);
                        T::PVar(v.len() - 1)
                    }
                    None => {
                        self.vleaves.push(leaves);
                        self.vnames.push(n.clone());
                        T::Var(self.vleaves.len() - 1)
                    }
                };
                names.insert(n.clone(), t.clone());
                t
            }
            P::App(f, _, args) if f == "inj" && args.len() == 1 => {
                self.conv(&args[0], names, aliases, pv)
            }
            P::App(f, _, args) => {
                let ts: Vec<T> = args
                    .iter()
                    .map(|a| self.conv(a, names, aliases, pv.as_deref_mut()))
                    .collect();
                if self.m.ctors.contains_key(f) {
                    T::Ctor(f.clone(), ts)
                } else {
                    T::Fn(f.clone(), ts)
                }
            }
            P::Dv(s, v) => {
                let s = sort_of(s);
                let v = if s == "SortInt" {
                    v.trim_start_matches('+').to_string()
                } else {
                    v.clone()
                };
                T::Lit(s, v)
            }
            P::And(_, ps) if !ps.is_empty() => {
                let ts: Vec<T> = ps
                    .iter()
                    .map(|q| self.conv(q, names, aliases, pv.as_deref_mut()))
                    .collect();
                let main = ts
                    .iter()
                    .find(|t| !matches!(t, T::Var(_) | T::PVar(_)))
                    .cloned()
                    .unwrap_or_else(|| ts[0].clone());
                for t in ts {
                    if t != main {
                        aliases.push((t, main.clone()));
                    }
                }
                main
            }
            other => self.unk(&format!("{:.40}", format!("{other:?}"))),
        }
    }

    fn atoms(
        &mut self,
        p: &P,
        names: &mut BTreeMap<String, T>,
        aliases: &mut Vec<(T, T)>,
        out: &mut Vec<(T, bool)>,
        pv: Option<&mut Vec<Leaves>>,
    ) {
        let mut pv = pv;
        match p {
            P::Top(_) => {}
            P::And(_, ps) => {
                for q in ps {
                    self.atoms(q, names, aliases, out, pv.as_deref_mut());
                }
            }
            P::Equals(_, _, l, r) => match (&**l, &**r) {
                (e, P::Dv(_, b)) | (P::Dv(_, b), e) => {
                    let t = self.conv(e, names, aliases, pv);
                    self.push_atom(t, b == "true", out);
                }
                _ => {
                    let u = self.unk("req");
                    out.push((u, true));
                }
            },
            _ => {
                let u = self.unk("req");
                out.push((u, true));
            }
        }
    }

    /// Splits `t = b` into atoms through the Boolean connectives (recorded in `used`: a proof
    /// reads them by unfolding the connectives).
    fn push_atom(&mut self, t: T, b: bool, out: &mut Vec<(T, bool)>) {
        if let T::Fn(f, args) = &t {
            match (self.hook(f), b) {
                (Some("BOOL.and" | "BOOL.andThen"), true)
                | (Some("BOOL.or" | "BOOL.orElse"), false) => {
                    self.used.insert(f.clone());
                    for a in args.clone() {
                        self.push_atom(a, b, out);
                    }
                    return;
                }
                (Some("BOOL.not"), _) => {
                    self.used.insert(f.clone());
                    self.push_atom(args[0].clone(), !b, out);
                    return;
                }
                _ => {}
            }
        }
        if let T::Lit(_, v) = &t
            && (v == "true") == b
        {
            return;
        }
        out.push((t, b));
    }

    fn convert_rule(&mut self, r: &Rule) -> CRule {
        let (l, q, rh) = &r.kore;
        let mut names = BTreeMap::new();
        let mut aliases = Vec::new();
        let lhs = self.conv(l, &mut names, &mut aliases, None);
        let mut req = Vec::new();
        let before = std::mem::take(&mut self.used);
        self.atoms(q, &mut names, &mut aliases, &mut req, None);
        let conns = std::mem::replace(&mut self.used, before);
        self.used.extend(conns.iter().cloned());
        let rhs = self.conv(rh, &mut names, &mut aliases, None);
        CRule {
            lhs,
            aliases,
            req,
            rhs,
            conns,
        }
    }

    fn templates(&mut self, f: &str) {
        if self.eqs.contains_key(f) {
            return;
        }
        let mut v = Vec::new();
        if let Some(es) = self.raw_eqs.get(f) {
            for e in es {
                let mut names = BTreeMap::new();
                let mut aliases = Vec::new();
                let mut pl = Vec::new();
                let args: Vec<T> = e
                    .args
                    .iter()
                    .map(|a| self.conv(a, &mut names, &mut aliases, Some(&mut pl)))
                    .collect();
                let mut req = Vec::new();
                for q in &e.requires {
                    self.atoms(q, &mut names, &mut aliases, &mut req, Some(&mut pl));
                }
                let rhs = self.conv(&e.rhs, &mut names, &mut aliases, Some(&mut pl));
                v.push(Tmpl {
                    args,
                    req,
                    rhs,
                    pleaves: pl,
                    aliases,
                });
            }
        }
        self.eqs.insert(f.to_string(), v);
    }
}

// ---------------------------------------------------------------- printing

pub fn show(t: &T, cx: &Cx, out: &mut String) {
    match t {
        T::Var(i) => {
            let n = cx
                .vnames
                .get(*i)
                .map(|s| crate::names::demangle(s))
                .unwrap_or_else(|| "_".into());
            let _ = write!(out, "{}#{i}", n.trim_start_matches("Var"));
        }
        T::PVar(i) => {
            let _ = write!(out, "?{i}");
        }
        T::Lit(_, v) => {
            let _ = write!(out, "{v:?}");
        }
        T::Unk(s) => {
            let _ = write!(out, "<{s}>");
        }
        T::Ctor(f, a) | T::Fn(f, a) => {
            out.push_str(crate::names::demangle(f).trim_start_matches("Lbl"));
            if !a.is_empty() {
                out.push('(');
                for (k, x) in a.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    show(x, cx, out);
                }
                out.push(')');
            }
        }
    }
}

fn shown(t: &T, cx: &Cx) -> String {
    let mut s = String::new();
    show(t, cx, &mut s);
    s
}

// ---------------------------------------------------------------- unification

#[derive(Clone)]
struct Un {
    sub: BTreeMap<usize, T>,
    ext: Vec<Leaves>,
    /// Reasons the unifier left a position undecided (collections, functions).
    unknown: BTreeSet<String>,
    deferred: Vec<(T, T, usize)>,
    steps: usize,
}

#[derive(PartialEq, Debug, Clone, Copy)]
enum M {
    Yes,
    No,
    Maybe,
}

impl Un {
    fn new() -> Self {
        Un {
            sub: BTreeMap::new(),
            ext: vec![],
            unknown: BTreeSet::new(),
            deferred: vec![],
            steps: 0,
        }
    }

    fn walk(&self, t: &T) -> T {
        let mut t = t.clone();
        while let T::Var(i) = t {
            match self.sub.get(&i) {
                Some(u) => t = u.clone(),
                None => break,
            }
        }
        t
    }

    fn resolve(&self, t: &T) -> T {
        match self.walk(t) {
            T::Ctor(f, a) => T::Ctor(f, a.iter().map(|x| self.resolve(x)).collect()),
            T::Fn(f, a) => T::Fn(f, a.iter().map(|x| self.resolve(x)).collect()),
            other => other,
        }
    }

    fn occurs(&self, v: usize, t: &T) -> bool {
        match self.walk(t) {
            T::Var(i) => i == v,
            T::Ctor(_, a) | T::Fn(_, a) => a.iter().any(|x| self.occurs(v, x)),
            _ => false,
        }
    }

    /// Whether `v` occurs in `t` outside the arguments of function calls (a collection's
    /// element and concatenation count as constructors: a collection is not a proper part of
    /// itself).
    fn occurs_ctor(&self, cx: &Cx, v: usize, t: &T) -> bool {
        match self.walk(t) {
            T::Var(i) => i == v,
            T::Ctor(_, a) => a.iter().any(|x| self.occurs_ctor(cx, v, x)),
            T::Fn(f, a) => {
                matches!(
                    cx.hook(&f).and_then(|h| h.split_once('.')),
                    Some(("MAP" | "SET" | "LIST", "concat" | "element"))
                ) && a.iter().any(|x| self.occurs_ctor(cx, v, x))
            }
            _ => false,
        }
    }

    fn fresh(&mut self, cx: &Cx, l: Leaves) -> usize {
        self.ext.push(l);
        cx.vleaves.len() + self.ext.len() - 1
    }

    fn bind(&mut self, cx: &Cx, v: usize, t: T, d: usize) -> Result<(), Clash> {
        let lv = cx.var_leaves(v, &self.ext);
        if let T::Var(w) = &t {
            if *w == v {
                return Ok(());
            }
            let lw = cx.var_leaves(*w, &self.ext);
            let inter: BTreeSet<String> = lv.intersection(&lw).cloned().collect();
            if inter.is_empty() {
                return Err(Clash {
                    depth: d,
                    kind: "sort",
                    at: "variable sorts".into(),
                });
            }
            if inter.len() == lw.len() {
                self.sub.insert(v, t);
            } else if inter.len() == lv.len() {
                self.sub.insert(*w, T::Var(v));
            } else {
                let z = self.fresh(cx, Rc::new(inter));
                self.sub.insert(v, T::Var(z));
                self.sub.insert(*w, T::Var(z));
            }
            return Ok(());
        }
        if let Some(lt) = cx.term_leaves(&t, &self.ext) {
            if lt.is_disjoint(&lv) {
                let what = match &t {
                    T::Ctor(f, _) => crate::names::demangle(f),
                    T::Lit(s, v) => format!("{s} {v}"),
                    _ => "term".into(),
                };
                return Err(Clash {
                    depth: d,
                    kind: "sort",
                    at: what,
                });
            }
            if matches!(t, T::Fn(..)) && !lt.is_subset(&lv) {
                self.unknown.insert("function result sort".into());
            }
        }
        if self.occurs(v, &t) {
            // through constructors only, `v` is a proper part of `t` and differs from it; under
            // a function call the two may be equal (`X = f(X)`), which is left undecided
            if !self.occurs_ctor(cx, v, &t) {
                self.unknown
                    .insert("function of the variable itself".into());
                return Ok(());
            }
            return Err(Clash {
                depth: d,
                kind: "occurs",
                at: String::new(),
            });
        }
        self.sub.insert(v, t);
        Ok(())
    }

    fn unify(&mut self, cx: &Cx, a: &T, b: &T, d: usize) -> Result<(), Clash> {
        self.steps += 1;
        let (a, b) = (self.walk(a), self.walk(b));
        if a == b {
            return Ok(());
        }
        match (&a, &b) {
            (T::Var(x), _) => self.bind(cx, *x, b.clone(), d),
            (_, T::Var(y)) => self.bind(cx, *y, a.clone(), d),
            (T::Ctor(f, xs), T::Ctor(g, ys)) => {
                if f != g || xs.len() != ys.len() {
                    let s1 = cx.m.ctors.get(f).map(|c| c.sort.clone());
                    let s2 = cx.m.ctors.get(g).map(|c| c.sort.clone());
                    let kind = if s1 == s2 { "ctor" } else { "sort" };
                    return Err(Clash {
                        depth: d,
                        kind,
                        at: format!(
                            "{} / {}",
                            crate::names::demangle(f),
                            crate::names::demangle(g)
                        ),
                    });
                }
                for (x, y) in xs.iter().zip(ys) {
                    self.unify(cx, x, y, d + 1)?;
                }
                Ok(())
            }
            (T::Lit(s, v), T::Lit(s2, w)) => {
                if s != s2 {
                    Err(Clash {
                        depth: d,
                        kind: "sort",
                        at: format!("{s} / {s2}"),
                    })
                } else if v != w {
                    Err(Clash {
                        depth: d,
                        kind: "lit",
                        at: format!("{s} {v} / {w}"),
                    })
                } else {
                    Ok(())
                }
            }
            (T::Ctor(..), T::Lit(..)) | (T::Lit(..), T::Ctor(..)) => Err(Clash {
                depth: d,
                kind: "sort",
                at: "constructor / literal".into(),
            }),
            (T::Fn(..), _) | (_, T::Fn(..)) => {
                // a collection pattern or a function: after the structural part
                self.deferred.push((a.clone(), b.clone(), d));
                Ok(())
            }
            _ => {
                self.unknown.insert("unmodelled pattern".into());
                Ok(())
            }
        }
    }

    /// The deferred positions: collections unified as far as keys and positions allow.
    fn finish(&mut self, cx: &Cx) -> Result<(), Clash> {
        for _round in 0..8 {
            let todo = std::mem::take(&mut self.deferred);
            if todo.is_empty() {
                return Ok(());
            }
            let mut progressed = false;
            for (a, b, d) in todo {
                let (a, b) = (self.resolve(&a), self.resolve(&b));
                if a == b {
                    progressed = true;
                    continue;
                }
                if matches!(a, T::Var(_)) || matches!(b, T::Var(_)) {
                    self.unify(cx, &a, &b, d)?;
                    progressed = true;
                    continue;
                }
                match self.coll_unify(cx, &a, &b, d)? {
                    1 => progressed = true,
                    2 => {
                        progressed = true;
                        self.deferred.push((a, b, d));
                    }
                    _ => self.deferred.push((a, b, d)),
                }
            }
            if !progressed {
                break;
            }
        }
        for (a, b, _) in std::mem::take(&mut self.deferred) {
            let why = match (&a, &b) {
                (T::Fn(f, _), _) | (_, T::Fn(f, _)) => match cx.hook(f) {
                    Some(h)
                        if h.starts_with("MAP.")
                            || h.starts_with("SET.")
                            || h.starts_with("LIST.") =>
                    {
                        format!("collection {}", &h[..h.find('.').unwrap()])
                    }
                    _ => format!("function {}", crate::names::demangle(f)),
                },
                _ => "unmodelled".into(),
            };
            self.unknown.insert(why);
        }
        Ok(())
    }

    /// Flatten a collection term: (kind, elements, rest terms), if it is one.
    fn coll_items(&self, cx: &Cx, t: &T) -> Option<(String, Vec<T>, Vec<T>)> {
        fn go(
            cx: &Cx,
            un: &Un,
            t: &T,
            kind: &mut Option<String>,
            el: &mut Vec<T>,
            rest: &mut Vec<T>,
        ) -> bool {
            let t = un.walk(t);
            if let T::Fn(f, a) = &t
                && let Some(h) = cx.hook(f)
            {
                let (k, op) = h.split_once('.').unwrap_or(("", ""));
                if matches!(k, "MAP" | "SET" | "LIST") {
                    if kind.as_deref().is_some_and(|x| x != k) {
                        return false;
                    }
                    *kind = Some(k.to_string());
                    match op {
                        "concat" => return a.iter().all(|x| go(cx, un, x, kind, el, rest)),
                        "unit" => return true,
                        "element" => {
                            el.push(t.clone());
                            return true;
                        }
                        _ => {}
                    }
                }
            }
            rest.push(t);
            true
        }
        let mut kind = None;
        let (mut el, mut rest) = (vec![], vec![]);
        if !go(cx, self, t, &mut kind, &mut el, &mut rest) {
            return None;
        }
        Some((kind?, el, rest))
    }

    /// Unify two collection terms as far as decidable: `Ok(1)` done, `Ok(2)` progressed (retry),
    /// `Ok(0)` undecided.
    fn coll_unify(&mut self, cx: &Cx, a: &T, b: &T, d: usize) -> Result<u8, Clash> {
        let (ca, cb) = (self.coll_items(cx, a), self.coll_items(cx, b));
        // a collection value against a constructor term or a builtin literal: a value of a
        // collection sort is built by its hooks only, so the two have different leaves (they
        // meet at a position of a supersort, `KItem`, through different injections)
        for (c, other) in [(&ca, b), (&cb, a)] {
            if let Some((k, _, _)) = c
                && matches!(other, T::Ctor(..) | T::Lit(..))
            {
                return Err(Clash {
                    depth: d,
                    kind: "sort",
                    at: format!("collection {k} / {}", head_name(other)),
                });
            }
        }
        let (Some((ka, ea, ra)), Some((kb, eb, rb))) = (ca, cb) else {
            return Ok(0);
        };
        if ka != kb {
            return Ok(0);
        }
        // rests that are not variables (a function call) keep the pair undecided
        if ra.iter().chain(&rb).any(|r| !matches!(r, T::Var(_))) {
            return Ok(0);
        }
        if ka == "LIST" {
            return self.list_unify(cx, a, b, d);
        }
        // maps and sets: match elements with syntactically equal keys
        let key = |e: &T| {
            if let T::Fn(_, x) = e {
                x[0].clone()
            } else {
                e.clone()
            }
        };
        let mut eb_left: Vec<T> = eb.clone();
        let mut ea_left: Vec<T> = vec![];
        let mut pairs = vec![];
        for x in &ea {
            let kx = self.resolve(&key(x));
            if let Some(j) = eb_left.iter().position(|y| self.resolve(&key(y)) == kx) {
                pairs.push((x.clone(), eb_left.remove(j)));
            } else {
                ea_left.push(x.clone());
            }
        }
        for (x, y) in pairs {
            if let (T::Fn(_, xa), T::Fn(_, ya)) = (&x, &y) {
                for (p, q) in xa.iter().zip(ya).skip(1) {
                    self.unify(cx, p, q, d + 1)?;
                }
            }
        }
        match (ea_left.is_empty(), eb_left.is_empty(), ra.len(), rb.len()) {
            (true, true, 0, 0) => Ok(1),
            (true, true, 1, 1) => {
                self.unify(cx, &ra[0], &rb[0], d + 1)?;
                Ok(1)
            }
            // one side has more elements and no rest: sizes differ
            (_, true, 0, 0) | (true, _, 0, 0) => Err(Clash {
                depth: d,
                kind: "coll",
                at: format!("{ka} size"),
            }),
            (true, false, 1, 0) => {
                // a's rest takes b's remaining elements
                let t = self.rebuild(cx, &ka, a, &eb_left, None);
                self.unify(cx, &ra[0], &t, d + 1)?;
                Ok(1)
            }
            (false, true, 0, 1) => {
                let t = self.rebuild(cx, &ka, b, &ea_left, None);
                self.unify(cx, &rb[0], &t, d + 1)?;
                Ok(1)
            }
            (true, false, 0, _) if !eb_left.is_empty() && rb.is_empty() => Err(Clash {
                depth: d,
                kind: "coll",
                at: format!("{ka} size"),
            }),
            (false, false, _, _) if cx.same_binding => {
                // two free keys: assume the same binding; with one binding left on each side the
                // keys need not be variables (a thread matched at `<id> T </id>`), since
                // `element(k₁, v₁) = element(k₂, v₂)` forces `k₁ = k₂`
                let (ka, kb) = (
                    self.resolve(&key(&ea_left[0])),
                    self.resolve(&key(&eb_left[0])),
                );
                let single = ea_left.len() == 1 && eb_left.len() == 1;
                if single || matches!(ka, T::Var(_)) && matches!(kb, T::Var(_)) {
                    self.unknown
                        .insert("free-key map: same binding assumed".into());
                    self.unify(cx, &ka, &kb, d + 1)?;
                    Ok(2)
                } else {
                    Ok(0)
                }
            }
            _ => Ok(0),
        }
    }

    /// A list term as its sequence of items: `Ok(elem)` an element term, `Err(t)` a sublist.
    fn list_seq(&self, cx: &Cx, t: &T, out: &mut Vec<Result<T, T>>) {
        let t = self.walk(t);
        if let T::Fn(f, a) = &t {
            match cx.hook(f) {
                Some("LIST.concat") => {
                    for x in a {
                        self.list_seq(cx, x, out);
                    }
                    return;
                }
                Some("LIST.unit") => return,
                Some("LIST.element") => {
                    out.push(Ok(t.clone()));
                    return;
                }
                _ => {}
            }
        }
        out.push(Err(t));
    }

    /// Lists: elements matched from both ends; a single remaining sublist variable takes the rest.
    fn list_unify(&mut self, cx: &Cx, a: &T, b: &T, d: usize) -> Result<u8, Clash> {
        let (mut sa, mut sb) = (vec![], vec![]);
        self.list_seq(cx, a, &mut sa);
        self.list_seq(cx, b, &mut sb);
        let el = |e: &T| {
            if let T::Fn(_, x) = e {
                x[0].clone()
            } else {
                e.clone()
            }
        };
        let mut progressed = false;
        while let (Some(Ok(x)), Some(Ok(y))) = (sa.first().cloned(), sb.first().cloned()) {
            self.unify(cx, &el(&x), &el(&y), d + 1)?;
            let _ = sa.remove(0);
            let _ = sb.remove(0);
            progressed = true;
        }
        while let (Some(Ok(x)), Some(Ok(y))) = (sa.last().cloned(), sb.last().cloned()) {
            self.unify(cx, &el(&x), &el(&y), d + 1)?;
            sa.pop();
            sb.pop();
            progressed = true;
        }
        let rebuild = |un: &Un, items: &[Result<T, T>]| -> T {
            let ts: Vec<T> = items
                .iter()
                .map(|i| match i {
                    Ok(t) | Err(t) => t.clone(),
                })
                .collect();
            un.rebuild(cx, "LIST", a, &ts, None)
        };
        let all_elems = |s: &[Result<T, T>]| s.iter().all(|i| i.is_ok());
        match (sa.len(), sb.len()) {
            (0, 0) => Ok(1),
            _ if sa.len() == 1 && matches!(sa[0], Err(T::Var(_))) => {
                let Err(v) = sa[0].clone() else {
                    unreachable!()
                };
                let t = rebuild(self, &sb);
                self.unify(cx, &v, &t, d + 1)?;
                Ok(1)
            }
            _ if sb.len() == 1 && matches!(sb[0], Err(T::Var(_))) => {
                let Err(v) = sb[0].clone() else {
                    unreachable!()
                };
                let t = rebuild(self, &sa);
                self.unify(cx, &v, &t, d + 1)?;
                Ok(1)
            }
            // one side is exhausted and the other still has elements
            (0, _) if sb.iter().any(|i| i.is_ok()) => Err(Clash {
                depth: d,
                kind: "coll",
                at: "list length".into(),
            }),
            (_, 0) if sa.iter().any(|i| i.is_ok()) => Err(Clash {
                depth: d,
                kind: "coll",
                at: "list length".into(),
            }),
            _ if all_elems(&sa) && all_elems(&sb) => Err(Clash {
                depth: d,
                kind: "coll",
                at: "list length".into(),
            }),
            _ => Ok(if progressed { 2 } else { 0 }),
        }
    }

    fn rebuild(&self, cx: &Cx, kind: &str, like: &T, elems: &[T], rest: Option<T>) -> T {
        let sort = match like {
            T::Fn(f, _) => cx.result_sort(f).unwrap_or_default(),
            _ => String::new(),
        };
        let concat = cx
            .coll_sym
            .get(&(format!("{kind}.concat"), sort.clone()))
            .cloned()
            .unwrap_or_else(|| format!("{kind}.concat"));
        let unit = cx
            .coll_sym
            .get(&(format!("{kind}.unit"), sort))
            .cloned()
            .unwrap_or_else(|| format!("{kind}.unit"));
        let mut items: Vec<T> = elems.to_vec();
        items.extend(rest);
        let mut it = items.into_iter();
        match it.next() {
            None => T::Fn(unit, vec![]),
            Some(first) => it.fold(first, |acc, x| T::Fn(concat.clone(), vec![acc, x])),
        }
    }

    // ------------------------------------------------------------ evaluation

    /// `t` with its variable chain followed, without copying.
    fn walk_ref<'s>(&'s self, t: &'s T) -> &'s T {
        let mut t = t;
        while let T::Var(i) = t {
            match self.sub.get(i) {
                Some(u) => t = u,
                None => break,
            }
        }
        t
    }

    fn eval(&self, cx: &mut Cx, t: &T, fuel: &mut usize) -> T {
        let t = self.walk_ref(t);
        if *fuel == 0 {
            return self.resolve(t);
        }
        *fuel -= 1;
        match t {
            T::Ctor(f, a) => {
                let a: Vec<T> = a.iter().map(|x| self.eval(cx, x, fuel)).collect();
                if a.iter().any(is_undef) {
                    return undef();
                }
                T::Ctor(f.clone(), a)
            }
            T::Fn(f, a) => {
                let a: Vec<T> = a.iter().map(|x| self.eval(cx, x, fuel)).collect();
                // strict: an undefined argument makes the application undefined
                if a.iter().any(is_undef) {
                    return undef();
                }
                if let Some(v) = self.hook_eval(cx, f, &a) {
                    cx.used.insert(f.clone());
                    return v;
                }
                if cx.raw_eqs.contains_key(f) {
                    let ground = cx.use_memo && a.iter().all(is_ground_value);
                    if ground && let Some(v) = cx.memo.get(&(f.clone(), a.clone())) {
                        cx.used.insert(f.clone());
                        return v.clone();
                    }
                    if let Some(v) = self.apply_eqs(cx, f, &a, fuel) {
                        cx.used.insert(f.clone());
                        if ground && *fuel > 0 {
                            // a bounded cache: emptied when it grows large
                            if cx.memo.len() > 5_000 {
                                cx.memo.clear();
                            }
                            cx.memo.insert((f.clone(), a), v.clone());
                        }
                        return v;
                    }
                }
                T::Fn(f.clone(), a)
            }
            other => self.resolve(other),
        }
    }

    fn lit_bool(b: bool) -> T {
        T::Lit("SortBool".into(), b.to_string())
    }

    fn as_bool(t: &T) -> Option<bool> {
        match t {
            T::Lit(s, v) if s == "SortBool" => Some(v == "true"),
            _ => None,
        }
    }

    fn as_int(t: &T) -> Option<BigInt> {
        match t {
            T::Lit(s, v) if s == "SortInt" => v.parse().ok(),
            _ => None,
        }
    }

    fn as_str(t: &T) -> Option<&str> {
        match t {
            T::Lit(s, v) if s == "SortString" || s == "SortBytes" => Some(v.as_str()),
            _ => None,
        }
    }

    /// Whether two terms certainly denote different values (they do not unify).
    fn differ(&self, cx: &Cx, a: &T, b: &T) -> bool {
        let mut u = self.clone();
        u.deferred.clear();
        match u.unify(cx, a, b, 0) {
            Err(_) => true,
            Ok(()) => u.finish(cx).is_err(),
        }
    }

    fn hook_eval(&self, cx: &Cx, f: &str, a: &[T]) -> Option<T> {
        use num_traits::{One, Signed, ToPrimitive, Zero};
        let h = cx.hook(f)?.to_string();
        let b = |i: usize| a.get(i).and_then(Self::as_bool);
        let n = |i: usize| a.get(i).and_then(Self::as_int);
        let st = |i: usize| a.get(i).and_then(Self::as_str).map(|x| x.to_string());
        let int = |v: BigInt| T::Lit("SortInt".into(), v.to_string());
        let res_sort = cx.result_sort(f).unwrap_or_default();
        let lit = |v: String| T::Lit(res_sort.clone(), v);
        let small = |v: &BigInt| v.to_i64();
        // the code points of a string, and the string of a list of code points
        let chars = |x: &str| -> Vec<char> { x.chars().collect() };
        let ofc = |v: &[char]| -> String { v.iter().collect() };
        Some(match h.as_str() {
            "BOOL.not" => Self::lit_bool(!b(0)?),
            "BOOL.and" | "BOOL.andThen" => match (b(0), b(1)) {
                (Some(false), _) | (_, Some(false)) => Self::lit_bool(false),
                (Some(true), _) => a[1].clone(),
                (_, Some(true)) => a[0].clone(),
                _ => return None,
            },
            "BOOL.or" | "BOOL.orElse" => match (b(0), b(1)) {
                (Some(true), _) | (_, Some(true)) => Self::lit_bool(true),
                (Some(false), _) => a[1].clone(),
                (_, Some(false)) => a[0].clone(),
                _ => return None,
            },
            "BOOL.xor" | "BOOL.ne" => Self::lit_bool(b(0)? != b(1)?),
            "BOOL.eq" => Self::lit_bool(b(0)? == b(1)?),
            "BOOL.implies" => match (b(0), b(1)) {
                (Some(false), _) | (_, Some(true)) => Self::lit_bool(true),
                (Some(true), Some(false)) => Self::lit_bool(false),
                _ => return None,
            },
            "INT.add" => int(n(0)? + n(1)?),
            "INT.sub" => int(n(0)? - n(1)?),
            "INT.mul" => int(n(0)? * n(1)?),
            "INT.lt" => Self::lit_bool(n(0)? < n(1)?),
            "INT.le" => Self::lit_bool(n(0)? <= n(1)?),
            "INT.gt" => Self::lit_bool(n(0)? > n(1)?),
            "INT.ge" => Self::lit_bool(n(0)? >= n(1)?),
            "INT.eq" => Self::lit_bool(n(0)? == n(1)?),
            "INT.ne" => Self::lit_bool(n(0)? != n(1)?),
            "INT.abs" => int(n(0)?.abs()),
            "INT.min" => int(n(0)?.min(n(1)?)),
            "INT.max" => int(n(0)?.max(n(1)?)),
            "INT.tdiv" | "INT.tmod" | "INT.ediv" | "INT.emod" => {
                let (x, y) = (n(0)?, n(1)?);
                if y.is_zero() {
                    return Some(undef());
                }
                // Euclidean: the remainder is non-negative, `x = y * q + r`
                let mut r = &x % &y;
                if r.is_negative() {
                    r += y.abs();
                }
                int(match h.as_str() {
                    "INT.tdiv" => &x / &y,
                    "INT.tmod" => &x % &y,
                    "INT.ediv" => (&x - &r) / &y,
                    _ => r,
                })
            }
            "INT.pow" => {
                let e = n(1)?;
                if e.is_negative() {
                    return Some(undef());
                }
                int(num_traits::pow(n(0)?, e.to_usize().filter(|e| *e <= 4096)?))
            }
            "INT.shl" | "INT.shr" => {
                let e = n(1)?;
                if e.is_negative() {
                    return Some(undef());
                }
                let e = e.to_usize().filter(|e| *e <= 4096)?;
                int(if h == "INT.shl" {
                    n(0)? << e
                } else {
                    n(0)? >> e
                })
            }
            "INT.and" => int(n(0)? & n(1)?),
            "INT.or" => int(n(0)? | n(1)?),
            "INT.xor" => int(n(0)? ^ n(1)?),
            "INT.not" => int(-n(0)? - BigInt::one()),
            "INT.log2" => {
                let x = n(0)?;
                if !x.is_positive() {
                    return Some(undef());
                }
                int(BigInt::from(x.bits() - 1))
            }
            "STRING.eq" | "STRING.ne" => match (&a[0], &a[1]) {
                (T::Lit(_, x), T::Lit(_, y)) => Self::lit_bool((x == y) == (h == "STRING.eq")),
                _ => return None,
            },
            "STRING.lt" => Self::lit_bool(st(0)? < st(1)?),
            "STRING.le" => Self::lit_bool(st(0)? <= st(1)?),
            "STRING.gt" => Self::lit_bool(st(0)? > st(1)?),
            "STRING.ge" => Self::lit_bool(st(0)? >= st(1)?),
            "STRING.concat" | "BYTES.concat" => lit(st(0)? + &st(1)?),
            "STRING.substr" => {
                let c = chars(&st(0)?);
                let (i, j) = (n(1)?, n(2)?);
                let len = c.len() as i64;
                let i = small(&i)?.max(0);
                let j = small(&j)?.max(0).min(len);
                lit(if i <= j {
                    ofc(&c[i as usize..j as usize])
                } else {
                    String::new()
                })
            }
            "STRING.find" => {
                let (hs, ns) = (chars(&st(0)?), chars(&st(1)?));
                let i = small(&n(2)?)?;
                if i < 0 {
                    return Some(undef());
                }
                let i = i as usize;
                if i > hs.len() {
                    int(BigInt::from(-1))
                } else {
                    let k = (i..=hs.len()).find(|&k| hs[k..].starts_with(&ns));
                    int(BigInt::from(k.map(|k| k as i64).unwrap_or(-1)))
                }
            }
            "STRING.string2int" => {
                let x = st(0)?;
                let d = x.strip_prefix(['-', '+']).unwrap_or(&x);
                if d.is_empty() || !d.chars().all(|c| c.is_ascii_digit()) {
                    return Some(undef());
                }
                int(x.trim_start_matches('+').parse().ok()?)
            }
            "STRING.int2string" => lit(n(0)?.to_string()),
            "STRING.base2string" => {
                let base = small(&n(1)?)?;
                if !(2..=36).contains(&base) {
                    return Some(undef());
                }
                lit(n(0)?.to_str_radix(base as u32))
            }
            "STRING.string2base" => {
                let base = small(&n(1)?)?;
                if !(2..=36).contains(&base) {
                    return Some(undef());
                }
                let x = st(0)?;
                let (neg, d) = match x.strip_prefix('-') {
                    Some(d) => (true, d),
                    None => (false, x.strip_prefix('+').unwrap_or(&x)),
                };
                match BigInt::parse_bytes(d.as_bytes(), base as u32) {
                    Some(v) if !d.is_empty() && !d.starts_with(['-', '+']) => {
                        int(if neg { -v } else { v })
                    }
                    _ => return Some(undef()),
                }
            }
            "STRING.replaceAll" => {
                let (x, from, to) = (st(0)?, st(1)?, st(2)?);
                lit(if from.is_empty() {
                    x
                } else {
                    x.replace(&from, &to)
                })
            }
            "STRING.replaceFirst" => {
                let (x, from, to) = (st(0)?, st(1)?, st(2)?);
                lit(if from.is_empty() {
                    x
                } else {
                    x.replacen(&from, &to, 1)
                })
            }
            "STRING.countAllOccurrences" => {
                let (x, nd) = (st(0)?, st(1)?);
                int(BigInt::from(if nd.is_empty() {
                    0
                } else {
                    x.matches(&nd).count()
                }))
            }
            "BYTES.substr" => {
                let c = chars(&st(0)?);
                let (i, j) = (small(&n(1)?)?, small(&n(2)?)?);
                if !(0 <= i && i <= j && j <= c.len() as i64) {
                    return Some(undef());
                }
                lit(ofc(&c[i as usize..j as usize]))
            }
            "BYTES.reverse" => lit(st(0)?.chars().rev().collect()),
            "BYTES.padLeft" | "BYTES.padRight" => {
                let x = st(0)?;
                let (l, v) = (small(&n(1)?)?, small(&n(2)?)?);
                if l < 0 || !(0..256).contains(&v) {
                    return Some(undef());
                }
                let k = (l as usize).saturating_sub(x.chars().count());
                let pad: String = std::iter::repeat_n(char::from_u32(v as u32)?, k).collect();
                lit(if h == "BYTES.padLeft" {
                    pad + &x
                } else {
                    x + &pad
                })
            }
            "BYTES.get" => {
                let c = chars(&st(0)?);
                let i = small(&n(1)?)?;
                if i < 0 || i as usize >= c.len() {
                    return Some(undef());
                }
                int(BigInt::from(c[i as usize] as u32))
            }
            "BYTES.bytes2string" => T::Lit("SortString".into(), st(0)?),
            "BYTES.string2bytes" => {
                let x = st(0)?;
                if x.chars().any(|c| c as u32 >= 256) {
                    return Some(undef());
                }
                T::Lit("SortBytes".into(), x)
            }
            "BYTES.bytes2int" => {
                let x = chars(&st(0)?);
                let (T::Ctor(e, _), T::Ctor(sg, _)) = (a.get(1)?, a.get(2)?) else {
                    return None;
                };
                let big = e == "LblbigEndianBytes";
                let signed = sg == "LblsignedBytes";
                let mut bytes: Vec<u8> = x.iter().map(|c| *c as u32 as u8).collect();
                if big {
                    bytes.reverse();
                }
                let mut v = BigInt::zero();
                for (k, by) in bytes.iter().enumerate() {
                    v += BigInt::from(*by) << (8 * k);
                }
                if signed && !bytes.is_empty() && v >= (BigInt::one() << (8 * bytes.len() - 1)) {
                    v -= BigInt::one() << (8 * bytes.len());
                }
                int(v)
            }
            "BYTES.int2bytes" => {
                let (len, x) = (small(&n(0)?)?, n(1)?);
                let T::Ctor(e, _) = a.get(2)? else {
                    return None;
                };
                let len = len.max(0) as usize;
                if len > 1 << 16 {
                    return None;
                }
                let m = BigInt::one() << (8 * len);
                let mut v = ((x % &m) + &m) % &m;
                let mut out = Vec::with_capacity(len);
                for _ in 0..len {
                    out.push(char::from_u32((&v % 256u32).to_u32()?)?);
                    v >>= 8;
                }
                if e == "LblbigEndianBytes" {
                    out.reverse();
                }
                lit(out.into_iter().collect())
            }
            "KEQUAL.eq" | "KEQUAL.ne" => {
                let eq = h == "KEQUAL.eq";
                if a[0] == a[1] && !contains_fn(&a[0]) {
                    Self::lit_bool(eq)
                } else if self.differ(cx, &a[0], &a[1]) {
                    Self::lit_bool(!eq)
                } else {
                    return None;
                }
            }
            "KEQUAL.ite" => {
                if b(0)? {
                    a[1].clone()
                } else {
                    a[2].clone()
                }
            }
            "MAP.in_keys" | "SET.in" | "LIST.in" => {
                // `K in_keys(M)`, `K in S`, `K inList L`: the element first, the collection second
                let (k, m) = (&a[0], &a[1]);
                let (_, el, rest) = self.coll_items(cx, m)?;
                let keys: Vec<T> = el
                    .iter()
                    .map(|e| {
                        if let T::Fn(_, x) = e {
                            x[0].clone()
                        } else {
                            e.clone()
                        }
                    })
                    .collect();
                if keys.iter().any(|x| x == k) {
                    Self::lit_bool(true)
                } else if rest.is_empty() && keys.iter().all(|x| self.differ(cx, x, k)) {
                    Self::lit_bool(false)
                } else {
                    return None;
                }
            }
            "BYTES.empty" => T::Lit("SortBytes".into(), String::new()),
            "SET.size" | "MAP.size" | "LIST.size" => {
                let (_, el, rest) = self.coll_items(cx, &a[0])?;
                if !rest.is_empty() {
                    return None;
                }
                int(BigInt::from(el.len()))
            }
            "BYTES.length" | "STRING.length" => match &a[0] {
                T::Lit(_, v) => int(BigInt::from(v.chars().count())),
                _ => return None,
            },
            "MAP.lookup" => {
                let (_, el, _) = self.coll_items(cx, &a[0])?;
                el.iter().find_map(|e| match e {
                    T::Fn(_, x) if x[0] == a[1] => Some(x[1].clone()),
                    _ => None,
                })?
            }
            "MAP.lookupOrDefault" => {
                // `M[K] orDefault D`: the value bound to `K`, or `D` when no binding has the key
                // `K` (the map has no unknown rest, and every key it has differs from `K`)
                let (_, el, rest) = self.coll_items(cx, &a[0])?;
                let mut keys = Vec::new();
                for e in &el {
                    let T::Fn(_, x) = e else { return None };
                    if x.len() != 2 {
                        return None;
                    }
                    keys.push((self.resolve(&x[0]), &x[1]));
                }
                let others_differ = |n: usize| {
                    keys.iter()
                        .filter(|(k, _)| *k != a[1])
                        .all(|(k, _)| self.differ(cx, k, &a[1]))
                        && keys.iter().filter(|(k, _)| *k == a[1]).count() == n
                };
                if let Some((_, v)) = keys.iter().find(|(k, _)| *k == a[1]) {
                    // a map with two bindings of one key is undefined, so the others must differ
                    if !others_differ(1) {
                        return None;
                    }
                    self.resolve(v)
                } else if rest.is_empty() && others_differ(0) {
                    a[2].clone()
                } else {
                    return None;
                }
            }
            _ => return None,
        })
    }

    fn apply_eqs(&self, cx: &mut Cx, f: &str, args: &[T], fuel: &mut usize) -> Option<T> {
        cx.templates(f);
        let n = cx.eqs[f].len();
        for k in 0..n {
            let (targs, treq, trhs, pleaves, taliases) = {
                let e = &cx.eqs[f][k];
                (
                    e.args.clone(),
                    e.req.clone(),
                    e.rhs.clone(),
                    e.pleaves.clone(),
                    e.aliases.clone(),
                )
            };
            if targs.len() != args.len() {
                return None;
            }
            let mut sg: BTreeMap<usize, T> = BTreeMap::new();
            let mut res = M::Yes;
            for (p, t) in targs.iter().zip(args) {
                match self.pmatch(cx, p, t, &pleaves, &mut sg) {
                    M::No => {
                        res = M::No;
                        break;
                    }
                    M::Maybe => res = M::Maybe,
                    M::Yes => {}
                }
            }
            // the aliases: each side matches the value the other was bound to
            if res == M::Yes {
                for (x, y) in &taliases {
                    let (x, y) = (psubst(x, &sg), psubst(y, &sg));
                    let r = if !contains_pvar(&y) {
                        self.pmatch(cx, &x, &y, &pleaves, &mut sg)
                    } else if !contains_pvar(&x) {
                        self.pmatch(cx, &y, &x, &pleaves, &mut sg)
                    } else {
                        M::Maybe
                    };
                    match r {
                        M::No => {
                            res = M::No;
                            break;
                        }
                        M::Maybe => res = M::Maybe,
                        M::Yes => {}
                    }
                }
            }
            match res {
                M::No => continue,
                M::Maybe => {
                    if std::env::var_os("K2LEAN_EVAL_TRACE").is_some() {
                        let mut a = String::new();
                        for x in args {
                            show(x, cx, &mut a);
                            a.push_str(" | ");
                        }
                        eprintln!("eval: {f} equation {k} undecided on {a:.300}");
                    }
                    return None;
                }
                M::Yes => {}
            }
            let mut ok = M::Yes;
            for (q, b) in &treq {
                let qi = psubst(q, &sg);
                let v = self.eval(cx, &qi, fuel);
                match Self::as_bool(&v) {
                    Some(x) if x == *b => {}
                    Some(_) => {
                        ok = M::No;
                        break;
                    }
                    None => ok = M::Maybe,
                }
            }
            match ok {
                M::No => continue,
                M::Maybe => {
                    if std::env::var_os("K2LEAN_EVAL_TRACE").is_some() {
                        let mut a = String::new();
                        for (q, b) in &treq {
                            let qi = psubst(q, &sg);
                            show(&qi, cx, &mut a);
                            a.push_str(&format!(" = {b} -> "));
                            let mut f2 = 100_000usize;
                            let v = self.eval(cx, &qi, &mut f2);
                            show(&v, cx, &mut a);
                            a.push_str(" | ");
                        }
                        eprintln!("eval: {f} equation {k} requires undecided: {a:.600}");
                    }
                    return None;
                }
                M::Yes => {
                    let r = psubst(&trhs, &sg);
                    if contains_pvar(&r) {
                        return None;
                    }
                    return Some(self.eval(cx, &r, fuel));
                }
            }
        }
        // no equation applies: the generated function is `none` there (unless a hook implements it)
        if cx.hook(f).is_none() {
            Some(undef())
        } else {
            None
        }
    }

    fn pmatch(&self, cx: &Cx, p: &T, t: &T, pl: &[Leaves], sg: &mut BTreeMap<usize, T>) -> M {
        let t = self.walk(t);
        match p {
            T::PVar(i) => {
                if let Some(u) = sg.get(i) {
                    return if *u == t && !contains_fn(&t) {
                        M::Yes
                    } else if self.differ(cx, u, &t) {
                        M::No
                    } else {
                        M::Maybe
                    };
                }
                let lp = &pl[*i];
                let fits = match &t {
                    T::Var(j) => {
                        let lt = cx.var_leaves(*j, &self.ext);
                        if lt.is_subset(lp) {
                            M::Yes
                        } else if lt.is_disjoint(lp) {
                            M::No
                        } else {
                            M::Maybe
                        }
                    }
                    T::Fn(..) => match cx.term_leaves(&t, &self.ext) {
                        Some(lt) if lt.is_subset(lp) => M::Yes,
                        Some(lt) if lt.is_disjoint(lp) => M::No,
                        _ => M::Maybe,
                    },
                    _ => match cx.term_leaves(&t, &self.ext) {
                        Some(lt) if lt.is_subset(lp) => M::Yes,
                        Some(_) => M::No,
                        None => M::Maybe,
                    },
                };
                if fits == M::Yes {
                    sg.insert(*i, self.resolve(&t));
                }
                fits
            }
            T::Ctor(f, ps) => match &t {
                T::Ctor(g, ts) => {
                    if f != g || ps.len() != ts.len() {
                        return M::No;
                    }
                    let mut r = M::Yes;
                    for (x, y) in ps.iter().zip(ts) {
                        match self.pmatch(cx, x, y, pl, sg) {
                            M::No => return M::No,
                            M::Maybe => r = M::Maybe,
                            M::Yes => {}
                        }
                    }
                    r
                }
                T::Lit(..) => M::No,
                _ => {
                    let cs =
                        cx.m.ctors
                            .get(f)
                            .map(|c| c.sort.clone())
                            .unwrap_or_default();
                    match cx.term_leaves(&t, &self.ext) {
                        Some(lt) if !lt.contains(&cs) => M::No,
                        _ => M::Maybe,
                    }
                }
            },
            T::Lit(s, v) => match &t {
                T::Lit(s2, w) => {
                    if s == s2 && v == w {
                        M::Yes
                    } else {
                        M::No
                    }
                }
                T::Ctor(..) => M::No,
                _ => match cx.term_leaves(&t, &self.ext) {
                    Some(lt) if !lt.contains(s) => M::No,
                    _ => M::Maybe,
                },
            },
            T::Fn(f, ps) => {
                // a collection pattern in an equation: the unit and exact element lists only
                match cx.hook(f) {
                    Some(h) if h.ends_with(".unit") => match self.coll_items(cx, &t) {
                        Some((_, el, rest)) if el.is_empty() && rest.is_empty() => M::Yes,
                        Some((_, el, _)) if !el.is_empty() => M::No,
                        _ => M::Maybe,
                    },
                    _ => {
                        let _ = ps;
                        M::Maybe
                    }
                }
            }
            _ => M::Maybe,
        }
    }
}

/// Whether `t` contains a pattern this analysis does not model. A function call is fine: two
/// syntactically equal calls have the same value where they are defined, and an undefined
/// requires is not `true`.
fn contains_fn(t: &T) -> bool {
    match t {
        T::Unk(_) => true,
        T::Ctor(_, a) | T::Fn(_, a) => a.iter().any(contains_fn),
        _ => false,
    }
}

/// A term without variables or unmodelled parts (its evaluation does not depend on a unifier).
fn is_ground_value(t: &T) -> bool {
    match t {
        T::Lit(..) => true,
        T::Ctor(_, a) | T::Fn(_, a) => a.iter().all(is_ground_value),
        _ => false,
    }
}

/// The value of a function where none of its equations applies (the generated `none`).
fn undef() -> T {
    T::Unk("undefined".into())
}

fn is_undef(t: &T) -> bool {
    matches!(t, T::Unk(s) if s == "undefined")
}

fn contains_pvar(t: &T) -> bool {
    match t {
        T::PVar(_) => true,
        T::Ctor(_, a) | T::Fn(_, a) => a.iter().any(contains_pvar),
        _ => false,
    }
}

fn psubst(t: &T, sg: &BTreeMap<usize, T>) -> T {
    match t {
        T::PVar(i) => sg.get(i).cloned().unwrap_or_else(|| t.clone()),
        T::Ctor(f, a) => T::Ctor(f.clone(), a.iter().map(|x| psubst(x, sg)).collect()),
        T::Fn(f, a) => T::Fn(f.clone(), a.iter().map(|x| psubst(x, sg)).collect()),
        other => other.clone(),
    }
}

// ---------------------------------------------------------------- SMT

/// The SMT sort of a K sort: integers, booleans, and strings and byte arrays as z3 strings.
fn smt_sort(s: &str) -> Option<&'static str> {
    match s {
        "SortInt" => Some("Int"),
        "SortBool" => Some("Bool"),
        "SortString" | "SortBytes" => Some("String"),
        _ => None,
    }
}

fn smt_string(v: &str) -> String {
    let mut o = String::from("\"");
    for c in v.chars() {
        if c.is_ascii_graphic() && c != '"' && c != '\\' || c == ' ' {
            o.push(c);
        } else {
            o.push_str(&format!("\\u{{{:x}}}", c as u32));
        }
    }
    o.push('"');
    o
}

struct Smt<'c, 'a> {
    decls: BTreeMap<String, (String, &'static str)>,
    /// What each declared constant stands for (a variable, an abstracted call, or `a ==K b`).
    terms: BTreeMap<String, T>,
    /// The length of a string or byte variable as an integer atom of its own (the witness
    /// search realizes it by a value of that length, which z3 need not construct).
    len_atoms: bool,
    cx: &'c Cx<'a>,
    un: &'c Un,
}

impl<'c, 'a> Smt<'c, 'a> {
    fn sort_of_term(&self, t: &T) -> Option<&'static str> {
        let s = match t {
            T::Lit(s, _) => s.clone(),
            T::Var(i) => {
                let l = self.cx.var_leaves(*i, &self.un.ext);
                if l.len() != 1 {
                    return None;
                }
                l.iter().next().unwrap().clone()
            }
            T::Fn(f, _) => self.cx.result_sort(f)?,
            T::Ctor(f, _) => self.cx.m.ctors.get(f)?.sort.clone(),
            _ => return None,
        };
        smt_sort(&s)
    }

    /// `t` at SMT sort `sort`: a variable whose sort includes one of that sort's K sorts is read
    /// as a value of it (sound for unsatisfiability: see `classify`).
    fn tr_as(&mut self, t: &T, sort: &'static str) -> Option<String> {
        if self.sort_of_term(t) == Some(sort) {
            return self.tr(t);
        }
        if let T::Var(i) = t {
            let l = self.cx.var_leaves(*i, &self.un.ext);
            if l.iter().any(|x| smt_sort(x) == Some(sort)) {
                return Some(self.atom_const(t, sort));
            }
        }
        None
    }

    /// `k ∈ items` for a collection whose elements are all known.
    fn member(&mut self, k: &T, coll: &T) -> Option<String> {
        let (_, el, rest) = self.un.coll_items(self.cx, coll)?;
        if !rest.is_empty() {
            return None;
        }
        if el.is_empty() {
            return Some("false".into());
        }
        let keys: Vec<T> = el
            .iter()
            .map(|e| {
                if let T::Fn(_, x) = e {
                    x[0].clone()
                } else {
                    e.clone()
                }
            })
            .collect();
        let sort = self.sort_of_term(&keys[0])?;
        let kk = self.tr_as(k, sort)?;
        let mut alts = Vec::new();
        for x in &keys {
            if self.sort_of_term(x) != Some(sort) {
                return None;
            }
            alts.push(format!("(= {kk} {})", self.tr(x)?));
        }
        Some(format!("(or {} false)", alts.join(" ")))
    }

    fn atom_const(&mut self, t: &T, sort: &'static str) -> String {
        let key = format!("{}::{sort}", shown(t, self.cx));
        let n = self.decls.len();
        let name = self
            .decls
            .entry(key)
            .or_insert_with(|| (format!("a{n}"), sort))
            .0
            .clone();
        self.terms.entry(name.clone()).or_insert_with(|| t.clone());
        name
    }

    fn tr(&mut self, t: &T) -> Option<String> {
        let sort = self.sort_of_term(t)?;
        match t {
            T::Lit(_, v) => Some(match sort {
                "Int" => {
                    if let Some(x) = v.strip_prefix('-') {
                        format!("(- {x})")
                    } else {
                        v.clone()
                    }
                }
                "String" => smt_string(v),
                _ => v.clone(),
            }),
            T::Var(_) => Some(self.atom_const(t, sort)),
            T::Fn(f, a) => {
                let h = self.cx.hook(f).unwrap_or("").to_string();
                let bin = |s: &mut Self, op: &str| -> Option<String> {
                    let x = s.tr(&a[0])?;
                    let y = s.tr(&a[1])?;
                    Some(format!("({op} {x} {y})"))
                };
                let r = match h.as_str() {
                    "INT.add" => bin(self, "+"),
                    "INT.sub" => bin(self, "-"),
                    "INT.mul" => bin(self, "*"),
                    "INT.lt" => bin(self, "<"),
                    "INT.le" => bin(self, "<="),
                    "INT.gt" => bin(self, ">"),
                    "INT.ge" => bin(self, ">="),
                    "INT.eq" | "BOOL.eq" => bin(self, "="),
                    "INT.ne" | "BOOL.ne" | "BOOL.xor" => bin(self, "distinct"),
                    "INT.min" | "INT.max" => {
                        let x = self.tr(&a[0])?;
                        let y = self.tr(&a[1])?;
                        Some(if h == "INT.min" {
                            format!("(ite (<= {x} {y}) {x} {y})")
                        } else {
                            format!("(ite (>= {x} {y}) {x} {y})")
                        })
                    }
                    "INT.abs" => self.tr(&a[0]).map(|x| format!("(abs {x})")),
                    "INT.ediv" | "INT.emod" => {
                        // Euclidean division by a non-zero literal is z3's div/mod
                        if Un::as_int(&a[1]).is_some_and(|k| k != BigInt::from(0)) {
                            bin(self, if h == "INT.ediv" { "div" } else { "mod" })
                        } else {
                            None
                        }
                    }
                    "BOOL.and" | "BOOL.andThen" => bin(self, "and"),
                    "BOOL.or" | "BOOL.orElse" => bin(self, "or"),
                    "BOOL.implies" => bin(self, "=>"),
                    "BOOL.not" => self.tr(&a[0]).map(|x| format!("(not {x})")),
                    "STRING.eq" => bin(self, "="),
                    "STRING.ne" => bin(self, "distinct"),
                    "BYTES.length" | "STRING.length"
                        if self.len_atoms && matches!(a[0], T::Var(_)) =>
                    {
                        Some(self.atom_const(t, "Int"))
                    }
                    "BYTES.length" | "STRING.length" => {
                        self.tr(&a[0]).map(|x| format!("(str.len {x})"))
                    }
                    "SET.in" | "MAP.in_keys" => self.member(&a[0], &a[1]),
                    "KEQUAL.eq" | "KEQUAL.ne" => {
                        // `x ~> .K ==K y ~> .K` compares the items
                        let unk = |t: &T| match t {
                            T::Ctor(k, xs)
                                if k == "kseq"
                                    && matches!(xs.get(1), Some(T::Ctor(d, _)) if d == "dotk") =>
                            {
                                xs[0].clone()
                            }
                            other => other.clone(),
                        };
                        let a = [unk(&a[0]), unk(&a[1])];
                        let (x, y) = (self.tr(&a[0]), self.tr(&a[1]));
                        let e = match (x, y) {
                            (Some(x), Some(y))
                                if self.sort_of_term(&a[0]) == self.sort_of_term(&a[1]) =>
                            {
                                format!("(= {x} {y})")
                            }
                            _ => {
                                // abstract `a ==K b` (unordered) as one boolean
                                let (p, q) = (shown(&a[0], self.cx), shown(&a[1], self.cx));
                                let key = if p <= q {
                                    format!("{p} ==K {q}")
                                } else {
                                    format!("{q} ==K {p}")
                                };
                                let n = self.decls.len();
                                let name = self
                                    .decls
                                    .entry(key)
                                    .or_insert_with(|| (format!("a{n}"), "Bool"))
                                    .0
                                    .clone();
                                self.terms.entry(name.clone()).or_insert_with(|| {
                                    T::Fn("==K".into(), vec![a[0].clone(), a[1].clone()])
                                });
                                name
                            }
                        };
                        Some(if h == "KEQUAL.ne" {
                            format!("(not {e})")
                        } else {
                            e
                        })
                    }
                    "KEQUAL.ite" => {
                        let c = self.tr(&a[0]);
                        let (x, y) = (self.tr(&a[1]), self.tr(&a[2]));
                        match (c, x, y) {
                            (Some(c), Some(x), Some(y)) => Some(format!("(ite {c} {x} {y})")),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                Some(r.unwrap_or_else(|| self.atom_const(t, sort)))
            }
            _ => Some(self.atom_const(t, sort)),
        }
    }
}

// ---------------------------------------------------------------- pairs

#[derive(Clone, Debug)]
pub struct PairOut {
    pub class: String,
    pub detail: String,
    pub depth: usize,
    /// For `exclusive`/`smt`: the SMT query (sat check pending).
    pub smt: Option<(String, Vec<String>)>,
    /// Case splits whose open cases need SMT: (label, one query per open case).
    pub cases: Vec<(String, Vec<String>)>,
    /// For a verdict by evaluation: the functions and hooks the evaluator applied to reach it
    /// (KORE symbols), the definitions a proof by evaluation unfolds.
    pub used: Option<BTreeSet<String>>,
}

fn head_name(t: &T) -> String {
    match t {
        T::Fn(f, _) | T::Ctor(f, _) => crate::names::demangle(f)
            .trim_start_matches("Lbl")
            .to_string(),
        T::Var(_) => "variable".into(),
        _ => "literal".into(),
    }
}

fn classify(cx: &mut Cx, a: &CRule, b: &CRule, same_rank: bool) -> PairOut {
    classify0(cx, a, b, same_rank)
}

#[allow(clippy::too_many_arguments)]
fn explain(
    cx: &Cx,
    un: &Un,
    what: &str,
    a: &CRule,
    b: &CRule,
    qa: &[(T, bool)],
    qb: &[(T, bool)],
    smt: &str,
) {
    eprintln!("=== {what}");
    eprintln!("lhs: {}", shown(&un.resolve(&a.lhs), cx));
    eprintln!("unknown: {:?}", un.unknown);
    for (t, b) in qa {
        eprintln!("  req1: {} = {b}", shown(t, cx));
    }
    for (t, b) in qb {
        eprintln!("  req2: {} = {b}", shown(t, cx));
    }
    eprintln!("rhs1: {}", shown(&un.resolve(&a.rhs), cx));
    eprintln!("rhs2: {}", shown(&un.resolve(&b.rhs), cx));
    eprintln!("smt:\n{smt}");
}

fn classify0(cx: &mut Cx, a: &CRule, b: &CRule, same_rank: bool) -> PairOut {
    cx.used.clear();
    let mut un = Un::new();
    let r = (|| -> Result<(), Clash> {
        for (x, y) in a.aliases.iter().chain(&b.aliases) {
            un.unify(cx, x, y, 0)?;
        }
        un.unify(cx, &a.lhs, &b.lhs, 0)?;
        un.finish(cx)
    })();
    if let Err(c) = r {
        return PairOut {
            class: "clash".into(),
            detail: format!("{}: {}", c.kind, c.at),
            depth: c.depth,
            smt: None,
            cases: vec![],
            used: None,
        };
    }
    let unk: Vec<String> = un.unknown.iter().cloned().collect();
    if !same_rank {
        return PairOut {
            class: "priority".into(),
            detail: unk.join(", "),
            depth: 0,
            smt: None,
            cases: vec![],
            used: None,
        };
    }
    // the requires clauses under the unifier
    let mut fuel = 20_000usize;
    let eval_atoms = |un: &mut Un,
                      cx: &mut Cx,
                      req: &[(T, bool)],
                      fuel: &mut usize|
     -> (Vec<(T, bool)>, Option<String>) {
        let mut out = Vec::new();
        for (e, bv) in req {
            let v = un.eval(cx, e, fuel);
            let mut parts = Vec::new();
            cx.push_atom(v, *bv, &mut parts);
            for (p, pb) in parts {
                if is_undef(&p) {
                    return (
                        out,
                        Some(format!("{}, undefined", head_name(&un.resolve(e)))),
                    );
                }
                if let Some(x) = Un::as_bool(&p) {
                    if x != pb {
                        return (out, Some(head_name(&un.resolve(e))));
                    }
                    continue;
                }
                out.push((p, pb));
            }
        }
        (out, None)
    };
    let (qa, fa) = eval_atoms(&mut un, cx, &a.req, &mut fuel);
    if let Some(h) = fa {
        return PairOut {
            class: "exclusive".into(),
            detail: format!("eval: first rule's requires is false ({h})"),
            depth: 0,
            smt: None,
            cases: vec![],
            used: Some(cx.used.clone()),
        };
    }
    let (qb, fb) = eval_atoms(&mut un, cx, &b.req, &mut fuel);
    if let Some(h) = fb {
        return PairOut {
            class: "exclusive".into(),
            detail: format!("eval: second rule's requires is false ({h})"),
            depth: 0,
            smt: None,
            cases: vec![],
            used: Some(cx.used.clone()),
        };
    }
    for (x, bx) in &qa {
        for (y, by) in &qb {
            if x == y && bx != by && !matches!(x, T::Unk(_)) {
                return PairOut {
                    class: "exclusive".into(),
                    detail: format!("complement ({})", head_name(x)),
                    depth: 0,
                    smt: None,
                    cases: vec![],
                    used: None,
                };
            }
        }
    }
    // joinable: equal right-hand sides
    let ra = un.eval(cx, &a.rhs, &mut fuel);
    let rb = un.eval(cx, &b.rhs, &mut fuel);
    let ra = un.resolve(&ra);
    let rb = un.resolve(&rb);
    // a rule whose result is undefined wherever both apply has no step there: the pair is
    // separated as steps (the step relation requires the result's partial calls to be defined)
    if is_undef(&ra) || is_undef(&rb) {
        return PairOut {
            class: "exclusive".into(),
            detail: format!(
                "eval: the {} rule's result is undefined",
                if is_undef(&ra) { "first" } else { "second" }
            ),
            depth: 0,
            smt: None,
            cases: vec![],
            used: Some(cx.used.clone()),
        };
    }
    let joinable = ra == rb;
    // the SMT query: both requires, every non-arithmetic subterm abstracted
    let (q, names, n_asserts) = smt_query(cx, &un, &qa, &qb);
    let undecided = if unk.is_empty() {
        "conditions".to_string()
    } else {
        unk.join(", ")
    };
    if cx.explain {
        explain(cx, &un, "pair", a, b, &qa, &qb, &q);
    }
    if joinable {
        return PairOut {
            class: "joinable".into(),
            detail: undecided,
            depth: 0,
            smt: None,
            cases: vec![],
            used: None,
        };
    }
    // a case split on a variable of a sort with constructors, which the conditions test
    let mut cases = Vec::new();
    let mut closed = None;
    let cands = split_candidates(cx, &un, &qa, &qb);
    let mut tries: Vec<Vec<usize>> = cands.iter().take(3).map(|&v| vec![v]).collect();
    if cands.len() >= 2 {
        tries.push(vec![cands[0], cands[1]]);
    }
    for vs in tries {
        match case_split(cx, &un, &vs, a, b) {
            Some((label, qs, refuting)) if qs.is_empty() => {
                closed = Some((label, refuting));
                break;
            }
            Some((label, qs, _)) => cases.push((label, qs)),
            None => {}
        }
    }
    if let Some((label, refuting)) = closed {
        return PairOut {
            class: "exclusive".into(),
            detail: format!("case split: {label}, every case by eval"),
            depth: 0,
            smt: None,
            cases: vec![],
            used: Some(refuting),
        };
    }
    PairOut {
        class: "overlap".into(),
        detail: undecided,
        depth: 0,
        smt: if n_asserts == 0 {
            None
        } else {
            Some((q, names))
        },
        cases,
        used: None,
    }
}

fn smt_query(cx: &Cx, un: &Un, qa: &[(T, bool)], qb: &[(T, bool)]) -> (String, Vec<String>, usize) {
    let mut q = String::new();
    let mut names = Vec::new();
    let atoms: Vec<&(T, bool)> = qa.iter().chain(qb).collect();
    let mut smt = Smt {
        decls: BTreeMap::new(),
        terms: BTreeMap::new(),
        len_atoms: false,
        cx,
        un,
    };
    let mut asserts = Vec::new();
    for (k, (e, bv)) in atoms.iter().enumerate() {
        if matches!(e, T::Unk(_)) {
            names.push(String::new());
            continue;
        }
        if let Some(s) = smt.tr(e) {
            asserts.push(format!("(assert (! (= {s} {bv}) :named q{k}))"));
        }
        names.push(head_name(e));
    }
    // a string constant that occurs only under `str.len` is only its length, a natural number
    // (every length has a string): z3 then need not build a long string to answer
    let mut lens = Vec::new();
    for (n, s) in smt.decls.values() {
        if *s != "String" {
            continue;
        }
        let whole = asserts.iter().map(|a| count_word(a, n)).sum::<usize>();
        let under = asserts
            .iter()
            .map(|a| a.matches(&format!("(str.len {n})")).count())
            .sum::<usize>();
        if whole > 0 && whole == under {
            lens.push(n.clone());
        }
    }
    for n in &lens {
        for a in asserts.iter_mut() {
            *a = a.replace(&format!("(str.len {n})"), &format!("{n}_len"));
        }
    }
    for (n, s) in smt.decls.values() {
        if lens.contains(n) {
            let _ = writeln!(q, "(declare-const {n}_len Int)\n(assert (>= {n}_len 0))");
        } else {
            let _ = writeln!(q, "(declare-const {n} {s})");
        }
    }
    for a in &asserts {
        q.push_str(a);
        q.push('\n');
    }
    (q, names, asserts.len())
}

/// The occurrences of the SMT symbol `w` in `text` as a whole token.
fn count_word(text: &str, w: &str) -> usize {
    let b = text.as_bytes();
    text.match_indices(w)
        .filter(|(i, _)| {
            let before = *i == 0 || !(b[i - 1].is_ascii_alphanumeric() || b[i - 1] == b'_');
            let j = i + w.len();
            let after = j >= b.len() || !(b[j].is_ascii_alphanumeric() || b[j] == b'_');
            before && after
        })
        .count()
}

fn vars_of(t: &T, out: &mut Vec<usize>) {
    match t {
        T::Var(i) => {
            if !out.contains(i) {
                out.push(*i)
            }
        }
        T::Ctor(_, a) | T::Fn(_, a) => a.iter().for_each(|x| vars_of(x, out)),
        _ => {}
    }
}

/// Variables of the conditions whose sort is made of constructor sorts only (a finite case split).
fn split_candidates(cx: &Cx, un: &Un, qa: &[(T, bool)], qb: &[(T, bool)]) -> Vec<usize> {
    let mut vs = Vec::new();
    for (t, _) in qa.iter().chain(qb) {
        vars_of(&un.resolve(t), &mut vs);
    }
    vs.retain(|&v| {
        let n = case_count(cx, &cx.var_leaves(v, &un.ext));
        n > 1
            && n <= 600
            && cx
                .var_leaves(v, &un.ext)
                .iter()
                .any(|x| cx.m.sorts.get(x).is_some_and(|s| !s.own.is_empty()))
    });
    vs
}

/// The cases of a variable: one per constructor of each leaf with constructors, one per other leaf.
fn case_count(cx: &Cx, l: &BTreeSet<String>) -> usize {
    l.iter()
        .map(|x| cx.m.sorts.get(x).map(|s| s.own.len().max(1)).unwrap_or(1))
        .sum()
}

fn cases_of(cx: &Cx, u: &mut Un, l: &BTreeSet<String>) -> Vec<T> {
    let mut out = Vec::new();
    for x in l {
        let own = cx.m.sorts.get(x).map(|s| s.own.clone()).unwrap_or_default();
        if own.is_empty() {
            out.push(T::Var(
                u.fresh(cx, Rc::new([x.clone()].into_iter().collect())),
            ));
            continue;
        }
        for c in own {
            let args: Vec<String> =
                cx.m.ctors
                    .get(&c)
                    .map(|ci| ci.args.clone())
                    .unwrap_or_default();
            let fresh: Vec<T> = args
                .iter()
                .map(|s| T::Var(u.fresh(cx, cx.leaves_of_sort(s))))
                .collect();
            out.push(T::Ctor(c.clone(), fresh));
        }
    }
    out
}

/// The case split on `vs` (the product of their cases): in each case the requires clauses are
/// re-evaluated; `None` if some case leaves no condition to refute. Returns (label, SMT queries of
/// the cases that evaluation did not close, and the definitions that refute the closed cases).
/// A case is closed by one atom of the requires evaluating to the opposite truth value (or to
/// undefined); the definitions that evaluation applied, with the connectives that split the
/// requires into atoms, are all a proof of that case unfolds.
fn case_split(
    cx: &mut Cx,
    un: &Un,
    vs: &[usize],
    a: &CRule,
    b: &CRule,
) -> Option<(String, Vec<String>, BTreeSet<String>)> {
    let mut combos: Vec<Un> = vec![un.clone()];
    let mut label = Vec::new();
    for &v in vs {
        let l = cx.var_leaves(v, &un.ext);
        label.push(format!(
            "{} ({} cases)",
            crate::names::short_sort(l.iter().next().map(|s| s.as_str()).unwrap_or("")),
            case_count(cx, &l)
        ));
        let mut next = Vec::new();
        for u in combos {
            let mut u0 = u.clone();
            for t in cases_of(cx, &mut u0, &l) {
                let mut u1 = u0.clone();
                if u1.unify(cx, &T::Var(v), &t, 0).is_ok() {
                    next.push(u1);
                }
            }
        }
        combos = next;
        if combos.len() > 2000 {
            return None;
        }
    }
    let n_cases = combos.len();
    let mut qs = Vec::new();
    let mut refuting: BTreeSet<String> = a.conns.union(&b.conns).cloned().collect();
    for u in combos {
        let mut fuel = 20_000usize;
        let mut closed = false;
        let mut qa = Vec::new();
        let mut qb = Vec::new();
        for (req, out) in [(&a.req, &mut qa), (&b.req, &mut qb)] {
            for (e, bv) in req.iter() {
                let saved = std::mem::take(&mut cx.used);
                let val = u.eval(cx, e, &mut fuel);
                let mut parts = Vec::new();
                cx.push_atom(val, *bv, &mut parts);
                let mut refutes = false;
                for (p, pb) in parts {
                    if is_undef(&p) {
                        refutes = true;
                        continue;
                    }
                    match Un::as_bool(&p) {
                        Some(x) if x != pb => refutes = true,
                        Some(_) => {}
                        None => out.push((p, pb)),
                    }
                }
                let atom = std::mem::replace(&mut cx.used, saved);
                cx.used.extend(atom.iter().cloned());
                // the first refuting atom of the case
                if refutes && !closed {
                    closed = true;
                    refuting.extend(atom);
                }
            }
        }
        if closed {
            continue;
        }
        let (q, _, n) = smt_query(cx, &u, &qa, &qb);
        if n == 0 {
            return None;
        }
        qs.push(q);
    }
    Some((
        format!("{} = {n_cases} cases", label.join(" × ")),
        qs,
        refuting,
    ))
}

/// The node at `path` in a lowered left-hand side, as the index reads it.
fn at_path<'l>(
    l: &'l crate::lower::L,
    path: &[(String, usize)],
    info: &crate::index::CtorInfo,
) -> Result<Option<&'l str>, ()> {
    use crate::lower::L;
    let mut cur = l;
    for (ctor, pos) in path {
        match cur {
            L::App(h, args) if info.contains_key(h) => {
                if h != ctor {
                    return Err(()); // absent: another constructor above
                }
                cur = &args[*pos];
            }
            _ => return Ok(None),
        }
    }
    Ok(match cur {
        L::App(h, _) if info.contains_key(h) => Some(h.as_str()),
        _ => None,
    })
}

/// The rules of the buckets `bucketOf` can return at an instance of `lhs` (design 1's candidates):
/// a tested node that is a constructor of `lhs` selects its branch, a variable selects all.
fn reach(t: &Tree, lhs: &crate::lower::L, info: &crate::index::CtorInfo, out: &mut Vec<usize>) {
    match t {
        Tree::Leaf(rs) => out.extend(rs.iter().copied()),
        Tree::Node {
            path,
            branches,
            rest,
            ..
        } => {
            match at_path(lhs, path, info) {
                Ok(Some(c)) => {
                    for (b, _, sub) in branches {
                        if b == c {
                            reach(sub, lhs, info, out);
                        }
                    }
                }
                Ok(None) => {
                    for (_, _, sub) in branches {
                        reach(sub, lhs, info, out);
                    }
                }
                Err(()) => {}
            }
            reach(rest, lhs, info, out);
        }
    }
}

/// The first item of the `<k>` cell of a converted left-hand side, as "constructor/ownctor", or
/// `None` when it is a variable (or there is no `<k>` cell).
fn k_head(t: &T, cx: &Cx) -> Option<String> {
    fn find(t: &T) -> Option<&T> {
        match t {
            T::Ctor(f, a) if f.contains("'-LT-'k'-GT-'") => a.first(),
            T::Ctor(_, a) => a.iter().find_map(find),
            _ => None,
        }
    }
    let k = find(t)?;
    let item = match k {
        T::Ctor(f, a) if f == "kseq" => &a[0],
        other => other,
    };
    match item {
        T::Ctor(f, _) => Some(f.clone()),
        T::Lit(s, _) => Some(s.clone()),
        T::Fn(f, _) => Some(format!("fn {f}")),
        _ => {
            let _ = cx;
            None
        }
    }
}

/// Pairs the index can put in one bucket: within a leaf, and across a merge.
fn index_pairs(t: &Tree, out: &mut Vec<(usize, usize, &'static str)>) -> Vec<usize> {
    match t {
        Tree::Leaf(rs) => {
            for (i, &x) in rs.iter().enumerate() {
                for &y in &rs[i + 1..] {
                    out.push((x.min(y), x.max(y), "leaf"));
                }
            }
            rs.clone()
        }
        Tree::Node { branches, rest, .. } => {
            let mut under = Vec::new();
            for (_, _, b) in branches {
                under.extend(index_pairs(b, out));
            }
            let r = index_pairs(rest, out);
            for &x in &under {
                for &y in &r {
                    out.push((x.min(y), x.max(y), "merge"));
                }
            }
            under.extend(r);
            under
        }
    }
}

fn leaf_sizes(t: &Tree, out: &mut Vec<usize>, merges: &mut usize) {
    match t {
        Tree::Leaf(r) => out.push(r.len()),
        Tree::Node { branches, rest, .. } => {
            if !matches!(&**rest, Tree::Leaf(v) if v.is_empty()) {
                *merges += 1;
            }
            for (_, _, b) in branches {
                leaf_sizes(b, out, merges);
            }
            leaf_sizes(rest, out, merges);
        }
    }
}

/// Each query's verdict and unsat core, from the `z3` executable (`Z3`, default `z3` on `PATH`).
/// The classification is untrusted, but a missing solver would turn its pairs into overlaps,
/// which weakens the theorem, so it is an error.
fn run_z3(queries: &[String]) -> Vec<(String, Vec<String>)> {
    if queries.is_empty() {
        return vec![];
    }
    let mut script = String::from(
        "(set-option :produce-unsat-cores true)\n(set-option :rlimit 500000)\n(set-option :timeout 20000)\n",
    );
    for q in queries {
        script.push_str("(push 1)\n");
        script.push_str(q);
        script.push_str("(check-sat)\n(get-unsat-core)\n(pop 1)\n");
    }
    let dir = std::env::temp_dir().join(format!("k2lean-pairs-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let f = dir.join("q.smt2");
    std::fs::write(&f, &script).unwrap();
    if let Ok(keep) = std::env::var("K2LEAN_KEEP_Z3") {
        let _ = std::fs::write(format!("{keep}-{}.smt2", queries.len()), &script);
    }
    let z3 = std::env::var("Z3").unwrap_or_else(|_| "z3".into());
    let out = std::process::Command::new(&z3)
        .arg(&f)
        .output()
        .unwrap_or_else(|e| {
            panic!("the rule-pair classification needs z3 ({z3}: {e}); set Z3 to its path")
        });
    let text = String::from_utf8_lossy(&out.stdout).to_string();
    let _ = std::fs::remove_dir_all(&dir);
    // each query prints its result line and a core line (or an error for sat)
    let mut res = Vec::new();
    let mut lines = text.lines().peekable();
    while let Some(l) = lines.next() {
        let l = l.trim();
        if l == "sat" || l == "unsat" || l == "unknown" {
            let core_line = lines.next().unwrap_or("").trim().to_string();
            let core: Vec<String> = if l == "unsat" {
                core_line
                    .trim_matches(|c| c == '(' || c == ')')
                    .split_whitespace()
                    .map(|s| s.to_string())
                    .collect()
            } else {
                vec![]
            };
            res.push((l.to_string(), core));
        }
    }
    assert_eq!(
        res.len(),
        queries.len(),
        "z3 output: {}",
        &text[..text.len().min(2000)]
    );
    res
}

pub fn run(def: &Def, rest: &[String], kore: &std::path::Path, runtime: Option<&std::path::Path>) {
    let mut out_dir = std::path::PathBuf::from(".");
    let mut name = "def".to_string();
    let mut all_pairs = false;
    let mut same_binding = false;
    let mut explain: Option<(String, String)> = None;
    let mut want_witnesses = false;
    let mut it = rest.iter();
    while let Some(x) = it.next() {
        match x.as_str() {
            "--out-dir" => out_dir = it.next().unwrap().into(),
            "--label" => name = it.next().unwrap().clone(),
            "--all-pairs" => all_pairs = true,
            "--same-binding" => same_binding = true,
            "--witnesses" => want_witnesses = true,
            "--explain" => explain = Some((it.next().unwrap().clone(), it.next().unwrap().clone())),
            _ => {}
        }
    }
    let _ = kore;
    let m = Model::build(def).unwrap_or_else(|e| panic!("{e}"));
    let order: Vec<String> = match runtime {
        Some(p) => {
            let j: serde_json::Value =
                serde_json::from_str(&std::fs::read_to_string(p).unwrap()).unwrap();
            j["execution_rewrite_order"]
                .as_array()
                .map(|v| {
                    v.iter()
                        .filter_map(|x| x.as_str().map(String::from))
                        .collect()
                })
                .unwrap_or_default()
        }
        None => vec![],
    };
    let mut roots = BTreeSet::new();
    for ax in &def.axioms {
        if let P::Rewrites(_, l, _) = &ax.pattern
            && crate::rules::absent_sort(l, &m).is_none()
        {
            crate::funcs::applied(&ax.pattern, def, &mut roots);
        }
    }
    roots.extend(m.anywhere.iter().cloned());
    let fgen = crate::funcs::generate(def, &m, &roots).unwrap_or_else(|e| panic!("functions: {e}"));
    let mut rs =
        crate::rules::collect(def, &m, &fgen.fns, &order).unwrap_or_else(|e| panic!("{e}"));
    let mut prios = crate::rules::priorities(def);
    let multi = rs.iter().any(|r| r.multi);
    if multi {
        rs = crate::rules::collect_with(def, &m, &fgen.fns, &order, true)
            .unwrap_or_else(|e| panic!("{e}"));
        prios.retain(|p| rs.iter().any(|r| r.priority == *p));
    }
    let rank = |r: &Rule| prios.iter().position(|p| *p == r.priority).unwrap();
    let info = crate::rules::ctor_info(&m);
    let raw_eqs = crate::funcs::equations_modulo_overloads(def, &m);
    let mut cx = Cx::new(def, &m, &raw_eqs);
    cx.same_binding = same_binding;
    let conv: Vec<CRule> = rs.iter().map(|r| cx.convert_rule(r)).collect();
    if let Some((x, y)) = &explain {
        let find = |n: &str| {
            rs.iter()
                .position(|r| crate::rules::display_name(r) == n)
                .unwrap_or_else(|| panic!("no rule {n}"))
        };
        let (i, j) = (find(x), find(y));
        cx.explain = true;
        let o = classify(&mut cx, &conv[i], &conv[j], rank(&rs[i]) == rank(&rs[j]));
        eprintln!("class {} ({}), depth {}", o.class, o.detail, o.depth);
        if let Some((q, _)) = &o.smt {
            eprintln!("z3: {:?}", run_z3(std::slice::from_ref(q)));
        }
        for (label, qs) in &o.cases {
            let res = run_z3(qs);
            let open: Vec<usize> = (0..qs.len()).filter(|&k| res[k].0 != "unsat").collect();
            eprintln!(
                "case split {label}: {} cases need smt, {} not unsat",
                qs.len(),
                open.len()
            );
            for &k in open.iter().take(3) {
                eprintln!("  open case:\n{}", qs[k]);
            }
        }
        return;
    }
    // per rank: the index tree and its pairs
    let mut rows: Vec<(usize, usize, usize, String, PairOut)> = Vec::new(); // (rank, i, j, origin, out)
    let mut summary = String::new();
    let _ = writeln!(
        summary,
        "[{name}]\nrules = {}\nranks = {:?}\nmulti_rules = {}",
        rs.len(),
        prios,
        rs.iter().filter(|r| r.multi).count()
    );
    let mut co_bucket: BTreeSet<(usize, usize)> = BTreeSet::new();
    for (ri, _) in prios.iter().enumerate() {
        let idx: Vec<usize> = (0..rs.len()).filter(|&k| rank(&rs[k]) == ri).collect();
        let lhs: Vec<&crate::lower::L> = idx.iter().map(|&k| &rs[k].app.index).collect();
        let tree = crate::index::build(&lhs, &info);
        let mut sizes = Vec::new();
        let mut merges = 0;
        leaf_sizes(&tree, &mut sizes, &mut merges);
        let mut ps = Vec::new();
        index_pairs(&tree, &mut ps);
        let sq: usize = sizes.iter().map(|s| s * s).sum();
        let _ = writeln!(
            summary,
            "\n[{name}.rank{ri}]\npriority = {}\nrules = {}\nbuckets = {}\nlargest_bucket = {}\nsum_size_squared = {sq}\nmerge_nodes = {merges}\nindex_pairs_leaf = {}\nindex_pairs_merge = {}\nall_unordered_pairs = {}",
            prios[ri],
            idx.len(),
            sizes.len(),
            sizes.iter().max().unwrap_or(&0),
            ps.iter().filter(|p| p.2 == "leaf").count(),
            ps.iter().filter(|p| p.2 == "merge").count(),
            idx.len() * idx.len().saturating_sub(1) / 2
        );
        // design 1: the candidates of each rule when the index is reduced on its left-hand side
        let mut reduced: BTreeSet<(usize, usize)> = BTreeSet::new();
        let mut ordered = 0usize;
        for (x, l) in lhs.iter().enumerate() {
            let mut out = Vec::new();
            reach(&tree, l, &info, &mut out);
            assert!(out.contains(&x), "rule not in its own bucket");
            ordered += out.len();
            for y in out {
                if y != x {
                    reduced.insert((x.min(y), x.max(y)));
                }
            }
        }
        let _ = writeln!(
            summary,
            "reduced_candidates_ordered = {ordered}\nreduced_pairs = {}",
            reduced.len()
        );
        let ps: Vec<(usize, usize, &'static str)> = ps
            .into_iter()
            .map(|(x, y, o)| {
                (
                    x,
                    y,
                    if reduced.contains(&(x, y)) {
                        if o == "leaf" { "leaf" } else { "merge" }
                    } else {
                        "merge-unreached"
                    },
                )
            })
            .collect();
        for (x, y, origin) in ps {
            let (i, j) = (idx[x], idx[y]);
            co_bucket.insert((i.min(j), i.max(j)));
            let o = classify(&mut cx, &conv[i], &conv[j], true);
            rows.push((ri, i.min(j), i.max(j), origin.to_string(), o));
        }
        if all_pairs {
            // the same-rank pairs the index separates: they must all clash (a check of the index)
            for (a, &i) in idx.iter().enumerate() {
                for &j in &idx[a + 1..] {
                    if co_bucket.contains(&(i.min(j), i.max(j))) {
                        continue;
                    }
                    let o = classify(&mut cx, &conv[i], &conv[j], true);
                    rows.push((ri, i.min(j), i.max(j), "separated".into(), o));
                }
            }
        }
    }
    // design 2 with the `<k>` head as the key: per rank, the rules grouped by the first item of
    // `<k>` (its leaf sort and own constructor), and the rules whose head is a variable (wildcard)
    for (ri, _) in prios.iter().enumerate() {
        let idx: Vec<usize> = (0..rs.len()).filter(|&k| rank(&rs[k]) == ri).collect();
        let mut groups: BTreeMap<String, usize> = BTreeMap::new();
        let mut wild = 0usize;
        for &k in &idx {
            match k_head(&conv[k].lhs, &cx) {
                Some(h) => *groups.entry(h).or_default() += 1,
                None => wild += 1,
            }
        }
        let n = idx.len();
        let concrete: usize = groups.values().sum();
        let sq: usize = groups.values().map(|g| g * g).sum();
        // inversions: a concrete-head rule inverts its group and the wildcard relation; a
        // wildcard rule inverts everything
        let inv = sq + concrete * wild + wild * n;
        let _ = writeln!(
            summary,
            "\n[{name}.rank{ri}.khead]\ngroups = {}\nlargest_group = {}\nwildcard_rules = {wild}\nsum_group_squared = {sq}\ninversions_design2 = {inv}\ninversions_full = {}",
            groups.len(),
            groups.values().max().unwrap_or(&0),
            n * n
        );
    }
    // cross-rank pairs: separated by priority when they unify
    for i in 0..rs.len() {
        for j in i + 1..rs.len() {
            if rank(&rs[i]) == rank(&rs[j]) {
                continue;
            }
            let o = classify(&mut cx, &conv[i], &conv[j], false);
            rows.push((usize::MAX, i, j, "cross-rank".into(), o));
        }
    }
    // the SMT checks of the undecided pairs
    let pending: Vec<usize> = (0..rows.len())
        .filter(|&k| rows[k].4.smt.is_some())
        .collect();
    let queries: Vec<String> = pending
        .iter()
        .map(|&k| rows[k].4.smt.as_ref().unwrap().0.clone())
        .collect();
    if !queries.is_empty() {
        let res = run_z3(&queries);
        for (&k, (r, core)) in pending.iter().zip(res) {
            if r == "unsat" {
                let names = rows[k].4.smt.as_ref().unwrap().1.clone();
                let mut heads: BTreeSet<String> = BTreeSet::new();
                for c in core {
                    if let Some(n) = c.strip_prefix('q').and_then(|x| x.parse::<usize>().ok())
                        && let Some(h) = names.get(n)
                    {
                        heads.insert(h.clone());
                    }
                }
                let o = &mut rows[k].4;
                o.class = "exclusive".into();
                o.detail = format!("smt: {}", heads.into_iter().collect::<Vec<_>>().join(" & "));
            }
        }
    }
    // case splits of the pairs still open: exclusive if every open case is unsatisfiable
    let mut cq: Vec<String> = Vec::new();
    let mut owners: Vec<(usize, usize)> = Vec::new(); // (row, case set)
    for (k, row) in rows.iter().enumerate() {
        if row.4.class != "overlap" {
            continue;
        }
        for (ci, (_, qs)) in row.4.cases.iter().enumerate() {
            for q in qs {
                cq.push(q.clone());
                owners.push((k, ci));
            }
        }
    }
    if !cq.is_empty() {
        let res = run_z3(&cq);
        let mut sat: BTreeSet<(usize, usize)> = BTreeSet::new();
        for (o, (r, _)) in owners.iter().zip(&res) {
            if r != "unsat" {
                sat.insert(*o);
            }
        }
        for (k, row) in rows.iter_mut().enumerate() {
            if row.4.class != "overlap" {
                continue;
            }
            if let Some((ci, (label, _))) = row
                .4
                .cases
                .iter()
                .enumerate()
                .find(|(ci, _)| !sat.contains(&(k, *ci)))
            {
                let _ = ci;
                row.4.class = "exclusive".into();
                row.4.detail = format!("case split: {label}, open cases by smt");
            }
        }
    }
    // witnesses of the overlapping pairs (`--witnesses`)
    if want_witnesses {
        let ov: Vec<(usize, usize)> = rows
            .iter()
            .filter(|r| r.0 != usize::MAX && r.4.class == "overlap")
            .map(|r| (r.1, r.2))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let top = crate::rules::top_sort(def).unwrap_or_default();
        let ws = witnesses(def, &m, &rs, &ov, &top);
        let conv = crate::convert::Conv::new(&m, def);
        let mut wtxt = String::new();
        let mut found = 0;
        for ((i, j), w) in &ws {
            let (n1, n2) = (
                crate::rules::display_name(&rs[*i]),
                crate::rules::display_name(&rs[*j]),
            );
            match w {
                Ok(w) => {
                    found += 1;
                    let r = |p: &P| {
                        conv.value(p, &top)
                            .map(|l| l.render())
                            .unwrap_or_else(|e| format!("<{e}>"))
                    };
                    let _ = writeln!(
                        wtxt,
                        "== {n1} / {n2}: witness\nconfig: {}\nnext1: {}\nnext2: {}",
                        r(&w.config),
                        r(&w.next.0),
                        r(&w.next.1)
                    );
                }
                Err(e) => {
                    let _ = writeln!(wtxt, "== {n1} / {n2}: none: {e}");
                }
            }
        }
        std::fs::create_dir_all(&out_dir).unwrap();
        std::fs::write(out_dir.join(format!("{name}-witnesses.txt")), &wtxt).unwrap();
        eprintln!("witnesses: {found} of {} overlapping pairs", ws.len());
    }
    // outputs
    let mut tsv = String::from("rank\torigin\tclass\tdepth\tdetail\trule1\trule2\n");
    let mut counts: BTreeMap<(String, String, String), usize> = BTreeMap::new();
    let mut depth_hist: BTreeMap<(String, usize), usize> = BTreeMap::new();
    let mut details: BTreeMap<(String, String), usize> = BTreeMap::new();
    for (ri, i, j, origin, o) in &rows {
        let rk = if *ri == usize::MAX {
            "x".to_string()
        } else {
            ri.to_string()
        };
        let _ = writeln!(
            tsv,
            "{rk}\t{origin}\t{}\t{}\t{}\t{}\t{}",
            o.class,
            o.depth,
            o.detail,
            crate::rules::display_name(&rs[*i]),
            crate::rules::display_name(&rs[*j])
        );
        let grp = if *ri == usize::MAX {
            "cross_rank".to_string()
        } else {
            format!("rank{ri}")
        };
        let og = if origin == "separated" {
            "separated"
        } else if origin == "cross-rank" {
            "all"
        } else if origin == "merge-unreached" {
            "merge_unreached"
        } else {
            "index"
        };
        *counts
            .entry((grp.clone(), og.to_string(), o.class.clone()))
            .or_default() += 1;
        if o.class == "clash" && og == "index" {
            *depth_hist.entry((grp.clone(), o.depth)).or_default() += 1;
        }
        if og == "index" {
            let key = if o.class == "clash" {
                o.detail.split(':').next().unwrap_or("").to_string()
            } else {
                o.detail.clone()
            };
            *details
                .entry((format!("{grp}.{}", o.class), key))
                .or_default() += 1;
        }
    }
    let _ = writeln!(summary, "\n[{name}.counts]");
    for ((g, og, c), n) in &counts {
        let _ = writeln!(summary, "\"{g}.{og}.{c}\" = {n}");
    }
    let _ = writeln!(summary, "\n[{name}.clash_depth]");
    for ((g, d), n) in &depth_hist {
        let _ = writeln!(summary, "\"{g}.{d}\" = {n}");
    }
    let _ = writeln!(summary, "\n[{name}.how]");
    for ((g, d), n) in &details {
        let _ = writeln!(summary, "{:?} = {n}", format!("{g}: {d}"));
    }
    std::fs::create_dir_all(&out_dir).unwrap();
    std::fs::write(out_dir.join(format!("{name}-pairs.tsv")), tsv).unwrap();
    std::fs::write(out_dir.join(format!("{name}-summary.toml")), &summary).unwrap();
    print!("{summary}");
}

/// Every same-rank pair `(i, j)`, `i < j`, of `rs` classified as `run` does (unification, the
/// requires under the unifier, z3 for the conditions evaluation leaves, case splits), for the
/// determinism emitter (`det2`). Untrusted: the emitter only uses the classes to choose which
/// certificate to try on a goal, and the kernel checks every proof.
pub fn classify_same_rank(
    def: &Def,
    m: &Model,
    rs: &[Rule],
    rank: &dyn Fn(&Rule) -> usize,
    same_binding: bool,
) -> BTreeMap<(usize, usize), PairOut> {
    let raw_eqs = crate::funcs::equations_modulo_overloads(def, m);
    let mut cx = Cx::new(def, m, &raw_eqs);
    cx.same_binding = same_binding;
    let conv: Vec<CRule> = rs.iter().map(|r| cx.convert_rule(r)).collect();
    let mut rows: Vec<(usize, usize, PairOut)> = Vec::new();
    for i in 0..rs.len() {
        for j in i + 1..rs.len() {
            if rank(&rs[i]) != rank(&rs[j]) {
                continue;
            }
            let o = classify(&mut cx, &conv[i], &conv[j], true);
            rows.push((i, j, o));
        }
    }
    if std::env::var_os("K2LEAN_WITNESS_TRACE").is_some() {
        let nq: usize = rows
            .iter()
            .map(|r| r.2.cases.iter().map(|c| c.1.len()).sum::<usize>())
            .sum();
        let bytes: usize = rows
            .iter()
            .map(|r| {
                r.2.cases
                    .iter()
                    .map(|c| c.1.iter().map(|q| q.len()).sum::<usize>())
                    .sum::<usize>()
                    + r.2.smt.as_ref().map(|q| q.0.len()).unwrap_or(0)
            })
            .sum();
        eprintln!(
            "classify: {} rows, {nq} case queries, {bytes} query bytes",
            rows.len()
        );
    }
    let pending: Vec<usize> = (0..rows.len())
        .filter(|&k| rows[k].2.smt.is_some())
        .collect();
    let queries: Vec<String> = pending
        .iter()
        .map(|&k| rows[k].2.smt.as_ref().unwrap().0.clone())
        .collect();
    if !queries.is_empty() {
        let res = run_z3(&queries);
        for (&k, (r, core)) in pending.iter().zip(res) {
            if r == "unsat" {
                let names = rows[k].2.smt.as_ref().unwrap().1.clone();
                let mut heads: BTreeSet<String> = BTreeSet::new();
                for c in core {
                    if let Some(n) = c.strip_prefix('q').and_then(|x| x.parse::<usize>().ok())
                        && let Some(h) = names.get(n)
                    {
                        heads.insert(h.clone());
                    }
                }
                let o = &mut rows[k].2;
                o.class = "exclusive".into();
                o.detail = format!("smt: {}", heads.into_iter().collect::<Vec<_>>().join(" & "));
            }
        }
    }
    let mut cq: Vec<String> = Vec::new();
    let mut owners: Vec<(usize, usize)> = Vec::new();
    for (k, row) in rows.iter().enumerate() {
        if row.2.class != "overlap" {
            continue;
        }
        for (ci, (_, qs)) in row.2.cases.iter().enumerate() {
            for q in qs {
                cq.push(q.clone());
                owners.push((k, ci));
            }
        }
    }
    if !cq.is_empty() {
        let res = run_z3(&cq);
        let mut sat: BTreeSet<(usize, usize)> = BTreeSet::new();
        for (o, (r, _)) in owners.iter().zip(&res) {
            if r != "unsat" {
                sat.insert(*o);
            }
        }
        for (k, row) in rows.iter_mut().enumerate() {
            if row.2.class != "overlap" {
                continue;
            }
            if let Some((_, (label, _))) = row
                .2
                .cases
                .iter()
                .enumerate()
                .find(|(ci, _)| !sat.contains(&(k, *ci)))
            {
                row.2.class = "exclusive".into();
                row.2.detail = format!("case split: {label}, open cases by smt");
            }
        }
    }
    rows.into_iter().map(|(i, j, o)| ((i, j), o)).collect()
}

// ---------------------------------------------------------------- overlap witnesses

/// A configuration where both rules of a pair apply, with their two results: ground KORE
/// patterns of the top sort. Untrusted, like the classification: `det2` states that both rules
/// step from `config` to `next.0` and `next.1` and that these differ, and Lean checks it by
/// evaluation.
#[derive(Clone, Debug)]
pub struct Witness {
    pub config: P,
    pub next: (P, P),
}

/// Whether `t` is a ground value: constructors, literals and collection terms only.
fn is_ground(t: &T, cx: &Cx) -> bool {
    match t {
        T::Lit(..) => true,
        T::Ctor(_, a) => a.iter().all(|x| is_ground(x, cx)),
        T::Fn(f, a) => {
            matches!(
                cx.hook(f),
                Some(
                    "MAP.concat"
                        | "MAP.element"
                        | "MAP.unit"
                        | "SET.concat"
                        | "SET.element"
                        | "SET.unit"
                        | "LIST.concat"
                        | "LIST.element"
                        | "LIST.unit"
                )
            ) && a.iter().all(|x| is_ground(x, cx))
        }
        _ => false,
    }
}

fn t_size(t: &T) -> usize {
    match t {
        T::Ctor(_, a) | T::Fn(_, a) => 1 + a.iter().map(t_size).sum::<usize>(),
        _ => 1,
    }
}

impl<'a> Cx<'a> {
    /// A small ground value of each sort that has one: a builtin's zero, a collection's unit, the
    /// smallest constructor term, or the smallest value of a leaf.
    fn inhabitants(&self) -> BTreeMap<String, T> {
        use crate::model::{Builtin, Coll, Kind};
        let mut inh: BTreeMap<String, T> = BTreeMap::new();
        for (s, i) in &self.m.sorts {
            let t = match &i.kind {
                Kind::Builtin(Builtin::Int) => Some(T::Lit(s.clone(), "0".into())),
                Kind::Builtin(Builtin::Bool) => Some(T::Lit(s.clone(), "false".into())),
                Kind::Builtin(Builtin::String | Builtin::Bytes) | Kind::Token => {
                    Some(T::Lit(s.clone(), String::new()))
                }
                Kind::Coll(c) => {
                    let k = match c {
                        Coll::Map => "MAP.unit",
                        Coll::Set => "SET.unit",
                        Coll::List => "LIST.unit",
                    };
                    self.coll_sym
                        .get(&(k.to_string(), s.clone()))
                        .map(|u| T::Fn(u.clone(), vec![]))
                }
                Kind::Plain => None,
            };
            if let Some(t) = t {
                inh.insert(s.clone(), t);
            }
        }
        for _ in 0..64 {
            let mut changed = false;
            for (s, i) in &self.m.sorts {
                let mut best: Option<T> = inh.get(s).cloned();
                for c in &i.own {
                    let Some(ci) = self.m.ctors.get(c) else {
                        continue;
                    };
                    let args: Option<Vec<T>> =
                        ci.args.iter().map(|a| inh.get(a).cloned()).collect();
                    if let Some(args) = args {
                        let t = T::Ctor(c.clone(), args);
                        if best.as_ref().is_none_or(|b| t_size(&t) < t_size(b)) {
                            best = Some(t);
                        }
                    }
                }
                for l in &i.leaves {
                    if l == s {
                        continue;
                    }
                    if let Some(t) = inh.get(l)
                        && best.as_ref().is_none_or(|b| t_size(t) < t_size(b))
                    {
                        best = Some(t.clone());
                    }
                }
                if let Some(b) = best
                    && inh.get(s) != Some(&b)
                {
                    inh.insert(s.clone(), b);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        inh
    }

    /// The sort of a ground term, as the analysis reads it (its leaf).
    fn ground_sort(&self, t: &T) -> Option<String> {
        match t {
            T::Lit(s, _) => Some(s.clone()),
            T::Ctor(f, _) => self.m.ctors.get(f).map(|c| c.sort.clone()),
            T::Fn(f, _) => self.result_sort(f),
            _ => None,
        }
    }

    /// A ground term as a KORE pattern at sort `expected`, with the injections the analysis
    /// dropped put back.
    fn to_pattern(&self, t: &T, expected: &str) -> Result<P, String> {
        use crate::ir::S;
        let actual = self
            .ground_sort(t)
            .ok_or_else(|| format!("not ground: {}", shown(t, self)))?;
        let p = match t {
            T::Lit(s, v) => P::Dv(S::App(s.clone(), vec![]), v.clone()),
            T::Ctor(f, a) => {
                let ci = &self.m.ctors[f];
                let args = a
                    .iter()
                    .zip(&ci.args)
                    .map(|(x, s)| self.to_pattern(x, s))
                    .collect::<Result<Vec<_>, _>>()?;
                P::App(f.clone(), vec![], args)
            }
            T::Fn(f, a) => {
                let d = self
                    .def
                    .symbols
                    .get(f)
                    .ok_or_else(|| format!("unknown symbol {f}"))?;
                let args = a
                    .iter()
                    .zip(&d.args)
                    .map(|(x, s)| self.to_pattern(x, &sort_of(s)))
                    .collect::<Result<Vec<_>, _>>()?;
                P::App(f.clone(), vec![], args)
            }
            _ => return Err(format!("not ground: {}", shown(t, self))),
        };
        if actual == expected {
            Ok(p)
        } else {
            Ok(P::App(
                "inj".into(),
                vec![S::App(actual, vec![]), S::App(expected.to_string(), vec![])],
                vec![p],
            ))
        }
    }
}

/// The requires atoms under `un` that evaluation does not decide; `Err` when one is false or
/// undefined.
fn residual(
    cx: &mut Cx,
    un: &mut Un,
    req: &[(T, bool)],
    fuel: &mut usize,
) -> Result<Vec<(T, bool)>, String> {
    let mut out = Vec::new();
    for (e, bv) in req {
        let v = un.eval(cx, e, fuel);
        let mut parts = Vec::new();
        cx.push_atom(v, *bv, &mut parts);
        for (p, pb) in parts {
            if is_undef(&p) {
                return Err(format!("{} undefined", head_name(&un.resolve(e))));
            }
            if let Some(x) = Un::as_bool(&p) {
                if x != pb {
                    return Err(format!("{} false", head_name(&un.resolve(e))));
                }
                continue;
            }
            if matches!(p, T::Unk(_)) {
                return Err("an unmodelled requires".into());
            }
            out.push((p, pb));
        }
    }
    Ok(out)
}

/// Parse z3's `(get-value (…))` answer: one (name, value) per constant, values as K literal
/// text (integers with a sign, strings decoded).
fn parse_values(text: &str) -> Vec<(String, String)> {
    #[derive(Debug)]
    enum Sx {
        A(String),
        S(String),
        L(Vec<Sx>),
    }
    fn parse(cs: &[char], i: &mut usize) -> Option<Sx> {
        while *i < cs.len() && cs[*i].is_whitespace() {
            *i += 1;
        }
        if *i >= cs.len() {
            return None;
        }
        match cs[*i] {
            '(' => {
                *i += 1;
                let mut v = Vec::new();
                loop {
                    while *i < cs.len() && cs[*i].is_whitespace() {
                        *i += 1;
                    }
                    if *i >= cs.len() {
                        return None;
                    }
                    if cs[*i] == ')' {
                        *i += 1;
                        return Some(Sx::L(v));
                    }
                    v.push(parse(cs, i)?);
                }
            }
            '"' => {
                *i += 1;
                let mut s = String::new();
                while *i < cs.len() {
                    if cs[*i] == '"' {
                        if *i + 1 < cs.len() && cs[*i + 1] == '"' {
                            s.push('"');
                            *i += 2;
                            continue;
                        }
                        *i += 1;
                        break;
                    }
                    if cs[*i] == '\\' && *i + 2 < cs.len() && cs[*i + 1] == 'u' && cs[*i + 2] == '{'
                    {
                        let mut j = *i + 3;
                        let mut h = String::new();
                        while j < cs.len() && cs[j] != '}' {
                            h.push(cs[j]);
                            j += 1;
                        }
                        if let Some(c) = u32::from_str_radix(&h, 16).ok().and_then(char::from_u32) {
                            s.push(c);
                        }
                        *i = j + 1;
                        continue;
                    }
                    s.push(cs[*i]);
                    *i += 1;
                }
                Some(Sx::S(s))
            }
            _ => {
                let mut s = String::new();
                while *i < cs.len() && !cs[*i].is_whitespace() && cs[*i] != '(' && cs[*i] != ')' {
                    s.push(cs[*i]);
                    *i += 1;
                }
                Some(Sx::A(s))
            }
        }
    }
    fn value(x: &Sx) -> Option<String> {
        match x {
            Sx::A(a) => Some(a.clone()),
            Sx::S(s) => Some(s.clone()),
            Sx::L(v) => match v.as_slice() {
                [Sx::A(m), y] if m == "-" => value(y).map(|y| format!("-{y}")),
                _ => None,
            },
        }
    }
    let cs: Vec<char> = text.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while let Some(x) = parse(&cs, &mut i) {
        if let Sx::L(items) = x {
            for it in items {
                if let Sx::L(kv) = it
                    && let [Sx::A(k), v] = kv.as_slice()
                    && let Some(v) = value(v)
                {
                    out.push((k.clone(), v));
                }
            }
        }
    }
    out
}

/// A model of the residual atoms by z3: (the term each constant stands for, its SMT sort, its
/// value), or `None` when z3 finds none.
fn smt_model(cx: &Cx, un: &Un, atoms: &[(T, bool)]) -> Option<Vec<(T, &'static str, String)>> {
    let mut smt = Smt {
        decls: BTreeMap::new(),
        terms: BTreeMap::new(),
        len_atoms: true,
        cx,
        un,
    };
    let mut asserts = Vec::new();
    for (e, bv) in atoms {
        let s = smt.tr(e)?;
        asserts.push(format!("(assert (= {s} {bv}))"));
    }
    let mut q = String::from("(set-option :rlimit 500000)\n(set-option :timeout 20000)\n");
    for (n, s) in smt.decls.values() {
        let _ = writeln!(q, "(declare-const {n} {s})");
    }
    // a length is not negative
    for (n, t) in &smt.terms {
        if let T::Fn(f, _) = t
            && matches!(cx.hook(f), Some("BYTES.length" | "STRING.length"))
        {
            let _ = writeln!(q, "(assert (>= {n} 0))");
        }
    }
    for a in &asserts {
        q.push_str(a);
        q.push('\n');
    }
    let names: Vec<String> = smt.decls.values().map(|(n, _)| n.clone()).collect();
    q.push_str("(check-sat)\n");
    if !names.is_empty() {
        let _ = writeln!(q, "(get-value ({}))", names.join(" "));
    }
    let dir =
        std::env::temp_dir().join(format!("k2lean-witness-{}-{}", std::process::id(), q.len()));
    std::fs::create_dir_all(&dir).ok()?;
    let f = dir.join("q.smt2");
    std::fs::write(&f, &q).ok()?;
    let z3 = std::env::var("Z3").unwrap_or_else(|_| "z3".into());
    let out = std::process::Command::new(&z3).arg(&f).output().ok()?;
    let _ = std::fs::remove_dir_all(&dir);
    let text = String::from_utf8_lossy(&out.stdout).to_string();
    let mut lines = text.lines();
    if lines.next().map(str::trim) != Some("sat") {
        return None;
    }
    let rest: String = lines.collect::<Vec<_>>().join("\n");
    let vals: BTreeMap<String, String> = parse_values(&rest).into_iter().collect();
    let sorts: BTreeMap<&String, &'static str> = smt.decls.values().map(|(n, s)| (n, *s)).collect();
    let mut res = Vec::new();
    for (n, t) in &smt.terms {
        if let (Some(v), Some(s)) = (vals.get(n), sorts.get(n)) {
            res.push((t.clone(), *s, v.clone()));
        }
    }
    Some(res)
}

/// A value of a list-shaped sort with `n` elements: a sort with a constant and a constructor
/// with one argument of the sort itself (`.WordStack`, `_:_`), or a builtin list.
fn list_of(cx: &Cx, leaves: &BTreeSet<String>, n: usize, inh: &BTreeMap<String, T>) -> Option<T> {
    use crate::model::{Coll, Kind};
    for s in leaves {
        if s == "SortString" || s == "SortBytes" {
            let c = if s == "SortString" { "a" } else { "\u{0}" };
            return Some(T::Lit(s.clone(), c.repeat(n)));
        }
    }
    let one = |s: &String| -> Option<T> {
        let info = cx.m.sorts.get(s)?;
        if let Kind::Coll(Coll::List) = info.kind {
            let el = cx.coll_sym.get(&("LIST.element".to_string(), s.clone()))?;
            let unit = cx.coll_sym.get(&("LIST.unit".to_string(), s.clone()))?;
            let concat = cx.coll_sym.get(&("LIST.concat".to_string(), s.clone()))?;
            let e = inh.get(info.elems.first()?)?.clone();
            let mut t = T::Fn(unit.clone(), vec![]);
            for _ in 0..n {
                t = T::Fn(concat.clone(), vec![T::Fn(el.clone(), vec![e.clone()]), t]);
            }
            return Some(t);
        }
        let nil = info
            .own
            .iter()
            .find(|c| cx.m.ctors.get(*c).is_some_and(|ci| ci.args.is_empty()))?;
        let cons = info.own.iter().find(|c| {
            cx.m.ctors
                .get(*c)
                .is_some_and(|ci| ci.args.iter().filter(|a| *a == s).count() == 1)
        })?;
        let ci = &cx.m.ctors[cons];
        let mut t = T::Ctor(nil.clone(), vec![]);
        for _ in 0..n {
            let args: Option<Vec<T>> = ci
                .args
                .iter()
                .map(|a| {
                    if a == s {
                        Some(t.clone())
                    } else {
                        inh.get(a).cloned()
                    }
                })
                .collect();
            t = T::Ctor(cons.clone(), args?);
        }
        Some(t)
    };
    leaves.iter().find_map(one)
}

/// A value of one of the sorts `leaves` other than the smallest one and different from `other`:
/// a constructor term of a leaf with arguments of the smallest values.
fn second_value(
    cx: &Cx,
    leaves: &BTreeSet<String>,
    inh: &BTreeMap<String, T>,
    other: &T,
) -> Option<T> {
    let mut cands: Vec<T> = Vec::new();
    for s in leaves {
        let Some(info) = cx.m.sorts.get(s) else {
            continue;
        };
        for c in &info.own {
            let Some(ci) = cx.m.ctors.get(c) else {
                continue;
            };
            if let Some(args) = ci
                .args
                .iter()
                .map(|a| inh.get(a).cloned())
                .collect::<Option<Vec<T>>>()
            {
                cands.push(T::Ctor(c.clone(), args));
            }
        }
        if let Some(t) = WSearch::alt(s, 1) {
            cands.push(t);
        }
        if let Some(t) = list_of(cx, &[s.clone()].into_iter().collect(), 1, inh) {
            cands.push(t);
        }
    }
    cands.sort_by_key(t_size);
    cands
        .into_iter()
        .find(|t| t != other && !matches!(other, T::Var(_)) || t != other)
}

/// A collection of one of the sorts `leaves` with the one element (key) `x`.
fn singleton(cx: &Cx, leaves: &BTreeSet<String>, x: &T, inh: &BTreeMap<String, T>) -> Option<T> {
    use crate::model::{Coll, Kind};
    for s in leaves {
        let info = cx.m.sorts.get(s)?;
        let (k, n) = match info.kind {
            Kind::Coll(Coll::List) => ("LIST", 1),
            Kind::Coll(Coll::Set) => ("SET", 1),
            Kind::Coll(Coll::Map) => ("MAP", 2),
            _ => continue,
        };
        let el = cx.coll_sym.get(&(format!("{k}.element"), s.clone()))?;
        let mut args = vec![x.clone()];
        if n == 2 {
            args.push(inh.get(info.elems.get(1)?)?.clone());
        }
        return Some(T::Fn(el.clone(), args));
    }
    None
}

struct WSearch<'r> {
    a: &'r CRule,
    b: &'r CRule,
    inh: &'r BTreeMap<String, T>,
    budget: usize,
    last: String,
    /// The evaluation steps spent on this pair; the search stops at `WORK_LIMIT` (a
    /// deterministic bound, so that generation does not depend on the machine's speed; a pair
    /// it gives up on stays unwitnessed, which the generated module reports).
    work: usize,
}

const WORK_LIMIT: usize = 60_000_000;

impl WSearch<'_> {
    /// Bind every variable left to a small value of its sort, then evaluate both requires (both
    /// `true`) and both right-hand sides (ground and different).
    fn concrete(&mut self, cx: &mut Cx, un: &Un) -> Option<(T, T, T)> {
        for variant in 0..6 {
            if let Some(w) = self.concrete1(cx, un, variant) {
                return Some(w);
            }
            if std::env::var("K2LEAN_WITNESS_TRACE").is_ok_and(|v| v == "2") {
                eprintln!("  concrete {variant}: {:.300}", self.last);
            }
        }
        None
    }

    /// A small value of one of the sorts `l` that holds the integer `n`: `n` itself, or a
    /// constructor with an `Int` argument `n` and the smallest values elsewhere (`ty(n)`); else
    /// the smallest value.
    fn nth_value(&self, cx: &Cx, l: &BTreeSet<String>, n: usize) -> Option<T> {
        if l.contains("SortInt") {
            return Some(T::Lit("SortInt".into(), n.to_string()));
        }
        let mut best: Option<T> = None;
        for s in l {
            let Some(info) = cx.m.sorts.get(s) else {
                continue;
            };
            for c in &info.own {
                let Some(ci) = cx.m.ctors.get(c) else {
                    continue;
                };
                if !ci.args.iter().any(|a| a == "SortInt") {
                    continue;
                }
                let args: Option<Vec<T>> = ci
                    .args
                    .iter()
                    .map(|a| {
                        if a == "SortInt" {
                            Some(T::Lit(a.clone(), n.to_string()))
                        } else {
                            self.inh.get(a).cloned()
                        }
                    })
                    .collect();
                if let Some(args) = args {
                    let t = T::Ctor(c.clone(), args);
                    if best.as_ref().is_none_or(|b| t_size(&t) < t_size(b)) {
                        best = Some(t);
                    }
                }
            }
        }
        best.or_else(|| {
            l.iter()
                .filter_map(|s| self.inh.get(s).cloned())
                .min_by_key(t_size)
        })
    }

    /// The witness chooses the bindings of a map that a stuck lookup `M[K] orDefault D` reads
    /// (the map's rest is a variable, and none of its bindings has the key `K`): `K` is one of
    /// the keys bound so far, or the map gets a new binding `K |-> V`, with the variables of `K`
    /// given small values different from the other keys' and `V` a new variable of the sort of
    /// `D` (the values the lookup's caller expects), which the search then refines as any other
    /// variable. `None` when no lookup is stuck that way (or its key gets no value); otherwise
    /// the search's result.
    fn extend_map(
        &mut self,
        cx: &mut Cx,
        u: &Un,
        atoms: &[(T, bool)],
        depth: usize,
    ) -> Option<Option<(T, T, T)>> {
        use crate::model::{Coll, Kind};
        let (m, keys, k, d) = atoms
            .iter()
            .find_map(|(t, _)| stuck_lookup(cx, u, &u.resolve(t)))?;
        for k2 in &keys {
            let mut u1 = u.clone();
            if u1.unify(cx, &k, k2, 0).is_ok()
                && let Some(w) = self.search(cx, u1, depth + 1)
            {
                return Some(Some(w));
            }
            if self.budget == 0 {
                return Some(None);
            }
        }
        let ml = cx.var_leaves(m, &u.ext);
        let msort = ml
            .iter()
            .find(|s| {
                cx.m.sorts
                    .get(*s)
                    .is_some_and(|i| matches!(i.kind, Kind::Coll(Coll::Map)))
            })?
            .clone();
        let el_sym = cx
            .coll_sym
            .get(&("MAP.element".into(), msort.clone()))?
            .clone();
        let cat_sym = cx.coll_sym.get(&("MAP.concat".into(), msort))?.clone();
        let vl = match &d {
            T::Var(i) => cx.var_leaves(*i, &u.ext),
            t => cx.leaves_of_sort(&cx.ground_sort(t)?),
        };
        let mut kvs = Vec::new();
        vars_of(&k, &mut kvs);
        let mut chosen = None;
        'n: for n in keys.len()..keys.len() + 8 {
            let mut u1 = u.clone();
            for &v in &kvs {
                let l = cx.var_leaves(v, &u1.ext);
                let Some(t) = self.nth_value(cx, &l, n) else {
                    continue 'n;
                };
                if u1.unify(cx, &T::Var(v), &t, 0).is_err() {
                    continue 'n;
                }
            }
            let k1 = u1.resolve(&k);
            if is_ground(&k1, cx) && keys.iter().all(|k2| u1.resolve(k2) != k1) {
                chosen = Some((u1, k1));
                break;
            }
        }
        let Some((mut u1, k1)) = chosen else {
            // the other strategies may still find one
            self.last = format!("no key for a binding of {}", shown(&k, cx));
            return None;
        };
        let v = T::Var(u1.fresh(cx, vl));
        let rest = T::Var(u1.fresh(cx, ml));
        let map = T::Fn(cat_sym, vec![T::Fn(el_sym, vec![k1, v]), rest]);
        if u1.unify(cx, &T::Var(m), &map, 0).is_err() {
            self.last = "a binding does not fit the map".into();
            return Some(None);
        }
        Some(self.search(cx, u1, depth))
    }

    /// A small value of a builtin sort other than the zero, for the `variant`-th attempt.
    fn alt(sort: &str, variant: usize) -> Option<T> {
        let pool: &[&str] = match sort {
            "SortString" => &["", "0x00", "0", "00", "a", "0x"],
            "SortBytes" => &["", "\u{0}", "\u{1}", "", "\u{0}\u{0}", ""],
            "SortInt" => &["0", "1", "2", "0", "1", "7"],
            "SortBool" => &["false", "true", "false", "true", "false", "true"],
            _ => return None,
        };
        let v = pool[variant % pool.len()].to_string();
        Some(T::Lit(sort.to_string(), v))
    }

    fn concrete1(&mut self, cx: &mut Cx, un: &Un, variant: usize) -> Option<(T, T, T)> {
        let mut u = un.clone();
        let mut vs = Vec::new();
        vars_of(&u.resolve(&self.a.lhs), &mut vs);
        for (e, _) in self.a.req.iter().chain(&self.b.req) {
            vars_of(&u.resolve(e), &mut vs);
        }
        vars_of(&u.resolve(&self.a.rhs), &mut vs);
        vars_of(&u.resolve(&self.b.rhs), &mut vs);
        for v in vs {
            if !matches!(u.walk(&T::Var(v)), T::Var(_)) {
                continue;
            }
            let l = cx.var_leaves(v, &u.ext);
            let t = l
                .iter()
                .filter_map(|s| {
                    if variant > 0
                        && let Some(a) = Self::alt(s, variant)
                    {
                        return Some(a);
                    }
                    self.inh.get(s).cloned()
                })
                .min_by_key(t_size);
            let Some(t) = t else {
                self.last = format!("no value of the sort of {}", shown(&T::Var(v), cx));
                return None;
            };
            if u.unify(cx, &T::Var(v), &t, 0).is_err() {
                self.last = "a value does not fit".into();
                return None;
            }
        }
        let mut fuel = 5_000_000usize;
        self.work += 1_000_000;
        for (e, bv) in self.a.req.iter().chain(&self.b.req) {
            let v = u.eval(cx, e, &mut fuel);
            if Un::as_bool(&v) != Some(*bv) {
                self.last = format!(
                    "requires {} = {} at the witness",
                    head_name(&u.resolve(e)),
                    shown(&v, cx)
                );
                return None;
            }
        }
        let lhs = u.resolve(&self.a.lhs);
        let ra = u.eval(cx, &self.a.rhs, &mut fuel);
        let rb = u.eval(cx, &self.b.rhs, &mut fuel);
        let (ra, rb) = (u.resolve(&ra), u.resolve(&rb));
        for (what, t, src) in [
            ("left-hand side", &lhs, &self.a.lhs),
            ("first result", &ra, &self.a.rhs),
            ("second result", &rb, &self.b.rhs),
        ] {
            if !is_ground(t, cx) {
                let why = if is_undef(t) {
                    let mut f2 = 1_000_000usize;
                    let r = u.resolve(src);
                    first_undefined(cx, &mut u, &r, &mut f2)
                        .map(|c| format!("undefined at {:.300}", shown(&c, cx)))
                        .unwrap_or_else(|| "undefined".into())
                } else {
                    format!("{:.300}", shown(t, cx))
                };
                self.last = format!("{what} not ground: {why}");
                return None;
            }
        }
        if ra == rb {
            self.last = "equal results at the witness".into();
            return None;
        }
        Some((lhs, ra, rb))
    }

    fn search(&mut self, cx: &mut Cx, un: Un, depth: usize) -> Option<(T, T, T)> {
        if self.budget == 0 || self.work > WORK_LIMIT {
            self.last = format!("search budget exhausted ({})", self.last);
            self.budget = 0;
            return None;
        }
        self.budget -= 1;
        let mut u = un;
        let mut fuel = 5_000_000usize;
        let qa = residual(cx, &mut u, &self.a.req, &mut fuel);
        let qb = match &qa {
            Ok(_) => residual(cx, &mut u, &self.b.req, &mut fuel),
            Err(e) => Err(e.clone()),
        };
        self.work += 5_000_000 - fuel;
        let (qa, qb) = match (qa, qb) {
            (Ok(a), Ok(b)) => (a, b),
            (Err(e), _) | (_, Err(e)) => {
                if std::env::var("K2LEAN_WITNESS_TRACE").is_ok_and(|v| v == "2") {
                    eprintln!("  node depth {depth}: {e}");
                }
                self.last = e;
                return None;
            }
        };
        if std::env::var("K2LEAN_WITNESS_TRACE").is_ok_and(|v| v == "2") {
            eprintln!(
                "  node depth {depth}: {}",
                qa.iter()
                    .chain(&qb)
                    .map(|(t, b)| format!("{:.150} = {b}", shown(t, cx)))
                    .collect::<Vec<_>>()
                    .join("; ")
            );
        }
        if qa.is_empty() && qb.is_empty() {
            return self.concrete(cx, &u);
        }
        let atoms: Vec<(T, bool)> = qa.iter().chain(&qb).cloned().collect();
        // a lookup in a map whose bindings are not known yet: choose the binding
        if let Some(r) = self.extend_map(cx, &u, &atoms, depth) {
            return r;
        }
        // a variable that a stuck call destructs: try its constructors
        if depth < 6 {
            let mut cands = split_candidates(cx, &u, &qa, &qb);
            let stuck_args: BTreeSet<usize> = atoms
                .iter()
                .flat_map(|(t, _)| {
                    let mut v = Vec::new();
                    stuck_call_vars(cx, &u.resolve(t), &mut v);
                    v
                })
                .collect();
            // a variable of a list-shaped sort is not split (it is realized by its length)
            cands.retain(|v| {
                stuck_args.contains(v)
                    && list_of(cx, &cx.var_leaves(*v, &u.ext), 0, self.inh).is_none()
            });
            if let Some(&v) = cands.first() {
                let l = cx.var_leaves(v, &u.ext);
                let mut u0 = u.clone();
                for t in cases_of(cx, &mut u0, &l) {
                    let mut u1 = u0.clone();
                    if u1.unify(cx, &T::Var(v), &t, 0).is_ok()
                        && let Some(w) = self.search(cx, u1, depth + 1)
                    {
                        return Some(w);
                    }
                    if self.budget == 0 {
                        return None;
                    }
                }
                return None;
            }
        }
        // the rest by a model: variables from their values, abstracted calls by realizing their
        // arguments (a list of the length the call's value asks for)
        let Some(model) = smt_model(cx, &u, &atoms) else {
            self.last = format!(
                "no model of {}",
                atoms
                    .iter()
                    .map(|(t, b)| format!("{} = {b}", shown(t, cx)))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            return None;
        };
        if depth >= 8 {
            self.last = "search depth".into();
            return None;
        }
        if std::env::var("K2LEAN_WITNESS_TRACE").is_ok_and(|v| v == "2") {
            for (t, so, v) in &model {
                eprintln!(
                    "  model {:.120} : {so} = {:.80} ({} chars)",
                    shown(t, cx),
                    v,
                    v.chars().count()
                );
            }
        }
        for offset in [0i64, -1, 1, -2, 2] {
            let mut u1 = u.clone();
            let mut progress = false;
            for (t, sort, v) in &model {
                match u1.walk(t) {
                    T::Var(i) => {
                        let l = cx.var_leaves(i, &u1.ext);
                        let ks: Vec<&String> =
                            l.iter().filter(|x| smt_sort(x) == Some(*sort)).collect();
                        if let Some(k) = ks.first() {
                            let val = if *sort == "Bool" {
                                v.clone()
                            } else {
                                v.trim_start_matches('+').to_string()
                            };
                            if u1
                                .unify(cx, &T::Var(i), &T::Lit((*k).clone(), val), 0)
                                .is_ok()
                            {
                                progress = true;
                            }
                        }
                    }
                    T::Fn(f, xs) if f == "==K" && v == "true" => {
                        if u1.unify(cx, &xs[0], &xs[1], 0).is_ok() {
                            progress = true;
                        }
                    }
                    T::Fn(f, xs) if f == "==K" && v == "false" => {
                        // a variable side gets a second value of its sort, different from the
                        // other side
                        for (x, y) in [(&xs[0], &xs[1]), (&xs[1], &xs[0])] {
                            let x = match u1.walk(x) {
                                T::Ctor(k, a) if k == "kseq" && a.len() == 2 => u1.walk(&a[0]),
                                other => other,
                            };
                            if let T::Var(i) = x {
                                let l = cx.var_leaves(i, &u1.ext);
                                if let Some(t) = second_value(cx, &l, self.inh, &u1.resolve(y))
                                    && u1.unify(cx, &T::Var(i), &t, 0).is_ok()
                                {
                                    progress = true;
                                    break;
                                }
                            }
                        }
                    }
                    T::Fn(f, xs)
                        if v == "true"
                            && matches!(
                                cx.hook(&f),
                                Some("LIST.in" | "SET.in" | "MAP.in_keys")
                            ) =>
                    {
                        // a collection variable gets the one element
                        if let T::Var(i) = u1.walk(&xs[1]) {
                            let l = cx.var_leaves(i, &u1.ext);
                            if let Some(t) = singleton(cx, &l, &xs[0], self.inh)
                                && u1.unify(cx, &T::Var(i), &t, 0).is_ok()
                            {
                                progress = true;
                            }
                        }
                    }
                    T::Fn(_, xs) if *sort == "Int" => {
                        let Ok(n) = v.parse::<i64>() else { continue };
                        let n = n + offset;
                        if !(0..=100_000).contains(&n) {
                            continue;
                        }
                        for x in xs {
                            if let T::Var(i) = u1.walk(&x) {
                                let l = cx.var_leaves(i, &u1.ext);
                                if let Some(lt) = list_of(cx, &l, n as usize, self.inh)
                                    && u1.unify(cx, &T::Var(i), &lt, 0).is_ok()
                                {
                                    progress = true;
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            if !progress {
                self.last = format!(
                    "a model that names no variable: {}",
                    atoms
                        .iter()
                        .map(|(t, b)| format!("{} = {b}", shown(t, cx)))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                return None;
            }
            if let Some(w) = self.search(cx, u1, depth + 1) {
                return Some(w);
            }
        }
        None
    }
}

/// The innermost call of `t` whose arguments evaluate and whose value is undefined (a witness
/// search diagnostic).
fn first_undefined(cx: &mut Cx, u: &mut Un, t: &T, fuel: &mut usize) -> Option<T> {
    match t {
        T::Ctor(_, a) => a.iter().find_map(|x| first_undefined(cx, u, x, fuel)),
        T::Fn(f, a) => {
            if let Some(x) = a.iter().find_map(|x| first_undefined(cx, u, x, fuel)) {
                return Some(x);
            }
            let args: Vec<T> = a.iter().map(|x| u.eval(cx, x, fuel)).collect();
            let v = u.eval(cx, &T::Fn(f.clone(), args.clone()), fuel);
            is_undef(&v).then(|| T::Fn(f.clone(), args))
        }
        _ => None,
    }
}

/// The variables that are direct arguments of a call the evaluator could not reduce.
fn stuck_call_vars(cx: &Cx, t: &T, out: &mut Vec<usize>) {
    if let T::Fn(f, a) = t {
        if cx.raw_eqs.contains_key(f) {
            for x in a {
                if let T::Var(i) = x {
                    out.push(*i);
                }
            }
        }
        for x in a {
            stuck_call_vars(cx, x, out);
        }
    } else if let T::Ctor(_, a) = t {
        for x in a {
            stuck_call_vars(cx, x, out);
        }
    }
}

/// Whether `t` has a function call other than a collection's constructors, or an unmodelled
/// part.
fn has_call(cx: &Cx, t: &T) -> bool {
    match t {
        T::Unk(_) => true,
        T::Ctor(_, a) => a.iter().any(|x| has_call(cx, x)),
        T::Fn(f, a) => {
            !matches!(
                cx.hook(f).and_then(|h| h.split_once('.')),
                Some(("MAP" | "SET" | "LIST", "concat" | "element" | "unit"))
            ) || a.iter().any(|x| has_call(cx, x))
        }
        _ => false,
    }
}

/// The innermost lookup `M[K] orDefault D` of `t` that is stuck on the map's unknown rest: the
/// rest is one variable and no binding of the map has the key `K`. Returns (the rest variable,
/// the keys bound, `K`, `D`).
fn stuck_lookup(cx: &Cx, u: &Un, t: &T) -> Option<(usize, Vec<T>, T, T)> {
    match t {
        T::Fn(f, a) => {
            if let Some(r) = a.iter().find_map(|x| stuck_lookup(cx, u, x)) {
                return Some(r);
            }
            if cx.hook(f) != Some("MAP.lookupOrDefault") || a.len() != 3 {
                return None;
            }
            // a map variable, or bindings and a variable rest
            let (el, rest) = match u.walk(&a[0]) {
                T::Var(m) => (vec![], vec![T::Var(m)]),
                m => {
                    let (_, el, rest) = u.coll_items(cx, &m)?;
                    (el, rest)
                }
            };
            let [r] = rest.as_slice() else { return None };
            let T::Var(m) = u.walk(r) else { return None };
            let mut keys = Vec::new();
            for e in &el {
                let T::Fn(_, x) = e else { return None };
                keys.push(u.resolve(x.first()?));
            }
            // a key that is a call waits until the search has made it a value
            let k = u.resolve(&a[1]);
            (!keys.contains(&k) && !has_call(cx, &k)).then(|| (m, keys, k, u.resolve(&a[2])))
        }
        T::Ctor(_, a) => a.iter().find_map(|x| stuck_lookup(cx, u, x)),
        _ => None,
    }
}

/// For each pair `(i, j)` of `pairs`, a witness that both rules step from one configuration to
/// different results, or why none was found.
pub fn witnesses(
    def: &Def,
    m: &Model,
    rs: &[Rule],
    pairs: &[(usize, usize)],
    top: &str,
) -> BTreeMap<(usize, usize), Result<Witness, String>> {
    let raw_eqs = crate::funcs::equations_modulo_overloads(def, m);
    let mut cx = Cx::new(def, m, &raw_eqs);
    cx.use_memo = true;
    let conv: Vec<CRule> = rs.iter().map(|r| cx.convert_rule(r)).collect();
    let inh = cx.inhabitants();
    let mut out = BTreeMap::new();
    let only = std::env::var("K2LEAN_WITNESS_ONLY").ok();
    for &(i, j) in pairs {
        if let Some(o) = &only
            && !(rs[i].name.contains(o.as_str()) || rs[j].name.contains(o.as_str()))
        {
            continue;
        }
        let t0 = std::time::Instant::now();
        let (a, b) = (&conv[i], &conv[j]);
        let mut un = Un::new();
        let r = (|| -> Result<(), Clash> {
            for (x, y) in a.aliases.iter().chain(&b.aliases) {
                un.unify(&cx, x, y, 0)?;
            }
            un.unify(&cx, &a.lhs, &b.lhs, 0)?;
            un.finish(&cx)
        })();
        let res = if let Err(c) = r {
            Err(format!("the left-hand sides clash ({}: {})", c.kind, c.at))
        } else if !un.unknown.is_empty() {
            Err(format!(
                "unification undecided: {}",
                un.unknown.iter().cloned().collect::<Vec<_>>().join(", ")
            ))
        } else {
            let mut ws = WSearch {
                a,
                b,
                inh: &inh,
                budget: 4000,
                last: String::new(),
                work: 0,
            };
            match ws.search(&mut cx, un, 0) {
                Some((c, x, y)) => (|| {
                    Ok(Witness {
                        config: cx.to_pattern(&c, top)?,
                        next: (cx.to_pattern(&x, top)?, cx.to_pattern(&y, top)?),
                    })
                })(),
                None => Err(if ws.last.is_empty() {
                    "no witness found".into()
                } else {
                    ws.last
                }),
            }
        };
        if std::env::var_os("K2LEAN_WITNESS_TRACE").is_some() {
            eprintln!(
                "witness {} / {} ({:.1} s): {}",
                rs[i].name,
                rs[j].name,
                t0.elapsed().as_secs_f64(),
                match &res {
                    Ok(_) => "found".to_string(),
                    Err(e) => format!("{e:.200}"),
                }
            );
        }
        out.insert((i, j), res);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn z3_values_are_read_with_signs_and_string_escapes() {
        let v = parse_values("((a0 1024)\n (a1 (- 3))\n (a2 \"x\\u{0}\"\"y\")\n (a3 true))");
        assert_eq!(
            v,
            vec![
                ("a0".into(), "1024".into()),
                ("a1".into(), "-3".into()),
                ("a2".into(), "x\u{0}\"y".into()),
                ("a3".into(), "true".into()),
            ]
        );
    }

    #[test]
    fn whole_smt_symbols_are_counted() {
        assert_eq!(count_word("(str.len a1) (= a1 a10)", "a1"), 2);
        assert_eq!(count_word("a1_len", "a1"), 0);
    }
}
