//! `k2lean soundness`: the generated part of a type-soundness proof (`docs/design.md`, §3.3).
//!
//! Inputs: the compiled KORE of a semantics `A` and of a type checker `B` written as a second K
//! definition over the same syntax (each generated into its own library, and the translation of
//! programs `tr : A → B` written by `k2lean relate --roots`), the checker's typing functions
//! (`--typing typeOf,wt`: each takes a syntax term and a typing environment; one returns a type,
//! one a `Bool` that accepts a program), and the cells of `A`'s configuration whose typing is
//! written by hand (`--store-cell env`).
//!
//! It writes two modules around a hand-written one:
//! 1. `Typing.lean` (before the hand module): the typing functions at `A`'s terms; one inversion
//!    lemma per checker equation whose first argument is a constructor (the equation's
//!    `requires` and right-hand side, with the calls of typing functions bound by `match`);
//!    `plug`, the item that cooling makes of a value and a freezer, read off the cooling rules;
//!    the stack typing `kty` of `<k>`, where a freezer is typed by plugging a value of the hole's
//!    type (`dflt`, read off the checker's equations at value sorts); `WTc St G`, the typing of a
//!    configuration for a typing `St` of each hand-typed cell; `Final`, `init`; and
//!    `Progress.Case.r St`, the progress obligation at the left-hand side of each rule `r` that
//!    reads a hand-typed cell.
//! 2. `Soundness.lean` (after it): `preserved` by `k2l_preserve … hand NS.hand` (the hand module's
//!    `hand.r` for the rules that read or write a hand-typed cell), the progress skeleton (cases on
//!    the head of `<k>` read off the term universe and the rules, then a search among the `App`
//!    constructors; at the head of a store-reading rule `r`, the hand module's
//!    `hand.progress.r`), and `soundness`.
//!
//! The hand module (`--hand-module`, default `NS.Store`) defines the store typings
//! (`--store-typing envTy`) and proves those cases.
//!
//! With `<k>` in each element of a cell map of threads (IMP++), `WTc` types every thread,
//! `Final` holds when every thread is done or waits at a head that needs another thread, the
//! theorem's alternative is `Applies` (some rule of some rank applies, for the ranked `Step`),
//! and preservation reduces a rule that rewrites one thread to that thread's step
//! (`k2l_thread_case`); `docs/design.md`, §3.3, "A semantics with threads".

use crate::funcs::{self, Equation};
use crate::ir::{self, Def, P, S};
use crate::lower::{FnSig, L};
use crate::model::{Kind, Model};
use crate::names;
use crate::rules::{self, Rule};
use crate::terms;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

fn fail(msg: &str) -> ! {
    eprintln!("soundness: {msg}");
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

/// One generated library: its definition, term universe and functions (and, for the
/// semantics, its rules).
pub(crate) struct Lib {
    pub(crate) def: Def,
    pub(crate) m: Model,
    pub(crate) fns: BTreeMap<String, FnSig>,
    fn_text: String,
    pub(crate) rules: Vec<Rule>,
    /// The rules use the ranked `Step`: `∃ i, App i c` stands for `App c`.
    pub(crate) ranked: bool,
    pub(crate) ns: String,
}

pub(crate) fn load(kore: &str, ns: &str, want_rules: bool, extra: &[String]) -> Lib {
    let l = load_ranked(kore, ns, want_rules, extra);
    if l.ranked {
        fail("rules of several priorities are not supported");
    }
    l
}

/// As `load`, and a semantics whose `Step` is the ranked one (rules of several priorities, or a
/// rule with several matches, such as a free-key match of a cell map of threads): `App i c` says
/// that a rule of rank `i` applies, and "some rule applies" is `∃ i, App i c`.
pub(crate) fn load_ranked(kore: &str, ns: &str, want_rules: bool, extra: &[String]) -> Lib {
    let text = std::fs::read_to_string(kore).unwrap_or_else(|e| fail(&format!("{kore}: {e}")));
    let def = ir::load(&text).unwrap_or_else(|e| fail(&format!("{kore}: {e}")));
    let m = Model::build(&def).unwrap_or_else(|e| fail(&e));
    let mut roots = BTreeSet::new();
    for ax in &def.axioms {
        if let P::Rewrites(_, l, _) = &ax.pattern
            && rules::absent_sort(l, &m).is_none()
        {
            funcs::applied(&ax.pattern, &def, &mut roots);
        }
    }
    roots.extend(m.anywhere.iter().cloned());
    roots.extend(extra.iter().cloned());
    let fgen =
        funcs::generate(&def, &m, &roots).unwrap_or_else(|e| fail(&format!("functions: {e}")));
    let (rules, ranked) = if want_rules {
        let (rs, _, ranked) =
            rules::collect_ranked(&def, &m, &fgen.fns, &[]).unwrap_or_else(|e| fail(&e));
        (rs, ranked)
    } else {
        (vec![], false)
    };
    Lib {
        def,
        m,
        fns: fgen.fns,
        fn_text: fgen.lean,
        rules,
        ranked,
        ns: ns.to_string(),
    }
}

/// A typing function of the checker.
pub(crate) struct TFn {
    pub(crate) sym: String,
    /// The name of its function at `A`'s terms (the K name up to `(`).
    pub(crate) name: String,
    /// The Lean name in `B`'s library.
    pub(crate) lean_b: String,
    /// The syntax sort it types (the same sort name in `A` and `B`).
    pub(crate) sort: String,
    pub(crate) env: String,
    pub(crate) result: String,
    /// `Bool`-valued: it accepts or rejects (a statement leaves nothing on `<k>`).
    pub(crate) accepts: bool,
}

pub(crate) fn short_name(sym: &str) -> String {
    let l = names::demangle(sym);
    l.split('(').next().unwrap_or(&l).to_string()
}

fn var_name(kore_var: &str) -> String {
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

pub(crate) fn sname(s: &S) -> String {
    s.name()
        .map(|n| n.to_string())
        .unwrap_or_else(|| fail(&format!("parametric sort {s}")))
}

/// The Lean type of sort `s` of library `ns`.
pub(crate) fn ty(ns: &str, s: &str) -> String {
    format!("{ns}.{s}")
}

/// `inj{A, B}(t)` → `(A, B, t)`.
pub(crate) fn as_inj(p: &P) -> Option<(String, String, &P)> {
    match p {
        P::App(f, ps, args) if f == "inj" && ps.len() == 2 && args.len() == 1 => {
            Some((sname(&ps[0]), sname(&ps[1]), &args[0]))
        }
        _ => None,
    }
}

/// `kseq(inj{S, KItem}(t), dotk())` → `(S, t)`: a term as a K sequence of one item.
fn as_kitem(p: &P) -> Option<(String, &P)> {
    let P::App(f, _, args) = p else { return None };
    if names::demangle(f) != "kseq" || args.len() != 2 {
        return None;
    }
    match &args[1] {
        P::App(g, _, ga) if names::demangle(g) == "dotk" && ga.is_empty() => {}
        _ => return None,
    }
    let (s, _, t) = as_inj(&args[0])?;
    Some((s, t))
}

pub(crate) struct Ctx<'a> {
    pub(crate) a: &'a Lib,
    pub(crate) b: &'a Lib,
    pub(crate) tfs: &'a [TFn],
    pub(crate) ty_sort: String,
    /// The checker's equations as noninterference reads them (`inversions_merged`): a call of
    /// another of the checker's functions, `orBool` and `==K` are values too.
    pub(crate) ext: bool,
}

impl Ctx<'_> {
    pub(crate) fn tf(&self, sym: &str) -> Option<&TFn> {
        self.tfs.iter().find(|t| t.sym == sym)
    }

    /// The value of sort `s` (of `A`) built by constructor `c` of `A` applied to `args`.
    pub(crate) fn ctor_value(&self, c: &str, args: &[String], s: &str) -> String {
        let m = &self.a.m;
        let ci = &m.ctors[c];
        let mut own = format!("{}.{}", self.a.ns, m.ctor_path(c));
        for x in args {
            own.push(' ');
            own.push_str(x);
        }
        let own = if args.is_empty() {
            own
        } else {
            format!("({own})")
        };
        if ci.sort == s && m.sort(s).is_simple() {
            own
        } else {
            format!("({}.{} {own})", self.a.ns, m.leaf_ctor(s, &ci.sort))
        }
    }

    /// The value of sort `s` of `A` injected from a value `x` of leaf sort `l`.
    pub(crate) fn leaf_value(&self, l: &str, x: &str, s: &str) -> String {
        if l == s && self.a.m.sort(s).is_simple() {
            x.to_string()
        } else {
            format!("({}.{} {x})", self.a.ns, self.a.m.leaf_ctor(s, l))
        }
    }
}

/// The rendering of one checker equation into Lean at `A`'s terms: the calls of typing functions
/// are bound to names (`r`, `r_1`, …) in order of occurrence.
struct Ren<'c, 'a> {
    cx: &'c Ctx<'a>,
    /// The equation's environment variable, which the statement names `G`.
    env: String,
    calls: Vec<(String, String)>,
    taken: BTreeSet<String>,
    /// The variables of another equation of the same constructor, renamed to the first one's
    /// (`inversion_merged`).
    rename: BTreeMap<String, String>,
}

type R<T> = Result<T, String>;

impl Ren<'_, '_> {
    fn bind(&mut self, call: String) -> String {
        if let Some((_, n)) = self.calls.iter().find(|(c, _)| *c == call) {
            return n.clone();
        }
        let mut i = 0;
        let mut n = "r".to_string();
        while self.taken.contains(&n) {
            i += 1;
            n = format!("r_{i}");
        }
        self.taken.insert(n.clone());
        self.calls.push((call, n.clone()));
        n
    }

    /// A syntax term of `A` (the argument of a typing function), at sort `s`.
    fn syn(&mut self, p: &P, s: &str) -> R<String> {
        match p {
            P::Var(v, vs) => {
                let x = var_name(v);
                let x = self.rename.get(&x).cloned().unwrap_or(x);
                let vs = sname(vs);
                if vs == s {
                    Ok(x)
                } else {
                    Ok(self.cx.leaf_value(&vs, &x, s))
                }
            }
            _ if as_inj(p).is_some() => {
                let (from, to, t) = as_inj(p).unwrap();
                if to != s {
                    return Err(format!("injection into {to} at sort {s}"));
                }
                match t {
                    P::Var(v, _) => {
                        let x = var_name(v);
                        let x = self.rename.get(&x).cloned().unwrap_or(x);
                        Ok(self.cx.leaf_value(&from, &x, s))
                    }
                    P::App(c, _, args) if self.cx.a.m.ctors.contains_key(c) => {
                        let xs = self.syn_args(c, args)?;
                        Ok(self.cx.ctor_value(c, &xs, s))
                    }
                    _ => Err("an injection of a compound term".into()),
                }
            }
            P::App(c, _, args) if self.cx.a.m.ctors.contains_key(c) => {
                let xs = self.syn_args(c, args)?;
                Ok(self.cx.ctor_value(c, &xs, s))
            }
            _ => Err(format!("a syntax term {}", crate::lower::short_dbg(p))),
        }
    }

    fn syn_args(&mut self, c: &str, args: &[P]) -> R<Vec<String>> {
        let sorts = self.cx.a.m.ctors[c].args.clone();
        let mut out = Vec::new();
        for (a, s) in args.iter().zip(&sorts) {
            let t = self.syn(a, s)?;
            out.push(if t.contains(' ') && !t.starts_with('(') {
                format!("({t})")
            } else {
                t
            });
        }
        Ok(out)
    }

    /// A value of the checker's result sorts: a type, a Boolean, or a call of a typing function.
    fn val(&mut self, p: &P) -> R<String> {
        let b = self.cx.b;
        match p {
            P::Dv(s, v) if sname(s) == "SortBool" => Ok(v.clone()),
            P::App(f, _, args) => {
                if let Some(t) = self.cx.tf(f) {
                    let (sort, name) = (t.sort.clone(), t.name.clone());
                    match &args[1] {
                        P::Var(v, _)
                            if self
                                .rename
                                .get(&var_name(v))
                                .cloned()
                                .unwrap_or(var_name(v))
                                == self.env => {}
                        _ => return Err("a typing call in another environment".into()),
                    }
                    let x = self.syn(&args[0], &sort)?;
                    let x = if x.contains(' ') && !x.starts_with('(') {
                        format!("({x})")
                    } else {
                        x
                    };
                    return Ok(self.bind(format!("{name} G {x}")));
                }
                if let Some(ci) = b.m.ctors.get(f)
                    && ci.sort == self.cx.ty_sort
                    && args.is_empty()
                {
                    return Ok(format!("{}.{}", b.ns, b.m.ctor_path(f)));
                }
                match b.m.hooks.get(f).map(|s| s.as_str()) {
                    Some("BOOL.and") => Ok(format!(
                        "({} && {})",
                        self.val(&args[0])?,
                        self.val(&args[1])?
                    )),
                    Some("BOOL.or") if self.cx.ext => Ok(format!(
                        "({} || {})",
                        self.val(&args[0])?,
                        self.val(&args[1])?
                    )),
                    Some("KEQUAL.eq") if self.cx.ext => Ok(format!("(decide ({}))", self.prop(p)?)),
                    None if self.cx.ext && b.fns.contains_key(f) => {
                        // a call of another of the checker's functions on values, bound like a
                        // typing call (its own equations compute it)
                        let sig = &b.fns[f];
                        let mut xs = Vec::new();
                        for a in args {
                            xs.push(self.val(a)?);
                        }
                        let call = format!("{}.{} {}", b.ns, sig.lean, xs.join(" "));
                        if sig.partial {
                            Ok(self.bind(call))
                        } else {
                            Ok(format!("({call})"))
                        }
                    }
                    _ => Err(format!("the value {}", names::demangle(f))),
                }
            }
            _ => Err(format!("the value {}", crate::lower::short_dbg(p))),
        }
    }

    /// A `Bool`-valued condition as a decidable proposition (`==K` of two values of one sort is
    /// their equality).
    fn prop(&mut self, p: &P) -> R<String> {
        let b = self.cx.b;
        match p {
            P::Dv(s, v) if sname(s) == "SortBool" && v == "true" => Ok("True".into()),
            P::App(f, _, args) => match b.m.hooks.get(f).map(|s| s.as_str()) {
                Some("KEQUAL.eq") => {
                    let (Some((s1, x)), Some((s2, y))) = (as_kitem(&args[0]), as_kitem(&args[1]))
                    else {
                        return Err("`==K` of K sequences".into());
                    };
                    if s1 != s2 {
                        return Err("`==K` across sorts".into());
                    }
                    Ok(format!("{} = {}", self.val(x)?, self.val(y)?))
                }
                Some("BOOL.and") => Ok(format!(
                    "{} ∧ {}",
                    self.prop_arg(&args[0])?,
                    self.prop_arg(&args[1])?
                )),
                Some("BOOL.or") if self.cx.ext => Ok(format!(
                    "{} ∨ {}",
                    self.prop_arg(&args[0])?,
                    self.prop_arg(&args[1])?
                )),
                // `=/=K` of two values of one sort: they differ
                Some("KEQUAL.ne") => {
                    let (Some((s1, x)), Some((s2, y))) = (as_kitem(&args[0]), as_kitem(&args[1]))
                    else {
                        return Err("`=/=K` of K sequences".into());
                    };
                    if s1 != s2 {
                        return Err("`=/=K` across sorts".into());
                    }
                    Ok(format!("{} ≠ {}", self.val(x)?, self.val(y)?))
                }
                // a call of a `Bool`-valued typing function: the condition is that it is `true`
                // (undefined, the equation does not apply, as for the calls `==K` compares)
                None if self.cx.tf(f).is_some_and(|t| t.accepts) => {
                    Ok(format!("{} = true", self.val(p)?))
                }
                _ => Err(format!("the condition {}", names::demangle(f))),
            },
            _ => Err(format!("the condition {}", crate::lower::short_dbg(p))),
        }
    }

    fn prop_arg(&mut self, p: &P) -> R<String> {
        let s = self.prop(p)?;
        let compound = self.cx.ext && (s.contains(" ∨ ") || s.contains(" ∧ "));
        Ok(if s.contains(' ') && (!s.contains(" = ") || compound) {
            format!("({s})")
        } else {
            s
        })
    }
}

/// `match c₁, …, cₙ with | some r₁, …, some rₙ => yes | _, …, _ => no` over the calls.
fn match_calls(calls: &[(String, String)], yes: &str, no: &str, indent: &str) -> String {
    if calls.is_empty() {
        return yes.to_string();
    }
    let scr: Vec<&str> = calls.iter().map(|(c, _)| c.as_str()).collect();
    let pats: Vec<String> = calls.iter().map(|(_, n)| format!("some {n}")).collect();
    let wild: Vec<&str> = calls.iter().map(|_| "_").collect();
    format!(
        "(match {} with\n{indent}  | {} => {yes}\n{indent}  | {} => {no})",
        scr.join(", "),
        pats.join(", "),
        wild.join(", ")
    )
}

/// An inversion lemma: the statement's binders, left-hand side and right-hand side.
struct Inv {
    name: String,
    binders: Vec<(String, String)>,
    lhs: String,
    rhs: String,
}

/// The constructor head of an equation's first argument, for overlap checks: the constructor
/// symbol, or the leaf sort of an injected variable.
fn head_key(p: &P) -> Option<String> {
    match p {
        P::App(c, _, _) if c != "inj" => Some(c.clone()),
        _ => {
            let (from, _, t) = as_inj(p)?;
            match t {
                P::Var(..) => Some(format!("leaf:{from}")),
                P::App(c, _, _) => Some(c.clone()),
                _ => None,
            }
        }
    }
}

fn inversion(cx: &Ctx, t: &TFn, eqs: &[Equation], e: &Equation, merged: bool) -> R<Inv> {
    if e.owise || e.args.len() != 2 {
        return Err("not a constructor equation".into());
    }
    let P::Var(gv, _) = &e.args[1] else {
        return Err("the environment is a pattern".into());
    };
    let env = var_name(gv);
    let key = head_key(&e.args[0]).ok_or("the first argument is not a constructor")?;
    let others = eqs
        .iter()
        .filter(|o| !o.owise && o.index != e.index)
        .any(|o| head_key(&o.args[0]).is_none_or(|k| k == key));
    if others && !merged {
        return Err("another equation matches the same constructor".into());
    }
    // the first argument: a constructor of variables, or an injected variable
    let mut binders: Vec<(String, String)> = vec![("G".into(), "TEnv".into())];
    let mut ren = Ren {
        cx,
        env: env.clone(),
        calls: vec![],
        taken: BTreeSet::new(),
        rename: BTreeMap::new(),
    };
    let (name, lhs_arg) = {
        let (c, args, leaf) = match &e.args[0] {
            P::App(c, _, args) if c != "inj" => (c.clone(), args.clone(), None),
            p => {
                let (from, _, inner) = as_inj(p).unwrap();
                match inner {
                    P::Var(v, _) => (
                        String::new(),
                        vec![P::Var(v.clone(), S::App(from.clone(), vec![]))],
                        Some(from),
                    ),
                    P::App(c, _, args) => (c.clone(), args.clone(), None),
                    _ => return Err("a compound injection".into()),
                }
            }
        };
        let mut xs = Vec::new();
        for a in &args {
            let P::Var(v, s) = a else {
                return Err("a constructor argument is a pattern".into());
            };
            let x = var_name(v);
            if x == "G" || binders.iter().any(|(b, _)| *b == x) {
                return Err("a repeated variable".into());
            }
            let s = sname(s);
            let tyname = match &leaf {
                Some(l) => {
                    let st = cx.a.m.sort(l);
                    if st.is_simple() || !matches!(st.kind, Kind::Plain) {
                        ty(&cx.a.ns, l)
                    } else {
                        ty(&cx.a.ns, &cx.a.m.own_ty(l))
                    }
                }
                None => ty(&cx.a.ns, &s),
            };
            binders.push((x.clone(), tyname));
            xs.push(x);
        }
        match leaf {
            Some(l) => (
                format!("inj_{}", names::short_sort(&l)),
                cx.leaf_value(&l, &xs[0], &t.sort),
            ),
            None => {
                if !cx.a.m.ctors.contains_key(&c) {
                    return Err(format!(
                        "{} is not a constructor of the semantics",
                        names::demangle(&c)
                    ));
                }
                (
                    cx.a.m.ctors[&c].lean.clone(),
                    cx.ctor_value(&c, &xs, &t.sort),
                )
            }
        }
    };
    for (b, _) in &binders {
        ren.taken.insert(b.clone());
    }
    // what the equation gives when it does not apply: the `owise` equation's value, or undefined
    let fall = match eqs.iter().find(|o| o.owise) {
        Some(o) => {
            let mut r2 = Ren {
                cx,
                env: ren.env.clone(),
                calls: vec![],
                taken: BTreeSet::new(),
                rename: BTreeMap::new(),
            };
            let v = r2.val(&o.rhs)?;
            if !r2.calls.is_empty() {
                return Err("an `owise` value with calls".into());
            }
            format!("some {v}")
        }
        None => "none".into(),
    };
    // the condition, then the value
    let mut conds = Vec::new();
    for q in &e.requires {
        let qp = match q {
            P::Equals(_, _, l, r) => match (&**l, &**r) {
                (x, P::Dv(_, v)) | (P::Dv(_, v), x) if v == "true" => x.clone(),
                _ => return Err("a requires clause that is not `= true`".into()),
            },
            other => other.clone(),
        };
        // one clause needs no parentheses (the extended reading would add them to `a ∧ b`)
        conds.push(if e.requires.len() == 1 && !merged {
            ren.prop(&qp)?
        } else {
            ren.prop_arg(&qp)?
        });
    }
    let qcalls = std::mem::take(&mut ren.calls);
    let single_call = matches!(&e.rhs, P::App(f, _, _) if cx.tf(f).is_some());
    let v = ren.val(&e.rhs)?;
    let rcalls = std::mem::take(&mut ren.calls);
    let value = if single_call && rcalls.len() == 1 {
        rcalls[0].0.clone()
    } else {
        match_calls(&rcalls, &format!("some {v}"), "none", "        ")
    };
    let conds: Vec<String> = conds.into_iter().filter(|c| c != "True").collect();
    let guarded = if conds.is_empty() {
        value
    } else {
        format!("if {} then {value} else {fall}", conds.join(" ∧ "))
    };
    let rhs = match_calls(&qcalls, &guarded, &fall, "      ");
    let rhs = rhs
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .filter(|_| !qcalls.is_empty())
        .map(|s| s.to_string())
        .unwrap_or(rhs);
    let lhs = format!("{} G {lhs_arg}", t.name);
    Ok(Inv {
        name: format!("{}.{}", t.name, name),
        binders,
        lhs,
        rhs,
    })
}

/// The lemmas of the constructors of `t`'s sort that no equation of `t` matches: there `t` has
/// its `owise` value (a constant), or no value. None when an equation's first argument is a
/// variable (it could match any constructor) or the `owise` value is not a constant.
fn no_equation(cx: &Ctx, t: &TFn, eqs: &[Equation]) -> Vec<Inv> {
    let keys: Vec<Option<String>> = eqs
        .iter()
        .filter(|e| !e.owise)
        .map(|e| head_key(&e.args[0]))
        .collect();
    if keys.iter().any(|k| k.is_none()) {
        return vec![];
    }
    let fall = match eqs.iter().find(|o| o.owise) {
        Some(o) => match &o.rhs {
            P::Dv(s, v) if sname(s) == "SortBool" => format!("some {v}"),
            P::App(c, _, xs)
                if xs.is_empty() && cx.b.m.ctors.get(c).is_some_and(|ci| ci.sort == cx.ty_sort) =>
            {
                format!("some {}.{}", cx.b.ns, cx.b.m.ctor_path(c))
            }
            _ => return vec![],
        },
        None => "none".into(),
    };
    let mut out = Vec::new();
    for c in &cx.a.m.sort(&t.sort).own {
        if keys.iter().any(|k| k.as_deref() == Some(c.as_str())) {
            continue;
        }
        let ci = &cx.a.m.ctors[c];
        let mut binders: Vec<(String, String)> = vec![("G".into(), "TEnv".into())];
        let mut xs = Vec::new();
        for (i, s) in ci.args.iter().enumerate() {
            let x = format!("x{}", i + 1);
            binders.push((x.clone(), ty(&cx.a.ns, s)));
            xs.push(x);
        }
        out.push(Inv {
            name: format!("{}.{}", t.name, ci.lean),
            binders,
            lhs: format!("{} G {}", t.name, cx.ctor_value(c, &xs, &t.sort)),
            rhs: fall.clone(),
        });
    }
    // a leaf that no equation names, by the leaf or by one of its constructors (a token sort such
    // as `Id`), or, when equations name some of its constructors, each constructor they do not
    // (IMP++'s `Ids` inside `AExps`: K's overloads normalize `.AExps` to the empty `Ids`)
    for l in &cx.a.m.sort(&t.sort).leaves {
        if *l == t.sort
            || keys
                .iter()
                .any(|k| k.as_deref() == Some(format!("leaf:{l}").as_str()))
        {
            continue;
        }
        let own = &cx.a.m.sort(l).own;
        if keys
            .iter()
            .any(|k| k.as_ref().is_some_and(|k| own.contains(k)))
        {
            for c in own {
                if keys.iter().any(|k| k.as_deref() == Some(c.as_str())) {
                    continue;
                }
                let ci = &cx.a.m.ctors[c];
                let mut binders: Vec<(String, String)> = vec![("G".into(), "TEnv".into())];
                let mut xs = Vec::new();
                for (i, s) in ci.args.iter().enumerate() {
                    let x = format!("x{}", i + 1);
                    binders.push((x.clone(), ty(&cx.a.ns, s)));
                    xs.push(x);
                }
                let v = cx.ctor_value(c, &xs, l);
                out.push(Inv {
                    name: format!("{}.inj_{}.{}", t.name, names::short_sort(l), ci.lean),
                    binders,
                    lhs: format!(
                        "{} G {}",
                        t.name,
                        cx.leaf_value(l, &format!("({v})"), &t.sort)
                    ),
                    rhs: fall.clone(),
                });
            }
            continue;
        }
        out.push(Inv {
            name: format!("{}.inj_{}", t.name, names::short_sort(l)),
            binders: vec![("G".into(), "TEnv".into()), ("x".into(), ty(&cx.a.ns, l))],
            lhs: format!("{} G {}", t.name, cx.leaf_value(l, "x", &t.sort)),
            rhs: fall.clone(),
        });
    }
    out
}

/// The arguments of an equation's first argument and its environment, renamed to `names` (the
/// first equation's) and `G`: (constructor or leaf sort, argument variables, environment).
fn eq_head(e: &Equation) -> R<(String, Vec<String>, String)> {
    let P::Var(gv, _) = &e.args[1] else {
        return Err("the environment is a pattern".into());
    };
    let (c, args) = match &e.args[0] {
        P::App(c, _, args) if c != "inj" => (c.clone(), args.clone()),
        p => {
            let (from, _, inner) = as_inj(p).ok_or("the first argument is not a constructor")?;
            match inner {
                P::Var(..) => (format!("leaf:{from}"), vec![inner.clone()]),
                P::App(c, _, args) => (c.clone(), args.clone()),
                _ => return Err("a compound injection".into()),
            }
        }
    };
    let mut xs = Vec::new();
    for a in &args {
        let P::Var(v, _) = a else {
            return Err("a constructor argument is a pattern".into());
        };
        xs.push(v.clone());
    }
    Ok((c, xs, gv.clone()))
}

/// One inversion lemma for all the equations of a typing function at one constructor (in their
/// order, the `owise` equation last): the calls of the guards are matched once (every guard must
/// call the same functions on the same terms), then the guards are tried in order, each value
/// matching its own calls, and the `owise` value (or undefined) is what is left. A call of
/// another of the checker's functions, `orBool` and `==K` are values (`Ctx::ext`).
fn inversion_merged(cx: &Ctx, t: &TFn, eqs: &[Equation], group: &[&Equation]) -> R<Inv> {
    let e0 = group[0];
    let (_, xs0, _) = eq_head(e0)?;
    // the first equation's names, and each other equation's variables renamed to them
    let rename_of = |e: &Equation| -> R<BTreeMap<String, String>> {
        let (_, xs, gv) = eq_head(e)?;
        let mut r: BTreeMap<String, String> = xs
            .iter()
            .zip(&xs0)
            .map(|(x, y)| (var_name(x), var_name(y)))
            .collect();
        r.insert(var_name(&gv), "G".into());
        Ok(r)
    };
    let base = inversion(cx, t, eqs, e0, true)?;
    let mut taken: BTreeSet<String> = base.binders.iter().map(|(b, _)| b.clone()).collect();
    let mut gcalls: Vec<(String, String)> = Vec::new();
    let mut arms: Vec<(Option<String>, String)> = Vec::new();
    let mut call_sets: Vec<BTreeSet<String>> = Vec::new();
    for e in group {
        let rn = rename_of(e)?;
        let mut ren = Ren {
            cx,
            env: "G".into(),
            calls: gcalls.clone(),
            taken: taken.clone(),
            rename: rn,
        };
        let mut conds = Vec::new();
        for q in &e.requires {
            let qp = match q {
                P::Equals(_, _, l, r) => match (&**l, &**r) {
                    (x, P::Dv(_, v)) | (P::Dv(_, v), x) if v == "true" => x.clone(),
                    _ => return Err("a requires clause that is not `= true`".into()),
                },
                other => other.clone(),
            };
            conds.push(ren.prop_arg(&qp)?);
        }
        let mine: BTreeSet<String> = ren
            .calls
            .iter()
            .filter(|(_, n)| conds.iter().any(|q| mentions(q, n)))
            .map(|(c, _)| c.clone())
            .collect();
        if !e.requires.is_empty() {
            call_sets.push(mine);
        }
        gcalls = ren.calls.clone();
        taken = ren.taken.clone();
        // the value, with its own calls
        let mut rv = Ren {
            cx,
            env: "G".into(),
            calls: vec![],
            taken: taken.clone(),
            rename: rename_of(e)?,
        };
        let single_call = matches!(&e.rhs, P::App(f, _, _) if cx.tf(f).is_some());
        let v = rv.val(&e.rhs)?;
        taken = rv.taken.clone();
        let value = if single_call && rv.calls.len() == 1 {
            rv.calls[0].0.clone()
        } else {
            match_calls_nested(&rv.calls, &format!("some {v}"), "none", "        ")
        };
        let conds: Vec<String> = conds.into_iter().filter(|c| c != "True").collect();
        arms.push(((!conds.is_empty()).then(|| conds.join(" ∧ ")), value));
    }
    if call_sets.windows(2).any(|w| w[0] != w[1]) {
        return Err("the guards call different functions or terms".into());
    }
    let fall = match eqs.iter().find(|o| o.owise) {
        Some(o) => {
            let mut r2 = Ren {
                cx,
                env: "G".into(),
                calls: vec![],
                taken: BTreeSet::new(),
                rename: rename_of(o).unwrap_or_default(),
            };
            let v = r2.val(&o.rhs)?;
            if !r2.calls.is_empty() {
                return Err("an `owise` value with calls".into());
            }
            format!("some {v}")
        }
        None => "none".into(),
    };
    let mut body = fall.clone();
    for (cond, value) in arms.iter().rev() {
        body = match cond {
            Some(c) => format!("if {c} then {value} else {body}"),
            None => value.clone(),
        };
    }
    let rhs = match_calls_nested(&gcalls, &body, &fall, "      ");
    let rhs = rhs
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .filter(|_| !gcalls.is_empty())
        .map(|s| s.to_string())
        .unwrap_or(rhs);
    Ok(Inv {
        name: base.name,
        binders: base.binders,
        lhs: base.lhs,
        rhs,
    })
}

/// Whether `text` uses the name `n` as a whole word.
fn mentions(text: &str, n: &str) -> bool {
    text.split(|ch: char| !(ch.is_alphanumeric() || ch == '_' || ch == '\''))
        .any(|w| w == n)
}

/// `match_calls`, nesting a call that uses the name bound by an earlier one in an inner `match`.
fn match_calls_nested(calls: &[(String, String)], yes: &str, no: &str, indent: &str) -> String {
    let k = (1..calls.len())
        .find(|&i| calls[..i].iter().any(|(_, n)| mentions(&calls[i].0, n)))
        .unwrap_or(calls.len());
    if k == calls.len() {
        return match_calls(calls, yes, no, indent);
    }
    let inner = match_calls_nested(&calls[k..], yes, no, &format!("{indent}  "));
    match_calls(&calls[..k], &inner, no, indent)
}

/// The inversion lemmas of the checker's functions as noninterference states them
/// (`inversion_merged`, one per constructor), written into `t`; the functions and constructors
/// without one are returned as notes.
pub(crate) fn inversions_merged(
    cx: &Ctx,
    eqs: &BTreeMap<String, Vec<Equation>>,
    t: &mut String,
) -> (Vec<String>, Vec<String>) {
    let mut names_out = Vec::new();
    let mut skipped = Vec::new();
    for f in cx.tfs {
        let Some(es) = eqs.get(&f.sym) else { continue };
        let mut groups: Vec<(String, Vec<&Equation>)> = Vec::new();
        for e in es.iter().filter(|e| !e.owise) {
            let key = head_key(&e.args[0]).unwrap_or_default();
            match groups.iter_mut().find(|(k, _)| *k == key) {
                Some((_, g)) => g.push(e),
                None => groups.push((key, vec![e])),
            }
        }
        for (key, g) in &groups {
            match inversion_merged(cx, f, es, g) {
                Ok(inv) => {
                    let bs: Vec<String> = inv
                        .binders
                        .iter()
                        .map(|(x, ty)| format!("({x} : {ty})"))
                        .collect();
                    writeln!(
                        t,
                        "theorem {} {} :\n    {} =\n      {} := by k2l_ty_inv",
                        inv.name,
                        bs.join(" "),
                        inv.lhs,
                        inv.rhs
                    )
                    .unwrap();
                    names_out.push(inv.name);
                }
                Err(why) => skipped.push(format!(
                    "{} at {}: {why}",
                    f.name,
                    names::demangle(key.trim_start_matches("leaf:"))
                )),
            }
        }
    }
    (names_out, skipped)
}

/// The literal a value sort's placeholder is built from.
pub(crate) fn literal(m: &Model, s: &str) -> Option<&'static str> {
    match &m.sort(s).kind {
        Kind::Builtin(crate::model::Builtin::Int) => Some("0"),
        Kind::Builtin(crate::model::Builtin::Bool) => Some("true"),
        Kind::Builtin(crate::model::Builtin::String) => Some("\"\""),
        _ => None,
    }
}

/// A rule's left-hand side, as the cells of the top cell.
fn cells_of(l: &L) -> Option<&[L]> {
    match l {
        L::App(_, args) => Some(args),
        _ => None,
    }
}

fn head(l: &L) -> &str {
    match l {
        L::App(h, _) => h,
        L::Var(v) => v,
        L::Raw(r) => r,
        L::Typed(..) => "",
    }
}

fn args(l: &L) -> &[L] {
    match l {
        L::App(_, a) => a,
        _ => &[],
    }
}

/// `proj_KItem_S y = some X` → `(S, y, X)`.
fn proj_hyp(h: &str) -> Option<(String, String, String)> {
    let rest = h.strip_prefix("proj_KItem_")?;
    let (s, rest) = rest.split_once(' ')?;
    let (y, x) = rest.split_once(" = some ")?;
    let ok = |t: &str| !t.is_empty() && t.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    (ok(s) && ok(y) && ok(x)).then(|| (s.to_string(), y.to_string(), x.to_string()))
}

/// A cell of the top cell: its sort, its constructor (qualified), its label and the sort of its
/// content.
pub(crate) struct Cell {
    pub(crate) sort: String,
    pub(crate) ctor: String,
    pub(crate) label: String,
    pub(crate) content: String,
}

/// The top cell of a library: its sort, its one constructor, its cells, and the position of the
/// cell holding the K sequence.
pub(crate) struct TopCells {
    pub(crate) top: String,
    pub(crate) top_ctor: String,
    pub(crate) cells: Vec<Cell>,
    pub(crate) kpos: usize,
}

pub(crate) fn top_cells(a: &Lib) -> TopCells {
    let na = &a.ns;
    let top = rules::top_sort(&a.def).unwrap_or_else(|e| fail(&e));
    let top_info = a.m.sort(&top);
    let [top_ctor] = top_info.own.as_slice() else {
        fail("the top cell is expected to have one constructor")
    };
    let cells: Vec<Cell> = a.m.ctors[top_ctor]
        .args
        .iter()
        .map(|c| {
            let info = a.m.sort(c);
            let [cc] = info.own.as_slice() else {
                fail(&format!("the cell {c} is expected to have one constructor"))
            };
            let ci = &a.m.ctors[cc];
            let label = ci
                .klabel
                .trim_start_matches('<')
                .trim_end_matches('>')
                .to_string();
            Cell {
                sort: c.clone(),
                ctor: format!("{na}.{}", a.m.ctor_path(cc)),
                label,
                content: ci.args.first().cloned().unwrap_or_default(),
            }
        })
        .collect();
    let kpos = cells
        .iter()
        .position(|c| c.content == "SortK")
        .unwrap_or_else(|| fail("no cell holds the K sequence"));
    TopCells {
        top: top.clone(),
        top_ctor: top_ctor.clone(),
        cells,
        kpos,
    }
}

/// The cooling rule of each freezer, and the one sort of their holes.
pub(crate) fn coolings(a: &Lib, kpos: usize) -> (BTreeMap<String, Cool>, String) {
    let mut cools: BTreeMap<String, Cool> = BTreeMap::new();
    for r in &a.rules {
        if let Some(c) = cooling(r, kpos) {
            if cools.contains_key(&c.frz) {
                fail(&format!("two cooling rules for {}", c.frz));
            }
            cools.insert(c.frz.clone(), c);
        }
    }
    let hole_sorts: BTreeSet<String> = cools.values().map(|c| c.hole_sort.clone()).collect();
    let hole_sort = match hole_sorts.iter().collect::<Vec<_>>().as_slice() {
        [h] => (*h).clone(),
        [] => fail("no cooling rules"),
        _ => fail("holes of several sorts are not supported"),
    };
    (cools, hole_sort)
}

/// `plug`, the item that cooling makes of a value and a freezer (one case per cooling rule),
/// written into `t`; the sorts its cases project to.
pub(crate) fn plug_def(
    a: &Lib,
    cools: &BTreeMap<String, Cool>,
    hole_sort: &str,
    t: &mut String,
) -> BTreeSet<String> {
    let na = &a.ns;
    let kitem_own = ty(na, &a.m.own_ty("SortKItem"));
    writeln!(
        t,
        "\nopen {na} in\n/-- The item that cooling makes of `e ~> f`: each case is the right-hand side of `f`'s cooling\nrule, with the hole `e`. -/\ndef plug : {kitem_own} → {} → Option {}",
        ty(na, hole_sort),
        ty(na, "SortKItem")
    )
    .unwrap();
    let mut projs: BTreeSet<String> = BTreeSet::new();
    for c in cools.values() {
        let mut body = format!("some {}", c.item);
        for (s, y, x) in c.binds.iter().rev() {
            projs.insert(s.clone());
            body = format!("(proj_KItem_{s} {y}).bind fun {x} => {body}");
        }
        let pats = if c.pats.is_empty() {
            String::new()
        } else {
            format!(" {}", c.pats.join(" "))
        };
        writeln!(t, "  | {}{pats}, {} => {body}", c.frz, c.hole).unwrap();
    }
    t.push_str("  | _, _ => none\n");
    projs
}

/// `plug` when the holes have several sorts: the value comes as a `KItem` and each case projects
/// it to its hole's sort, so a value of another sort plugs into nothing (`none`).
fn plug_def_kitem(a: &Lib, cools: &BTreeMap<String, Cool>, t: &mut String) -> BTreeSet<String> {
    let na = &a.ns;
    let kitem_own = ty(na, &a.m.own_ty("SortKItem"));
    let kitem_t = ty(na, "SortKItem");
    writeln!(
        t,
        "\nopen {na} in\n/-- The item that cooling makes of `v ~> f`: each case is the right-hand side of `f`'s cooling\nrule, with the hole the value `v` projected to the hole's sort. -/\ndef plug : {kitem_own} → {kitem_t} → Option {kitem_t}"
    )
    .unwrap();
    let mut projs: BTreeSet<String> = BTreeSet::new();
    for c in cools.values() {
        let mut body = format!("some {}", c.item);
        for (s, y, x) in c.binds.iter().rev() {
            projs.insert(s.clone());
            body = format!("(proj_KItem_{s} {y}).bind fun {x} => {body}");
        }
        let hs = c.hole_sort.trim_start_matches("Sort");
        projs.insert(hs.to_string());
        body = format!("(proj_KItem_{hs} v).bind fun {} => {body}", c.hole);
        let pats = if c.pats.is_empty() {
            String::new()
        } else {
            format!(" {}", c.pats.join(" "))
        };
        writeln!(t, "  | {}{pats}, v => {body}", c.frz).unwrap();
    }
    t.push_str("  | _, _ => none\n");
    projs
}

/// A rule seen from one `<k>` cell inside a cell collection (a thread of a cell map): the
/// contents of that cell on the two sides, lowered on their own with the content as the matched
/// value, when the rule rewrites that cell only.
struct KView {
    index: L,
    rhs: L,
    hyps: Vec<(String, String)>,
    binders: Vec<(String, String)>,
}

/// The contents of the cells `ksym` in `p`.
fn k_contents<'p>(p: &'p P, ksym: &str, out: &mut Vec<&'p P>) {
    match p {
        P::App(f, _, xs) if f == ksym => out.extend(xs.first()),
        P::App(_, _, xs) | P::And(_, xs) | P::Or(_, xs) => {
            xs.iter().for_each(|x| k_contents(x, ksym, out))
        }
        _ => {}
    }
}

/// `p` with the content of every cell `ksym` left out.
fn blank_k(p: &P, ksym: &str) -> P {
    match p {
        P::App(f, s, _) if f == ksym => P::App(f.clone(), s.clone(), vec![]),
        P::App(f, s, xs) => P::App(
            f.clone(),
            s.clone(),
            xs.iter().map(|x| blank_k(x, ksym)).collect(),
        ),
        P::And(s, xs) => P::And(s.clone(), xs.iter().map(|x| blank_k(x, ksym)).collect()),
        other => other.clone(),
    }
}

/// The view of rule `r` from its one `<k>` cell (`ksym`), when the rule matches one such cell,
/// writes one, and changes nothing else; the side condition must read only that cell.
fn k_view(a: &Lib, r: &Rule, ksym: &str) -> Option<KView> {
    let (lhs, cond, rhs) = &r.kore;
    let (mut lk, mut rk) = (Vec::new(), Vec::new());
    k_contents(lhs, ksym, &mut lk);
    k_contents(rhs, ksym, &mut rk);
    let ([l], [rr]) = (lk.as_slice(), rk.as_slice()) else {
        return None;
    };
    if blank_k(lhs, ksym) != blank_k(rhs, ksym) {
        return None;
    }
    let mut lw = crate::lower::Lower::new(&a.m, &a.fns, &[]);
    lw.param("k", "SortK");
    lw.pat(l, "k", "SortK", true).ok()?;
    lw.finish_lhs().ok()?;
    lw.cond(cond).ok()?;
    let rhs_l = lw.expr(rr, "SortK").ok()?;
    let rel = crate::render::relation(&lw.steps, "k", &lw.ty, &[]);
    Some(KView {
        rhs: rhs_l.subst(&rel.subst),
        index: rel.index,
        hyps: rel.hyps,
        binders: rel.binders,
    })
}

/// The cooling rule of each freezer, read off the rules' views from `<k>` inside a cell
/// collection, and the sorts of their holes.
fn coolings_in(a: &Lib, ksym: &str) -> (BTreeMap<String, Cool>, BTreeSet<String>) {
    let mut cools: BTreeMap<String, Cool> = BTreeMap::new();
    for r in &a.rules {
        let Some(v) = k_view(a, r, ksym) else {
            continue;
        };
        if let Some(c) = cooling_k(&v.index, &v.rhs, &v.hyps, &v.binders, &r.name) {
            if cools.contains_key(&c.frz) {
                fail(&format!("two cooling rules for {}", c.frz));
            }
            cools.insert(c.frz.clone(), c);
        }
    }
    if cools.is_empty() {
        fail("no cooling rules");
    }
    let holes = cools.values().map(|c| c.hole_sort.clone()).collect();
    (cools, holes)
}

/// The heads at which a thread may wait: the `<k>` contents, as terms with their variables
/// (binders), of the threads that a rule matching two elements of the cell collection rewrites
/// (`join`, which reads another thread's `<k>`). Such a rule needs another thread's state, so a
/// thread at its head has not terminated, and need not step until the other thread gets there.
fn wait_heads(a: &Lib, ksym: &str) -> Vec<(Vec<(String, String)>, String)> {
    let mut out: Vec<(Vec<(String, String)>, String)> = Vec::new();
    for r in &a.rules {
        let (lhs, _, _) = &r.kore;
        let mut lk = Vec::new();
        k_contents(lhs, ksym, &mut lk);
        if lk.len() < 2 {
            continue;
        }
        for l in lk {
            let mut lw = crate::lower::Lower::new(&a.m, &a.fns, &[]);
            lw.param("k", "SortK");
            if lw.pat(l, "k", "SortK", true).is_err() || lw.finish_lhs().is_err() {
                fail(&format!(
                    "rule {}: the `<k>` of a thread it matches is not a pattern of `<k>` alone",
                    r.name
                ));
            }
            let rel = crate::render::relation(&lw.steps, "k", &lw.ty, &[]);
            // the other thread's `<k>` (`.K` for `join`) is what the waiting one needs
            if !head(&rel.index).ends_with("kseq") {
                continue;
            }
            if !rel.hyps.is_empty() {
                fail(&format!(
                    "rule {}: the head of a thread that may wait has side conditions",
                    r.name
                ));
            }
            let bs: Vec<(String, String)> = rel
                .binders
                .iter()
                .filter(|(b, _)| b != "k")
                .cloned()
                .collect();
            let pat = rel.index.render();
            if !out.iter().any(|(_, p)| *p == pat) {
                out.push((bs, pat));
            }
        }
    }
    out
}

/// `<k>` inside a cell map of threads (IMP++'s `<threads>`, whose `<thread>` cells are keyed by
/// their `<id>`): the path from the top cell to it, read as Lean patterns and terms.
struct Thr {
    /// The symbol of the `<k>` cell.
    ksym: String,
    /// The Lean types of the cell map, its keys and its elements.
    coll_t: String,
    key_t: String,
    elem_t: String,
    /// The pattern of the top cell that binds `m` to the cell map, the element's pattern that
    /// binds `k` to the content of `<k>`, and the one that binds `x` to the key cell.
    elem_key_pat: String,
    /// One projection per cell level, from the top cell down to the cell map and from an element
    /// down to the content of `<k>`: Lean definitions, their names, and the two compositions.
    /// Each reduces as soon as its argument is a constructor application, so on a rule that does
    /// not rewrite a cell (a cell variable on both sides) both sides read the same variable.
    proj_defs: String,
    proj_names: Vec<String>,
    coll_chain: String,
    k_chain: String,
    /// `k2l_cases` patterns that take a configuration apart down to the contents of its cells
    /// (the cell map is `m`), and an element (the content of `<k>` is `k`).
    top_destr: String,
    elem_destr: String,
    /// The initial configuration of the program item: one thread, keyed by `i`, whose `<k>`
    /// holds the program, every other cell a parameter; its parameters.
    init_term: String,
    init_params: Vec<(String, String)>,
}

/// The one constructor of a cell sort, when `s` is one.
fn cell_of<'m>(m: &'m Model, s: &str) -> Option<&'m crate::model::CtorInfo> {
    let info = m.sorts.get(s)?;
    let [c] = info.own.as_slice() else {
        return None;
    };
    let ci = m.ctors.get(c)?;
    (ci.klabel.starts_with('<') && ci.klabel.ends_with('>')).then_some(ci)
}

/// `(f a…)` with `x` at argument `at` and `_` elsewhere.
fn pat_at(f: &str, arity: usize, at: usize, x: &str) -> String {
    let xs: Vec<&str> = (0..arity).map(|j| if j == at { x } else { "_" }).collect();
    format!("({f} {})", xs.join(" "))
}

/// The `k2l_cases` pattern of a value of sort `s` taken apart down to the contents of its cells:
/// `name(s)` names a content (or a value of a sort that is not a cell).
fn destr(m: &Model, s: &str, name: &mut dyn FnMut(&str) -> String) -> String {
    match cell_of(m, s) {
        Some(ci) => {
            let xs: Vec<String> = ci.args.iter().map(|x| destr(m, x, name)).collect();
            format!("⟨{}⟩", xs.join(", "))
        }
        None => name(s),
    }
}

/// `<k>` inside one cell map (`None` when `<k>` is a cell of the top cell, the shape `top_cells`
/// reads); the program item `pitem` for the initial configuration.
fn thr_of(a: &Lib, top: &str, pitem: &str) -> Option<Thr> {
    let na = &a.ns;
    let path = crate::invariants::find_cell(&a.m, top, "k").unwrap_or_else(|e| fail(&e));
    let (coll, inner) = match path.colls.as_slice() {
        [] => return None,
        [c] => c,
        _ => fail("`<k>` inside nested cell collections is not supported"),
    };
    if !matches!(coll.kind, crate::model::Coll::Map) || coll.elems.len() != 2 {
        fail("`<k>` inside a cell collection other than a cell map is not supported");
    }
    let Some(first) = inner.first() else {
        fail("`<k>` is the element of a cell map")
    };
    let elem = cell_of(&a.m, &first.sort).unwrap_or_else(|| fail("a cell map of non-cells"));
    let key_pos = elem
        .args
        .iter()
        .position(|s| *s == coll.elems[0])
        .unwrap_or_else(|| fail("the key of the cell map is not a cell of its element"));
    let q = |lean: &str| format!("{na}.{lean}");
    let elem_key_pat = pat_at(&q(&first.lean), first.arity, key_pos, "x");
    // the projections, one per level
    let mut proj_defs = String::new();
    let mut proj_names = Vec::new();
    let mut proj = |name: String, from: &str, to: &str, pat: String, doc: String| -> String {
        writeln!(
            proj_defs,
            "/-- {doc} -/\ndef {name} : {} → {}\n  | {pat} => x",
            ty(na, from),
            ty(na, to)
        )
        .unwrap();
        proj_names.push(name.clone());
        name
    };
    let mut coll_chain = "c".to_string();
    for lv in &path.levels {
        let n = proj(
            format!("cell_{}", lv.name),
            &lv.sort,
            &lv.child,
            pat_at(&q(&lv.lean), lv.arity, lv.index, "x"),
            format!("The cell `<{}>`.", lv.name),
        );
        coll_chain = format!("{n} ({coll_chain})");
    }
    let n = proj(
        format!("content_{}", coll.holder_name),
        &coll.holder_sort,
        &coll.sort,
        pat_at(&q(&coll.holder_lean), coll.holder_arity, coll.index, "x"),
        format!("The cell map of `<{}>`.", coll.holder_name),
    );
    let coll_chain = format!("{n} ({coll_chain})");
    let mut k_chain = "th".to_string();
    for lv in inner {
        let n = proj(
            format!("cell_{}", lv.name),
            &lv.sort,
            &lv.child,
            pat_at(&q(&lv.lean), lv.arity, lv.index, "x"),
            format!("The cell `<{}>` of an element.", lv.name),
        );
        k_chain = format!("{n} ({k_chain})");
    }
    let n = proj(
        "content_k".to_string(),
        &path.cell_sort,
        "SortK",
        format!("({} x)", q(&path.cell_lean)),
        "The content of `<k>`.".to_string(),
    );
    let k_chain = format!("{n} ({k_chain})");
    // destructuring
    let mut n = 0;
    let top_destr = destr(&a.m, top, &mut |s| {
        if s == coll.sort {
            "m".into()
        } else {
            n += 1;
            format!("g{n}")
        }
    });
    let mut n2 = 0;
    let elem_destr = destr(&a.m, &first.sort, &mut |s| {
        if s == "SortK" {
            "k".into()
        } else {
            n2 += 1;
            format!("x{n2}")
        }
    });
    // the initial configuration, built from `<k>` up
    let args_of = |sym: &str| -> Vec<String> {
        a.m.ctors
            .values()
            .find(|c| c.sym == sym)
            .map(|c| c.args.clone())
            .unwrap_or_else(|| fail(&format!("no constructor {sym}")))
    };
    let mut params: Vec<(String, String)> = Vec::new();
    let mut build = |f: &str, sorts: &[String], at: usize, x: &str, key: Option<usize>| -> String {
        let xs: Vec<String> = sorts
            .iter()
            .enumerate()
            .map(|(j, s)| {
                if j == at {
                    x.to_string()
                } else if key == Some(j) {
                    "i".to_string()
                } else {
                    let v = if params.is_empty() {
                        "g".to_string()
                    } else {
                        format!("g_{}", params.len() + 1)
                    };
                    params.push((v.clone(), ty(na, s)));
                    v
                }
            })
            .collect();
        format!("({f} {})", xs.join(" "))
    };
    let mut term = format!("({} (.kseq ({pitem}) .dotk))", q(&path.cell_lean));
    for (j, lv) in inner.iter().enumerate().rev() {
        let key = (j == 0).then_some(key_pos);
        term = build(&q(&lv.lean), &args_of(&lv.sym), lv.index, &term, key);
    }
    term = format!("(KPrelude.MapHook.element i {term})");
    term = build(
        &q(&coll.holder_lean),
        &args_of(&coll.holder_sym),
        coll.index,
        &term,
        None,
    );
    for lv in path.levels.iter().rev() {
        term = build(&q(&lv.lean), &args_of(&lv.sym), lv.index, &term, None);
    }
    let mut init_params = vec![("i".to_string(), ty(na, &coll.elems[0]))];
    init_params.extend(params);
    Some(Thr {
        ksym: path.cell_sym.clone(),
        coll_t: ty(na, &coll.sort),
        key_t: ty(na, &coll.elems[0]),
        elem_t: ty(na, &coll.elems[1]),
        elem_key_pat,
        proj_defs,
        proj_names,
        coll_chain,
        k_chain,
        top_destr,
        elem_destr,
        init_term: term,
        init_params,
    })
}

/// The sorts of the arguments that hold a cooling rule's hole deeper down (IMP++'s `print(HOLE,
/// AEs)`: the hole is the head of `print`'s `AExps` argument), read off the item's constructors.
fn hole_containers(a: &Lib, cools: &BTreeMap<String, Cool>) -> BTreeSet<String> {
    let by_path: BTreeMap<String, &String> =
        a.m.ctors.keys().map(|c| (a.m.ctor_path(c), c)).collect();
    fn has(l: &L, v: &str) -> bool {
        match l {
            L::Var(x) => x == v,
            L::App(_, xs) => xs.iter().any(|x| has(x, v)),
            _ => false,
        }
    }
    fn walk(
        a: &Lib,
        by_path: &BTreeMap<String, &String>,
        l: &L,
        v: &str,
        out: &mut BTreeSet<String>,
    ) {
        let L::App(h, xs) = l else { return };
        for (i, x) in xs.iter().enumerate() {
            if !has(x, v) || matches!(x, L::Var(y) if y == v) {
                continue;
            }
            if let Some(c) = by_path.get(h)
                && let Some(s) = a.m.ctors[*c].args.get(i)
            {
                out.insert(s.clone());
            }
            walk(a, by_path, x, v, out);
        }
    }
    let mut out = BTreeSet::new();
    for c in cools.values() {
        walk(a, &by_path, &c.item_l, &c.hole, &mut out);
    }
    out
}

/// One cooling rule: `HOLE ~> f(args) => item` (in `A`'s names, unqualified).
pub(crate) struct Cool {
    frz: String,
    pats: Vec<String>,
    binds: Vec<(String, String, String)>,
    hole: String,
    hole_sort: String,
    item: String,
    /// The item, as a term (for the sorts of the arguments the hole sits inside).
    item_l: L,
}

/// The cooling rule of a freezer, from a rule whose `<k>` is `HOLE ~> f(…) ~> REST` on the left
/// and `item ~> REST` on the right, every other cell unchanged.
fn cooling(r: &Rule, kpos: usize) -> Option<Cool> {
    let lhs = &r.step.index;
    let rhs = r.rhs.subst(&r.step.subst);
    let (lc, rc) = (cells_of(lhs)?, cells_of(&rhs)?);
    if lc.len() != rc.len() {
        return None;
    }
    for (i, (x, y)) in lc.iter().zip(rc).enumerate() {
        if i != kpos && x != y {
            return None;
        }
    }
    let lk = args(&lc[kpos]).first()?;
    let rk = args(&rc[kpos]).first()?;
    cooling_k(lk, rk, &r.step.hyps, &r.step.binders, &r.name)
}

/// The cooling rule read off the contents `lk` and `rk` of `<k>` on the two sides of a rule
/// that changes nothing else, with the rule's hypotheses and binders.
fn cooling_k(
    lk: &L,
    rk: &L,
    hyps: &[(String, String)],
    binders: &[(String, String)],
    name: &str,
) -> Option<Cool> {
    if !head(lk).ends_with("kseq") || !head(rk).ends_with("kseq") {
        return None;
    }
    let (h, second) = (&args(lk)[0], &args(lk)[1]);
    let L::Var(hv) = h else { return None };
    if !head(second).ends_with("kseq") {
        return None;
    }
    let (fi, rest) = (&args(second)[0], &args(second)[1]);
    if !head(fi).ends_with("inj_KItem") {
        return None;
    }
    let f = args(fi).first()?;
    if !head(f).contains("#freezer") {
        return None;
    }
    let (item, rrest) = (&args(rk)[0], &args(rk)[1]);
    if rrest != rest {
        return None;
    }
    let mut hole = None;
    let mut binds = Vec::new();
    for (_, p) in hyps {
        if let Some((s, y, x)) = proj_hyp(p) {
            if y == *hv {
                hole = Some((x, s));
            } else {
                binds.push((s, y, x));
            }
        } else if !p.contains("isKResult") {
            fail(&format!(
                "the cooling rule {name} has a side condition other than the hole's: {p}"
            ));
        }
    }
    let (hole, hole_sort) = hole?;
    // a freezer argument whose item the rule's substitution destructed (`kseq (inj_L x) dotk`) is
    // matched as `kseq y dotk` and projected, as the arguments the rule projects already are
    let taken: BTreeSet<String> = binders.iter().map(|(b, _)| b.clone()).collect();
    let mut fresh = 0;
    let mut pats = Vec::new();
    for a in args(f) {
        if head(a).ends_with("kseq")
            && let [it, rest] = args(a)
            && head(rest).ends_with("dotk")
            && let Some(l) = head(it).strip_prefix("SortKItem.inj_")
            && let [L::Var(x)] = args(it)
            && l != "KItem"
        {
            let y = loop {
                fresh += 1;
                let y = format!("y{fresh}");
                if !taken.contains(&y) {
                    break y;
                }
            };
            binds.push((l.to_string(), y.clone(), x.clone()));
            pats.push(format!("(SortK.kseq {y} SortK.dotk)"));
        } else {
            pats.push(a.render_arg());
        }
    }
    Some(Cool {
        frz: head(f).to_string(),
        pats,
        binds,
        hole,
        hole_sort: format!("Sort{hole_sort}"),
        item: item.render_arg(),
        item_l: item.clone(),
    })
}

struct Opts {
    tr_module: String,
    hand_module: String,
    hand_ns: String,
    store_cells: Vec<String>,
    store_typing: Vec<String>,
    /// `--program F`: the typing function that accepts programs, when several are `Bool`-valued
    program: Option<String>,
    /// `--aux F,…`: typing functions that the checker's equations call on syntax that is never an
    /// item of `<k>` (IMP++'s `printable` of `print`'s argument list)
    aux: Vec<String>,
    /// `--env-item S,…`: sorts of items that are environments a scope saves on `<k>` and a rule
    /// restores (IMP++'s `{Ss} => Ss ~> Rho`); such an item leaves nothing for the next one
    env_items: Vec<String>,
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
    let list = |k: &str| -> Vec<String> {
        opt.get(k)
            .map(|v| {
                v.split(',')
                    .filter(|s| !s.is_empty())
                    .map(|s| s.to_string())
                    .collect()
            })
            .unwrap_or_default()
    };
    let ns = get("ns");
    let mut wanted = list("typing");
    if wanted.is_empty() {
        fail("--typing is required");
    }
    wanted.extend(list("aux"));
    let b_def_text =
        std::fs::read_to_string(get("kore-b")).unwrap_or_else(|e| fail(&format!("--kore-b: {e}")));
    let b_def0 = ir::load(&b_def_text).unwrap_or_else(|e| fail(&e));
    let mut syms = Vec::new();
    for w in &wanted {
        let found: Vec<&String> = b_def0
            .symbols
            .iter()
            .filter(|(s, d)| d.is_function() && short_name(s) == *w)
            .map(|(s, _)| s)
            .collect();
        match found.as_slice() {
            [s] => syms.push((*s).clone()),
            [] => fail(&format!("no function {w} in --kore-b")),
            _ => fail(&format!("several functions named {w} in --kore-b")),
        }
    }
    let a = load_ranked(&get("kore-a"), &get("name-a"), true, &[]);
    let b = load(&get("kore-b"), &get("name-b"), false, &syms);
    let o = Opts {
        tr_module: opt.get("tr-module").cloned().unwrap_or(format!("{ns}.Tr")),
        hand_module: opt
            .get("hand-module")
            .cloned()
            .unwrap_or(format!("{ns}.Store")),
        hand_ns: format!("{ns}.hand"),
        store_cells: list("store-cell"),
        store_typing: list("store-typing"),
        program: opt.get("program").cloned(),
        aux: list("aux"),
        env_items: list("env-item")
            .iter()
            .map(|x| format!("Sort{x}"))
            .collect(),
    };
    if opt.contains_key("per-sort-terms") {
        fail("--per-sort-terms: removed with the per-sort encoding");
    }
    if o.store_cells.len() != o.store_typing.len() {
        fail("--store-typing names one typing per --store-cell");
    }
    let (typing, sound) = generate(&a, &b, &syms, &ns, &o);
    write_file(&get("out-typing"), &typing);
    write_file(&get("out-soundness"), &sound);
}

/// `xs` joined by spaces, after a space; nothing when empty.
fn spaced(xs: &[String]) -> String {
    xs.iter().map(|x| format!(" {x}")).collect()
}

/// The two modules, `Typing.lean` and `Soundness.lean`.
fn generate(a: &Lib, b: &Lib, syms: &[String], ns: &str, o: &Opts) -> (String, String) {
    let (na, nb) = (&a.ns, &b.ns);
    // the typing functions
    let mut tfs = Vec::new();
    for s in syms {
        let d = &b.def.symbols[s];
        let sig = b
            .fns
            .get(s)
            .unwrap_or_else(|| fail(&format!("{} is not generated", names::demangle(s))));
        if !sig.partial {
            fail(&format!(
                "{} is total in its library; a typing function is expected to be `Option`-valued",
                names::demangle(s)
            ));
        }
        let args: Vec<String> = d.args.iter().map(sname).collect();
        if args.len() != 2 {
            fail(&format!(
                "{} takes {} arguments; a typing function takes a term and an environment",
                names::demangle(s),
                args.len()
            ));
        }
        if !a.m.sorts.contains_key(&args[0]) {
            fail(&format!(
                "{} types {}, which the semantics lacks",
                names::demangle(s),
                args[0]
            ));
        }
        let result = sname(&d.result);
        tfs.push(TFn {
            sym: s.clone(),
            name: names::ident(&short_name(s)),
            lean_b: format!("{nb}.{}", sig.lean),
            sort: args[0].clone(),
            env: args[1].clone(),
            accepts: result == "SortBool",
            result,
        });
    }
    let env_sort = tfs[0].env.clone();
    if tfs.iter().any(|t| t.env != env_sort) {
        fail("the typing functions take environments of different sorts");
    }
    let ty_sorts: BTreeSet<String> = tfs
        .iter()
        .filter(|t| !t.accepts)
        .map(|t| t.result.clone())
        .collect();
    let ty_sort = match ty_sorts.iter().collect::<Vec<_>>().as_slice() {
        [t] => (*t).clone(),
        _ => fail(
            "exactly one sort of types is expected (the result of the non-Bool typing functions)",
        ),
    };
    let ty_ctors: Vec<String> = b.m.sort(&ty_sort).own.clone();
    if ty_ctors.iter().any(|c| !b.m.ctors[c].args.is_empty()) || !b.m.sort(&ty_sort).is_simple() {
        fail("the types are expected to be an enumeration");
    }
    let accept: Vec<&TFn> = tfs.iter().filter(|t| t.accepts).collect();
    // the function that accepts programs: the one `--program` names, the Bool-valued one, or,
    // when there is none, the one type-returning function, whose programs then end with a value
    // on `<k>` (an expression language), so that `kty` and `Final` allow one value left
    let named = o.program.as_ref().map(|p| {
        tfs.iter()
            .find(|t| t.name == names::ident(p))
            .unwrap_or_else(|| fail(&format!("--program {p} is not one of --typing")))
    });
    let (prog, value_result): (&TFn, bool) = match (named, accept.as_slice()) {
        (Some(p), _) => (p, !p.accepts),
        (None, a) => match a {
            [p] => (p, false),
            [] => match tfs
                .iter()
                .filter(|t| !t.accepts)
                .collect::<Vec<_>>()
                .as_slice()
            {
                [p] => (p, true),
                _ => fail(
                    "with no Bool-valued typing function, exactly one type-returning function (it accepts programs) is expected",
                ),
            },
            _ => fail(
                "with several Bool-valued typing functions, --program names the one that accepts programs",
            ),
        },
    };
    let cx = Ctx {
        a,
        b,
        tfs: &tfs,
        ty_sort: ty_sort.clone(),
        ext: true,
    };
    let ty_ctor = |c: &str| format!("{nb}.{}", b.m.ctor_path(c));
    let eqs = funcs::equations(&b.def);

    // ---- Typing.lean
    let mut t = String::new();
    let fnames: Vec<String> = tfs.iter().map(|f| f.name.clone()).collect();
    writeln!(
        t,
        "import {}\nimport {na}.Rules\nimport {na}.Preserves\nimport KPrelude.InvAttr\nimport KPrelude.Soundness\nimport KPrelude.Tactic\n",
        o.tr_module
    )
    .unwrap();
    let cells_doc: Vec<String> = o.store_cells.iter().map(|c| format!("`<{c}>`")).collect();
    writeln!(
        t,
        "/-! Generated by `k2lean soundness`; do not edit.\n\n\
The runtime typing of `{na}` configurations for the type checker `{nb}` ({}), read off\n\
the two K definitions (`k2lean/docs/design.md`, §3.3):\n\
- the typing functions at `{na}`'s terms, through the translation `tr` (`{}`), and one\n  \
inversion lemma per checker equation whose first argument is a constructor;\n\
- `plug`, the item that cooling makes of a value and a freezer (one case per cooling rule);\n\
- `kty`, the typing of `<k>` as a stack: each item consumes what the previous one leaves\n  \
(`some t` for a value of type `t`, `none` for an accepted statement), and a freezer is typed\n  \
by plugging a value of the hole's type (`dflt`);\n\
- `WTc`, the typing of a configuration, for a typing of each cell written by hand ({});\n\
- `Progress.Case.r`, the progress obligation at the left-hand side of each rule `r` that\n  \
reads a cell typed by hand.\n\
Every lemma that computes the typing is `@[k2l_pres]`, so `k2l_preserve` unfolds with it. -/\n",
        fnames
            .iter()
            .map(|f| format!("`{f}`"))
            .collect::<Vec<_>>()
            .join(", "),
        o.tr_module,
        if cells_doc.is_empty() {
            "none".to_string()
        } else {
            cells_doc.join(", ")
        }
    )
    .unwrap();
    t.push_str("set_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\n");
    writeln!(t, "namespace {ns}\n\nopen KPrelude\n").unwrap();
    writeln!(
        t,
        "/-- The types: the result sort of the typing functions. -/\nabbrev Ty := {}\n/-- Typing environments: the last argument of the typing functions. -/\nabbrev TEnv := {}\n",
        ty(nb, &ty_sort),
        ty(nb, &env_sort)
    )
    .unwrap();
    t.push_str(
        "/-! ## 1. The typing functions at the semantics' terms, and their inversion lemmas -/\n\n",
    );
    for f in &tfs {
        let rt = if f.accepts {
            "Bool".to_string()
        } else {
            "Ty".to_string()
        };
        writeln!(
            t,
            "/-- `{}` on the translation of `x`. -/\ndef {} (G : TEnv) (x : {}) : Option {rt} :=\n  {} ({} x) G",
            names::demangle(&f.sym),
            f.name,
            ty(na, &f.sort),
            f.lean_b,
            format_args!("tr_{}", terms::fsuffix(&f.sort))
        )
        .unwrap();
    }
    let convs: Vec<String> = tfs
        .iter()
        .map(|f| format!("(conv => lhs; rw [{}.eq_def])", f.lean_b))
        .collect();
    // the hooks the checker's equations compute with beyond `==K` and `andBool`
    let mut used: BTreeSet<String> = BTreeSet::new();
    fn apps(p: &P, out: &mut BTreeSet<String>) {
        if let P::App(f, _, xs) = p {
            out.insert(f.clone());
            xs.iter().for_each(|x| apps(x, out));
        }
        if let P::Equals(_, _, l, r) = p {
            apps(l, out);
            apps(r, out);
        }
    }
    let mut in_conds: BTreeSet<String> = BTreeSet::new();
    for f in &tfs {
        for e in eqs.get(&f.sym).into_iter().flatten() {
            e.requires.iter().for_each(|q| apps(q, &mut in_conds));
            apps(&e.rhs, &mut used);
        }
    }
    used.extend(in_conds.iter().cloned());
    // a `Bool` typing call as a condition binds a `Bool`, which the computation splits
    let bool_split = if tfs.iter().any(|f| f.accepts && in_conds.contains(&f.sym)) {
        "\n  all_goals try k2l_cases_bools"
    } else {
        ""
    };
    let extra_hooks: String = [("KEQUAL.ne", "KEqHook.ne"), ("BOOL.or", "BoolHook.or")]
        .iter()
        .filter(|(h, _)| {
            used.iter()
                .any(|f| b.m.hooks.get(f).map(|x| x.as_str()) == Some(*h))
        })
        .map(|(_, l)| format!(", {l}"))
        .collect();
    writeln!(
        t,
        "\n/-- An inversion lemma: unfold the checker's function once at the left-hand side, case on the\nvalues of the typing functions, and compute. -/\nlocal macro \"k2l_ty_inv\" : tactic => `(tactic| (\n  simp only [{}, k2l_tr]\n  first\n    | {}\n  try simp only []\n  try k2l_cases_apps [{}]{bool_split}\n  all_goals simp_all [KEqHook.eq, BoolHook.and{extra_hooks}]))\n",
        fnames.join(", "),
        convs.join("\n    | "),
        tfs.iter().map(|f| f.lean_b.clone()).collect::<Vec<_>>().join(", ")
    )
    .unwrap();
    let mut inv_names = Vec::new();
    let mut skipped = Vec::new();
    let mut dflt: BTreeMap<String, String> = BTreeMap::new();
    // the same values as items, for holes of several sorts
    let mut dflt_k: BTreeMap<String, String> = BTreeMap::new();
    let mut dflt_leaf: BTreeMap<String, (String, &str)> = BTreeMap::new();
    let mut value_lemmas = Vec::new();
    for f in &tfs {
        let Some(es) = eqs.get(&f.sym) else { continue };
        for e in es.iter().filter(|e| !e.owise) {
            match inversion(&cx, f, es, e, false) {
                Ok(inv) => {
                    let bs: Vec<String> = inv
                        .binders
                        .iter()
                        .map(|(x, ty)| format!("({x} : {ty})"))
                        .collect();
                    writeln!(
                        t,
                        "@[k2l_pres] theorem {} {} :\n    {} =\n      {} := by k2l_ty_inv",
                        inv.name,
                        bs.join(" "),
                        inv.lhs,
                        inv.rhs
                    )
                    .unwrap();
                    // a value sort: `f(_:L, _) => t` with `L` a builtin sort
                    if let Some((from, _, P::Var(..))) = as_inj(&e.args[0])
                        && e.requires.is_empty()
                        && let P::App(c, _, cargs) = &e.rhs
                        && cargs.is_empty()
                        && ty_ctors.contains(c)
                        && let Some(lit) = literal(&a.m, &from)
                    {
                        dflt.entry(c.clone()).or_insert_with(|| {
                            cx.leaf_value(&from, &format!("({lit} : {})", ty(na, &from)), &f.sort)
                        });
                        dflt_k.entry(c.clone()).or_insert_with(|| {
                            format!(
                                "{na}.{} ({lit} : {})",
                                a.m.leaf_ctor("SortKItem", &from),
                                ty(na, &from)
                            )
                        });
                        dflt_leaf.entry(c.clone()).or_insert((from.clone(), lit));
                        value_lemmas.push(inv.name.clone());
                    }
                    inv_names.push(inv.name);
                }
                Err(why) => skipped.push(format!(
                    "{} at {}: {why}",
                    f.name,
                    head_key(&e.args[0])
                        .map(|k| names::demangle(&k))
                        .unwrap_or("?".into())
                )),
            }
        }
    }
    // the constructors that no equation matches (IMP++'s `read()`, which its checker rejects)
    {
        for f in &tfs {
            let Some(es) = eqs.get(&f.sym) else { continue };
            for inv in no_equation(&cx, f, es) {
                let bs: Vec<String> = inv
                    .binders
                    .iter()
                    .map(|(x, ty)| format!("({x} : {ty})"))
                    .collect();
                writeln!(
                    t,
                    "@[k2l_pres] theorem {} {} :\n    {} =\n      {} := by k2l_ty_inv",
                    inv.name,
                    bs.join(" "),
                    inv.lhs,
                    inv.rhs
                )
                .unwrap();
                inv_names.push(inv.name);
            }
        }
    }
    for s in &skipped {
        eprintln!("soundness: no inversion lemma for {s}");
    }
    // ---- runtime typing
    let kitem = a.m.sort("SortKItem");
    let pitem = if kitem.leaves.contains(&prog.sort) && a.m.sort(&prog.sort).is_simple() {
        format!("{na}.{} P", a.m.leaf_ctor("SortKItem", &prog.sort))
    } else {
        format!("{na}.inj_{}_KItem P", names::short_sort(&prog.sort))
    };
    // `<k>` in the top cell, or in each thread of a cell map
    let top_sort = rules::top_sort(&a.def).unwrap_or_else(|e| fail(&e));
    let thr = thr_of(a, &top_sort, &pitem);
    let waits = thr
        .as_ref()
        .map(|th| wait_heads(a, &th.ksym))
        .unwrap_or_default();

    let TopCells {
        top,
        top_ctor,
        cells,
        kpos,
    } = match &thr {
        Some(_) => {
            if !o.store_cells.is_empty() {
                fail("cells typed by hand next to a cell map of threads are not supported yet");
            }
            if value_result {
                fail("programs that end with a value are not supported with a cell map of threads");
            }
            TopCells {
                top: top_sort.clone(),
                top_ctor: String::new(),
                cells: vec![],
                kpos: 0,
            }
        }
        None => top_cells(a),
    };
    // `App`, or for the ranked `Step` `Applies` (a rule of some rank applies; `Step` takes the
    // highest rank that applies, so such a configuration steps or has an undefined result)
    let app = if a.ranked {
        "Applies".to_string()
    } else {
        format!("{na}.App")
    };
    let store: Vec<usize> = o
        .store_cells
        .iter()
        .map(|l| {
            cells
                .iter()
                .position(|c| c.label == *l)
                .unwrap_or_else(|| fail(&format!("no cell <{l}> in the top cell")))
        })
        .collect();
    let top_path = if thr.is_some() {
        String::new()
    } else {
        format!("{na}.{}", a.m.ctor_path(&top_ctor))
    };
    // cooling rules → plug; with holes of several sorts the values are items (`dflt_k`)
    let (cools, hole_sorts) = match &thr {
        Some(th) => coolings_in(a, &th.ksym),
        None => {
            let (c, h) = coolings(a, kpos);
            (c, BTreeSet::from([h]))
        }
    };
    let multi = hole_sorts.len() > 1;
    let hole_shorts: Vec<String> = hole_sorts
        .iter()
        .map(|h| h.trim_start_matches("Sort").to_string())
        .collect();
    let hole_sort = hole_sorts.iter().next().cloned().unwrap_or_default();
    for h in &hole_sorts {
        if !tfs.iter().any(|f| !f.accepts && f.sort == *h) {
            fail(&format!("no typing function types the holes' sort {h}"));
        }
    }
    let ty_fn = tfs
        .iter()
        .find(|f| !f.accepts && f.sort == hole_sort)
        .unwrap();
    t.push_str("\n/-! ## 2. The typing of `<k>` -/\n\n");
    writeln!(
        t,
        "/-- A value of each type (the checker's equations at value sorts). -/\ndef dflt : Ty → {}",
        if multi {
            ty(na, "SortKItem")
        } else {
            ty(na, &hole_sort)
        }
    )
    .unwrap();
    for c in &ty_ctors {
        let v = if multi { dflt_k.get(c) } else { dflt.get(c) }.unwrap_or_else(|| {
            fail(&format!(
                "no value of type {}: no equation `{}(_:S, _) => {}` at a builtin sort",
                names::demangle(c),
                ty_fn.name,
                names::demangle(c)
            ))
        });
        writeln!(t, "  | {} => {v}", ty_ctor(c)).unwrap();
    }
    let kitem_own = ty(na, &a.m.own_ty("SortKItem"));
    let projs = if multi {
        plug_def_kitem(a, &cools, &mut t)
    } else {
        plug_def(a, &cools, &hole_sort, &mut t)
    };
    // item0
    let mut item_arms: Vec<(String, String, String, String)> = Vec::new(); // (leaf, ctor, arg type, rhs)
    // `--aux`: called by the checker's equations, typing no item
    let is_aux = |f: &TFn| o.aux.iter().any(|x| names::ident(x) == f.name);
    let typed_leaf = |l: &str| -> Option<&TFn> {
        let fs: Vec<&TFn> = tfs
            .iter()
            .filter(|f| !is_aux(f))
            .filter(|f| a.m.sort(&f.sort).leaves.iter().any(|x| x == l))
            .collect();
        match fs.as_slice() {
            [] => None,
            [f] => Some(*f),
            _ => fail(&format!(
                "the leaf {l} is typed by several typing functions"
            )),
        }
    };
    let typing_of = |f: &TFn, x: &str| -> String {
        if f.accepts {
            format!("if {} G {x} = some true then some none else none", f.name)
        } else {
            format!("({} G {x}).map some", f.name)
        }
    };
    for l in &kitem.leaves {
        if let Some(f) = typed_leaf(l) {
            let v = cx.leaf_value(l, "x", &f.sort);
            let lt = {
                let st = a.m.sort(l);
                if matches!(st.kind, Kind::Plain) {
                    ty(na, &a.m.own_ty(l))
                } else {
                    ty(na, l)
                }
            };
            item_arms.push((
                l.clone(),
                format!("{na}.{}", a.m.leaf_ctor("SortKItem", l)),
                lt,
                typing_of(f, &v),
            ));
        }
    }
    // an environment that a scope saves on `<k>` leaves nothing: no typing reads the environment
    // cell, so restoring one changes no typing
    for l in &o.env_items {
        if !kitem.leaves.contains(l) {
            fail(&format!("--env-item: {l} is not a sort of items"));
        }
        if typed_leaf(l).is_some() {
            fail(&format!("--env-item: {l} is typed by a typing function"));
        }
        item_arms.push((
            l.clone(),
            format!("{na}.{}", a.m.leaf_ctor("SortKItem", l)),
            ty(na, l),
            "some none".to_string(),
        ));
    }
    let is_typed = |l: &str| typed_leaf(l).is_some() || o.env_items.iter().any(|e| e == l);
    writeln!(
        t,
        "\n/-- An item with no pending value: what it leaves for the next item (`some (some t)` for a\nterm of type `t`, `some none` for an accepted statement); `none` when it is ill-typed. -/\ndef item0 (G : TEnv) : {} → Option (Option Ty)",
        ty(na, "SortKItem")
    )
    .unwrap();
    for (_, c, _, rhs) in &item_arms {
        writeln!(t, "  | {c} x => {rhs}").unwrap();
    }
    t.push_str("  | _ => none\n");
    writeln!(
        t,
        "\n/-- An item that receives a pending value of type `t`: a freezer, typed as the item that\ncooling makes of it and a value of type `t`. -/\ndef item (G : TEnv) : Option Ty → {kitem_t} → Option (Option Ty)\n  | none, it => item0 G it\n  | some t, {na}.SortKItem.inj_KItem f => (plug f (dflt t)).bind (item0 G)\n  | some _, _ => none\n\n\
/-- A well-typed continuation: each item consumes what the previous one leaves, and {kend_doc}\nleft at the end. -/\ndef kty (G : TEnv) : Option Ty → {na}.SortK → Bool\n  {kend}\n  | i, .kseq it k => match item G i it with\n    | some o => kty G o k\n    | none => false\n\nattribute [k2l_pres] dflt plug\n",
        kitem_t = ty(na, "SortKItem"),
        kend_doc = if value_result { "at most one value is" } else { "nothing is" },
        kend = if value_result { "| _, .dotk => true" } else { "| i, .dotk => i.isNone" },
    )
    .unwrap();
    if multi {
        // a value plugged into a hole: its projection to the hole's sort, computed
        for c in &ty_ctors {
            let Some((from, lit)) = dflt_leaf.get(c) else {
                continue;
            };
            for h in &hole_sorts {
                let v = if a.m.sort(h).leaves.contains(from) {
                    format!(
                        "some ({})",
                        cx.leaf_value(from, &format!("({lit} : {})", ty(na, from)), h)
                    )
                } else {
                    "none".to_string()
                };
                writeln!(
                    t,
                    "@[k2l_pres] theorem proj_{}_dflt_{} : {na}.proj_KItem_{} ({}) = {v} := rfl",
                    h.trim_start_matches("Sort"),
                    names::ident(&b.m.ctors[c].lean),
                    h.trim_start_matches("Sort"),
                    dflt_k[c]
                )
                .unwrap();
            }
        }
    }
    // the functions the cooling rules' items call (K's overloaded list constructors), unfolded
    let mut item_fns: BTreeSet<String> = BTreeSet::new();
    fn heads(l: &L, out: &mut BTreeSet<String>) {
        if let L::App(h, xs) = l {
            if h.starts_with("K.") {
                out.insert(h.clone());
            }
            xs.iter().for_each(|x| heads(x, out));
        }
    }
    for c in cools.values() {
        heads(&c.item_l, &mut item_fns);
    }
    if !item_fns.is_empty() {
        let fs: Vec<String> = item_fns
            .iter()
            .flat_map(|h| {
                let mut v = vec![format!("{na}.{h}")];
                if a.fn_text.contains(&format!("def {h}.rule1 ")) {
                    v.push(format!("{na}.{h}.rule1"));
                }
                v
            })
            .collect();
        writeln!(t, "attribute [k2l_pres] {}\n", fs.join(" ")).unwrap();
    }
    for (l, c, lt, rhs) in &item_arms {
        writeln!(
            t,
            "@[k2l_pres] theorem item0_inj_{} (G : TEnv) (x : {lt}) : item0 G ({c} x) = {rhs} := rfl",
            names::short_sort(l)
        )
        .unwrap();
    }
    // `item0` and `item` are not unfolded (`ty_simp`): a fallback arm's
    // equation has a side condition per other arm, that the item is not built by that arm's
    // constructor, which on the family is `Term.inj` against `Term.inj` and costly to refute;
    // their value at each leaf is stated instead, by `rfl` at a concrete leaf
    for l in &kitem.leaves {
        let c = format!("{na}.{}", a.m.leaf_ctor("SortKItem", l));
        if c == format!("{na}.SortKItem.inj_KItem") {
            continue;
        }
        let lt = if matches!(a.m.sort(l).kind, Kind::Plain) {
            ty(na, &a.m.own_ty(l))
        } else {
            ty(na, l)
        };
        let short = names::short_sort(l);
        if !item_arms.iter().any(|(m, ..)| m == l) {
            writeln!(
                t,
                "@[k2l_pres] theorem item0_inj_{short} (G : TEnv) (x : {lt}) : item0 G ({c} x) = none := rfl"
            )
            .unwrap();
        }
        writeln!(
            t,
            "@[k2l_pres] theorem item_some_inj_{short} (G : TEnv) (t : Ty) (x : {lt}) : item G (some t) ({c} x) = none := rfl"
        )
        .unwrap();
    }
    writeln!(
        t,
        "@[k2l_pres] theorem item0_inj_KItem (G : TEnv) (x : {kitem_own}) : item0 G ({na}.SortKItem.inj_KItem x) = none := rfl"
    )
    .unwrap();
    for f in tfs.iter().filter(|f| !is_aux(f)) {
        let s = &f.sort;
        let inj = format!("{na}.inj_{}_KItem", names::short_sort(s));
        let proof = if a.m.sort(s).is_simple() {
            "rfl"
        } else {
            "by k2l_cases x <;> rfl"
        };
        writeln!(
            t,
            "/-- Through the injection of `{}` into `KItem`, without casing on the injected value. -/\n@[k2l_pres] theorem item0_{} (G : TEnv) (x : {}) : item0 G ({inj} x) = {} := {proof}",
            names::short_sort(s),
            names::short_sort(s),
            ty(na, s),
            typing_of(f, "x")
        )
        .unwrap();
    }
    // case splits by `k2l_cases` (only the sort's value forms), and `kty`'s equations, since
    // recursion on `SortK` (the family at one index) is well-founded, not structural, so `kty`
    // does not reduce by `rfl`
    let (cases_t, kty_pf) = ("k2l_cases", "by simp only [kty]");
    writeln!(
        t,
        "@[k2l_pres] theorem item_none (G : TEnv) (it : {kitem_t}) : item G none it = item0 G it := by {cases_t} it <;> rfl\n\
@[k2l_pres] theorem item_frz (G : TEnv) (t : Ty) (f : {kitem_own}) : item G (some t) ({na}.SortKItem.inj_KItem f) = (plug f (dflt t)).bind (item0 G) := rfl\n\
@[k2l_pres] theorem kty_dotk (G : TEnv) (i : Option Ty) : kty G i .dotk = {kty_end} := {kty_pf}\n\
@[k2l_pres] theorem kty_kseq (G : TEnv) (i : Option Ty) (it : {kitem_t}) (k : {na}.SortK) :\n    kty G i (.kseq it k) = (match item G i it with | some o => kty G o k | none => false) := {kty_pf}\n{dflt_lemma}",
        kitem_t = ty(na, "SortKItem"),
        kty_end = if value_result { "true" } else { "i.isNone" },
        // the value of each type has that type: as a term of the hole's sort, or as an item
        dflt_lemma = if multi {
            format!(
                "@[k2l_pres] theorem item0_dflt (G : TEnv) (t : Ty) : item0 G (dflt t) = some (some t) := by\n  {cases_t} t <;> simp only [dflt, k2l_pres, Option.map_some]\n"
            )
        } else {
            format!(
                "@[k2l_pres] theorem {}_dflt (G : TEnv) (t : Ty) : {} G (dflt t) = some t := by\n  {cases_t} t <;> simp only [dflt, {}]\n",
                ty_fn.name,
                ty_fn.name,
                value_lemmas.join(", ")
            )
        }
    )
    .unwrap();
    let proj_lemmas: Vec<String> = projs
        .iter()
        .chain(hole_shorts.iter())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|s| format!("{na}.proj_inj_KItem_{s}"))
        .collect();
    writeln!(t, "attribute [k2l_pres] {}\n", proj_lemmas.join(" ")).unwrap();
    // configurations
    t.push_str("/-! ## 3. The typing of a configuration -/\n\n");
    let top_t = ty(na, &top);
    if a.ranked {
        writeln!(
            t,
            "/-- Some rule applies, of some rank (`{na}.Step` takes a rule of the highest rank that applies). -/\ndef Applies (c : {top_t}) : Prop := ∃ i, {na}.App i c\n"
        )
        .unwrap();
    }
    let pat_at = |i: usize, p: &str| -> String {
        let ps: Vec<String> = (0..cells.len())
            .map(|j| if j == i { p.to_string() } else { "_".into() })
            .collect();
        format!("{top_path} {}", ps.join(" "))
    };
    if let Some(th) = &thr {
        let waits_def = if waits.is_empty() {
            "False".to_string()
        } else {
            waits
                .iter()
                .map(|(bs, p)| {
                    let bs: Vec<String> = bs.iter().map(|(b, t)| format!("({b} : {t})")).collect();
                    format!("(∃ {}, k = {p})", bs.join(" "))
                })
                .collect::<Vec<_>>()
                .join(" ∨ ")
        };
        writeln!(
            t,
            "{}\n/-- The cell map that holds `<k>` in each of its elements. -/\ndef threadsOf (c : {top_t}) : {} :=\n  {}\n\
/-- The content of an element's `<k>`. -/\ndef kOf (th : {}) : {na}.SortK :=\n  {}\n\
/-- An element's key cell. -/\ndef keyOf : {} → {}\n  | {} => x\n\n\
open {na} in\n/-- The heads at which a thread may wait: the head of a rule that also needs another\nthread's `<k>` (read off the rules that match two elements of the cell map). -/\ndef Waits (k : SortK) : Prop :=\n  {waits_def}\n\n\
/-- A thread that is done: nothing left in its `<k>`, or waiting at a head that needs another thread. -/\ndef kDone (k : {na}.SortK) : Prop := k = .dotk ∨ Waits k\n\n\
/-- A well-typed thread: stored under its own key, and its `<k>` a well-typed continuation that\nleaves nothing. -/\ndef threadTy (G : TEnv) (q : {} × {}) : Prop :=\n  q.1 = keyOf q.2 ∧ kty G none (kOf q.2) = true\n",
            th.proj_defs,
            th.coll_t,
            th.coll_chain,
            th.elem_t,
            th.k_chain,
            th.elem_t,
            th.key_t,
            th.elem_key_pat,
            th.key_t,
            th.elem_t,
        )
        .unwrap();
    } else {
        writeln!(
            t,
            "/-- The content of `<k>`. -/\ndef kOf : {top_t} → {na}.SortK\n  | {} => k",
            pat_at(kpos, &format!("({} k)", cells[kpos].ctor))
        )
        .unwrap();
    }
    let st_name = |i: usize| -> String {
        if store.len() == 1 {
            "St".into()
        } else {
            format!("St_{}", names::ident(&cells[store[i]].label))
        }
    };
    let mut heads_pres = if let Some(th) = &thr {
        let mut v: Vec<String> = vec!["threadsOf", "kOf", "keyOf", "threadTy"]
            .into_iter()
            .map(String::from)
            .collect();
        v.extend(th.proj_names.iter().cloned());
        v
    } else {
        vec!["kOf".to_string()]
    };
    let mut st_binders = Vec::new();
    let mut conj = vec!["kty G none (kOf c) = true".to_string()];
    for (i, &ci) in store.iter().enumerate() {
        let c = &cells[ci];
        let l = names::ident(&c.label);
        let st = st_name(i);
        writeln!(
            t,
            "/-- The cell `<{}>`. -/\ndef {l}Of : {top_t} → {}\n  | {} => c\n/-- The typing `{st}` of the content of `<{}>`. -/\ndef {l}CellTy ({st} : TEnv → {} → Prop) (G : TEnv) : {} → Prop\n  | {} x => {st} G x",
            c.label,
            ty(na, &c.sort),
            pat_at(ci, "c"),
            c.label,
            ty(na, &c.content),
            ty(na, &c.sort),
            c.ctor
        )
        .unwrap();
        heads_pres.push(format!("{l}Of"));
        heads_pres.push(format!("{l}CellTy"));
        st_binders.push(format!("({st} : TEnv → {} → Prop)", ty(na, &c.content)));
        conj.push(format!("{l}CellTy {st} G ({l}Of c)"));
    }
    writeln!(t, "\nattribute [k2l_pres] {}\n", heads_pres.join(" ")).unwrap();
    let st_args: Vec<String> = (0..store.len()).map(st_name).collect();
    let st_bs = if st_binders.is_empty() {
        String::new()
    } else {
        format!("{} ", st_binders.join(" "))
    };
    if thr.is_some() {
        writeln!(
            t,
            "/-- A well-typed configuration: every thread is well-typed (`threadTy`). -/\ndef WTc (G : TEnv) (c : {top_t}) : Prop :=\n  KPrelude.MapHook.WF (threadsOf c) ∧ KPrelude.MapHook.EntriesOn (threadTy G) (threadsOf c)\n\n\
/-- A terminated configuration: every thread is done (`kDone`). -/\ndef Final (c : {top_t}) : Prop :=\n  KPrelude.MapHook.EntriesOn (fun q => kDone (kOf q.2)) (threadsOf c)\n"
        )
        .unwrap();
    } else {
        writeln!(
        t,
        "/-- A well-typed configuration: `<k>` is a well-typed continuation that leaves {}, and each\ncell typed by hand is typed by its typing. -/\ndef WTc {st_bs}(G : TEnv) (c : {top_t}) : Prop :=\n  {}\n",
        if value_result { "at most one value" } else { "nothing" },
        conj.join(" ∧ ")
    )
    .unwrap();
    }
    // with a value result, also a value alone (a leaf of `KResult` at the head, nothing after)
    let final_values: Vec<String> = if value_result {
        a.m.sorts
            .get("SortKResult")
            .map(|kr| {
                kitem
                    .leaves
                    .iter()
                    .filter(|l| kr.leaves.contains(l))
                    .map(|l| {
                        pat_at(
                            kpos,
                            &format!(
                                "({} (.kseq ({na}.{} _) .dotk))",
                                cells[kpos].ctor,
                                a.m.leaf_ctor("SortKItem", l)
                            ),
                        )
                    })
                    .collect()
            })
            .unwrap_or_default()
    } else {
        vec![]
    };
    if thr.is_none() {
        writeln!(
        t,
        "/-- A terminated configuration: nothing left in `<k>`{}. -/\ndef Final : {top_t} → Prop\n  | {} => True\n{}  | _ => False\n",
        if value_result { ", or one value" } else { "" },
        pat_at(kpos, &format!("({} .dotk)", cells[kpos].ctor)),
        final_values
            .iter()
            .map(|p| format!("  | {p} => True\n"))
            .collect::<String>()
    )
    .unwrap();
    }
    // init
    let mut init_bs = vec![format!("(P : {})", ty(na, &prog.sort))];
    let mut init_args = Vec::new();
    let mut store_vars = Vec::new();
    let mut other_vars = Vec::new();
    for (i, c) in cells.iter().enumerate() {
        if i == kpos {
            init_args.push(format!("({} (.kseq ({pitem}) .dotk))", c.ctor));
        } else if let Some(j) = store.iter().position(|&s| s == i) {
            let v = if j == 0 {
                "E".to_string()
            } else {
                format!("E_{}", j + 1)
            };
            init_bs.push(format!("({v} : {})", ty(na, &c.content)));
            init_args.push(format!("({} {v})", c.ctor));
            store_vars.push((v, ty(na, &c.content)));
        } else {
            let n = other_vars.len();
            let v = if n == 0 {
                "g".to_string()
            } else {
                format!("g_{}", n + 1)
            };
            init_bs.push(format!("({v} : {})", ty(na, &c.sort)));
            init_args.push(v.clone());
            other_vars.push((v, ty(na, &c.sort)));
        }
    }
    if let Some(th) = &thr {
        // one thread, keyed by `i`, whose `<k>` holds the program
        for (v, vt) in &th.init_params {
            init_bs.push(format!("({v} : {vt})"));
            other_vars.push((v.clone(), vt.clone()));
        }
        writeln!(
            t,
            "/-- The initial configuration of program `P`: one thread, keyed by `i`, whose `<k>` holds `P`;\nevery other cell is a parameter. -/\ndef init {} : {top_t} :=\n  {}\n",
            init_bs.join(" "),
            th.init_term
        )
        .unwrap();
    } else {
        writeln!(
        t,
        "/-- The initial configuration of program `P`: `<k>` holds `P`, each cell typed by hand holds its\nparameter, and every other cell is a parameter. -/\ndef init {} : {top_t} :=\n  {top_path} {}\n",
        init_bs.join(" "),
        init_args.join(" ")
    )
    .unwrap();
    }
    // store rules, and the progress cases at the ones that read the store
    let store_var = |r: &Rule, l: &L, i: usize| -> Option<String> {
        let _ = r;
        match &args(l).get(i).and_then(|c| args(c).first()) {
            Some(L::Var(v)) => Some(v.clone()),
            _ => None,
        }
    };
    let mut store_rules = Vec::new();
    let mut prog_hand: BTreeMap<String, (String, Vec<String>)> = BTreeMap::new(); // KItem leaf → (rule, head args)
    t.push_str("/-! ## 4. Progress at the rules that read a cell typed by hand -/\n\n");
    for r in &a.rules {
        let lhs = &r.step.index;
        let rhs = r.rhs.subst(&r.step.subst);
        let mut touches = false;
        let mut reads = false;
        for &ci in &store {
            let (lc, rc) = (args(lhs).get(ci), args(&rhs).get(ci));
            if lc != rc {
                touches = true;
            }
            // a pattern on the cell (or a variable of its content constrained by a side condition)
            let Some(lcell) = lc else { continue };
            if matches!(lcell, L::Var(_)) {
                continue;
            }
            match store_var(r, lhs, ci) {
                Some(v) => {
                    let mentions = r.step.hyps.iter().any(|(_, p)| {
                        p.split(|ch: char| !(ch.is_alphanumeric() || ch == '_'))
                            .any(|w| w == v)
                    });
                    if mentions {
                        reads = true;
                    }
                }
                None => reads = true,
            }
        }
        if reads {
            touches = true;
        }
        if touches {
            store_rules.push(r.lean.clone());
        }
        if !reads {
            continue;
        }
        // the head of `<k>`: a constructor of `KItem` applied to variables
        let kc = &args(lhs)[kpos];
        let content = args(kc)
            .first()
            .unwrap_or_else(|| fail("a `<k>` without content"));
        let bad = || -> ! {
            fail(&format!(
                "the rule {} reads a cell typed by hand, and its `<k>` is not `C(x…) ~> REST` for a constructor `C` of `KItem`",
                r.name
            ))
        };
        if !head(content).ends_with("kseq") {
            bad()
        }
        let (h, rest) = (&args(content)[0], &args(content)[1]);
        let L::Var(rest) = rest else { bad() };
        let hc = head(h);
        let Some(leaf) = hc.strip_prefix("SortKItem.inj_") else {
            bad()
        };
        let mut hargs = Vec::new();
        for x in args(h) {
            let L::Var(x) = x else { bad() };
            hargs.push(x.clone());
        }
        let leaf_sort = kitem
            .leaves
            .iter()
            .find(|l| names::short_sort(l) == leaf)
            .cloned()
            .unwrap_or_else(|| bad());
        if prog_hand.contains_key(&leaf_sort) {
            fail(&format!(
                "two rules that read a cell typed by hand have the head {}",
                hc
            ));
        }
        let bty = |v: &str| -> String {
            r.step
                .binders
                .iter()
                .find(|(b, _)| b == v)
                .map(|(_, ty)| format!("{na}.{ty}"))
                .unwrap_or_else(|| bad())
        };
        let mut bs = vec!["(G : TEnv)".to_string()];
        for x in &hargs {
            bs.push(format!("({x} : {})", bty(x)));
        }
        bs.push(format!("({rest} : {na}.SortK)"));
        let mut cfg_args = Vec::new();
        let mut call_args = vec!["G".to_string(), "x".to_string()];
        let mut k_used = false;
        for (i, c) in cells.iter().enumerate() {
            if i == kpos {
                cfg_args.push(format!(
                    "({} (.kseq ({na}.{hc} {}) {rest}))",
                    c.ctor,
                    hargs.join(" ")
                ));
                if !k_used {
                    call_args.push("K".into());
                    k_used = true;
                }
            } else if let Some(j) = store.iter().position(|&s| s == i) {
                let (v, vt) = &store_vars[j];
                bs.push(format!("({v} : {vt})"));
                cfg_args.push(format!("({} {v})", c.ctor));
                call_args.push(v.clone());
            } else {
                let L::Var(v) = &args(lhs)[i] else { bad() };
                bs.push(format!("({v} : {})", bty(v)));
                cfg_args.push(v.clone());
                let n = other_vars.iter().position(|(_, s)| *s == ty(na, &c.sort));
                call_args.push(n.map(|n| other_vars[n].0.clone()).unwrap_or("_".into()));
            }
        }
        let cfg = format!("({top_path} {})", cfg_args.join(" "));
        let st_ps = st_args.join(" ");
        writeln!(
            t,
            "/-- Progress at the left-hand side of rule {}, which reads a cell typed by\nhand: a well-typed configuration of that shape has a rule that applies. -/\ndef Progress.Case.{} {st_bs}: Prop :=\n  ∀ {},\n    WTc {st_ps} G {cfg} →\n    {app} {cfg}\n",
            rules::doc(r),
            r.lean,
            bs.join(" ")
        )
        .unwrap();
        prog_hand.insert(leaf_sort, (r.lean.clone(), call_args));
    }
    let mut guard = inv_names.clone();
    guard.push(if multi {
        "item0_dflt".to_string()
    } else {
        format!("{}_dflt", ty_fn.name)
    });
    writeln!(t, "#k2l_assert_axioms {}\n\nend {ns}", guard.join(" ")).unwrap();

    // ---- Soundness.lean
    let mut s = String::new();
    let st_inst = o.store_typing.join(" ");
    let wtc = if st_inst.is_empty() {
        "WTc".to_string()
    } else {
        format!("WTc {st_inst}")
    };
    writeln!(
        s,
        "import {}\nimport KPrelude.InvTactic\nimport KPrelude.InvColl\nimport KPrelude.Relate\n",
        o.hand_module
    )
    .unwrap();
    writeln!(
        s,
        "/-! Generated by `k2lean soundness`; do not edit.\n\n\
Type soundness of `{na}` for the type checker `{nb}`, from the runtime typing of `Typing.lean`\n\
and the hand module `{}` (the typings {} of the cells {}, and the cases of the rules that\n\
read or write them):\n\
- `preserved`: every rule keeps `{wtc} G`; the case of rule `r` is `hand.r` when the hand module\n  \
has it, and `k2l_preserve`'s otherwise;\n\
- `progress`: a well-typed configuration has terminated or has a rule that applies, by cases on\n  \
the head of `<k>` (its operands, the freezer that waits for a value) and a search among the\n  \
constructors of `{na}.App`; at the head of a rule `r` that reads a cell typed by hand, by\n  \
`hand.progress.r`;\n\
- `soundness`: a program that the checker accepts, started with cells typed by their typings,\n  \
never gets stuck. -/\n",
        o.hand_module,
        if o.store_typing.is_empty() { "(none)".into() } else { o.store_typing.iter().map(|x| format!("`{x}`")).collect::<Vec<_>>().join(", ") },
        if cells_doc.is_empty() { "(none)".into() } else { cells_doc.join(", ") },
    )
    .unwrap();
    s.push_str("set_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\n");
    writeln!(s, "namespace {ns}\n\nopen KPrelude\n").unwrap();
    writeln!(
        s,
        "/-! ## Preservation -/\n\n/-- The runtime typing is preserved by every rule of `{na}`. -/\ntheorem preserved (G : TEnv) : Preserved {na}.Step ({wtc} G) := by\n{pres_pf}\n\ntheorem preservation {{G : TEnv}} {{c c' : {top_t}}} (h : {na}.Step c c') :\n    {wtc} G c → {wtc} G c' :=\n  fun hw => preserved G c c' hw h\n",
        pres_pf = match &thr {
            // a rule that rewrites one thread is that thread's step (`k2l_thread_case`), closed on
            // the thread's typing alone; any other rule (one that adds a thread, reads two, or
            // leaves the threads as they are) by the closers on the whole configuration
            Some(th) => format!(
                "  apply {na}.Step.preserves_of\n  all_goals first\n    | (k2l_thread_case [WTc, threadsOf, {projs}]\n       all_goals k2l_close [threadTy, keyOf, kOf, {projs}] split [{fns}])\n    | k2l_preserve split [{fns}]",
                projs = th.proj_names.join(", "),
                fns = fnames.join(", ")
            ),
            None => format!("  k2l_preserve split [{}] hand {}", fnames.join(", "), o.hand_ns),
        },
    )
    .unwrap();
    // progress tactics
    let projs_all: BTreeSet<String> = projs
        .iter()
        .cloned()
        .chain(hole_shorts.iter().cloned())
        .collect();
    let proj_fns: Vec<String> = projs_all
        .iter()
        .map(|p| format!("{na}.proj_KItem_{p}"))
        .collect();
    let proj_eqs: Vec<String> = projs_all
        .iter()
        .map(|p| format!("{na}.proj_eq_some_KItem_{p}"))
        .collect();
    // the functions the rules' side conditions use
    let mut close_unfold: BTreeSet<String> = BTreeSet::new();
    for r in &a.rules {
        for (_, p) in &r.step.hyps {
            for w in p.split(|ch: char| !(ch.is_alphanumeric() || ch == '_' || ch == '.')) {
                if w.starts_with("proj_") || w == "K.isKResult" {
                    close_unfold.insert(format!("{na}.{w}"));
                }
            }
        }
    }
    if close_unfold.contains(&format!("{na}.K.isKResult")) {
        if a.fn_text.contains("def K.isKResult.rule1") {
            close_unfold.insert(format!("{na}.K.isKResult.rule1"));
        }
        if a.m.sorts.contains_key("SortKResult") {
            close_unfold.insert(format!("{na}.proj_KItem_KResult"));
        }
    }
    for h in &hole_shorts {
        close_unfold.insert(format!("{na}.inj_{h}_KItem"));
    }
    // a projection of a hole or of a freezer argument a cooling rule binds
    let proj_closes: String = projs_all
        .iter()
        .map(|h| format!(" | exact {na}.proj_inj_KItem_{h} _"))
        .collect();
    // the sorts that hold a hole deeper down, split through by `k2l_cases_args … within`
    let containers: Vec<String> = hole_containers(a, &cools)
        .into_iter()
        .flat_map(|s| {
            // and the sorts injected into it (IMP++'s `Ids` inside `AExps`)
            let mut v: Vec<String> =
                a.m.sort(&s)
                    .leaves
                    .iter()
                    .filter(|l| !a.m.sort(l).own.is_empty())
                    .cloned()
                    .collect();
            v.push(s);
            v
        })
        .collect::<BTreeSet<String>>()
        .into_iter()
        .filter(|s| !hole_sorts.contains(s))
        .flat_map(|s| {
            // a sort's own constructors build its `Own` type
            let own = a.m.own_ty(&s);
            let mut v = vec![ty(na, &s)];
            if own != s && !a.m.sort(&s).own.is_empty() {
                v.push(ty(na, &own));
            }
            v
        })
        .collect();
    let within = if containers.is_empty() {
        String::new()
    } else {
        // the split goes through the container, its constructor, then the hole's operand
        format!(" within [{}] fuel 4", containers.join(", "))
    };
    let hole_tys: String = hole_sorts
        .iter()
        .map(|h| ty(na, h))
        .collect::<Vec<_>>()
        .join(", ");
    let mut close_list: Vec<String> = close_unfold.into_iter().collect();
    close_list.extend(["BoolHook.and".to_string(), "BoolHook.not".to_string()]);
    writeln!(
        s,
        "/-! ## Progress -/\n\n\
/-- Compute the typing of `<k>` (with the hypotheses, which record the cases taken); a typing that\n\
computes to `false` is `false = true`, `False`, and closes the goal `typing → App c`. -/\n\
local macro \"ty_simp\" : tactic => `(tactic| simp only [k2l_pres, WTc, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none, Option.isNone_some, Option.isNone_none, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, ite_true, ite_false, ↓reduceIte, and_self, and_true, true_and, Bool.false_eq_true, false_implies, reduceCtorEq, Option.some.injEq, *])\n\n\
/-- An ill-typed shape: the typing of `<k>` computes to `false`. -/\n\
local macro \"prog_absurd\" : tactic => `(tactic| (ty_simp; done))\n\n\
/-- A side condition of a rule: by unification, an assumption, or by computing it. -/\n\
local macro \"prog_close\" : tactic => `(tactic| first | rfl | assumption{proj_closes} | (simp_all [{}]; done))\n\n\
/-- The variables of sorted projections, substituted. -/\n\
local macro \"prog_proj\" : tactic => `(tactic| (simp only [{}] at *; subst_vars))\n\n\
/-- What the typing of the head depends on: the sort projections of variables, the typing functions. -/\n\
local macro \"prog_cases\" : tactic => `(tactic| k2l_cases_typing [{}] [{}] => (try ty_simp))\n\n\
{waits_m}{nohyg}/-- One shape of the head of `<k>`: case on what its typing depends on, then find the rule. -/\n\
local macro \"prog_leaf\" : tactic => `(tactic| {leaf})\n",
        close_list.join(", "),
        proj_eqs.join(", "),
        proj_fns.join(", "),
        fnames.join(", "),
        // the thread's macros name the proof's hypotheses `hnd` and `hcat`
        nohyg = if thr.is_some() { "set_option hygiene false in\n" } else { "" },
        // with threads, a thread at a head where it may wait is done (`hnd` says it is not)
        leaf = if thr.is_some() {
            let (r0, r1) = if a.ranked { ("(apply Exists.intro; ", ")") } else { ("", "") };
            // the head of `<k>` is in `hcat` only, where the Boolean splits look for it
            format!("(first | prog_waits | (prog_cases; all_goals (intro _hk; (try prog_proj); revert hcat; k2l_cases_bools; all_goals (intro hcat; {r0}k2l_ctor_search {na}.App => prog_close{r1}))))")
        } else {
            let (r0, r1) = if a.ranked { ("(apply Exists.intro; ", ")") } else { ("", "") };
            format!("(prog_cases; all_goals (intro _hk; (try prog_proj); k2l_cases_bools; all_goals {r0}k2l_ctor_search {na}.App => prog_close{r1}))")
        },
        waits_m = if thr.is_some() {
            let n = waits.len();
            let pfs: Vec<String> = waits
                .iter()
                .enumerate()
                .map(|(i, (bs, _))| {
                    let w = if bs.is_empty() {
                        "rfl".to_string()
                    } else {
                        format!("⟨{}rfl⟩", "_, ".repeat(bs.len()))
                    };
                    let path = format!("{}{}", "right; ".repeat(i), if i + 1 < n { "left; " } else { "" });
                    format!(" | (exfalso; apply hnd; unfold kDone Waits; right; {path}exact {w})")
                })
                .collect();
            format!(
                "set_option hygiene false in\n/-- A thread at a head where it may wait is done, against `hnd`. -/\nlocal macro \"prog_waits\" : tactic => `(tactic| first | fail \"not a waiting head\"{})\n\n",
                pfs.concat()
            )
        } else {
            String::new()
        },
    )
    .unwrap();
    // the destructuring of the configuration
    let mut obt = Vec::new();
    let mut he_names = Vec::new();
    {
        let mut oi = 0;
        for (i, _) in cells.iter().enumerate() {
            if i == kpos {
                obt.push("⟨k⟩".to_string());
            } else if let Some(j) = store.iter().position(|&x| x == i) {
                obt.push(format!("⟨{}⟩", store_vars[j].0));
            } else {
                obt.push(other_vars[oi].0.clone());
                oi += 1;
            }
        }
        for j in 0..store.len() {
            he_names.push(if j == 0 {
                "he".to_string()
            } else {
                format!("he_{}", j + 1)
            });
        }
    }
    let mut unf = vec!["kOf".to_string()];
    for &ci in &store {
        let l = names::ident(&cells[ci].label);
        unf.push(format!("{l}Of"));
        unf.push(format!("{l}CellTy"));
    }
    let hw_pat = std::iter::once("hk".to_string())
        .chain(he_names.iter().cloned())
        .collect::<Vec<_>>()
        .join(", ");
    let he_at = if he_names.is_empty() {
        String::new()
    } else {
        format!(" {}", he_names.join(" "))
    };
    // with a value result, a value alone is terminated, so each case chooses `App` itself
    // (`progress_app`), and the value case before it, where nothing follows, `Final`
    if value_result {
        writeln!(
            s,
            "/-- A case that ends in a rule that applies. -/\ntheorem progress_app {{p q r : Prop}} (h : p → r) : p → q ∨ r := fun hp => Or.inr (h hp)\n"
        )
        .unwrap();
    }
    // the typing: a conjunction with the cells typed by hand, or the typing of `<k>` alone
    let hw_get = if he_names.is_empty() {
        unf.insert(0, wtc.to_string());
        "have hk := hw".to_string()
    } else {
        format!("obtain ⟨{hw_pat}⟩ := hw")
    };
    // value leaves: the next item is a freezer waiting for the value
    let values: Vec<String> = match a.m.sorts.get("SortKResult") {
        Some(kr) => kitem
            .leaves
            .iter()
            .filter(|l| kr.leaves.contains(l))
            .cloned()
            .collect(),
        None => vec![],
    };
    // typed leaves with constructors: case on the constructor and the operands
    let own_typed: Vec<String> = kitem
        .leaves
        .iter()
        .filter(|l| typed_leaf(l).is_some() && !a.m.sort(l).own.is_empty())
        .map(|l| format!("{na}.{}", a.m.leaf_ctor("SortKItem", l)))
        .collect();
    // (a freezer is not computed before its split, nor before its `SortK` arguments are split
    // as far as the cooling patterns go: with the freezer or an argument a variable, every equation
    // of `plug` but its fallback fails, and the fallback's side conditions, `Term.c…` against
    // `Term.c…`, are costly)
    // the splits are `k2l_cases` (the goals of the sort's value forms, which carry no
    // constructor names to choose a case by), so each shape of the head of `<k>` is a case of
    // `first`, guarded by its constructor (`k2l_has_ctor`); a guard or a case that fails leaves
    // the goal to the next, and `prog_absurd`, last, closes the ill-typed shapes. After the split of
    // the continuation the `kseq` case comes first: its first step names `it₂`, which the
    // `dotk` case does not bind, so it fails there at once
    let mut cases: Vec<String> = Vec::new();
    if !values.is_empty() {
        let vcs: Vec<String> = values
            .iter()
            .map(|l| format!("{na}.{}", a.m.leaf_ctor("SortKItem", l)))
            .collect();
        cases.push(format!(
            "-- a value: the next item is a freezer waiting for it (a cooling rule applies)\n          | (k2l_has_ctor [{}]\n             k2l_cases K with ⟨it₂, K₂⟩ <;> first\n               | ({}k2l_cases it₂ with ⟨f⟩ <;> k2l_norm_idx <;>\n                    (first | k2l_has_ctor [{na}.SortKItem.inj_KItem] | (try prog_absurd))\n                  all_goals (k2l_cases f <;> k2l_norm_idx <;>\n                    (k2l_cases_frz [{na}.SortKItem.inj_KItem] [{na}.SortK] => skip) <;> k2l_norm_idx <;>\n                    (try prog_absurd) <;> prog_leaf)\n                  done)\n               | {})",
            vcs.join(", "),
            if value_result { "apply progress_app\n                  " } else { "" },
            if value_result { "exact fun _ => Or.inl trivial" } else { "prog_absurd" }
        ));
    }
    // the heads of rules that read a cell typed by hand
    for (leaf, (rule, call_args)) in &prog_hand {
        let hw_args = std::iter::once("hk".to_string())
            .chain(he_names.iter().cloned())
            .collect::<Vec<_>>()
            .join(", ");
        cases.push(format!(
            "-- the head of rule {rule}, which reads a cell typed by hand\n          | (k2l_has_ctor [{na}.{}]\n             exact fun hk => {}hand.progress.{rule} {} ⟨{hw_args}⟩{})",
            a.m.leaf_ctor("SortKItem", leaf),
            if value_result { "Or.inr (" } else { "" },
            call_args.join(" "),
            if value_result { ")" } else { "" }
        ));
    }
    for l in &kitem.leaves {
        if !is_typed(l) || values.contains(l) || prog_hand.contains_key(l) {
            continue;
        }
        let guard = format!("{na}.{}", a.m.leaf_ctor("SortKItem", l));
        let to_app_f = if value_result {
            "apply progress_app\n             "
        } else {
            ""
        };
        if a.m.sort(l).own.is_empty() {
            cases.push(format!(
                "| (k2l_has_ctor [{guard}]\n             {to_app_f}prog_leaf\n             done)"
            ));
        } else {
            cases.push(format!(
                "| (k2l_has_ctor [{guard}]\n             {to_app_f}k2l_cases x <;> k2l_norm_idx <;> k2l_cases_args [{}] [{}]{within} <;> prog_leaf\n             done)",
                own_typed.join(", "),
                hole_tys
            ));
        }
    }
    let right_f = if value_result { "" } else { "right\n       " };
    if let Some(th) = &thr {
        writeln!(
            s,
            "theorem progress {{G : TEnv}} (c : {top_t}) (hw : {wtc} G c) : Final c ∨ {app} c := by\n  by_cases hd : Final c\n  · exact Or.inl hd\n  right\n  k2l_cases c with {}\n  simp only [WTc, Final, threadsOf, {projs}] at hw hd\n  obtain ⟨hwf, hall⟩ := hw\n  -- a thread that is not done\n  obtain ⟨key, th, rest, hcat, hnd⟩ := KPrelude.MapHook.exists_not_of_not_entriesOn hwf hd\n  have hth := KPrelude.MapHook.entry_of_concat_element hcat hall\n  k2l_cases th with {}\n  simp only [threadTy, keyOf, kOf, {projs}] at hth hnd\n  obtain ⟨rfl, hk⟩ := hth\n  revert hk\n  k2l_cases k with ⟨it, K⟩\n  all_goals first\n    | exact absurd (Or.inl rfl) hnd\n    | (k2l_cases it with ⟨x⟩\n       all_goals k2l_norm_idx\n       all_goals first\n          {}\n          | prog_absurd\n       done)\n",
            th.top_destr,
            th.elem_destr,
            cases.join("\n          "),
            projs = th.proj_names.join(", "),
        )
        .unwrap();
    } else {
        writeln!(
        s,
        "theorem progress {{G : TEnv}} (c : {top_t}) (hw : {wtc} G c) : Final c ∨ {app} c := by\n  k2l_cases c with ⟨{}⟩\n  k2l_cases k with ⟨it, K⟩\n  all_goals first\n    | exact Or.inl trivial\n    | ({right_f}{hw_get}\n       simp only [{}] at hk{he_at}\n       revert hk\n       k2l_cases it with ⟨x⟩\n       all_goals k2l_norm_idx\n       all_goals first\n          {}\n          | prog_absurd\n       done)\n",
        obt.join(", "),
        unf.join(", "),
        cases.join("\n          ")
    )
    .unwrap();
    }
    // soundness
    let he_bs: Vec<String> = store_vars
        .iter()
        .zip(&o.store_typing)
        .enumerate()
        .map(|(j, ((v, _), st))| {
            let h = if j == 0 {
                "hE".to_string()
            } else {
                format!("hE_{}", j + 1)
            };
            format!("({h} : {st} G {v})")
        })
        .collect();
    let he_args: Vec<String> = (0..store_vars.len())
        .map(|j| {
            if j == 0 {
                "hE".to_string()
            } else {
                format!("hE_{}", j + 1)
            }
        })
        .collect();
    let mut implicit: Vec<String> = vec![format!("{{P : {}}}", ty(na, &prog.sort))];
    // the program is accepted: the Bool-valued function says `true`, or it has a type `t`
    let accepted = if value_result {
        implicit.push("{t : Ty}".to_string());
        "some t"
    } else {
        "some true"
    };
    for (v, vt) in &store_vars {
        implicit.push(format!("{{{v} : {vt}}}"));
    }
    for (v, vt) in &other_vars {
        implicit.push(format!("{{{v} : {vt}}}"));
    }
    let init_call: Vec<String> = std::iter::once("P".to_string())
        .chain(
            cells
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != kpos)
                .map(|(i, _)| match store.iter().position(|&x| x == i) {
                    Some(j) => store_vars[j].0.clone(),
                    None => {
                        let n = cells
                            .iter()
                            .enumerate()
                            .filter(|(k, _)| *k != kpos && !store.contains(k) && *k < i)
                            .count();
                        other_vars[n].0.clone()
                    }
                }),
        )
        .collect();
    let init_call = if thr.is_some() {
        std::iter::once("P".to_string())
            .chain(other_vars.iter().map(|(v, _)| v.clone()))
            .collect::<Vec<_>>()
            .join(" ")
    } else {
        init_call.join(" ")
    };
    let wt_init_he = std::iter::once("by simp [init, k2l_pres, hP]".to_string())
        .chain(he_args.iter().cloned())
        .collect::<Vec<_>>()
        .join(", ");
    // a conjunction with the cells typed by hand, or the typing of `<k>` alone
    let wt_init_pf = if thr.is_some() {
        "by\n    simp only [WTc, threadsOf, init, k2l_pres]\n    refine ⟨KPrelude.MapHook.wf_element, KPrelude.MapHook.entriesOn_element ?_⟩\n    simp [threadTy, keyOf, kOf, k2l_pres, hP]".to_string()
    } else if he_args.is_empty() {
        format!("by simp [init, {wtc}, k2l_pres, hP]")
    } else {
        format!("⟨{wt_init_he}⟩")
    };
    writeln!(
        s,
        "/-! ## Soundness -/\n\n\
theorem wt_init {{G : TEnv}} {} (hP : {} G P = {accepted}){} :\n    {wtc} G (init {init_call}) :=\n  {wt_init_pf}\n\n\
theorem wt_stepsN {{G : TEnv}} : ∀ {{n : Nat}} {{c c' : {top_t}}},\n    StepsN {na}.Step n c c' → {wtc} G c → {wtc} G c'\n  | _, _, _, .refl _, h => h\n  | _, _, _, .step hs rest, h => wt_stepsN rest (preservation hs h)\n\n\
/-- **Type soundness.** A program that the type checker accepts, started with cells typed by\nhand by their typings, never gets stuck: every reachable configuration has terminated{} or has a\nrule that applies (a step, or an undefined result). -/\n\
theorem soundness {{G : TEnv}} {}\n    (hP : {} (tr_{} P) G = {accepted}){}\n    {{n : Nat}} {{c : {top_t}}} (h : StepsN {na}.Step n (init {init_call}) c) :\n    Final c ∨ {app} c :=\n  progress c (wt_stepsN h (wt_init hP{}))\n\n\
#k2l_assert_axioms preserved preservation progress wt_init wt_stepsN soundness\n\nend {ns}",
        implicit.join(" "),
        prog.name,
        spaced(&he_bs),
        if value_result { " (nothing left, or one value)" } else { "" },
        implicit.join(" "),
        prog.lean_b,
        terms::fsuffix(&prog.sort),
        spaced(&he_bs),
        spaced(&he_args)
    )
    .unwrap();
    eprintln!(
        "soundness: {} inversion lemmas, {} cooling rules, rules reading or writing a cell typed by hand: {:?}, progress cases by hand: {:?}",
        inv_names.len(),
        cools.len(),
        store_rules,
        prog_hand
            .values()
            .map(|(r, _)| r.clone())
            .collect::<Vec<_>>()
    );
    (t, s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_call_on_names_bound_by_earlier_calls_is_matched_inside_them() {
        let calls = [
            ("lev G E1".to_string(), "r".to_string()),
            ("lev G E2".to_string(), "r_1".to_string()),
            ("K.join r r_1".to_string(), "r_2".to_string()),
        ];
        assert_eq!(
            match_calls_nested(&calls, "some r_2", "none", ""),
            "(match lev G E1, lev G E2 with\n  | some r, some r_1 => (match K.join r r_1 with\n    | some r_2 => some r_2\n    | _ => none)\n  | _, _ => none)"
        );
        assert!(mentions("K.join r r_1", "r_1") && !mentions("K.join r r_12", "r_1"));
    }

    #[test]
    fn projection_hypotheses_are_read() {
        assert_eq!(
            proj_hyp("proj_KItem_Expr y_2 = some K1"),
            Some(("Expr".into(), "y_2".into(), "K1".into()))
        );
        assert_eq!(proj_hyp("proj_KItem_Expr (f y) = some K1"), None);
        assert_eq!(proj_hyp("KPrelude.BoolHook.and true x = true"), None);
    }

    #[test]
    fn calls_are_matched_together() {
        let calls = vec![
            ("f G a".to_string(), "r".to_string()),
            ("f G b".to_string(), "r_1".to_string()),
        ];
        assert_eq!(
            match_calls(&calls, "yes", "no", ""),
            "(match f G a, f G b with\n  | some r, some r_1 => yes\n  | _, _ => no)"
        );
        assert_eq!(match_calls(&[], "yes", "no", ""), "yes");
    }

    #[test]
    fn kore_variables_become_lean_names() {
        assert_eq!(var_name("VarE1"), "E1");
        assert_eq!(var_name("Var'Unds'Gen0"), "Gen0");
    }
}
