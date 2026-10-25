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
    pub(crate) ns: String,
}

pub(crate) fn load(kore: &str, ns: &str, want_rules: bool, extra: &[String]) -> Lib {
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
    let rules = if want_rules {
        let (rs, prios, ranked) =
            rules::collect_ranked(&def, &m, &fgen.fns, &[]).unwrap_or_else(|e| fail(&e));
        if ranked || prios.len() > 1 {
            fail("rules of several priorities are not supported");
        }
        rs
    } else {
        vec![]
    };
    Lib {
        def,
        m,
        fns: fgen.fns,
        fn_text: fgen.lean,
        rules,
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
        conds.push(ren.prop_arg(&qp)?);
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

/// The Lean types reachable from `roots` in `A`'s term universe whose translation is a
/// generated function `tr_…` of a plain sort (or of its own constructors).
pub(crate) fn tr_names(m: &Model, roots: &[String]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut todo: Vec<String> = roots.to_vec();
    let mut out = Vec::new();
    while let Some(s) = todo.pop() {
        if !seen.insert(s.clone()) {
            continue;
        }
        let Some(info) = m.sorts.get(&s) else {
            continue;
        };
        if !matches!(info.kind, Kind::Plain) {
            continue;
        }
        out.push(format!("tr_{}", terms::fsuffix(&s)));
        if !info.is_simple() {
            if !info.own.is_empty() {
                out.push(format!("tr_{}", terms::fsuffix(&format!("{s}.Own"))));
            }
            todo.extend(info.leaves.iter().filter(|l| **l != s).cloned());
        }
        for c in &info.own {
            todo.extend(m.ctors[c].args.iter().cloned());
        }
    }
    out.sort();
    out.dedup();
    out
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

/// One cooling rule: `HOLE ~> f(args) => item` (in `A`'s names, unqualified).
pub(crate) struct Cool {
    frz: String,
    pats: Vec<String>,
    binds: Vec<(String, String, String)>,
    hole: String,
    hole_sort: String,
    item: String,
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
    for (_, p) in &r.step.hyps {
        if let Some((s, y, x)) = proj_hyp(p) {
            if y == *hv {
                hole = Some((x, s));
            } else {
                binds.push((s, y, x));
            }
        } else if !p.contains("isKResult") {
            fail(&format!(
                "the cooling rule {} has a side condition other than the hole's: {p}",
                r.name
            ));
        }
    }
    let (hole, hole_sort) = hole?;
    // a freezer argument whose item the rule's substitution destructed (`kseq (inj_L x) dotk`) is
    // matched as `kseq y dotk` and projected, as the arguments the rule projects already are
    let taken: BTreeSet<String> = r.step.binders.iter().map(|(b, _)| b.clone()).collect();
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
    })
}

struct Opts {
    tr_module: String,
    hand_module: String,
    hand_ns: String,
    store_cells: Vec<String>,
    store_typing: Vec<String>,
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
    let wanted = list("typing");
    if wanted.is_empty() {
        fail("--typing is required");
    }
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
    let a = load(&get("kore-a"), &get("name-a"), true, &[]);
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
    };
    if o.store_cells.len() != o.store_typing.len() {
        fail("--store-typing names one typing per --store-cell");
    }
    let (typing, sound) = generate(&a, &b, &syms, &ns, &o);
    write_file(&get("out-typing"), &typing);
    write_file(&get("out-soundness"), &sound);
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
    let [prog] = accept.as_slice() else {
        fail("exactly one Bool-valued typing function (it accepts programs) is expected")
    };
    let cx = Ctx {
        a,
        b,
        tfs: &tfs,
        ty_sort: ty_sort.clone(),
        ext: false,
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
    let trs = tr_names(
        &a.m,
        &tfs.iter().map(|f| f.sort.clone()).collect::<Vec<_>>(),
    );
    let convs: Vec<String> = tfs
        .iter()
        .map(|f| format!("(conv => lhs; rw [{}.eq_def])", f.lean_b))
        .collect();
    writeln!(
        t,
        "\n/-- An inversion lemma: unfold the checker's function once at the left-hand side, case on the\nvalues of the typing functions, and compute. -/\nmacro \"k2l_ty_inv\" : tactic => `(tactic| (\n  simp only [{}, {}]\n  first\n    | {}\n  try simp only []\n  try k2l_cases_apps [{}]\n  all_goals simp_all [KEqHook.eq, BoolHook.and]))\n",
        fnames.join(", "),
        trs.join(", "),
        convs.join("\n    | "),
        tfs.iter().map(|f| f.lean_b.clone()).collect::<Vec<_>>().join(", ")
    )
    .unwrap();
    let mut inv_names = Vec::new();
    let mut skipped = Vec::new();
    let mut dflt: BTreeMap<String, String> = BTreeMap::new();
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
    for s in &skipped {
        eprintln!("soundness: no inversion lemma for {s}");
    }
    // ---- runtime typing
    let TopCells {
        top,
        top_ctor,
        cells,
        kpos,
    } = top_cells(a);
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
    let top_path = format!("{na}.{}", a.m.ctor_path(&top_ctor));
    // cooling rules → plug
    let (cools, hole_sort) = coolings(a, kpos);
    let ty_fn = tfs
        .iter()
        .find(|f| !f.accepts && f.sort == hole_sort)
        .unwrap_or_else(|| {
            fail(&format!(
                "no typing function types the holes' sort {hole_sort}"
            ))
        });
    t.push_str("\n/-! ## 2. The typing of `<k>` -/\n\n");
    writeln!(
        t,
        "/-- A value of each type (the checker's equations at value sorts). -/\ndef dflt : Ty → {}",
        ty(na, &hole_sort)
    )
    .unwrap();
    for c in &ty_ctors {
        let v = dflt.get(c).unwrap_or_else(|| {
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
    let projs = plug_def(a, &cools, &hole_sort, &mut t);
    // item0
    let kitem = a.m.sort("SortKItem");
    let mut item_arms: Vec<(String, String, String, String)> = Vec::new(); // (leaf, ctor, arg type, rhs)
    let typed_leaf = |l: &str| -> Option<&TFn> {
        let fs: Vec<&TFn> = tfs
            .iter()
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
/-- A well-typed continuation: each item consumes what the previous one leaves, and nothing is\nleft at the end. -/\ndef kty (G : TEnv) : Option Ty → {na}.SortK → Bool\n  | i, .dotk => i.isNone\n  | i, .kseq it k => match item G i it with\n    | some o => kty G o k\n    | none => false\n\nattribute [k2l_pres] dflt plug\n",
        kitem_t = ty(na, "SortKItem")
    )
    .unwrap();
    for (l, c, lt, rhs) in &item_arms {
        writeln!(
            t,
            "@[k2l_pres] theorem item0_inj_{} (G : TEnv) (x : {lt}) : item0 G ({c} x) = {rhs} := rfl",
            names::short_sort(l)
        )
        .unwrap();
    }
    writeln!(
        t,
        "@[k2l_pres] theorem item0_inj_KItem (G : TEnv) (x : {kitem_own}) : item0 G ({na}.SortKItem.inj_KItem x) = none := rfl"
    )
    .unwrap();
    for f in &tfs {
        let s = &f.sort;
        let inj = format!("{na}.inj_{}_KItem", names::short_sort(s));
        let proof = if a.m.sort(s).is_simple() {
            "rfl"
        } else {
            "by cases x <;> rfl"
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
    writeln!(
        t,
        "@[k2l_pres] theorem item_none (G : TEnv) (it : {kitem_t}) : item G none it = item0 G it := by cases it <;> rfl\n\
@[k2l_pres] theorem item_frz (G : TEnv) (t : Ty) (f : {kitem_own}) : item G (some t) ({na}.SortKItem.inj_KItem f) = (plug f (dflt t)).bind (item0 G) := rfl\n\
@[k2l_pres] theorem kty_dotk (G : TEnv) (i : Option Ty) : kty G i .dotk = i.isNone := rfl\n\
@[k2l_pres] theorem kty_kseq (G : TEnv) (i : Option Ty) (it : {kitem_t}) (k : {na}.SortK) :\n    kty G i (.kseq it k) = (match item G i it with | some o => kty G o k | none => false) := rfl\n\
@[k2l_pres] theorem {}_dflt (G : TEnv) (t : Ty) : {} G (dflt t) = some t := by\n  cases t <;> simp only [dflt, {}]\n",
        ty_fn.name,
        ty_fn.name,
        value_lemmas.join(", "),
        kitem_t = ty(na, "SortKItem")
    )
    .unwrap();
    let proj_lemmas: Vec<String> = projs
        .iter()
        .chain(std::iter::once(
            &hole_sort.trim_start_matches("Sort").to_string(),
        ))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|s| format!("{na}.proj_inj_KItem_{s}"))
        .collect();
    writeln!(t, "attribute [k2l_pres] {}\n", proj_lemmas.join(" ")).unwrap();
    // configurations
    t.push_str("/-! ## 3. The typing of a configuration -/\n\n");
    let top_t = ty(na, &top);
    let pat_at = |i: usize, p: &str| -> String {
        let ps: Vec<String> = (0..cells.len())
            .map(|j| if j == i { p.to_string() } else { "_".into() })
            .collect();
        format!("{top_path} {}", ps.join(" "))
    };
    writeln!(
        t,
        "/-- The content of `<k>`. -/\ndef kOf : {top_t} → {na}.SortK\n  | {} => k",
        pat_at(kpos, &format!("({} k)", cells[kpos].ctor))
    )
    .unwrap();
    let st_name = |i: usize| -> String {
        if store.len() == 1 {
            "St".into()
        } else {
            format!("St_{}", names::ident(&cells[store[i]].label))
        }
    };
    let mut heads_pres = vec!["kOf".to_string()];
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
    writeln!(
        t,
        "/-- A well-typed configuration: `<k>` is a well-typed continuation that leaves nothing, and each\ncell typed by hand is typed by its typing. -/\ndef WTc {st_bs}(G : TEnv) (c : {top_t}) : Prop :=\n  {}\n",
        conj.join(" ∧ ")
    )
    .unwrap();
    writeln!(
        t,
        "/-- A terminated configuration: nothing left in `<k>`. -/\ndef Final : {top_t} → Prop\n  | {} => True\n  | _ => False\n",
        pat_at(kpos, &format!("({} .dotk)", cells[kpos].ctor))
    )
    .unwrap();
    // init
    let mut init_bs = vec![format!("(P : {})", ty(na, &prog.sort))];
    let mut init_args = Vec::new();
    let mut store_vars = Vec::new();
    let mut other_vars = Vec::new();
    let pitem = if kitem.leaves.contains(&prog.sort) && a.m.sort(&prog.sort).is_simple() {
        format!("{na}.{} P", a.m.leaf_ctor("SortKItem", &prog.sort))
    } else {
        format!("{na}.inj_{}_KItem P", names::short_sort(&prog.sort))
    };
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
    writeln!(
        t,
        "/-- The initial configuration of program `P`: `<k>` holds `P`, each cell typed by hand holds its\nparameter, and every other cell is a parameter. -/\ndef init {} : {top_t} :=\n  {top_path} {}\n",
        init_bs.join(" "),
        init_args.join(" ")
    )
    .unwrap();
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
            "/-- Progress at the left-hand side of rule {}, which reads a cell typed by\nhand: a well-typed configuration of that shape has a rule that applies. -/\ndef Progress.Case.{} {st_bs}: Prop :=\n  ∀ {},\n    WTc {st_ps} G {cfg} →\n    {na}.App {cfg}\n",
            rules::doc(r),
            r.lean,
            bs.join(" ")
        )
        .unwrap();
        prog_hand.insert(leaf_sort, (r.lean.clone(), call_args));
    }
    let mut guard = inv_names.clone();
    guard.push(format!("{}_dflt", ty_fn.name));
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
        "/-! ## Preservation -/\n\n/-- The runtime typing is preserved by every rule of `{na}`. -/\ntheorem preserved (G : TEnv) : Preserved {na}.Step ({wtc} G) := by\n  k2l_preserve split [{}] hand {}\n\ntheorem preservation {{G : TEnv}} {{c c' : {top_t}}} (h : {na}.Step c c') :\n    {wtc} G c → {wtc} G c' :=\n  fun hw => preserved G c c' hw h\n",
        fnames.join(", "),
        o.hand_ns
    )
    .unwrap();
    // progress tactics
    let projs_all: BTreeSet<String> = projs
        .iter()
        .cloned()
        .chain(std::iter::once(
            hole_sort.trim_start_matches("Sort").to_string(),
        ))
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
    let hole_short = hole_sort.trim_start_matches("Sort");
    close_unfold.insert(format!("{na}.inj_{hole_short}_KItem"));
    let mut close_list: Vec<String> = close_unfold.into_iter().collect();
    close_list.extend(["BoolHook.and".to_string(), "BoolHook.not".to_string()]);
    writeln!(
        s,
        "/-! ## Progress -/\n\n\
/-- Compute the typing of `<k>` (with the hypotheses, which record the cases taken); a typing that\n\
computes to `false` is `false = true`, `False`, and closes the goal `typing → App c`. -/\n\
macro \"ty_simp\" : tactic => `(tactic| simp only [k2l_pres, item, item0, WTc, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none, Option.isNone_some, Option.isNone_none, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, ite_true, ite_false, ↓reduceIte, and_self, and_true, true_and, Bool.false_eq_true, false_implies, *])\n\n\
/-- An ill-typed shape: the typing of `<k>` computes to `false`. -/\n\
macro \"prog_absurd\" : tactic => `(tactic| (ty_simp; done))\n\n\
/-- A side condition of a rule: by unification, an assumption, or by computing it. -/\n\
macro \"prog_close\" : tactic => `(tactic| first | rfl | assumption | exact {na}.proj_inj_KItem_{hole_short} _ | (simp_all [{}]; done))\n\n\
/-- The variables of sorted projections, substituted. -/\n\
macro \"prog_proj\" : tactic => `(tactic| (simp only [{}] at *; subst_vars))\n\n\
/-- What the typing of the head depends on: the sort projections of variables, the typing functions. -/\n\
macro \"prog_cases\" : tactic => `(tactic| k2l_cases_typing [{}] [{}] => (try ty_simp))\n\n\
/-- One shape of the head of `<k>`: case on what its typing depends on, then find the rule. -/\n\
macro \"prog_leaf\" : tactic => `(tactic| (prog_cases; all_goals (intro _hk; (try prog_proj); k2l_cases_bools; all_goals k2l_ctor_search {na}.App => prog_close)))\n",
        close_list.join(", "),
        proj_eqs.join(", "),
        proj_fns.join(", "),
        fnames.join(", ")
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
    writeln!(
        s,
        "theorem progress {{G : TEnv}} (c : {top_t}) (hw : {wtc} G c) : Final c ∨ {na}.App c := by\n  obtain ⟨{}⟩ := c\n  cases k with\n  | dotk => exact Or.inl trivial\n  | kseq it K =>\n    right\n    obtain ⟨{hw_pat}⟩ := hw\n    simp only [{}] at hk{he_at}\n    revert hk\n    cases it",
        obt.join(", "),
        unf.join(", ")
    )
    .unwrap();
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
    if !values.is_empty() {
        let cs: Vec<String> = values
            .iter()
            .map(|l| format!("inj_{} x", names::short_sort(l)))
            .collect();
        writeln!(
            s,
            "    -- a value: the next item is a freezer waiting for it (a cooling rule applies)\n    case {} =>\n      cases K with\n      | dotk => prog_absurd\n      | kseq it₂ K₂ =>\n        cases it₂ <;> (try prog_absurd)\n        rename_i f\n        cases f <;> (try prog_absurd) <;>\n          (k2l_cases_frz [{na}.SortKItem.inj_KItem] [{na}.SortK] => prog_absurd) <;> prog_leaf",
            cs.join(" | ")
        )
        .unwrap();
    }
    // the heads of rules that read a cell typed by hand
    for (leaf, (rule, call_args)) in &prog_hand {
        let hw_args = std::iter::once("hk".to_string())
            .chain(he_names.iter().cloned())
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            s,
            "    -- the head of rule {rule}, which reads a cell typed by hand\n    case inj_{} x => exact fun hk => hand.progress.{rule} {} ⟨{hw_args}⟩",
            names::short_sort(leaf),
            call_args.join(" ")
        )
        .unwrap();
    }
    // typed leaves: case on the constructor and the operands
    let own_typed: Vec<String> = kitem
        .leaves
        .iter()
        .filter(|l| typed_leaf(l).is_some() && !a.m.sort(l).own.is_empty())
        .map(|l| format!("{na}.{}", a.m.leaf_ctor("SortKItem", l)))
        .collect();
    for l in &kitem.leaves {
        if typed_leaf(l).is_none() || values.contains(l) || prog_hand.contains_key(l) {
            continue;
        }
        let short = names::short_sort(l);
        if a.m.sort(l).own.is_empty() {
            writeln!(s, "    case inj_{short} x => prog_leaf").unwrap();
        } else {
            writeln!(
                s,
                "    case inj_{short} x =>\n      cases x <;> k2l_cases_args [{}] [{}] <;> prog_leaf",
                own_typed.join(", "),
                ty(na, &hole_sort)
            )
            .unwrap();
        }
    }
    s.push_str("    all_goals prog_absurd\n\n");
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
    let init_call = init_call.join(" ");
    let wt_init_he = std::iter::once("by simp [init, k2l_pres, hP]".to_string())
        .chain(he_args.iter().cloned())
        .collect::<Vec<_>>()
        .join(", ");
    writeln!(
        s,
        "/-! ## Soundness -/\n\n\
theorem wt_init {{G : TEnv}} {} (hP : {} G P = some true) {} :\n    {wtc} G (init {init_call}) :=\n  ⟨{wt_init_he}⟩\n\n\
theorem wt_stepsN {{G : TEnv}} : ∀ {{n : Nat}} {{c c' : {top_t}}},\n    StepsN {na}.Step n c c' → {wtc} G c → {wtc} G c'\n  | _, _, _, .refl _, h => h\n  | _, _, _, .step hs rest, h => wt_stepsN rest (preservation hs h)\n\n\
/-- **Type soundness.** A program that the type checker accepts, started with cells typed by\nhand by their typings, never gets stuck: every reachable configuration has terminated or has a\nrule that applies (a step, or an undefined result). -/\n\
theorem soundness {{G : TEnv}} {}\n    (hP : {} (tr_{} P) G = some true) {}\n    {{n : Nat}} {{c : {top_t}}} (h : StepsN {na}.Step n (init {init_call}) c) :\n    Final c ∨ {na}.App c :=\n  progress c (wt_stepsN h (wt_init hP {}))\n\n\
#k2l_assert_axioms preserved preservation progress wt_init wt_stepsN soundness\n\nend {ns}",
        implicit.join(" "),
        prog.name,
        he_bs.join(" "),
        implicit.join(" "),
        prog.lean_b,
        terms::fsuffix(&prog.sort),
        he_bs.join(" "),
        he_args.join(" ")
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
