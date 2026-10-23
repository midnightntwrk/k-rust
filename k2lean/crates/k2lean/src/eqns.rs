//! K equations and simplification rules as Lean theorems about the generated definitions and
//! the hook library: proving every equation of the theory about a concrete
//! Lean model shows the theory, restricted to these symbols, is consistent; a simplification
//! rule that cannot be proved is either unsound or needs real mathematics.
//!
//! An equation `φ → f(p̄) = r` is stated over the variables of `p̄`, `φ` and `r`. Partial
//! subterms make both sides `Option`-valued (`⊥` is `none`; matching logic's `\equals` holds
//! between two `⊥`s). An `owise` equation also assumes that no competing equation applies.

use crate::funcs::Equation;
use crate::ir::{Def, P, S};
use crate::lower::{Fns, L, Lower, Step};
use crate::model::Model;
use crate::names;
use std::collections::{BTreeMap, BTreeSet};

pub struct Stated {
    pub name: String,
    pub statement: String,
    pub what: String,
    /// Definitions to unfold in the goal first (the generated function and its equations).
    pub unfold_first: Vec<String>,
}

fn vars_of(p: &P, out: &mut BTreeMap<String, S>) {
    match p {
        P::Var(n, s) => {
            out.insert(n.clone(), s.clone());
        }
        P::App(_, _, args) | P::And(_, args) | P::Or(_, args) => {
            args.iter().for_each(|a| vars_of(a, out))
        }
        P::Not(_, a) | P::Ceil(_, _, a) | P::Floor(_, _, a) => vars_of(a, out),
        P::Equals(_, _, a, b) | P::In(_, _, a, b) | P::Implies(_, a, b) | P::Iff(_, a, b) => {
            vars_of(a, out);
            vars_of(b, out);
        }
        P::Exists(_, v, _, b) | P::Forall(_, v, _, b) => {
            let mut inner = BTreeMap::new();
            vars_of(b, &mut inner);
            inner.remove(v);
            out.extend(inner);
        }
        _ => {}
    }
}

/// Render a term whose lowering pushed `Bind` steps as an `Option` expression.
fn option_expr(steps: &[Step], value: &L) -> Option<String> {
    let mut e = format!("some {}", value.render_arg());
    for s in steps.iter().rev() {
        match s {
            Step::Bind { expr, var, .. } => {
                e = format!("(Option.bind {} fun {var} => {e})", expr.render_arg())
            }
            _ => return None,
        }
    }
    Some(e)
}

pub fn equation_theorems(
    def: &Def,
    m: &Model,
    fns: &Fns,
    eqs: &BTreeMap<String, Vec<Equation>>,
) -> Vec<Stated> {
    let mut out = Vec::new();
    for (f, es) in eqs {
        let Some(sig) = fns.get(f) else { continue };
        if sig.args.iter().any(|a| a == "?") {
            continue;
        }
        let comps: Vec<&Equation> = es.iter().filter(|e| !e.owise).collect();
        for (i, e) in es.iter().enumerate() {
            let what = format!("{} equation {}", names::demangle(f), i + 1);
            let unfold_first = if sig.lean.starts_with("K.") {
                let mut v = vec![sig.lean.clone()];
                for k in 1..=es.len() {
                    v.push(format!("{}.rule{k}", sig.lean));
                }
                v
            } else {
                vec![]
            };
            match state_one(def, m, fns, f, sig, e, if e.owise { &comps } else { &[] }) {
                Ok(statement) => out.push(Stated {
                    name: format!(
                        "Eqn.{}",
                        names::ident(&format!("{}_{}", names::demangle(f), i + 1))
                    ),
                    statement,
                    what,
                    unfold_first,
                }),
                Err(err) => eprintln!("note: {what} not stated: {err}"),
            }
        }
    }
    out
}

fn bind_vars(
    lw: &mut Lower,
    vars: &BTreeMap<String, S>,
    prefix: &str,
) -> Result<Vec<(String, String)>, String> {
    let mut binders = Vec::new();
    for (v, s) in vars {
        let sort = s.name().ok_or("parametric variable sort")?.to_string();
        if !m_has(lw, &sort) {
            return Err(format!("variable of unsupported sort {sort}"));
        }
        let base = format!("{prefix}{}", sanitize(v));
        let n = lw.param(&base, &sort);
        lw.vars.insert(v.clone(), n.clone());
        binders.push((n, sort));
    }
    Ok(binders)
}

fn m_has(lw: &Lower, sort: &str) -> bool {
    lw.m.sorts.contains_key(sort)
}

fn sanitize(v: &str) -> String {
    let d = names::demangle(v);
    let d = d.strip_prefix("Var").unwrap_or(&d).to_string();
    let s: String = d
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    let s = s.trim_matches('_').to_string();
    if s.is_empty() || s.chars().next().unwrap().is_ascii_digit() {
        format!("v{s}")
    } else {
        s
    }
}

fn cond_props(lw: &mut Lower, requires: &[P]) -> Result<Vec<String>, String> {
    let mut props = Vec::new();
    for r in requires {
        let start = lw.steps.len();
        lw.cond(r)?;
        let new: Vec<Step> = lw.steps[start..].to_vec();
        lw.steps.truncate(start);
        // the last step is the condition; earlier ones are partial calls inside it
        let (last, binds) = new.split_last().ok_or("empty requires")?;
        let (lhs, rhs) = match last {
            Step::Cond { cond, .. } => (cond.clone(), L::Raw("true".into())),
            Step::CondEq { lhs, rhs, .. } => (lhs.clone(), rhs.clone()),
            _ => return Err("unexpected requires shape".into()),
        };
        if binds.is_empty() {
            props.push(format!("{} = {}", lhs.render(), rhs.render()));
        } else {
            let oe = option_expr(binds, &lhs).ok_or("requires with a non-call step")?;
            props.push(format!("{oe} = some {}", rhs.render_arg()));
        }
    }
    Ok(props)
}

/// `\and(t, V)` (an `#as` pattern) in a term position: the value is `t`, also named `V`.
fn strip_as(p: &P, subst: &mut BTreeMap<String, P>) -> P {
    match p {
        P::And(_, ps) if ps.len() == 2 => {
            let (vars, terms): (Vec<&P>, Vec<&P>) =
                ps.iter().partition(|q| matches!(q, P::Var(..)));
            match (vars.as_slice(), terms.as_slice()) {
                ([P::Var(v, _)], [t]) => {
                    let t = strip_as(t, subst);
                    subst.insert(v.clone(), t.clone());
                    t
                }
                _ => p.clone(),
            }
        }
        P::App(f, sp, args) => P::App(
            f.clone(),
            sp.clone(),
            args.iter().map(|a| strip_as(a, subst)).collect(),
        ),
        other => other.clone(),
    }
}

fn subst_vars(p: &P, subst: &BTreeMap<String, P>) -> P {
    match p {
        P::Var(v, _) => subst.get(v).cloned().unwrap_or_else(|| p.clone()),
        P::App(f, sp, args) => P::App(
            f.clone(),
            sp.clone(),
            args.iter().map(|a| subst_vars(a, subst)).collect(),
        ),
        P::And(s, ps) => P::And(s.clone(), ps.iter().map(|a| subst_vars(a, subst)).collect()),
        P::Equals(a, b, l, r) => P::Equals(
            a.clone(),
            b.clone(),
            Box::new(subst_vars(l, subst)),
            Box::new(subst_vars(r, subst)),
        ),
        other => other.clone(),
    }
}

fn state_one(
    _def: &Def,
    m: &Model,
    fns: &Fns,
    _f: &str,
    sig: &crate::lower::FnSig,
    e: &Equation,
    comps: &[&Equation],
) -> Result<String, String> {
    let mut lw = Lower::new(m, fns, &[]);
    let mut asv = BTreeMap::new();
    let e_args: Vec<P> = e.args.iter().map(|a| strip_as(a, &mut asv)).collect();
    let e_requires: Vec<P> = e.requires.iter().map(|r| subst_vars(r, &asv)).collect();
    let e_rhs = subst_vars(&e.rhs, &asv);
    let mut vars = BTreeMap::new();
    for a in &e_args {
        vars_of(a, &mut vars);
    }
    for r in &e_requires {
        vars_of(r, &mut vars);
    }
    vars_of(&e_rhs, &mut vars);
    let binders = bind_vars(&mut lw, &vars, "")?;
    let mut args = Vec::new();
    for (a, s) in e_args.iter().zip(&sig.args) {
        args.push(lw.expr(a, s)?);
    }
    if !lw.steps.is_empty() {
        return Err("a partial function in an argument pattern".into());
    }
    let hyps = cond_props(&mut lw, &e_requires)?;
    let rhs = lw.expr(&e_rhs, &sig.result)?;
    let rhs_steps = std::mem::take(&mut lw.steps);
    let call = L::app(sig.lean.clone(), args.clone()).render();
    let concl = match (sig.partial, rhs_steps.is_empty()) {
        (false, true) => format!("{call} = {}", rhs.render()),
        (true, true) => format!("{call} = some {}", rhs.render_arg()),
        (true, false) => format!("{call} = {}", option_expr(&rhs_steps, &rhs).ok_or("rhs")?),
        (false, false) => format!(
            "some ({call}) = {}",
            option_expr(&rhs_steps, &rhs).ok_or("rhs")?
        ),
    };
    // the owise guard: no competitor applies at these arguments
    let mut guards = Vec::new();
    for (j, c) in comps.iter().enumerate() {
        let mut lc = Lower::new(m, fns, &[]);
        let mut cv = BTreeMap::new();
        for a in &c.args {
            vars_of(a, &mut cv);
        }
        for r in &c.requires {
            vars_of(r, &mut cv);
        }
        let cb = bind_vars(&mut lc, &cv, &format!("o{j}_"))?;
        // the guard's own variables must not capture the equation's: rename the equation's args
        // into the competitor's Lower by rendering them as raw text
        let mut eqs = Vec::new();
        for (a, s) in c.args.iter().zip(&sig.args) {
            let ca = lc.expr(a, s)?;
            let _ = s;
            eqs.push(ca);
        }
        if !lc.steps.is_empty() {
            return Err("owise competitor with a partial argument".into());
        }
        let ch = cond_props(&mut lc, &c.requires)?;
        let mut body: Vec<String> = args
            .iter()
            .zip(&eqs)
            .map(|(x, y)| format!("{} = {}", x.render(), y.render()))
            .collect();
        body.extend(ch);
        let quant: Vec<String> = cb.iter().map(|(n, t)| format!("({n} : {t})")).collect();
        let q = if quant.is_empty() {
            String::new()
        } else {
            format!("∀ {}, ", quant.join(" "))
        };
        guards.push(format!("{q}{} → False", body.join(" → ")));
    }
    let mut stmt = String::new();
    for (n, t) in &binders {
        stmt.push_str(&format!(" ({n} : {t})"));
    }
    for (k, h) in hyps.iter().enumerate() {
        stmt.push_str(&format!("\n    (hreq{k} : {h})"));
    }
    for (k, g) in guards.iter().enumerate() {
        stmt.push_str(&format!("\n    (howise{k} : {g})"));
    }
    stmt.push_str(&format!(" :\n    {concl}"));
    Ok(stmt)
}

/// Simplification rules (`[simplification]` axioms), stated the same way.
pub fn simplification_theorems(def: &Def, m: &Model, fns: &Fns) -> Vec<Stated> {
    let mut out = Vec::new();
    for (idx, a) in def.axioms.iter().enumerate() {
        if !a.attrs.has("simplification") {
            continue;
        }
        let what = format!(
            "simplification {} ({})",
            a.attrs
                .string("UNIQUE'Unds'ID")
                .map(|u| u[..12.min(u.len())].to_string())
                .unwrap_or_default(),
            a.attrs
                .string("org'Stop'kframework'Stop'attributes'Stop'Source")
                .map(|s| s
                    .rsplit('/')
                    .next()
                    .unwrap_or("")
                    .trim_end_matches(')')
                    .to_string())
                .unwrap_or_default()
        );
        match state_simpl(m, fns, &a.pattern) {
            Ok(st) => {
                // named by the rule's `UNIQUE'Unds'ID` (a digest of the rule), so that a name does not
                // depend on where the rule is in the definition
                let uid = a
                    .attrs
                    .string("UNIQUE'Unds'ID")
                    .map(|u| u[..12.min(u.len())].to_string());
                let name = match uid {
                    Some(u) => format!("Simp.s_{u}"),
                    None => format!("Simp.s{idx}"),
                };
                out.push(Stated {
                    name,
                    statement: st,
                    what,
                    unfold_first: vec![],
                })
            }
            Err(err) => eprintln!("note: {what} not stated: {err}"),
        }
    }
    out
}

/// A matching-logic predicate pattern as a Lean proposition (`\equals` is `=`, `\ceil` of a
/// term is its definedness, the connectives are the propositional ones).
fn prop(lw: &mut Lower, p: &P) -> Result<String, String> {
    Ok(match p {
        P::Top(_) => "True".into(),
        P::Bottom(_) => "False".into(),
        P::Not(_, a) => format!("¬ ({})", prop(lw, a)?),
        P::And(_, ps) => {
            let v: Result<Vec<String>, String> = ps
                .iter()
                .map(|q| prop(lw, q).map(|x| format!("({x})")))
                .collect();
            v?.join(" ∧ ")
        }
        P::Or(_, ps) => {
            let v: Result<Vec<String>, String> = ps
                .iter()
                .map(|q| prop(lw, q).map(|x| format!("({x})")))
                .collect();
            v?.join(" ∨ ")
        }
        P::Equals(os, _, a, b) => {
            let sort = os.name().ok_or("parametric operand sort")?.to_string();
            let start = lw.steps.len();
            let la = lw.expr(a, &sort)?;
            let sa: Vec<Step> = lw.steps.drain(start..).collect();
            let lb = lw.expr(b, &sort)?;
            let sb: Vec<Step> = lw.steps.drain(start..).collect();
            if sa.is_empty() && sb.is_empty() {
                format!("{} = {}", la.render(), lb.render())
            } else {
                format!(
                    "{} = {}",
                    option_expr(&sa, &la).ok_or("lhs")?,
                    option_expr(&sb, &lb).ok_or("rhs")?
                )
            }
        }
        P::Ceil(os, _, a) => {
            let sort = os.name().ok_or("parametric operand sort")?.to_string();
            let start = lw.steps.len();
            let la = lw.expr(a, &sort)?;
            let sa: Vec<Step> = lw.steps.drain(start..).collect();
            if sa.is_empty() {
                "True".into()
            } else {
                format!("({}).isSome = true", option_expr(&sa, &la).ok_or("ceil")?)
            }
        }
        other => return Err(format!("predicate {}", crate::lower::short_dbg(other))),
    })
}

fn state_simpl(m: &Model, fns: &Fns, p: &P) -> Result<String, String> {
    let (req, eq) = match p {
        P::Implies(_, l, r) => (Some(&**l), &**r),
        other => (None, other),
    };
    let P::Equals(os, _, lhs, rhs) = eq else {
        return Err("not an equation".into());
    };
    if os.name().is_none() {
        // an equivalence of predicates
        let rhs = match &**rhs {
            P::And(_, parts) if parts.len() == 2 && matches!(parts[1], P::Top(_)) => &parts[0],
            other => other,
        };
        let mut lw = Lower::new(m, fns, &[]);
        let mut vars = BTreeMap::new();
        vars_of(lhs, &mut vars);
        vars_of(rhs, &mut vars);
        if let Some(r) = req {
            vars_of(r, &mut vars);
        }
        let binders = bind_vars(&mut lw, &vars, "")?;
        let hyp = match req {
            Some(r) if !matches!(r, P::Top(_)) => Some(prop(&mut lw, r)?),
            _ => None,
        };
        let l = prop(&mut lw, lhs)?;
        let r = prop(&mut lw, rhs)?;
        let mut stmt = String::new();
        for (n, t) in &binders {
            stmt.push_str(&format!(" ({n} : {t})"));
        }
        if let Some(h) = hyp {
            stmt.push_str(&format!("\n    (hreq0 : {h})"));
        }
        stmt.push_str(&format!(" :\n    ({l}) ↔ ({r})"));
        return Ok(stmt);
    }
    let sort = os.name().ok_or("parametric equation sort")?.to_string();
    let rhs = match &**rhs {
        P::And(_, parts) if parts.len() == 2 && matches!(parts[1], P::Top(_)) => &parts[0],
        other => other,
    };
    let mut requires = Vec::new();
    if let Some(r) = req {
        let mut conj = Vec::new();
        crate::funcs::flatten_and(r, &mut conj);
        for c in conj {
            match c {
                P::Top(_) => {}
                P::Equals(..) => requires.push(c.clone()),
                other => return Err(format!("requires {}", crate::lower::short_dbg(other))),
            }
        }
    }
    let mut lw = Lower::new(m, fns, &[]);
    let mut vars = BTreeMap::new();
    vars_of(lhs, &mut vars);
    vars_of(rhs, &mut vars);
    for r in &requires {
        vars_of(r, &mut vars);
    }
    let binders = bind_vars(&mut lw, &vars, "")?;
    let hyps = cond_props(&mut lw, &requires)?;
    let l = lw.expr(lhs, &sort)?;
    let lsteps = std::mem::take(&mut lw.steps);
    let r = lw.expr(rhs, &sort)?;
    let rsteps = std::mem::take(&mut lw.steps);
    let concl = if lsteps.is_empty() && rsteps.is_empty() {
        format!("{} = {}", l.render(), r.render())
    } else {
        format!(
            "{} = {}",
            option_expr(&lsteps, &l).ok_or("lhs")?,
            option_expr(&rsteps, &r).ok_or("rhs")?
        )
    };
    let mut stmt = String::new();
    for (n, t) in &binders {
        stmt.push_str(&format!(" ({n} : {t})"));
    }
    for (k, h) in hyps.iter().enumerate() {
        stmt.push_str(&format!("\n    (hreq{k} : {h})"));
    }
    stmt.push_str(&format!(" :\n    {concl}"));
    Ok(stmt)
}

/// The proposition of a theorem statement ` BINDERS :\n    CONCLUSION`, as the body of a `Prop`
/// definition: `∀ BINDERS, CONCLUSION`, or the conclusion alone when there are no binders.
/// The binders and the conclusion are split first, so that a conclusion starting with `(` is not
/// mistaken for a binder.
fn open_statement(statement: &str) -> String {
    let join = |t: &str| t.replace("\n    (", " (");
    match statement.split_once(" :\n    ") {
        Some((binders, concl)) if binders.trim().is_empty() => format!(" {}", join(concl)),
        // a conclusion starting with `(` joins the binders' line
        Some((binders, concl)) => format!("∀{}", join(&format!("{binders},\n    {concl}"))),
        None => {
            let body = join(statement);
            if body.starts_with(" (") || body.starts_with(" {") {
                format!("∀{body}")
            } else {
                format!(" {}", body.trim_start_matches(':').trim_start())
            }
        }
    }
}

/// `emit_with` without list-recursive functions.
#[cfg(test)]
fn emit(
    ns: &str,
    stated: &[Stated],
    open: &BTreeSet<String>,
    unfold: &[String],
    recursive: &BTreeSet<String>,
) -> String {
    emit_with(ns, stated, open, &[], unfold, recursive, &BTreeSet::new())
}

/// The definitions a theorem's proof may unfold: those its statement names, with their rule
/// helpers (`f.rule1`, …), and the definitions its `unfold_first` lists. A simp set with every
/// generated definition makes Lean generate the equation lemmas of all of them in this module,
/// for an imported definition under the default heartbeat limit, whatever this file sets; on a
/// large definition (KEVM: 886 names) one of those generations exceeds it, which failed every
/// proof that reached `simp`.
fn own_defs<'a>(s: &Stated, defs: &'a [String]) -> Vec<&'a str> {
    defs.iter()
        .filter(|d| {
            s.statement.contains(d.as_str())
                || s.unfold_first.iter().any(|u| u == *d)
                || d.rsplit_once(".rule").is_some_and(|(f, k)| {
                    k.chars().all(|c| c.is_ascii_digit()) && s.statement.contains(f)
                })
        })
        .map(|d| d.as_str())
        .collect()
}

/// `Equations.lean`: every stated equation and simplification, proved by the generic tactics or,
/// when it is in `open`, stated as an open obligation. `base` (hook definitions and projection
/// lemmas) is in every proof's simp set; of `defs` (the generated definitions) each proof gets
/// its own (`own_defs`). `recursive` holds the Lean names of the generated functions that are
/// well-founded recursive (`funcs::Generated::recursive`); their equations get the recursive
/// proof (`k2l_eqn_r`), and those of `list_recursive` (recursion on a builtin `List`) also
/// `k2l_fold_eqn`.
pub fn emit_with(
    ns: &str,
    stated: &[Stated],
    open: &BTreeSet<String>,
    base: &[String],
    defs: &[String],
    recursive: &BTreeSet<String>,
    list_recursive: &BTreeSet<String>,
) -> String {
    let fold_import = if list_recursive.is_empty() {
        ""
    } else {
        "import KPrelude.InvFold\n"
    };
    let mut o = format!(
        "import {ns}.Functions\nimport KPrelude.Tactic\n{fold_import}\n/-! Generated by k2lean; do not edit.\n\n\
K's function equations and simplification rules, as theorems about the generated definitions and\n\
the hook library. A statement whose generic proof attempt failed is kept as an open obligation\n\
(a `Prop` definition, not an axiom). -/\n\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\nset_option maxHeartbeats 400000\nset_option maxRecDepth 100000\n\nnamespace {ns}\n\nopen KPrelude\n\n"
    );
    // the generic proofs, defined once with the shared simp lemmas; a theorem's script passes
    // the definitions it may unfold
    let u = if base.is_empty() {
        "$xs,*".to_string()
    } else {
        format!("{}, $xs,*", base.join(", "))
    };
    o.push_str(&format!(
        "/-- The generic proof attempts without case splits. -/\nlocal macro \"k2l_eqn_a\" \" [\" xs:Lean.Parser.Tactic.simpLemma,* \"]\" : tactic => `(tactic| first\n  | rfl\n  | (simp [{u}]; done)\n  | (simp_all [{u}]; done)\n  | (simp_all [{u}]; omega)\n  | (simp only [{u}]; rw [Bool.eq_iff_iff]; simp_all; done)\n  | (simp only [{u}]; rw [Bool.eq_iff_iff]; simp_all; omega))\n\n\
/-- The generic proof by case splits (equations `x = t` from a split substituted first: `simp_all`\nuses an equation `t = x` only from left to right). -/\nlocal macro \"k2l_eqn_b\" \" [\" xs:Lean.Parser.Tactic.simpLemma,* \"]\" : tactic => `(tactic| ((repeat' (first | split | k2l_split_hyps)) <;> (try subst_vars) <;> simp_all [{u}]))\n\n"
    ));
    // the equations of a recursive function: a well-founded definition, which `simp` cannot unfold
    let rec_of = |s: &Stated| {
        s.unfold_first
            .first()
            .filter(|n| recursive.contains(*n))
            .cloned()
    };
    let rec_fns: BTreeSet<String> = stated.iter().filter_map(rec_of).collect();
    if !rec_fns.is_empty() {
        // `k2l_case_rec` and `k2l_case_discr` are in `KPrelude.Tactic`
        // what the proof cases on: the recursive calls, and the projections out of injections
        // (`proj_Y_X`, named like their `proj_eq_some_Y_X` lemmas), whose `match hp : proj … with`
        // in a cascade `simp` cannot rewrite
        let mut case_on: Vec<String> = rec_fns.iter().cloned().collect();
        case_on.extend(
            base.iter()
                .chain(defs)
                .filter_map(|n| n.strip_prefix("proj_eq_some_"))
                .map(|p| format!("proj_{p}")),
        );
        let r = case_on.join(", ");
        o.push_str(&format!(
            "/-- The generic proof of an equation of a recursive function `f`, which `simp` does not\n\
unfold: unfold `f` once on the left-hand side (`f.eq_def`), reduce the cascade of its equations,\n\
case on the variables that the cascade matches, on the recursive calls and on the projections,\n\
then close each case as the generic tactics do. -/\n\
local macro \"k2l_eqn_r \" f:ident \" [\" xs:Lean.Parser.Tactic.simpLemma,* \"]\" : tactic => do\n  let e := Lean.mkIdent (f.getId.str \"eq_def\")\n  \
`(tactic| (\n    \
(conv => lhs; rw [$e:ident])\n    \
try simp only []\n    \
try (repeat' (first | (k2l_case_discr <;> try simp only []) | (k2l_case_rec [{r}] <;> try simp only [Option.bind])))\n    \
all_goals first\n      \
| (simp_all [{u}]; done)\n      \
| ((repeat' (first | split | k2l_split_hyps)) <;> (try simp_all [{u}]) <;> omega)))\n\n"
        ));
    }
    for s in stated {
        let uf: Vec<&String> = s.unfold_first.iter().filter(|n| defs.contains(n)).collect();
        let first = if uf.is_empty() {
            String::new()
        } else {
            format!(
                "unfold {}; ",
                uf.iter().map(|n| n.as_str()).collect::<Vec<_>>().join(" ")
            )
        };
        let own = own_defs(s, defs).join(", ");
        // the generic tactics do not unfold a well-founded recursive function (none of the 32
        // such equations of SIMPLE and imp-typing closed that way), so its equations get only the
        // recursive proof
        let tac = match rec_of(s) {
            Some(f) if list_recursive.contains(&f) => {
                format!("by\n  intros\n  first\n  | k2l_eqn_r {f} [{own}]\n  | k2l_fold_eqn {f}")
            }
            Some(f) => format!("by\n  intros\n  k2l_eqn_r {f} [{own}]"),
            None => format!(
                "by\n  intros\n  first\n  | k2l_eqn_a [{own}]\n  | ({first}k2l_eqn_b [{own}])"
            ),
        };
        if open.contains(&s.name) {
            let prop = open_statement(&s.statement);
            o.push_str(&format!(
                "/-- Open obligation: {} -/\ndef {}.statement : Prop :={}\n\n",
                s.what, s.name, prop
            ));
        } else {
            o.push_str(&format!(
                "/-- {} -/\ntheorem {}{} := {tac}\n\n",
                s.what, s.name, s.statement
            ));
        }
    }
    o.push_str(&format!("end {ns}\n"));
    o
}

#[cfg(test)]
mod tests {
    //! The proof each equation statement gets: the recursive proof for a recursive function's
    //! equation, the generic tactics (unfolding the function first) otherwise, and no proof at all
    //! (a `Prop` statement) for an open obligation.
    use super::*;

    fn st(name: &str, statement: &str, unfold_first: &[&str]) -> Stated {
        Stated {
            name: name.into(),
            statement: statement.into(),
            what: format!("{name} (test)"),
            unfold_first: unfold_first.iter().map(|s| s.to_string()).collect(),
        }
    }

    fn sample() -> Vec<Stated> {
        vec![
            st(
                "Eqn.f_1",
                " (x : SortNat) :\n    K.f x = some x",
                &["K.f", "K.f.rule1"],
            ),
            st(
                "Eqn.g_1",
                " (x : SortNat)\n    (hreq0 : K.h x = true) :\n    K.g x = x",
                &["K.g", "K.g.rule1"],
            ),
            st(
                "Simp.s_0123456789ab",
                " (b : Bool) :\n    (b && true) = b",
                &[],
            ),
        ]
    }

    #[test]
    fn recursive_equations_get_the_recursive_proof() {
        let rec: BTreeSet<String> = ["K.f".to_string()].into();
        let unfold = vec!["K.g".to_string(), "K.g.rule1".to_string()];
        let o = emit("N", &sample(), &BTreeSet::new(), &unfold, &rec);
        assert!(o.contains("theorem Eqn.f_1 (x : SortNat) :\n    K.f x = some x := by\n  intros\n  k2l_eqn_r K.f []\n"), "{o}");
        assert!(o.contains("local macro \"k2l_eqn_r \" f:ident"));
        // the recursive function is cased on, never unfolded by simp
        assert!(o.contains("k2l_case_rec [K.f]"));
        // a non-recursive function: the generic tactics, unfolding it (and its equations) first
        assert!(o.contains(
            "theorem Eqn.g_1 (x : SortNat)\n    (hreq0 : K.h x = true) :\n    K.g x = x := by\n  intros\n  first\n  | k2l_eqn_a [K.g, K.g.rule1]\n  | (unfold K.g K.g.rule1; k2l_eqn_b [K.g, K.g.rule1])\n"
        ), "{o}");
        // a statement that names no generated definition unfolds none
        assert!(o.contains("theorem Simp.s_0123456789ab (b : Bool) :\n    (b && true) = b := by\n  intros\n  first\n  | k2l_eqn_a []\n  | (k2l_eqn_b [])\n"));
    }

    #[test]
    fn no_recursive_macro_without_recursive_functions() {
        let o = emit("N", &sample(), &BTreeSet::new(), &[], &BTreeSet::new());
        assert!(!o.contains("k2l_eqn_r"), "{o}");
        assert!(o.contains("local macro \"k2l_eqn_a\""));
        assert!(o.contains("local macro \"k2l_eqn_b\""));
        // `K.f` is not in the unfold list, so it is not unfolded first either
        assert!(o.contains("theorem Eqn.f_1 (x : SortNat) :\n    K.f x = some x := by\n  intros\n  first\n  | k2l_eqn_a []\n  | (k2l_eqn_b [])\n"), "{o}");
    }

    #[test]
    fn open_obligations_are_statements_with_their_hypotheses() {
        let open: BTreeSet<String> =
            ["Eqn.g_1".to_string(), "Simp.s_0123456789ab".to_string()].into();
        let o = emit("N", &sample(), &open, &[], &BTreeSet::new());
        assert!(o.contains("/-- Open obligation: Eqn.g_1 (test) -/\ndef Eqn.g_1.statement : Prop :=∀ (x : SortNat) (hreq0 : K.h x = true),\n    K.g x = x\n"), "{o}");
        // a conclusion that starts with `(` is joined to the binders' line
        assert!(
            o.contains(
                "def Simp.s_0123456789ab.statement : Prop :=∀ (b : Bool), (b && true) = b\n"
            ),
            "{o}"
        );
        assert!(!o.contains("theorem Eqn.g_1") && !o.contains("theorem Simp.s_0123456789ab"));
        assert!(o.contains("theorem Eqn.f_1"));
        assert!(!o.contains("sorry") && !o.contains("\naxiom "));
    }

    /// An open statement without binders whose conclusion starts with `(` (a predicate
    /// equivalence `(l) ↔ (r)` over constants) is the conclusion alone (it once rendered as
    /// `Prop := , (l) ↔ (r)`, which does not parse); with binders, the old layout is kept.
    #[test]
    fn open_obligation_without_binders() {
        let s = vec![st(
            "Simp.s_000000000000",
            " :\n    (true && true) = true",
            &[],
        )];
        let open: BTreeSet<String> = ["Simp.s_000000000000".to_string()].into();
        let o = emit("N", &s, &open, &[], &BTreeSet::new());
        assert!(
            o.contains("def Simp.s_000000000000.statement : Prop := (true && true) = true\n"),
            "{o}"
        );
        assert_eq!(
            open_statement(" (x : Nat)\n    (h : x = 1) :\n    (x = 1)"),
            "∀ (x : Nat) (h : x = 1), (x = 1)"
        );
        assert_eq!(
            open_statement(" (x : Nat) :\n    x = x"),
            "∀ (x : Nat),\n    x = x"
        );
    }
}
