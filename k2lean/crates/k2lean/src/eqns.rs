//! K equations and simplification rules as Lean theorems about the generated definitions and
//! the hook library: proving every equation of the theory about a concrete
//! Lean model shows the theory, restricted to these symbols, is consistent; a simplification
//! rule that cannot be proved is either unsound or needs real mathematics.
//!
//! An equation `φ → f(p̄) = r` is stated over the variables of `p̄`, `φ` and `r`. Partial
//! subterms make both sides `Option`-valued (`⊥` is `none`; matching logic's `\equals` holds
//! between two `⊥`s). An `owise` equation also assumes that no competing equation applies.
//!
//! An equation of a hooked function (one the prelude implements) also assumes that each of its
//! variables of a `Set` or `Map` sort is well formed (`wf_premises`): K's variables of these
//! sorts range over sets and maps, the Lean carriers also hold lists that represent neither,
//! and the hook models implement K's meaning on the sets and maps only (`design.md` §3).

use crate::funcs::Equation;
use crate::ir::{Def, P, S};
use crate::lower::{Fns, L, Lower, Step};
use crate::model::{Coll, Kind, Model};
use crate::names;
use std::collections::{BTreeMap, BTreeSet};

pub struct Stated {
    pub name: String,
    pub statement: String,
    pub what: String,
    /// Definitions to unfold in the goal first (the generated function and its equations).
    pub unfold_first: Vec<String>,
    /// The `Option` binders of a simplification's set variables, cased before the generic proof.
    pub case_first: Vec<String>,
    /// Simp sets the generic proof also uses (`k2l_hook`, the collection laws, for a
    /// simplification over a `Set` or `Map`).
    pub simp_with: Vec<String>,
    /// The normalizers of overloaded symbols in the left-hand side, with their equations
    /// (`K.f`, `K.f.rule1`, …): a match on a normalizer's application decides only once it is
    /// unfolded, which a recursive function's proof then tries (EQ-17).
    pub normalizers: Vec<String>,
    /// The lemmas that decide its `Term.nf` premises and fold a value back into a normalizer's
    /// application (`normal::lemmas`), when it has such premises (EQ-18).
    pub nf: Vec<String>,
}

/// Whether symbol `g` occurs in `p`.
fn mentions(p: &P, g: &str) -> bool {
    match p {
        P::App(f, _, args) => f == g || args.iter().any(|a| mentions(a, g)),
        P::And(_, args) | P::Or(_, args) => args.iter().any(|a| mentions(a, g)),
        _ => false,
    }
}

pub(crate) fn vars_of(p: &P, out: &mut BTreeMap<String, S>) {
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

/// The set variables of a pattern (`@X`), with their sorts.
fn set_vars_of(p: &P, out: &mut BTreeMap<String, S>) {
    match p {
        P::SetVar(n, s) => {
            out.insert(n.clone(), s.clone());
        }
        P::App(_, _, args) | P::And(_, args) | P::Or(_, args) => {
            args.iter().for_each(|a| set_vars_of(a, out))
        }
        P::Not(_, a) | P::Ceil(_, _, a) | P::Floor(_, _, a) => set_vars_of(a, out),
        P::Equals(_, _, a, b) | P::In(_, _, a, b) | P::Implies(_, a, b) | P::Iff(_, a, b) => {
            set_vars_of(a, out);
            set_vars_of(b, out);
        }
        P::Exists(_, _, _, b) | P::Forall(_, _, _, b) => set_vars_of(b, out),
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
            // an equation's `ensures`: undefined where it is false
            Step::Cond { cond, .. } => {
                e = format!("(if {} = true then {e} else none)", cond.render())
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
    let supers = crate::funcs::overload_supers(def);
    // the sorts whose values can be no K value, modulo the overload axioms (EQ-18)
    let nf_sorts = crate::normal::sorts(def, m, fns, eqs);
    let nf_lemmas = crate::normal::lemmas(def, m, fns, eqs);
    for (f, es) in eqs {
        let Some(sig) = fns.get(f) else { continue };
        if sig.args.iter().any(|a| a == "?") {
            continue;
        }
        // the equations K writes; their overload variants (`funcs::equations_modulo_overloads`)
        // are arms of the definition, which the normalizers in the statements already cover
        let comps: Vec<&Equation> = es.iter().filter(|e| !e.owise && e.variant == 0).collect();
        for (i, e) in es.iter().filter(|e| e.variant == 0).enumerate() {
            let what = format!("{} equation {}", names::demangle(f), i + 1);
            let mut normalizers = Vec::new();
            for g in &supers {
                if !e.args.iter().any(|a| mentions(a, g)) {
                    continue;
                }
                let Some(gs) = fns.get(g).filter(|gs| gs.lean.starts_with("K.")) else {
                    continue;
                };
                normalizers.push(gs.lean.clone());
                for k in 1..=eqs.get(g).map_or(0, |v| v.len()) {
                    normalizers.push(format!("{}.rule{k}", gs.lean));
                }
            }
            let unfold_first = if sig.lean.starts_with("K.") {
                let mut v = vec![sig.lean.clone()];
                for k in 1..=es.len() {
                    v.push(format!("{}.rule{k}", sig.lean));
                }
                v
            } else {
                vec![]
            };
            let comps = if e.owise { &comps[..] } else { &[] };
            match state_one(def, m, fns, f, sig, e, comps, &nf_sorts) {
                Ok(statement) => out.push(Stated {
                    nf: if statement.contains("\n    (hnf") {
                        nf_lemmas.clone()
                    } else {
                        vec![]
                    },
                    name: format!(
                        "Eqn.{}",
                        names::ident(&format!("{}_{}", names::demangle(f), i + 1))
                    ),
                    statement,
                    what,
                    unfold_first,
                    case_first: vec![],
                    simp_with: vec![],
                    normalizers: normalizers.clone(),
                }),
                Err(err) => eprintln!("note: {what} not stated: {err}"),
            }
        }
    }
    out
}

pub(crate) fn bind_vars(
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

/// The well-formedness premises of an equation of a hooked function: `KPrelude.SetHook.WF X`
/// or `KPrelude.MapHook.WF X` for each bound variable `X` of a `Set` or `Map` sort. An equation
/// of a generated function gets none: the function is defined by its equations, so they hold at
/// every carrier value, and a premise would only weaken a theorem that holds without it. A
/// `List` carrier has no values that are not lists, so it needs no premise.
fn wf_premises(m: &Model, sig: &crate::lower::FnSig, binders: &[(String, String)]) -> Vec<String> {
    if sig.lean.starts_with("K.") {
        return Vec::new();
    }
    binders
        .iter()
        .filter_map(|(n, t)| wf_pred(m, t).map(|w| format!("{w} {n}")))
        .collect()
}

/// The well-formedness predicate of a `Set` or `Map` sort (cell maps included).
fn wf_pred(m: &Model, sort: &str) -> Option<&'static str> {
    match m.sorts.get(sort).map(|s| &s.kind) {
        Some(Kind::Coll(Coll::Set)) => Some("KPrelude.SetHook.WF"),
        Some(Kind::Coll(Coll::Map)) => Some("KPrelude.MapHook.WF"),
        _ => None,
    }
}

/// The binders and well-formedness premises of a simplification, over the variables of `pats`.
///
/// A set variable (`@X`) ranges over sets of values, while a term of the model denotes at most
/// one value: it is bound as an `Option` (`none` the empty set), and each occurrence binds the
/// element (`Lower::set_vars`). Restricted to such sets, `domains.md`'s set-variable rules hold
/// in the model; some are false at sets of two elements (`design.md` §3).
///
/// Every variable of a `Set` or `Map` sort, element or set, gets the well-formedness premise,
/// whatever the head symbol: a simplification is an axiom K trusts about K values, which are the
/// well-formed carrier values, so the premise is its statement; unlike a generated function's
/// equation, it defines nothing, and some fail at carrier values that are no K value
/// (`intersectSet(S, S) => S` at an unsorted list).
fn simpl_binders(lw: &mut Lower, pats: &[&P]) -> Result<Simpl, String> {
    let (mut vars, mut svars) = (BTreeMap::new(), BTreeMap::new());
    for p in pats {
        vars_of(p, &mut vars);
        set_vars_of(p, &mut svars);
    }
    let binders = bind_vars(lw, &vars, "")?;
    let mut opts = Vec::new();
    for (v, s) in &svars {
        let sort = s.name().ok_or("parametric variable sort")?.to_string();
        if !m_has(lw, &sort) {
            return Err(format!("set variable of unsupported sort {sort}"));
        }
        let n = lw.param(
            &sanitize(v.trim_start_matches('@')),
            &format!("Option {sort}"),
        );
        lw.set_vars.insert(v.clone(), n.clone());
        opts.push((n, sort));
    }
    let mut text = String::new();
    for (n, t) in &binders {
        text.push_str(&format!(" ({n} : {t})"));
    }
    for (n, t) in &opts {
        text.push_str(&format!(" ({n} : Option {t})"));
    }
    let wf = binders
        .iter()
        .filter_map(|(n, t)| wf_pred(lw.m, t).map(|w| format!("{w} {n}")))
        .chain(
            opts.iter()
                .filter_map(|(n, t)| wf_pred(lw.m, t).map(|w| format!("∀ m ∈ {n}, {w} m"))),
        );
    for (k, h) in wf.enumerate() {
        text.push_str(&format!("\n    (hwf{k} : {h})"));
    }
    Ok(Simpl {
        binders: text,
        case_first: opts.into_iter().map(|(n, _)| n).collect(),
    })
}

/// A simplification's binders and premises (`simpl_binders`), and the `Option` binders its
/// proof cases first.
struct Simpl {
    binders: String,
    case_first: Vec<String>,
}

/// The simp sets a simplification's proof also uses: the collection laws (`k2l_hook`,
/// `HookLaws.lean`) for one about maps or sets.
fn simp_with(statement: &str) -> Vec<String> {
    if statement.contains("KPrelude.MapHook.") || statement.contains("KPrelude.SetHook.") {
        vec!["k2l_hook".to_string()]
    } else {
        vec![]
    }
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

/// The aliases of an equation's arguments eliminated (`P #as X`, KORE `\and(P, X)` in a term
/// position): the arguments with every alias replaced by its pattern, and the substitution that
/// replaces each alias variable by its pattern, to apply to the requires and the right-hand side.
///
/// `\and(P, X)` matches a value that matches `P` and is the value of `X`; `P` is functional (a
/// constructor term, a literal, a list pattern: it denotes one value), so the axiom over `X` is the
/// one with `P` for `X` everywhere `X` occurs: in this argument, the other arguments (`f(c(N) #as X,
/// X)` constrains both), the requires and the right-hand side. `X #as Y` (no term) identifies the
/// two variables; nested aliases bind every variable to the one pattern. A variable inside its own
/// pattern, and a conjunction of two non-variable patterns, are refused.
/// Also returns each alias pattern with its sort.
type Aliases = (Vec<P>, BTreeMap<String, P>, Vec<(P, S)>);
fn strip_aliases(args: &[P]) -> Result<Aliases, String> {
    fn walk(p: &P, raw: &mut Vec<(String, P)>, pats: &mut Vec<(P, S)>) -> Result<P, String> {
        Ok(match p {
            P::And(sort, ps) => {
                let mut flat = Vec::new();
                flatten_and(ps, &mut flat);
                let (vars, terms): (Vec<&P>, Vec<&P>) =
                    flat.into_iter().partition(|q| matches!(q, P::Var(..)));
                let value = match terms.as_slice() {
                    [t] => {
                        let t = walk(t, raw, pats)?;
                        pats.push((t.clone(), sort.clone()));
                        t
                    }
                    [] => (*vars.first().ok_or("an empty conjunction")?).clone(),
                    _ => return Err("conjunction of two non-variable patterns".into()),
                };
                for v in vars {
                    if let P::Var(n, _) = v
                        && *v != value
                    {
                        raw.push((n.clone(), value.clone()));
                    }
                }
                value
            }
            P::App(f, sp, args) => P::App(
                f.clone(),
                sp.clone(),
                args.iter()
                    .map(|a| walk(a, raw, pats))
                    .collect::<Result<_, _>>()?,
            ),
            other => other.clone(),
        })
    }
    fn flatten_and<'a>(ps: &'a [P], out: &mut Vec<&'a P>) {
        for q in ps {
            match q {
                P::And(_, qs) => flatten_and(qs, out),
                other => out.push(other),
            }
        }
    }
    let (mut raw, mut pats) = (Vec::new(), Vec::new());
    let stripped: Vec<P> = args
        .iter()
        .map(|a| walk(a, &mut raw, &mut pats))
        .collect::<Result<_, _>>()?;
    // one binding per variable (a variable aliased twice is bound to its first pattern, the second
    // occurrence then equates the two: substituted, both name the same value)
    let mut subst: BTreeMap<String, P> = BTreeMap::new();
    for (v, t) in raw {
        subst.entry(v).or_insert(t);
    }
    // closed under itself (`Y := wrap(X)`, `X := c(N)`), with the occurs check
    let keys: Vec<String> = subst.keys().cloned().collect();
    for _ in 0..=keys.len() {
        let next: BTreeMap<String, P> = subst
            .iter()
            .map(|(k, t)| (k.clone(), subst_vars(t, &subst)))
            .collect();
        if next == subst {
            break;
        }
        subst = next;
    }
    for (k, t) in &subst {
        let mut vs = BTreeMap::new();
        vars_of(t, &mut vs);
        if vs.contains_key(k) {
            return Err("alias variable inside its own pattern".into());
        }
    }
    Ok((
        stripped.iter().map(|a| subst_vars(a, &subst)).collect(),
        subst,
        pats,
    ))
}

/// `p` with the substitution applied to its free variables (a binder shadows its variable).
fn subst_vars(p: &P, subst: &BTreeMap<String, P>) -> P {
    let b = |q: &P| Box::new(subst_vars(q, subst));
    let all = |qs: &[P]| qs.iter().map(|q| subst_vars(q, subst)).collect();
    match p {
        P::Var(v, _) => subst.get(v).cloned().unwrap_or_else(|| p.clone()),
        P::App(f, sp, args) => P::App(f.clone(), sp.clone(), all(args)),
        P::And(s, ps) => P::And(s.clone(), all(ps)),
        P::Or(s, ps) => P::Or(s.clone(), all(ps)),
        P::Not(s, a) => P::Not(s.clone(), b(a)),
        P::Implies(s, l, r) => P::Implies(s.clone(), b(l), b(r)),
        P::Iff(s, l, r) => P::Iff(s.clone(), b(l), b(r)),
        P::Rewrites(s, l, r) => P::Rewrites(s.clone(), b(l), b(r)),
        P::Ceil(a, s, q) => P::Ceil(a.clone(), s.clone(), b(q)),
        P::Floor(a, s, q) => P::Floor(a.clone(), s.clone(), b(q)),
        P::Equals(a, s, l, r) => P::Equals(a.clone(), s.clone(), b(l), b(r)),
        P::In(a, s, l, r) => P::In(a.clone(), s.clone(), b(l), b(r)),
        P::Exists(s, v, vs, q) | P::Forall(s, v, vs, q) => {
            let mut inner = subst.clone();
            inner.remove(v);
            let q = Box::new(subst_vars(q, &inner));
            if matches!(p, P::Exists(..)) {
                P::Exists(s.clone(), v.clone(), vs.clone(), q)
            } else {
                P::Forall(s.clone(), v.clone(), vs.clone(), q)
            }
        }
        P::Str(_) | P::SetVar(..) | P::Dv(..) | P::Top(_) | P::Bottom(_) | P::Other(_) => p.clone(),
    }
}

#[allow(clippy::too_many_arguments)]
fn state_one(
    _def: &Def,
    m: &Model,
    fns: &Fns,
    _f: &str,
    sig: &crate::lower::FnSig,
    e: &Equation,
    comps: &[&Equation],
    nf_sorts: &BTreeSet<String>,
) -> Result<String, String> {
    let mut lw = Lower::new(m, fns, &[]);
    let (e_args, asv, alias_pats) = strip_aliases(&e.args)?;
    let e_requires: Vec<P> = e.requires.iter().map(|r| subst_vars(r, &asv)).collect();
    let (value, ensures) = e.value();
    let e_rhs = subst_vars(value, &asv);
    let e_ens = ensures.map(|p| subst_vars(p, &asv));
    let mut vars = BTreeMap::new();
    for a in &e_args {
        vars_of(a, &mut vars);
    }
    for r in &e_requires {
        vars_of(r, &mut vars);
    }
    vars_of(&e_rhs, &mut vars);
    if let Some(ens) = &e_ens {
        vars_of(ens, &mut vars);
    }
    let binders = bind_vars(&mut lw, &vars, "")?;
    let wf = wf_premises(m, sig, &binders);
    let mut args = Vec::new();
    for (a, s) in e_args.iter().zip(&sig.args) {
        args.push(lw.expr(a, s)?);
    }
    if !lw.steps.is_empty() {
        // an alias of a map or set pattern (partial: overlapping keys give `⊥`) is such an argument
        // too; stated with the map-pattern equations, when those are (`design.md` §8)
        let partial_alias = alias_pats.iter().any(|(t, sort)| {
            let n = lw.steps.len();
            let lowered = sort.name().map(|so| lw.expr(t, so));
            let partial = lowered.is_some_and(|r| r.is_err() || lw.steps.len() > n);
            lw.steps.truncate(n);
            partial
        });
        return Err(if partial_alias {
            "alias of a map or set pattern".into()
        } else {
            "a partial function in an argument pattern".into()
        });
    }
    let hyps = cond_props(&mut lw, &e_requires)?;
    // the `ensures`, as in the definition (`funcs::lower_equation`): checked after the match
    if let Some(ens) = &e_ens {
        lw.cond(ens)?;
    }
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
        let (c_args, casv, _) = strip_aliases(&c.args)?;
        let c_requires: Vec<P> = c.requires.iter().map(|r| subst_vars(r, &casv)).collect();
        let mut cv = BTreeMap::new();
        for a in &c_args {
            vars_of(a, &mut cv);
        }
        for r in &c_requires {
            vars_of(r, &mut cv);
        }
        let cb = bind_vars(&mut lc, &cv, &format!("o{j}_"))?;
        // the competitor's argument `a` matches the equation's `x`: `x = a`, or, when `a` has partial
        // calls (a map or set pattern's concatenation), `a` is defined and is `x`
        let mut body = Vec::new();
        for ((x, a), s) in args.iter().zip(&c_args).zip(&sig.args) {
            let start = lc.steps.len();
            let ca = lc.expr(a, s)?;
            let st: Vec<Step> = lc.steps.drain(start..).collect();
            if st.is_empty() {
                body.push(format!("{} = {}", x.render(), ca.render()));
                continue;
            }
            // `bind e fun r => some r` is `e`
            let oe = match (st.split_last(), &ca) {
                (Some((Step::Bind { expr, var, .. }, init)), L::Var(v)) if v == var => {
                    init.iter().rev().try_fold(expr.render(), |e, s| match s {
                        Step::Bind { expr, var, .. } => Some(format!(
                            "(Option.bind {} fun {var} => {e})",
                            expr.render_arg()
                        )),
                        _ => None,
                    })
                }
                _ => option_expr(&st, &ca),
            }
            .ok_or("owise competitor with a partial argument")?;
            body.push(format!("{oe} = some {}", x.render_arg()));
        }
        body.extend(cond_props(&mut lc, &c_requires)?);
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
    for (k, h) in wf.iter().enumerate() {
        stmt.push_str(&format!("\n    (hwf{k} : {h})"));
    }
    // the no-match premises are about K values: each variable that can hold a term at which an
    // overload rule applies (no K value) is assumed in normal form, as `WF` is assumed of a set
    // (EQ-18, `normal.rs`)
    if !guards.is_empty() {
        let nf = binders
            .iter()
            .filter(|(_, t)| crate::normal::reaches(m, t, nf_sorts));
        for (k, (n, _)) in nf.enumerate() {
            stmt.push_str(&format!("\n    (hnf{k} : Term.nf {n} = true)"));
        }
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
    let mut taken: BTreeMap<String, usize> = BTreeMap::new();
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
            Ok((st, Simpl { case_first, .. })) => {
                // named by the rule's `UNIQUE'Unds'ID` (a digest of the rule), so that a name does not
                // depend on where the rule is in the definition; a definition can contain one rule
                // twice (KEVM's `int-simplification.k` restates `domains.md`'s `A modInt B => A`,
                // with the same digest), and each axiom is stated, the later ones numbered
                let uid = a
                    .attrs
                    .string("UNIQUE'Unds'ID")
                    .map(|u| u[..12.min(u.len())].to_string());
                let base = match uid {
                    Some(u) => format!("Simp.s_{u}"),
                    None => format!("Simp.s{idx}"),
                };
                let name = numbered(base, &mut taken);
                out.push(Stated {
                    name,
                    what,
                    unfold_first: vec![],
                    case_first,
                    simp_with: simp_with(&st),
                    normalizers: vec![],
                    nf: vec![],
                    statement: st,
                })
            }
            Err(err) => eprintln!("note: {what} not stated: {err}"),
        }
    }
    out
}

/// `base`, or `base_k` for its `k`-th use (`k ≥ 2`).
fn numbered(base: String, taken: &mut BTreeMap<String, usize>) -> String {
    let seen = taken.entry(base.clone()).or_insert(0);
    *seen += 1;
    if *seen == 1 {
        base
    } else {
        format!("{base}_{seen}")
    }
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

fn state_simpl(m: &Model, fns: &Fns, p: &P) -> Result<(String, Simpl), String> {
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
        let mut pats = vec![&**lhs, rhs];
        pats.extend(req);
        let sb = simpl_binders(&mut lw, &pats)?;
        let mut stmt = sb.binders.clone();
        let hyp = match req {
            Some(r) if !matches!(r, P::Top(_)) => Some(prop(&mut lw, r)?),
            _ => None,
        };
        let l = prop(&mut lw, lhs)?;
        let r = prop(&mut lw, rhs)?;
        if let Some(h) = hyp {
            stmt.push_str(&format!("\n    (hreq0 : {h})"));
        }
        stmt.push_str(&format!(" :\n    ({l}) ↔ ({r})"));
        return Ok((stmt, sb));
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
    let mut pats = vec![&**lhs, rhs];
    pats.extend(requires.iter());
    let sb = simpl_binders(&mut lw, &pats)?;
    let mut stmt = sb.binders.clone();
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
    for (k, h) in hyps.iter().enumerate() {
        stmt.push_str(&format!("\n    (hreq{k} : {h})"));
    }
    stmt.push_str(&format!(" :\n    {concl}"));
    Ok((stmt, sb))
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
    let budget = Budget::default();
    emit_with(
        ns,
        stated,
        open,
        &[],
        unfold,
        recursive,
        &BTreeSet::new(),
        &budget,
    )
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

/// The heartbeat budget of each generated proof (Lean's `maxHeartbeats`, per declaration): the
/// module's `default` (`gen --equations-heartbeats`), and for the theorems of `per_theorem` their
/// own (`gen --equations-heartbeats-file`, lines `NAME HEARTBEATS`), written as
/// `set_option maxHeartbeats N in` before the theorem. The budget bounds what a failing proof
/// costs: a proof that the tactics cannot finish runs until it exhausts it.
pub struct Budget {
    pub default: usize,
    pub per_theorem: BTreeMap<String, usize>,
}

/// The default budget of a generated proof. On KEVM's 1,111 statements (each elaborated alone,
/// 2026-10-24), the 872 proved theorems used at most 315,000 heartbeats, 155,000 at the 99th
/// percentile and 33,000 at the 95th; 15 used more than 67,000 (two thirds of this default) and
/// are given 400,000 by `pipelines/kevm-heartbeats.txt`. The 53 proofs that ran out of 400,000
/// took 60 to 1,114 s each, and most of the cost of the failing ones.
pub const DEFAULT_HEARTBEATS: usize = 100_000;

impl Budget {
    /// Reads per-theorem budgets from `text`, lines `NAME HEARTBEATS` (blank lines and `#`
    /// comments skipped; the name may hold spaces inside `«…»`, the budget is the last word).
    /// A name that is not one of `stated` is an error: the file only raises budgets, so an entry
    /// left behind by a renamed theorem would otherwise leave the renamed theorem at the default
    /// without a word, and the first sign would be a proof out of heartbeats in a long build.
    pub fn read_overrides(&mut self, text: &str, stated: &[Stated]) -> Result<(), String> {
        let names: BTreeSet<&str> = stated.iter().map(|s| s.name.as_str()).collect();
        let mut unknown = Vec::new();
        for l in text.lines().map(str::trim) {
            if l.is_empty() || l.starts_with('#') {
                continue;
            }
            let (name, h) = l
                .rsplit_once(char::is_whitespace)
                .and_then(|(n, h)| Some((n.trim(), h.parse::<usize>().ok().filter(|h| *h > 0)?)))
                .ok_or_else(|| format!("`{l}` is not `NAME HEARTBEATS`"))?;
            if !names.contains(name) {
                unknown.push(name.to_string());
            }
            self.per_theorem.insert(name.to_string(), h);
        }
        if unknown.is_empty() {
            Ok(())
        } else {
            Err(format!("names no generated theorem: {unknown:?}"))
        }
    }
}

impl Default for Budget {
    fn default() -> Self {
        Budget {
            default: DEFAULT_HEARTBEATS,
            per_theorem: BTreeMap::new(),
        }
    }
}

/// `Equations.lean`: every stated equation and simplification, proved by the generic tactics or,
/// when it is in `open`, stated as an open obligation. `base` (hook definitions and projection
/// lemmas) is in every proof's simp set; of `defs` (the generated definitions) each proof gets
/// its own (`own_defs`). `recursive` holds the Lean names of the generated functions that are
/// well-founded recursive (`funcs::Generated::recursive`); their equations get the recursive
/// proof (`k2l_eqn_r`), and those of `list_recursive` (recursion on a builtin `List`) also
/// `k2l_fold_eqn`.
#[allow(clippy::too_many_arguments)]
pub fn emit_with(
    ns: &str,
    stated: &[Stated],
    open: &BTreeSet<String>,
    base: &[String],
    defs: &[String],
    recursive: &BTreeSet<String>,
    list_recursive: &BTreeSet<String>,
    budget: &Budget,
) -> String {
    let cx = Cx {
        ns,
        open,
        base,
        defs,
        recursive,
        list_recursive,
        rec_fns: rec_fns(stated, recursive),
        budget,
    };
    emit_part(&cx, &stated.iter().collect::<Vec<_>>(), None)
}

/// What every module of `Equations` shares.
struct Cx<'a> {
    ns: &'a str,
    open: &'a BTreeSet<String>,
    base: &'a [String],
    defs: &'a [String],
    recursive: &'a BTreeSet<String>,
    list_recursive: &'a BTreeSet<String>,
    /// The recursive functions of all the statements, not only of one module's: `k2l_eqn_r` cases
    /// on their calls, so that a proof is the same whichever module it is in.
    rec_fns: BTreeSet<String>,
    budget: &'a Budget,
}

/// Whether `s` gets `k2l_eqn_o`: it has no-match premises (`howise…`: the rule is `owise`, or
/// tried after others), and it is the equation of a generated function, which the proof unfolds.
fn uses_eqn_o(s: &Stated, defs: &[String], recursive: &BTreeSet<String>) -> bool {
    s.statement.contains("\n    (howise")
        && (rec_of(s, recursive).is_some() || s.unfold_first.iter().any(|n| defs.contains(n)))
}

/// The recursive function whose equation `s` is, if any.
fn rec_of(s: &Stated, recursive: &BTreeSet<String>) -> Option<String> {
    s.unfold_first
        .first()
        .filter(|n| recursive.contains(*n))
        .cloned()
}

fn rec_fns(stated: &[Stated], recursive: &BTreeSet<String>) -> BTreeSet<String> {
    stated.iter().filter_map(|s| rec_of(s, recursive)).collect()
}

/// One module of statements: `part = None` for the whole of `Equations.lean`, `Some((k, n))` for
/// part `k` of `n` (`Equations/Part{k}.lean`), whose statements are a subsequence of the whole.
fn emit_part(cx: &Cx, stated: &[&Stated], part: Option<(usize, usize)>) -> String {
    let Cx {
        ns,
        open,
        base,
        defs,
        recursive,
        list_recursive,
        budget,
        ..
    } = cx;
    let fold_import = if list_recursive.is_empty() {
        ""
    } else {
        "import KPrelude.InvFold\n"
    };
    let doc = match part {
        None => "K's function equations and simplification rules, as theorems about the generated definitions and\n\
the hook library. A statement whose generic proof attempt failed is kept as an open obligation\n\
(a `Prop` definition, not an axiom).".to_string(),
        Some((k, n)) => format!("Part {k} of {n} of `{ns}.Equations`: K's function equations and simplification rules, as theorems\n\
about the generated definitions and the hook library. A statement whose generic proof attempt\n\
failed is kept as an open obligation (a `Prop` definition, not an axiom)."),
    };
    let mut o = format!(
        "import {ns}.Functions\nimport KPrelude.Tactic\n{fold_import}\n/-! Generated by k2lean; do not edit.\n\n\
{doc} -/\n\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\nset_option maxHeartbeats {hb}\nset_option maxRecDepth 100000\n\nnamespace {ns}\n\nopen KPrelude\n\n",
        hb = budget.default
    );
    // the generic proofs, defined once with the shared simp lemmas; a theorem's script passes
    // the definitions it may unfold
    let u = if base.is_empty() {
        "$xs,*".to_string()
    } else {
        format!("{}, $xs,*", base.join(", "))
    };
    o.push_str(&format!(
        "/-- The generic proof attempts without case splits. -/\nlocal macro \"k2l_eqn_a\" \" [\" xs:Lean.Parser.Tactic.simpLemma,* \"]\" : tactic => `(tactic| first\n  | rfl\n  | k2l_hook_law\n  | (simp [{u}]; done)\n  | (simp_all [{u}]; done)\n  | (simp_all [{u}]; omega)\n  | (simp only [{u}]; rw [Bool.eq_iff_iff]; simp_all; done)\n  | (simp only [{u}]; rw [Bool.eq_iff_iff]; simp_all; omega))\n\n\
/-- The generic proof by case splits (equations `x = t` from a split substituted first: `simp_all`\nuses an equation `t = x` only from left to right); a case `simp_all` leaves is closed by `omega`\n(a `requires` that excludes an earlier equation's by linear arithmetic). -/\nlocal macro \"k2l_eqn_b\" \" [\" xs:Lean.Parser.Tactic.simpLemma,* \"]\" : tactic => `(tactic| ((repeat' (first | split | k2l_split_hyps)) <;> (try subst_vars) <;> first | (simp_all [{u}]; done) | ((try simp_all [{u}]) <;> omega)))\n\n\
/-- The generic proof by cases on the partial calls that the cascade matches (`k2l_case_call`),\nwhich the statement binds with `Option.bind`: after each case both sides reduce, and the cases\nare closed as `k2l_eqn_a` does. Fails unless there is such a call. -/\nlocal macro \"k2l_eqn_c\" \" [\" xs:Lean.Parser.Tactic.simpLemma,* \"]\" : tactic => `(tactic| ((try simp only []); (k2l_case_call <;> try simp only [Option.bind]); (repeat' (k2l_case_call <;> try simp only [Option.bind])); all_goals k2l_eqn_a [$xs,*]))\n\n"
    ));
    // the equations of a recursive function: a well-founded definition, which `simp` cannot unfold;
    // the macro is in the whole module when some function is recursive, and in a part when one of
    // its statements is a recursive function's
    let needs_r = match part {
        None => !cx.rec_fns.is_empty(),
        Some(_) => stated.iter().any(|s| rec_of(s, recursive).is_some()),
    };
    // `k2l_case_rec`, `k2l_case_discr` and `k2l_case_call` are in `KPrelude.Tactic`
    // what the proof cases on: the recursive calls, and the projections out of injections
    // (`proj_Y_X`, named like their `proj_eq_some_Y_X` lemmas), whose `match hp : proj … with`
    // in a cascade `simp` cannot rewrite
    let mut case_on: Vec<String> = cx.rec_fns.iter().cloned().collect();
    case_on.extend(
        base.iter()
            .chain(defs.iter())
            .filter_map(|n| n.strip_prefix("proj_eq_some_"))
            .map(|p| format!("proj_{p}")),
    );
    let r = case_on.join(", ");
    if needs_r {
        o.push_str(&format!(
            "/-- The generic proof of an equation of a recursive function `f`, which `simp` does not\n\
unfold: unfold `f` once on the left-hand side (`f.eq_def`), reduce the cascade of its equations,\n\
decide its matches on a list pattern of the left-hand side (`k2l_case_list`), case on the variables\n\
that the cascade matches, on the recursive calls, on the projections and on the other partial\n\
calls that its matches inspect (`k2l_case_call`: hooks and functions that are not recursive,\n\
after which a recursive call whose argument is such a call's value is cased too), then close each\n\
case as the generic tactics do. -/\n\
local macro \"k2l_eqn_r \" f:ident \" [\" xs:Lean.Parser.Tactic.simpLemma,* \"]\" : tactic => do\n  let e := Lean.mkIdent (f.getId.str \"eq_def\")\n  \
`(tactic| (\n    \
(conv => lhs; rw [$e:ident])\n    \
try simp only []\n    \
try (repeat' (first | k2l_case_list | (k2l_case_discr <;> try simp only []) | (k2l_case_rec [{r}] <;> try simp only [Option.bind]) | (k2l_case_call <;> try simp only [Option.bind])))\n    \
all_goals first\n      \
| (simp_all [{u}]; done)\n      \
| ((repeat' (first | split | k2l_split_hyps)) <;> (try simp_all [{u}]) <;> omega)))\n\n"
        ));
    }
    if stated.iter().any(|s| uses_eqn_o(s, defs, recursive)) {
        let case_rec = if case_on.is_empty() {
            String::new()
        } else {
            format!(" | (k2l_case_rec [{r}] <;> try simp only [Option.bind])")
        };
        // a statement with `Term.nf` premises (EQ-18): a match on a term with a variable inside
        // (`inj_Exps a` against a nested pattern) cases that variable, and a case the no-match
        // premises refute only once its value is read as K's term (the normalizer's
        // application) is closed after deciding `Term.nf` and folding the value
        let nf = stated
            .iter()
            .find(|s| !s.nf.is_empty())
            .map(|s| s.nf.join(", "));
        let (case_sub, nf_arm) = match &nf {
            Some(nf) => (
                " | (k2l_case_sub <;> try simp only [])".to_string(),
                format!(
                    " | ((simp_all only [{nf}]); first | rfl | k2l_no_arm | k2l_owise_apply | (simp_all [{u}]; done))"
                ),
            ),
            None => (String::new(), String::new()),
        };
        let nf_arm_top = if nf_arm.is_empty() {
            String::new()
        } else {
            format!("{}\n      ", nf_arm.trim_start())
        };
        o.push_str(&format!(
            "/-- The proof of an equation with no-match premises (an `owise` rule's, whose left-hand side\n\
is usually a variable), after the function is unfolded: reduce the cascade as `k2l_eqn_r` does,\n\
also splitting a list variable that it takes apart (`k2l_case_lvar`), then close each case by\n\
reduction, by the no-match premise of the rule whose arm the case is (`k2l_owise_arm`; applied,\n\
with its `requires` computed from the case's facts, `k2l_owise_apply`), or as the generic tactics\n\
do, after splitting the remaining `if`s and `match`es (a rule's `requires`). -/\n\
local macro \"k2l_eqn_o\" \" [\" xs:Lean.Parser.Tactic.simpLemma,* \"]\" : tactic => `(tactic| (\n    \
(try simp only [])\n    \
(try (repeat' (first | k2l_case_list | k2l_case_lvar | (k2l_case_discr <;> try simp only []){case_sub}{case_rec} | (k2l_case_call <;> try simp only [Option.bind]))))\n    \
all_goals first\n      \
| rfl\n      \
| k2l_owise_arm\n      \
{nf_arm_top}| (simp_all [{u}]; done)\n      \
| ((repeat' (first | split | k2l_split_hyps | k2l_case_choose)) <;> first | rfl | k2l_owise_arm{nf_arm} | (simp_all [{u}]; done) | k2l_owise_apply | ((try simp_all [{u}]) <;> omega))))\n\n"
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
        let mut own = own_defs(s, defs);
        own.extend(s.simp_with.iter().map(|x| x.as_str()));
        let own = own.join(", ");
        // the generic tactics do not unfold a well-founded recursive function (none of the 32
        // such equations of SIMPLE and imp-typing closed that way), so its equations get only the
        // recursive proof
        // an equation with no-match premises gets `k2l_eqn_o` last, after the function is unfolded
        let owise = uses_eqn_o(s, defs, recursive);
        let tac = match rec_of(s, recursive) {
            Some(f) if list_recursive.contains(&f) || owise => {
                // an equation with no-match premises gets `k2l_eqn_o` first: `k2l_eqn_r` cases on
                // every call of the cascade, which on an `owise` equation over a sort of many
                // constructors exceeds any budget (impplustypes' `wt` equation 8), and a timeout
                // is not caught by `first`
                let mut t = if owise {
                    format!(
                        "by\n  intros\n  first\n  | ((conv => lhs; rw [{f}.eq_def]); k2l_eqn_o [{own}])\n  | k2l_eqn_r {f} [{own}]"
                    )
                } else {
                    format!("by\n  intros\n  first\n  | k2l_eqn_r {f} [{own}]")
                };
                // `k2l_fold_eqn` can leave goals, so it ends in `done` for `first` to go on
                match (list_recursive.contains(&f), owise) {
                    (true, false) => t.push_str(&format!("\n  | k2l_fold_eqn {f}")),
                    (true, true) => t.push_str(&format!("\n  | (k2l_fold_eqn {f}; done)")),
                    _ => {}
                }
                t
            }
            Some(f) if !s.normalizers.is_empty() => format!(
                // first: a heartbeat timeout of the other alternative is not caught by `first`
                "by\n  intros\n  first\n  | (simp only [{}]; k2l_eqn_r {f} [{own}])\n  | k2l_eqn_r {f} [{own}]",
                s.normalizers.join(", ")
            ),
            Some(f) => format!("by\n  intros\n  k2l_eqn_r {f} [{own}]"),
            // last, a case split on the variables under injections, which reduces a cascade that
            // matches the injected term (`k2l_eqn_b` can leave goals, so it must end in `done`
            // for `first` to go on); then cases on the partial calls of the right-hand side
            None => {
                // a simplification over set variables: each `Option` binder cased (the empty set,
                // one element), then the generic proof
                let cases = if s.case_first.is_empty() {
                    String::new()
                } else {
                    let c: Vec<String> = s
                        .case_first
                        .iter()
                        .map(|x| format!("(cases {x})"))
                        .collect();
                    format!("\n  | ({} <;> k2l_eqn_a [{own}])", c.join(" <;> "))
                };
                // a normalizer in the left-hand side unfolded, then cases on the variables its
                // matches inspect (EQ-17); first, as a timeout of a later one is not caught
                let norm = if s.normalizers.is_empty() {
                    String::new()
                } else {
                    format!(
                        "\n  | (simp only [{}]; (repeat' (k2l_case_discr <;> try simp only [])) <;> k2l_eqn_a [{own}])",
                        s.normalizers.join(", ")
                    )
                };
                let mut t = format!(
                    "by\n  intros\n  first{norm}\n  | k2l_eqn_a [{own}]{cases}\n  | ({first}k2l_eqn_b [{own}]; done)\n  | ((repeat' k2l_case_inj) <;> k2l_eqn_a [{own}])\n  | ({first}k2l_eqn_c [{own}])"
                );
                if owise {
                    t.push_str(&format!("\n  | ({first}k2l_eqn_o [{own}])"));
                }
                t
            }
        };
        if open.contains(&s.name) {
            let prop = open_statement(&s.statement);
            o.push_str(&format!(
                "/-- Open obligation: {} -/\ndef {}.statement : Prop :={}\n\n",
                s.what, s.name, prop
            ));
        } else {
            let own_budget = match budget.per_theorem.get(&s.name) {
                Some(h) if *h != budget.default => format!("set_option maxHeartbeats {h} in\n"),
                _ => String::new(),
            };
            o.push_str(&format!(
                "{own_budget}/-- {} -/\ntheorem {}{} := {tac}\n\n",
                s.what, s.name, s.statement
            ));
        }
    }
    o.push_str(&format!("end {ns}\n"));
    o
}

/// The weight of a statement, the unit `--equations-part-weight` bounds: 1 plus the definitions
/// its generic proof may unfold, each a simp lemma whose equation lemmas the proof makes Lean
/// generate and try. An open obligation keeps the weight of its proof, so that the part a
/// statement is in does not depend on the open list: after `open-from-log`, the next generation
/// puts every remaining theorem into the module where it was elaborated before.
pub fn weight(s: &Stated, defs: &[String]) -> usize {
    1 + own_defs(s, defs).len()
}

/// `Equations` as modules of bounded weight (`weight`): `[("Equations", text)]`, the module
/// `emit_with` writes, when the statements' total weight is at most `max_weight`; otherwise
/// `Equations/Part1` … `Equations/Part{n}` (`parts`) and `Equations`, which imports them all.
/// The statements, their proofs and their names are the same either way; only the module that
/// holds a theorem changes, so that no Lean process elaborates more than one part (on KEVM one
/// module of 1,111 statements exceeds 20 GB). The paths are relative to the namespace's
/// directory, without `.lean`.
#[allow(clippy::too_many_arguments)]
pub fn emit_modules(
    ns: &str,
    stated: &[Stated],
    open: &BTreeSet<String>,
    base: &[String],
    defs: &[String],
    recursive: &BTreeSet<String>,
    list_recursive: &BTreeSet<String>,
    max_weight: usize,
    budget: &Budget,
) -> Vec<(String, String)> {
    let weights: Vec<usize> = stated.iter().map(|s| weight(s, defs)).collect();
    if weights.iter().sum::<usize>() <= max_weight {
        let whole = emit_with(
            ns,
            stated,
            open,
            base,
            defs,
            recursive,
            list_recursive,
            budget,
        );
        return vec![("Equations".into(), whole)];
    }
    let cx = Cx {
        ns,
        open,
        base,
        defs,
        recursive,
        list_recursive,
        rec_fns: rec_fns(stated, recursive),
        budget,
    };
    let assigned = parts(&weights, max_weight);
    let n = assigned.len();
    let mut out: Vec<(String, String)> = assigned
        .iter()
        .enumerate()
        .map(|(k, idx)| {
            let r: Vec<&Stated> = idx.iter().map(|&i| &stated[i]).collect();
            (
                format!("Equations/Part{}", k + 1),
                emit_part(&cx, &r, Some((k + 1, n))),
            )
        })
        .collect();
    let mut agg: String = (1..=n)
        .map(|k| format!("import {ns}.Equations.Part{k}\n"))
        .collect();
    agg.push_str(&format!(
        "\n/-! Generated by k2lean; do not edit.\n\nK's function equations and simplification rules, as theorems about the generated definitions and\n\
the hook library, in {n} modules of bounded size (`Equations/Part1.lean` … `Equations/Part{n}.lean`;\n\
`gen --equations-part-weight`). A statement whose generic proof attempt failed is kept as an open\n\
obligation (a `Prop` definition, not an axiom). -/\n"
    ));
    out.push(("Equations".into(), agg));
    out
}

/// The statements (by index) of each part, for statements of weights `weights` whose total
/// exceeds `max_weight`: the fewest parts `n` (from the total weight over `max_weight`, rounded
/// up) such that, taking the statements in order and putting each into the part of least weight
/// so far (the first of those on a tie), no part weighs more than `max_weight` (a statement
/// heavier than that is alone in its part). Each part lists its statements in their order.
///
/// The statements of one function are consecutive and share their proof (the same tactic, the
/// same definitions to unfold, the same recursion), so they tend to cost alike; in a run of
/// consecutive statements, a function whose proofs exhaust the heartbeat limit (KEVM's schedule
/// functions: 173 equations, each failing one taking minutes and about 1 GB) would put all of
/// those proofs in one module, where Lean elaborates them concurrently. Spreading the statements
/// over the parts this way gives each part a share of every function's statements.
fn parts(weights: &[usize], max_weight: usize) -> Vec<Vec<usize>> {
    let total: usize = weights.iter().sum();
    let mut n = total.div_ceil(max_weight).max(1);
    loop {
        let mut load = vec![0usize; n];
        let mut out: Vec<Vec<usize>> = vec![Vec::new(); n];
        let mut fits = true;
        for (i, &w) in weights.iter().enumerate() {
            let k = (0..n).min_by_key(|&k| (load[k], k)).unwrap();
            if load[k] > 0 && load[k] + w > max_weight {
                fits = false;
                break;
            }
            load[k] += w;
            out[k].push(i);
        }
        if fits {
            out.retain(|p| !p.is_empty());
            return out;
        }
        n += 1;
    }
}

#[cfg(test)]
mod tests {
    //! The proof each equation statement gets: the recursive proof for a recursive function's
    //! equation, the generic tactics (unfolding the function first) otherwise, and no proof at all
    //! (a `Prop` statement) for an open obligation.
    use super::*;

    /// A definition can contain one simplification twice (the same `UNIQUE'Unds'ID`): each is
    /// stated, the later ones under numbered names.
    #[test]
    fn a_repeated_simplification_gets_a_numbered_name() {
        let mut taken = BTreeMap::new();
        let names: Vec<String> = ["Simp.s_a", "Simp.s_b", "Simp.s_a", "Simp.s_a"]
            .iter()
            .map(|b| numbered(b.to_string(), &mut taken))
            .collect();
        assert_eq!(names, ["Simp.s_a", "Simp.s_b", "Simp.s_a_2", "Simp.s_a_3"]);
    }

    fn pr() -> S {
        S::App("SortPr".into(), vec![])
    }
    fn v(n: &str) -> P {
        P::Var(n.into(), pr())
    }
    fn c(args: Vec<P>) -> P {
        P::App("Lblc".into(), vec![], args)
    }
    fn w(args: Vec<P>) -> P {
        P::App("Lblw".into(), vec![], args)
    }
    fn al(ps: Vec<P>) -> P {
        P::And(pr(), ps)
    }

    /// `c(N) #as X`: the argument is `c(N)` and `X` is `c(N)`, also where `X` occurs bare in
    /// another argument, before or after the alias.
    #[test]
    fn an_alias_is_its_pattern_in_every_argument() {
        let (args, subst, _) = strip_aliases(&[al(vec![c(vec![v("N")]), v("X")]), v("X")]).unwrap();
        assert_eq!(args, vec![c(vec![v("N")]), c(vec![v("N")])]);
        assert_eq!(subst.get("X"), Some(&c(vec![v("N")])));
        let (args, _, _) = strip_aliases(&[v("X"), al(vec![c(vec![v("N")]), v("X")])]).unwrap();
        assert_eq!(args, vec![c(vec![v("N")]), c(vec![v("N")])]);
    }

    /// `(c(N) #as X) #as Y`, `X #as Y`, and a chain `w(X) #as Y`, `c(N) #as X`.
    #[test]
    fn nested_aliases_variables_and_chains() {
        let (args, subst, _) =
            strip_aliases(&[al(vec![al(vec![c(vec![v("N")]), v("X")]), v("Y")])]).unwrap();
        assert_eq!(args, vec![c(vec![v("N")])]);
        assert_eq!(subst.get("X"), subst.get("Y"));
        let (args, subst, _) = strip_aliases(&[al(vec![v("X"), v("Y")])]).unwrap();
        assert_eq!(args, vec![v("X")]);
        assert_eq!(subst.get("Y"), Some(&v("X")));
        let (args, subst, _) = strip_aliases(&[
            al(vec![w(vec![v("X")]), v("Y")]),
            al(vec![c(vec![v("N")]), v("X")]),
        ])
        .unwrap();
        assert_eq!(args, vec![w(vec![c(vec![v("N")])]), c(vec![v("N")])]);
        assert_eq!(subst.get("Y"), Some(&w(vec![c(vec![v("N")])])));
    }

    #[test]
    fn two_patterns_and_a_variable_in_its_own_pattern_are_refused() {
        let e = strip_aliases(&[al(vec![c(vec![v("N")]), w(vec![v("M")])])]).unwrap_err();
        assert!(e.contains("two non-variable patterns"), "{e}");
        let e = strip_aliases(&[al(vec![c(vec![v("X")]), v("X")])]).unwrap_err();
        assert!(e.contains("inside its own pattern"), "{e}");
    }

    fn st(name: &str, statement: &str, unfold_first: &[&str]) -> Stated {
        Stated {
            name: name.into(),
            statement: statement.into(),
            what: format!("{name} (test)"),
            unfold_first: unfold_first.iter().map(|s| s.to_string()).collect(),
            case_first: vec![],
            simp_with: vec![],
            normalizers: vec![],
            nf: vec![],
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
        // the recursive function is cased on, never unfolded by simp; so are the other partial
        // calls the cascade matches, after which a recursive call on such a call's value is closed
        assert!(o.contains("k2l_case_rec [K.f]"));
        assert!(o.contains(
            "k2l_case_rec [K.f] <;> try simp only [Option.bind]) | (k2l_case_call <;> try simp only [Option.bind])))"
        ), "{o}");
        // a non-recursive function: the generic tactics, unfolding it (and its equations) first,
        // and last the cases on the partial calls of its right-hand side
        assert!(o.contains(
            "theorem Eqn.g_1 (x : SortNat)\n    (hreq0 : K.h x = true) :\n    K.g x = x := by\n  intros\n  first\n  | k2l_eqn_a [K.g, K.g.rule1]\n  | (unfold K.g K.g.rule1; k2l_eqn_b [K.g, K.g.rule1]; done)\n  | ((repeat' k2l_case_inj) <;> k2l_eqn_a [K.g, K.g.rule1])\n  | (unfold K.g K.g.rule1; k2l_eqn_c [K.g, K.g.rule1])\n"
        ), "{o}");
        assert!(o.contains("local macro \"k2l_eqn_c\""), "{o}");
        // a statement that names no generated definition unfolds none
        assert!(o.contains("theorem Simp.s_0123456789ab (b : Bool) :\n    (b && true) = b := by\n  intros\n  first\n  | k2l_eqn_a []\n  | (k2l_eqn_b []; done)\n  | ((repeat' k2l_case_inj) <;> k2l_eqn_a [])\n  | (k2l_eqn_c [])\n"));
    }

    #[test]
    fn owise_equations_get_the_owise_proof_last() {
        let rec: BTreeSet<String> = ["K.f".to_string()].into();
        let unfold = vec![
            "K.f".to_string(),
            "K.g".to_string(),
            "K.g.rule1".to_string(),
        ];
        let mut ss = sample();
        ss.push(st(
            "Eqn.f_2",
            " (Gen0 : SortNat)\n    (howise0 : ∀ (o0_x : SortNat), Gen0 = o0_x → False) :\n    K.f Gen0 = none",
            &["K.f", "K.f.rule1"],
        ));
        ss.push(st(
            "Eqn.g_2",
            " (Gen0 : SortNat)\n    (howise0 : ∀ (o0_x : SortNat), Gen0 = o0_x → K.h o0_x = true → False) :\n    K.g Gen0 = Gen0",
            &["K.g", "K.g.rule1"],
        ));
        let o = emit("N", &ss, &BTreeSet::new(), &unfold, &rec);
        assert!(o.contains("local macro \"k2l_eqn_o\""), "{o}");
        assert!(o.contains("| k2l_case_list | k2l_case_lvar |"), "{o}");
        assert!(o.contains("k2l_split_hyps | k2l_case_choose"), "{o}");
        // a recursive function's: unfolded by its equation lemma, after the recursive proof
        assert!(o.contains(
            "K.f Gen0 = none := by\n  intros\n  first\n  | ((conv => lhs; rw [K.f.eq_def]); k2l_eqn_o [K.f])\n  | k2l_eqn_r K.f [K.f]\n"
        ), "{o}");
        // the other's: unfolded as `k2l_eqn_c` unfolds it, after the generic proofs
        assert!(o.contains(
            "  | (unfold K.g K.g.rule1; k2l_eqn_c [K.g, K.g.rule1])\n  | (unfold K.g K.g.rule1; k2l_eqn_o [K.g, K.g.rule1])\n"
        ), "{o}");
        // the statements without no-match premises keep their proofs
        assert!(
            o.contains("K.f x = some x := by\n  intros\n  k2l_eqn_r K.f [K.f]\n"),
            "{o}"
        );
        // and without one, no macro
        let o = emit("N", &sample(), &BTreeSet::new(), &unfold, &rec);
        assert!(!o.contains("k2l_eqn_o"), "{o}");
    }

    #[test]
    fn no_recursive_macro_without_recursive_functions() {
        let o = emit("N", &sample(), &BTreeSet::new(), &[], &BTreeSet::new());
        assert!(!o.contains("k2l_eqn_r"), "{o}");
        assert!(o.contains("local macro \"k2l_eqn_a\""));
        assert!(o.contains("local macro \"k2l_eqn_b\""));
        // the laws of `KPrelude.HookLaws` are tried right after `rfl`
        assert!(
            o.contains("tactic| first\n  | rfl\n  | k2l_hook_law\n"),
            "{o}"
        );
        // `K.f` is not in the unfold list, so it is not unfolded first either
        assert!(o.contains("theorem Eqn.f_1 (x : SortNat) :\n    K.f x = some x := by\n  intros\n  first\n  | k2l_eqn_a []\n  | (k2l_eqn_b []; done)\n  | ((repeat' k2l_case_inj) <;> k2l_eqn_a [])\n"), "{o}");
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

    /// Within the bound, `Equations` is the one module `emit_with` writes; beyond it, parts of
    /// bounded weight, each statement in the part of least weight so far, each a module with the shared header (and the recursive
    /// macro where a part needs it, casing on every recursive function's calls), and an
    /// `Equations` that imports them; every statement is in exactly one part, with its proof
    /// unchanged.
    #[test]
    fn equations_in_parts() {
        let rec: BTreeSet<String> = ["K.f".to_string()].into();
        let defs = vec!["K.g".to_string(), "K.g.rule1".to_string()];
        let open = BTreeSet::new();
        let bd = Budget::default();
        let whole = emit_with(
            "N",
            &sample(),
            &open,
            &[],
            &defs,
            &rec,
            &BTreeSet::new(),
            &bd,
        );
        let weights: Vec<usize> = sample().iter().map(|s| weight(s, &defs)).collect();
        // `Eqn.g_1` unfolds `K.g` and `K.g.rule1`; the others name no definition of `defs`
        assert_eq!(weights, vec![1, 3, 1]);
        let one = emit_modules(
            "N",
            &sample(),
            &open,
            &[],
            &defs,
            &rec,
            &BTreeSet::new(),
            5,
            &bd,
        );
        assert_eq!(one, vec![("Equations".to_string(), whole.clone())]);
        let parts = emit_modules(
            "N",
            &sample(),
            &open,
            &[],
            &defs,
            &rec,
            &BTreeSet::new(),
            4,
            &bd,
        );
        let names: Vec<&str> = parts.iter().map(|(p, _)| p.as_str()).collect();
        assert_eq!(names, ["Equations/Part1", "Equations/Part2", "Equations"]);
        let (p1, p2, agg) = (&parts[0].1, &parts[1].1, &parts[2].1);
        assert!(
            agg.starts_with("import N.Equations.Part1\nimport N.Equations.Part2\n"),
            "{agg}"
        );
        assert!(!agg.contains("theorem "));
        // each statement goes to the part of least weight so far: `Eqn.f_1` (1) to part 1,
        // `Eqn.g_1` (3) to part 2, the simplification (1) to part 1, after `Eqn.f_1`
        let f = p1.find("theorem Eqn.f_1").expect(p1);
        let simp = p1.find("theorem Simp.s_0123456789ab").expect(p1);
        assert!(f < simp && !p1.contains("theorem Eqn.g_1"), "{p1}");
        assert!(
            p2.contains("theorem Eqn.g_1") && !p2.contains("theorem Simp."),
            "{p2}"
        );
        assert!(p1.contains("local macro \"k2l_eqn_r \"") && p1.contains("k2l_case_rec [K.f]"));
        assert!(!p2.contains("k2l_eqn_r"), "{p2}");
        for p in [p1, p2] {
            assert!(p.starts_with("import N.Functions\nimport KPrelude.Tactic\n"));
            assert!(
                p.contains("local macro \"k2l_eqn_a\"")
                    && p.contains("set_option maxHeartbeats 100000")
            );
            assert!(p.ends_with("end N\n"));
        }
        // each theorem's text is the whole module's
        for s in sample() {
            let block = whole
                .split("\n\n")
                .find(|b| b.contains(&format!("theorem {} ", s.name)))
                .unwrap();
            assert_eq!(
                [p1, p2].iter().filter(|p| p.contains(block)).count(),
                1,
                "{block}"
            );
        }
        // a statement heavier than the bound is a part of its own; the weights' sum fixes the
        // fewest parts, and a part is added when the statements do not fit them
        // an open obligation stays in its proof's part: opening `Eqn.g_1` moves no statement
        let open_g: BTreeSet<String> = ["Eqn.g_1".to_string()].into();
        let reparts = emit_modules(
            "N",
            &sample(),
            &open_g,
            &[],
            &defs,
            &rec,
            &BTreeSet::new(),
            4,
            &bd,
        );
        assert_eq!(reparts.len(), 3);
        assert!(reparts[0].1.contains("theorem Eqn.f_1") && reparts[0].1.contains("theorem Simp."));
        assert!(
            reparts[1].1.contains("def Eqn.g_1.statement : Prop"),
            "{}",
            reparts[1].1
        );
        // the module's budget in its header, a theorem's own before it
        let mut own = Budget::default();
        own.per_theorem.insert("Eqn.g_1".into(), 400_000);
        let b = emit_with(
            "N",
            &sample(),
            &open,
            &[],
            &defs,
            &rec,
            &BTreeSet::new(),
            &own,
        );
        assert!(b.contains("set_option maxHeartbeats 100000\n"));
        assert!(
            b.contains("set_option maxHeartbeats 400000 in\n/-- "),
            "{b}"
        );
        assert_eq!(b.matches(" in\n/-- ").count(), 1);
        let tiny = emit_modules(
            "N",
            &sample(),
            &open,
            &[],
            &defs,
            &rec,
            &BTreeSet::new(),
            1,
            &bd,
        );
        assert_eq!(tiny.len(), 4);
    }

    /// The overrides file names generated theorems only: a name that no statement has (a renamed
    /// or removed theorem) is an error, and so is a line without a positive budget.
    #[test]
    fn overrides_name_generated_theorems() {
        let mut b = Budget::default();
        b.read_overrides("# comment\n\nEqn.g_1 400000\n", &sample())
            .unwrap();
        assert_eq!(b.per_theorem.get("Eqn.g_1"), Some(&400_000));
        let e = Budget::default()
            .read_overrides("Eqn.g_1 400000\nEqn.gone_1 400000\n", &sample())
            .unwrap_err();
        assert!(e.contains("Eqn.gone_1") && !e.contains("Eqn.g_1\""), "{e}");
        for bad in ["Eqn.g_1", "Eqn.g_1 many", "Eqn.g_1 0"] {
            assert!(
                Budget::default().read_overrides(bad, &sample()).is_err(),
                "{bad}"
            );
        }
    }

    /// Statements of equal weight go round the parts in turn, so that consecutive statements (one
    /// function's) are spread over all of them; a part is added when the least loaded one cannot
    /// take the next statement.
    #[test]
    fn parts_spread_and_fit() {
        assert_eq!(parts(&[1; 6], 2), vec![vec![0, 3], vec![1, 4], vec![2, 5]]);
        // two parts (12 over 6) do not fit 3, 3, 2, 2, 2: the last 2 meets loads 5 and 5
        assert_eq!(
            parts(&[3, 3, 2, 2, 2], 6),
            vec![vec![0, 4], vec![1], vec![2, 3]]
        );
        assert_eq!(parts(&[9, 1], 4), vec![vec![0], vec![1]]);
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
