//! The initial configuration (`init`), from the configuration declaration as compiled KORE
//! records it.
//!
//! K compiles `configuration <k> $PGM:Stmt </k> <env> $ENV:Map </env> …` into the function
//! named by the definition's `topCellInitializer` attribute (`initGeneratedTopCell`), with one
//! function `initXCell` per cell, each defined by a single unconditional equation over the map
//! `Init` of configuration variables:
//! `initKCell(Init) = <k> project:Stmt(#unboxKConfigValue(Init[$PGM])) ~> .K </k>`.
//! `krun` builds the initial configuration of an input as `initGeneratedTopCell(Init)` with
//! `Init` mapping each `$X` to `#KConfigValue(t)` for the parsed term `t` of `$X`'s declared sort.
//!
//! `init` is that term with
//! - every application of a function with a single unconditional equation over variables (the
//!   cell initializers, and constants such as `#stdin`) replaced by the equation's right-hand
//!   side, which the equation makes equal to it;
//! - every `project:S(#unboxKConfigValue(Init[$X]))` replaced by a parameter `x : S`: for
//!   `Init[$X] = #KConfigValue(t)` with `t` of sort `S`, the lookup is `#KConfigValue(t)`, the
//!   unboxing `t`, and the projection to `S` is `t` itself.
//!
//! So `init x₁ … xₙ` is the configuration `krun` starts from when `$Xᵢ` is `xᵢ`, and every cell
//! that holds no configuration variable is at the default the declaration gives it.

use crate::funcs::Equation;
use crate::ir::{Def, P, S};
use crate::lower::{Fns, Lower};
use crate::model::Model;
use crate::names;
use std::collections::{BTreeMap, BTreeSet};

/// A configuration variable: its name (`$PGM`), the KORE variable standing for it in the
/// expanded term, and its declared sort.
#[derive(Clone, Debug)]
pub struct ConfigVar {
    pub name: String,
    pub kore_var: String,
    pub sort: String,
}

/// The initial configuration term with the configuration variables as KORE variables.
pub struct InitTerm {
    pub term: P,
    pub vars: Vec<ConfigVar>,
}

fn initializer(def: &Def) -> Option<String> {
    match def.attrs.get("topCellInitializer")? {
        P::App(_, _, args) => args.first()?.app_name().map(|s| s.to_string()),
        _ => None,
    }
}

/// A single unconditional equation `f(X₁, …, Xₙ) = rhs` over distinct variables.
fn single_equation<'a>(
    f: &str,
    eqs: &'a BTreeMap<String, Vec<Equation>>,
) -> Option<(Vec<String>, &'a P)> {
    let v = eqs.get(f)?;
    let [e] = v.as_slice() else { return None };
    if !e.requires.is_empty() || e.owise {
        return None;
    }
    let mut xs = Vec::new();
    for a in &e.args {
        let P::Var(x, _) = a else { return None };
        if xs.contains(x) {
            return None;
        }
        xs.push(x.clone());
    }
    Some((xs, &e.rhs))
}

fn subst(p: &P, s: &BTreeMap<String, P>) -> P {
    match p {
        P::Var(x, _) => s.get(x).cloned().unwrap_or_else(|| p.clone()),
        P::App(f, ps, args) => P::App(
            f.clone(),
            ps.clone(),
            args.iter().map(|a| subst(a, s)).collect(),
        ),
        P::And(srt, ps) => P::And(srt.clone(), ps.iter().map(|a| subst(a, s)).collect()),
        other => other.clone(),
    }
}

/// `project:S(#unboxKConfigValue(Map:lookup(_, inj(\dv{KConfigVar}("$X")))))` → (`$X`, `S`).
fn config_lookup(p: &P, def: &Def) -> Option<(String, String)> {
    let P::App(proj, _, a) = p else { return None };
    if !names::demangle(proj).starts_with("project:") {
        return None;
    }
    let P::App(unbox, _, a) = a.first()? else {
        return None;
    };
    if names::demangle(unbox) != "#unboxKConfigValue" {
        return None;
    }
    let P::App(lookup, _, a) = a.first()? else {
        return None;
    };
    if names::demangle(lookup) != "Map:lookup" {
        return None;
    }
    let mut key = a.get(1)?;
    while let P::App(i, _, b) = key {
        if i != "inj" {
            break;
        }
        key = b.first()?;
    }
    let P::Dv(ks, name) = key else { return None };
    if ks.name() != Some("SortKConfigVar") {
        return None;
    }
    let sort = def.symbols.get(proj)?.result.name()?.to_string();
    Some((name.clone(), sort))
}

/// The expanded initial configuration (module documentation), or why there is none.
pub fn term(def: &Def, eqs: &BTreeMap<String, Vec<Equation>>) -> Result<InitTerm, String> {
    let f = initializer(def).ok_or("no topCellInitializer attribute")?;
    let d = def
        .symbols
        .get(&f)
        .ok_or(format!("initializer {f} is not declared"))?;
    // the initializer's arguments: the configuration-variable map (a variable)
    let args: Vec<P> = d
        .args
        .iter()
        .enumerate()
        .map(|(i, s)| P::Var(format!("Var'Init'{i}"), s.clone()))
        .collect();
    let mut vars: Vec<ConfigVar> = Vec::new();
    fn go(
        p: &P,
        def: &Def,
        eqs: &BTreeMap<String, Vec<Equation>>,
        vars: &mut Vec<ConfigVar>,
        depth: usize,
    ) -> Result<P, String> {
        if depth > 64 {
            return Err("initializer equations nest too deeply".into());
        }
        if let Some((name, sort)) = config_lookup(p, def) {
            let kore_var = format!("Var'Config'{}", name.trim_start_matches('$'));
            match vars.iter().find(|v| v.name == name) {
                Some(v) if v.sort != sort => {
                    return Err(format!(
                        "configuration variable {name} is read at sorts {} and {sort}",
                        v.sort
                    ));
                }
                Some(_) => {}
                None => vars.push(ConfigVar {
                    name,
                    kore_var: kore_var.clone(),
                    sort: sort.clone(),
                }),
            }
            return Ok(P::Var(kore_var, S::App(sort, vec![])));
        }
        match p {
            P::App(f, ps, args) => {
                let args: Vec<P> = args
                    .iter()
                    .map(|a| go(a, def, eqs, vars, depth))
                    .collect::<Result<_, _>>()?;
                if def.symbols.get(f).is_some_and(|s| s.is_function())
                    && let Some((xs, rhs)) = single_equation(f, eqs)
                {
                    let s: BTreeMap<String, P> = xs.into_iter().zip(args).collect();
                    return go(&subst(rhs, &s), def, eqs, vars, depth + 1);
                }
                Ok(P::App(f.clone(), ps.clone(), args))
            }
            other => Ok(other.clone()),
        }
    }
    let t = go(&P::App(f, vec![], args), def, eqs, &mut vars, 0)?;
    fn mentions_init(p: &P) -> bool {
        match p {
            P::Var(x, _) => x.starts_with("Var'Init'"),
            P::App(_, _, args) | P::And(_, args) => args.iter().any(mentions_init),
            _ => false,
        }
    }
    if mentions_init(&t) {
        return Err(
            "the configuration-variable map is used other than by looking up a variable".into(),
        );
    }
    Ok(InitTerm { term: t, vars })
}

/// The functions `init` still applies (to generate them).
pub fn functions(t: &InitTerm, def: &Def) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    crate::funcs::applied(&t.term, def, &mut out);
    out
}

/// A parameter name for configuration variable `$X`: `x` in lower case.
pub fn param_name(v: &str) -> String {
    let s: String = v
        .trim_start_matches('$')
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() {
                c.to_ascii_lowercase()
            } else {
                '_'
            }
        })
        .collect();
    if s.is_empty() || s.starts_with(|c: char| c.is_ascii_digit()) {
        format!("v{s}")
    } else {
        s
    }
}

/// The parameters of `init`, one per configuration variable: (Lean name, Lean type, `$X`).
pub type InitParams = Vec<(String, String, String)>;

/// `{ns}/Init.lean`, and the parameters of `init`.
pub fn emit(
    t: &InitTerm,
    m: &Model,
    fns: &Fns,
    top: &str,
    ns: &str,
) -> Result<(String, InitParams), String> {
    let mut lw = Lower::new(m, fns, &["init"]);
    let mut params = Vec::new();
    for v in &t.vars {
        if !m.sorts.contains_key(&v.sort) {
            return Err(format!(
                "configuration variable {} has sort {}, which has no values in the model",
                v.name, v.sort
            ));
        }
        let n = lw.param(&param_name(&v.name), &v.sort);
        lw.vars.insert(v.kore_var.clone(), n.clone());
        params.push((n, v.sort.clone(), v.name.clone()));
    }
    let e = lw.expr(&t.term, top)?;
    if !lw.steps.is_empty() {
        return Err("the initial configuration applies a partial function".into());
    }
    let needs_functions = {
        let mut fs = BTreeSet::new();
        fn calls(p: &P, fns: &Fns, out: &mut BTreeSet<String>) {
            if let P::App(f, _, args) = p {
                if fns.contains_key(f) {
                    out.insert(f.clone());
                }
                args.iter().for_each(|a| calls(a, fns, out));
            }
        }
        calls(&t.term, fns, &mut fs);
        fs.iter().any(|f| fns[f].lean.starts_with("K."))
    };
    let import = if needs_functions {
        "Functions"
    } else {
        "Terms"
    };
    let sig: String = params
        .iter()
        .map(|(n, s, _)| format!(" ({n} : {s})"))
        .collect();
    let vars_doc: Vec<String> = params
        .iter()
        .map(|(n, s, v)| format!("`{n} : {s}` for `{v}`"))
        .collect();
    let vars_doc = if vars_doc.is_empty() {
        "no configuration variables".to_string()
    } else {
        vars_doc.join(", ")
    };
    let text = format!(
        "import {ns}.{import}\n\n/-! Generated by k2lean; do not edit.\n\n\
The initial configuration of the configuration declaration: the configuration `krun` starts\n\
from, with each configuration variable a parameter of its declared sort ({vars_doc}) and\n\
every other cell at the default the declaration gives it. -/\n\n\
namespace {ns}\n\nopen KPrelude\n\n\
/-- The initial configuration for the configuration variables {}. -/\n\
def init{sig} : {top} :=\n  {}\n\nend {ns}\n",
        params
            .iter()
            .map(|(_, _, v)| format!("`{v}`"))
            .collect::<Vec<_>>()
            .join(", "),
        e.render()
    );
    Ok((text, params))
}

/// A theorem that configuration `d` (a definition of the top sort) is `init` at some values of
/// the configuration variables: it holds exactly when every cell of `d` that holds no
/// configuration variable is the declared default. A value given in `witnesses` is written out;
/// the others (`None`) are found by unification. The proof is `rfl`: both sides compute to the
/// same value.
pub fn check_theorem(vars: &[ConfigVar], d: &str, witnesses: &[Option<String>]) -> String {
    let binders: String = vars
        .iter()
        .map(|v| format!(" ({} : {})", param_name(&v.name), v.sort))
        .collect();
    let args: String = vars
        .iter()
        .map(|v| format!(" {}", param_name(&v.name)))
        .collect();
    let holes: String = (0..vars.len())
        .map(|i| {
            format!(
                "{}, ",
                witnesses
                    .get(i)
                    .cloned()
                    .flatten()
                    .unwrap_or_else(|| "_".into())
            )
        })
        .collect();
    let ex = if vars.is_empty() {
        String::new()
    } else {
        format!("∃{binders}, ")
    };
    let proof = if vars.is_empty() {
        "rfl".to_string()
    } else {
        format!("⟨{holes}rfl⟩")
    };
    format!("theorem {d}_is_init : {ex}init{args} = {d} := {proof}\n")
}

/// Whether configuration variable `v` occurs under a function application in the initial
/// configuration (a collection operation such as `ListItem`): unification cannot find its value
/// through the function, so a check gives it explicitly.
pub fn under_function(t: &InitTerm, v: &ConfigVar, def: &Def) -> bool {
    fn go(p: &P, v: &str, def: &Def, under: bool) -> bool {
        match p {
            P::Var(x, _) => under && x == v,
            P::App(f, _, args) => {
                let u = under || def.symbols.get(f).is_some_and(|s| s.is_function());
                args.iter().any(|a| go(a, v, def, u))
            }
            _ => false,
        }
    }
    go(&t.term, &v.kore_var, def, false)
}

/// The values of the configuration variables in a configuration that `init` produces (a KORE
/// term, as krust prints it), by matching it against the initial configuration with the
/// variables free; an associative collection operation (an `element` or `assoc` symbol) is matched
/// up to its nesting, since printers associate it either way.
pub fn witnesses(t: &InitTerm, actual: &P, def: &Def) -> Option<Vec<P>> {
    let assoc = |f: &str| {
        def.symbols
            .get(f)
            .is_some_and(|s| s.attrs.has("assoc") || s.attrs.has("element"))
    };
    fn flat<'a>(p: &'a P, f: &str, out: &mut Vec<&'a P>) {
        match p {
            P::App(g, _, args) if g == f && args.len() == 2 => {
                flat(&args[0], f, out);
                flat(&args[1], f, out);
            }
            other => out.push(other),
        }
    }
    fn m<'a>(
        pat: &P,
        act: &'a P,
        assoc: &dyn Fn(&str) -> bool,
        out: &mut BTreeMap<String, &'a P>,
    ) -> bool {
        match (pat, act) {
            (P::Var(x, _), _) if x.starts_with("Var'Config'") => match out.get(x) {
                Some(prev) => *prev == act,
                None => {
                    out.insert(x.clone(), act);
                    true
                }
            },
            (P::App(f, fp, fa), P::App(g, gp, ga)) if f == g && fp == gp => {
                if assoc(f) && fa.len() == 2 {
                    let (mut xs, mut ys) = (Vec::new(), Vec::new());
                    flat(pat, f, &mut xs);
                    flat(act, f, &mut ys);
                    xs.len() == ys.len() && xs.iter().zip(&ys).all(|(x, y)| m(x, y, assoc, out))
                } else {
                    fa.len() == ga.len() && fa.iter().zip(ga).all(|(x, y)| m(x, y, assoc, out))
                }
            }
            (a, b) => a == b,
        }
    }
    let mut out = BTreeMap::new();
    if !m(&t.term, actual, &assoc, &mut out) {
        return None;
    }
    t.vars
        .iter()
        .map(|v| out.get(&v.kore_var).map(|p| (*p).clone()))
        .collect()
}

/// The definition's initial configuration, when it has one.
pub fn of(def: &Def) -> Option<InitTerm> {
    term(def, &crate::funcs::equations(def)).ok()
}

/// The check of configuration `d` (KORE `actual`, Lean definition `d`): the values of the
/// configuration variables under a function are written out (rendered by `value`).
pub fn check(
    t: &InitTerm,
    def: &Def,
    d: &str,
    actual: &P,
    value: &dyn Fn(&P, &str) -> Option<String>,
) -> String {
    let ws = witnesses(t, actual, def);
    let given: Vec<Option<String>> = t
        .vars
        .iter()
        .enumerate()
        .map(|(i, v)| {
            if !under_function(t, v, def) {
                return None;
            }
            ws.as_ref().and_then(|w| value(&w[i], &v.sort))
        })
        .collect();
    check_theorem(&t.vars, d, &given)
}
