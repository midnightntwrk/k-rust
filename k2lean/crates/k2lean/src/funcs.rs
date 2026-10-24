//! Functions: hooks from the registry, and functions defined by KORE equations, which become
//! Lean definitions.
//!
//! A function's equations are tried in priority order (`owise` last). An equation applies when
//! its argument patterns match and its requires is `true`; the first that applies gives the value,
//! even when its right-hand side is undefined (no fall-through on `⊥`, unlike an `<|>` cascade).
//! An `owise` equation's KORE guard is the negation of its competitors' applicability, which is
//! exactly what the cascade position realizes. Where no equation applies the result is `none`
//! (the least-defined model; KORE leaves the value unconstrained there).

use crate::hooks;
use crate::ir::{Def, P};
use crate::lower::{FnSig, Fns, L, Lower};
use crate::model::{Model, sort_name};
use crate::names;
use crate::render;
use std::collections::{BTreeMap, BTreeSet};

pub struct Equation {
    pub args: Vec<P>,
    pub requires: Vec<P>,
    pub rhs: P,
    pub priority: i64,
    pub index: usize,
    pub owise: bool,
    pub uid: String,
}

/// Equations of each function symbol (simplification rules excluded).
pub fn equations(def: &Def) -> BTreeMap<String, Vec<Equation>> {
    let mut out: BTreeMap<String, Vec<Equation>> = BTreeMap::new();
    for a in &def.axioms {
        if a.attrs.has("simplification") || !a.params.iter().all(|p| p == "R") {
            continue;
        }
        let P::Implies(_, left, right) = &a.pattern else {
            continue;
        };
        let P::Equals(_, _, lhs, rhs) = &**right else {
            continue;
        };
        let P::App(f, _, fargs) = &**lhs else {
            continue;
        };
        if !def.symbols.get(f).is_some_and(|s| s.is_function()) {
            continue;
        }
        let mut conj = Vec::new();
        flatten_and(left, &mut conj);
        let mut ins: BTreeMap<String, P> = BTreeMap::new();
        let mut requires = Vec::new();
        for c in conj {
            match c {
                P::Top(_) => {}
                P::In(_, _, x, p) => {
                    if let P::Var(n, _) = &**x {
                        ins.insert(n.clone(), (**p).clone());
                    }
                }
                P::Not(..) => {} // owise guard: realized by the cascade order
                P::Equals(..) => requires.push(c.clone()),
                other => requires.push(other.clone()),
            }
        }
        let args: Vec<P> = fargs
            .iter()
            .map(|x| match x {
                P::Var(n, _) => ins.get(n).cloned().unwrap_or_else(|| x.clone()),
                other => other.clone(),
            })
            .map(|x| normalize_consts(&x, def))
            .collect();
        let rhs = match &**rhs {
            P::And(_, parts) if parts.len() == 2 && matches!(parts[1], P::Top(_)) => {
                parts[0].clone()
            }
            other => other.clone(),
        };
        let owise = a.attrs.has("owise");
        let priority = if owise {
            200
        } else {
            a.attrs
                .string("priority")
                .and_then(|p| p.parse().ok())
                .unwrap_or(50)
        };
        out.entry(f.clone()).or_default().push(Equation {
            args,
            requires,
            rhs,
            priority,
            index: a.index,
            owise,
            uid: a.attrs.string("UNIQUE'Unds'ID").unwrap_or_default(),
        });
    }
    // overload axioms `f_super(inj(x)…) = inj(f_sub(x…))` (`symbol-overload`): the super symbol
    // is normalized to the sub symbol wherever its arguments allow (K applies them anywhere)
    for a in &def.axioms {
        if !a.attrs.has("symbol-overload") {
            continue;
        }
        let P::Equals(_, _, lhs, rhs) = &a.pattern else {
            continue;
        };
        let P::App(f, _, fargs) = &**lhs else {
            continue;
        };
        out.entry(f.clone()).or_default().push(Equation {
            args: fargs.clone(),
            requires: vec![],
            rhs: (**rhs).clone(),
            priority: 50,
            index: a.index,
            owise: false,
            uid: format!("overload-{}", a.index),
        });
    }
    for v in out.values_mut() {
        v.sort_by_key(|e| (e.priority, e.index));
    }
    out
}

/// The symbols that overload axioms normalize (the super symbols), with their 0-ary normal forms.
pub fn overload_supers(def: &Def) -> BTreeSet<String> {
    def.axioms
        .iter()
        .filter(|a| a.attrs.has("symbol-overload"))
        .filter_map(|a| match &a.pattern {
            P::Equals(_, _, l, _) => l.app_name().map(|s| s.to_string()),
            _ => None,
        })
        .collect()
}

/// Replace the overloaded constants of a pattern by their normal forms (`.Ids` is
/// `inj{Bottoms, Ids}(.Bottoms)`), so that left-hand sides match normal-form values.
pub fn normalize_consts(p: &P, def: &Def) -> P {
    fn norm_const(f: &str, def: &Def, depth: usize) -> Option<P> {
        if depth > 8 {
            return None;
        }
        for a in &def.axioms {
            if !a.attrs.has("symbol-overload") {
                continue;
            }
            let P::Equals(_, _, l, r) = &a.pattern else {
                continue;
            };
            let P::App(g, _, args) = &**l else { continue };
            if g != f || !args.is_empty() {
                continue;
            }
            // r = inj{Sub,Super}(h())
            if let P::App(i, ps, inner) = &**r
                && i == "inj"
                && let Some(P::App(h, _, hargs)) = inner.first()
                && hargs.is_empty()
                && let Some(P::App(i2, ps2, inner2)) = norm_const(h, def, depth + 1)
            {
                // inj{A,Sub}(x) under inj{Sub,Super}: inj{A,Super}(x)
                if i2 == "inj" {
                    return Some(P::App(
                        "inj".into(),
                        vec![ps2[0].clone(), ps[1].clone()],
                        inner2,
                    ));
                }
            }
            return Some((**r).clone());
        }
        None
    }
    match p {
        P::App(f, sp, args) if args.is_empty() && f != "dotk" => {
            norm_const(f, def, 0).unwrap_or_else(|| P::App(f.clone(), sp.clone(), vec![]))
        }
        P::App(f, sp, args) => P::App(
            f.clone(),
            sp.clone(),
            args.iter().map(|a| normalize_consts(a, def)).collect(),
        ),
        P::And(s, ps) => P::And(
            s.clone(),
            ps.iter().map(|a| normalize_consts(a, def)).collect(),
        ),
        other => other.clone(),
    }
}

pub fn flatten_and<'a>(p: &'a P, out: &mut Vec<&'a P>) {
    match p {
        P::And(_, ps) => ps.iter().for_each(|q| flatten_and(q, out)),
        other => out.push(other),
    }
}

/// Function symbols applied in a pattern.
pub fn applied(p: &P, def: &Def, out: &mut BTreeSet<String>) {
    match p {
        P::App(f, _, args) => {
            if def.symbols.get(f).is_some_and(|s| s.is_function()) {
                out.insert(f.clone());
            }
            args.iter().for_each(|a| applied(a, def, out));
        }
        P::And(_, ps) | P::Or(_, ps) => ps.iter().for_each(|q| applied(q, def, out)),
        P::Not(_, a)
        | P::Ceil(_, _, a)
        | P::Floor(_, _, a)
        | P::Exists(_, _, _, a)
        | P::Forall(_, _, _, a) => applied(a, def, out),
        P::Implies(_, a, b)
        | P::Iff(_, a, b)
        | P::Rewrites(_, a, b)
        | P::Equals(_, _, a, b)
        | P::In(_, _, a, b) => {
            applied(a, def, out);
            applied(b, def, out);
        }
        _ => {}
    }
}

/// The `anywhere`/overloaded constructor symbols applied in a pattern.
pub fn applied_ctors(p: &P, anywhere: &BTreeSet<String>, out: &mut BTreeSet<String>) {
    match p {
        P::App(f, _, args) => {
            if anywhere.contains(f) {
                out.insert(f.clone());
            }
            args.iter().for_each(|a| applied_ctors(a, anywhere, out));
        }
        P::And(_, ps) | P::Or(_, ps) => ps.iter().for_each(|q| applied_ctors(q, anywhere, out)),
        P::Equals(_, _, a, b) | P::In(_, _, a, b) => {
            applied_ctors(a, anywhere, out);
            applied_ctors(b, anywhere, out);
        }
        _ => {}
    }
}

pub struct Generated {
    pub fns: Fns,
    /// The hooks without an implementation in the hook library, and the functions with neither
    /// equations nor a hook: parameters of the generated library (the fields of its `Hooks`
    /// class), as (field name, argument sorts, result sort).
    pub params: Vec<(String, Vec<String>, String)>,
    pub lean: String,
    /// Names to unfold in generated proofs.
    pub unfold: Vec<String>,
    /// Lean names of the functions on a call cycle (well-founded recursive, `Option`-valued); not
    /// in `unfold`, since `simp` cannot unfold a well-founded definition.
    pub recursive: BTreeSet<String>,
    /// Lean names of the recursive functions that recurse on a builtin `List` parameter (the length
    /// measure of `list_measure`).
    pub list_recursive: BTreeSet<String>,
    pub notes: Vec<String>,
}

/// Lean name of a generated function.
pub fn fn_name(sym: &str) -> String {
    format!("K.{}", names::ident(&names::demangle(sym)))
}

/// The match steps, the number of left-hand-side steps and the right-hand side of one equation.
fn lower_equation(
    m: &Model,
    fns: &Fns,
    f: &str,
    sig: &FnSig,
    params: &[String],
    e: &Equation,
) -> Result<(Vec<crate::lower::Step>, usize, crate::lower::L), String> {
    let mut lw = Lower::new(m, fns, &[]);
    for (p, s) in params.iter().zip(&sig.args) {
        lw.param(p, s);
    }
    let err = |err: String| format!("{} equation {}: {err}", names::demangle(f), e.uid);
    for ((a, p), s) in e.args.iter().zip(params).zip(&sig.args) {
        lw.pat(a, p, s, true).map_err(err)?;
    }
    lw.finish_lhs().map_err(err)?;
    for r in &e.requires {
        lw.cond(r).map_err(err)?;
    }
    let lhs_len = lw.steps.len();
    let rhs = lw.expr(&e.rhs, &sig.result).map_err(err)?;
    Ok((lw.steps, lhs_len, rhs))
}

/// The constructor term of an `anywhere` symbol applied to the parameters.
fn anywhere_ctor(m: &Model, f: &str, params: &[String]) -> crate::lower::L {
    let ci = &m.ctors[f];
    let own = crate::lower::L::app(
        m.ctor_path(f),
        params
            .iter()
            .map(|p| crate::lower::L::Var(p.clone()))
            .collect(),
    );
    if m.sort(&ci.sort).is_simple() {
        own
    } else {
        crate::lower::L::app(m.leaf_ctor(&ci.sort, &ci.sort), vec![own])
    }
}

/// Tarjan's algorithm: the strongly connected components of `nodes` under `calls`, each
/// component after the components it calls.
fn sccs(nodes: &[String], calls: &BTreeMap<String, BTreeSet<String>>) -> Vec<Vec<String>> {
    struct St<'a> {
        calls: &'a BTreeMap<String, BTreeSet<String>>,
        nodes: &'a BTreeSet<String>,
        index: BTreeMap<String, usize>,
        low: BTreeMap<String, usize>,
        on: BTreeSet<String>,
        stack: Vec<String>,
        next: usize,
        out: Vec<Vec<String>>,
    }
    fn go(st: &mut St, v: &str) {
        st.index.insert(v.to_string(), st.next);
        st.low.insert(v.to_string(), st.next);
        st.next += 1;
        st.stack.push(v.to_string());
        st.on.insert(v.to_string());
        let succ: Vec<String> = st
            .calls
            .get(v)
            .into_iter()
            .flatten()
            .filter(|w| st.nodes.contains(*w))
            .cloned()
            .collect();
        for w in succ {
            if !st.index.contains_key(&w) {
                go(st, &w);
                let lw = st.low[&w];
                let lv = st.low.get_mut(v).unwrap();
                *lv = (*lv).min(lw);
            } else if st.on.contains(&w) {
                let iw = st.index[&w];
                let lv = st.low.get_mut(v).unwrap();
                *lv = (*lv).min(iw);
            }
        }
        if st.low[v] == st.index[v] {
            let mut comp = Vec::new();
            loop {
                let w = st.stack.pop().unwrap();
                st.on.remove(&w);
                comp.push(w.clone());
                if w == v {
                    break;
                }
            }
            comp.sort();
            st.out.push(comp);
        }
    }
    let set: BTreeSet<String> = nodes.iter().cloned().collect();
    let mut st = St {
        calls,
        nodes: &set,
        index: BTreeMap::new(),
        low: BTreeMap::new(),
        on: BTreeSet::new(),
        stack: vec![],
        next: 0,
        out: vec![],
    };
    for n in nodes {
        if !st.index.contains_key(n) {
            go(&mut st, n);
        }
    }
    st.out
}

/// Per-definition termination inputs (`gen --termination FILE`, a TOML file), keyed by the K
/// function's label as the generated comment prints it (`` `label` (recursive) ``):
///
/// ```toml
/// [functions."qsortJSONs"]
/// termination_by = "sizeOf x0"           # a Lean term over the parameters x0, x1, …
/// decreasing_by = "all_goals …"          # a tactic; replaces the generated one
/// before = """theorem …"""               # declarations emitted before the function's group
/// partial_fixpoint = true                # no measure exists: the least fixed point instead
/// ```
///
/// For the definitions whose termination needs facts about other functions (a filter returns a
/// shorter list, an opcode width is positive) or a measure no generic rule derives. Nothing in
/// it changes what a definition computes: it supplies the proof of termination only.
///
/// `partial_fixpoint` is for a function whose equations do not terminate on some arguments (K
/// gives it no value there): it is defined as the least fixed point of its equations
/// (`partial_fixpoint`, flat order on `Option`), which is `none` exactly where the rewriting
/// diverges and the value of the equations wherever it terminates. Lean proves the equations
/// monotone only in a direct form, so the function is rendered as an `if` chain over the
/// equations' guards with `do` binds on the right-hand sides; this needs every left-hand side
/// to be guards only (no patterns).
#[derive(Default, Clone, Debug)]
pub struct SideEntry {
    pub termination_by: Option<String>,
    pub decreasing_by: Option<String>,
    pub before: Option<String>,
    pub partial_fixpoint: bool,
}

/// The termination inputs of a definition (`SideEntry`), by K function label.
#[derive(Default, Clone, Debug)]
pub struct Sidecar {
    pub functions: BTreeMap<String, SideEntry>,
}

impl Sidecar {
    pub fn load(path: &std::path::Path) -> Result<Sidecar, String> {
        let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        let v: toml::Table = text
            .parse()
            .map_err(|e| format!("{}: {e}", path.display()))?;
        let mut out = Sidecar::default();
        for k in v.keys() {
            if k != "functions" {
                return Err(format!("{}: unknown key {k}", path.display()));
            }
        }
        if let Some(fs) = v.get("functions").and_then(|f| f.as_table()) {
            for (label, e) in fs {
                let t = e
                    .as_table()
                    .ok_or(format!("functions.{label}: not a table"))?;
                for k in t.keys() {
                    if ![
                        "termination_by",
                        "decreasing_by",
                        "before",
                        "partial_fixpoint",
                    ]
                    .contains(&k.as_str())
                    {
                        return Err(format!("functions.{label}: unknown key {k}"));
                    }
                }
                let get = |k: &str| t.get(k).and_then(|x| x.as_str()).map(|x| x.to_string());
                let pf = t
                    .get("partial_fixpoint")
                    .and_then(|x| x.as_bool())
                    .unwrap_or(false);
                out.functions.insert(
                    label.clone(),
                    SideEntry {
                        termination_by: get("termination_by"),
                        decreasing_by: get("decreasing_by"),
                        before: get("before"),
                        partial_fixpoint: pf,
                    },
                );
            }
        }
        Ok(out)
    }

    /// The labels that name no recursive function of the definition (a misspelt key).
    pub fn unknown(&self, recursive_labels: &BTreeSet<String>) -> Vec<String> {
        self.functions
            .keys()
            .filter(|k| !recursive_labels.contains(*k))
            .cloned()
            .collect()
    }
}

/// `ListSizeOf` for each collection sort of the arity-indexed universe (`Term.coll_S l` has
/// `sizeOf` one more than `l`): the size facts of the collection hooks in termination proofs.
pub fn list_size_instances(m: &Model) -> String {
    let mut o = String::new();
    for (s, info) in &m.sorts {
        let crate::model::Kind::Coll(k) = &info.kind else {
            continue;
        };
        let e = &info.elems;
        let elem = match k {
            crate::model::Coll::Map => format!("{} × {}", e[0], e[1]),
            crate::model::Coll::Set => format!("{} × Unit", e[0]),
            crate::model::Coll::List => e[0].clone(),
        };
        o.push_str(&format!(
            "instance : KPrelude.ListSizeOf {s} ({elem}) := ⟨fun _ => by simp [ListIso.ofList, {s}.ofList]⟩\n"
        ));
    }
    if !o.is_empty() {
        o.push('\n');
    }
    o
}

/// `MapSizeOf` for each map sort of the per-sort universe, from the structural facts of
/// `Terms.lean` (`S.sizeOf_lookupR`, `S.sizeOf_eraseR`): the termination facts of a function that
/// recurses on the value or the rest of `K |-> V REST`; `ListSizeAffine` for each list sort (its
/// `sizeOf` is its list's), those of `ListItem(X) REST`.
pub fn map_size_instances(m: &Model) -> String {
    let mut o = String::new();
    for s in &m.block {
        let info = m.sort(s);
        match info.kind {
            crate::model::Kind::Coll(crate::model::Coll::Map) => o.push_str(&format!(
                "instance : KPrelude.MapSizeOf {s} {} {} := ⟨{s}.sizeOf_lookupR, {s}.sizeOf_eraseR⟩\n",
                info.elems[0], info.elems[1]
            )),
            crate::model::Kind::Coll(crate::model::Coll::List) => o.push_str(&format!(
                "instance : KPrelude.ListSizeAffine {s} {} := ⟨⟨0, {s}.sizeOf_ofList_eq⟩⟩\n",
                info.elems[0]
            )),
            _ => {}
        }
    }
    if !o.is_empty() {
        o.push('\n');
    }
    o
}

/// The equations of one function, lowered: (equation index, steps, left-hand-side steps, result).
type Lowered = Vec<(usize, Vec<crate::lower::Step>, usize, L)>;

/// The body of a function defined as a least fixed point: an `if` chain over the equations'
/// guards (in cascade order), each right-hand side a `do` block over its partial calls. Lean's
/// `partial_fixpoint` proves this form monotone (`Option`'s bind); the cascade form is not.
fn render_fixpoint(
    m: &Model,
    f: &str,
    params: &[String],
    lowered: &Lowered,
) -> Result<String, String> {
    use crate::lower::Step;
    let mut o = String::new();
    for (k, (_, steps, lhs_len, rhs)) in lowered.iter().enumerate() {
        let mut conds = Vec::new();
        for s in &steps[..*lhs_len] {
            match s {
                Step::Cond { cond, .. } => conds.push(format!("{} = true", cond.render())),
                Step::CondEq { lhs, rhs, .. } => {
                    conds.push(format!("{} = {}", lhs.render(), rhs.render()))
                }
                _ => {
                    return Err("partial_fixpoint needs left-hand sides made of guards only".into());
                }
            }
        }
        let mut d = String::from("do\n");
        for s in &steps[*lhs_len..] {
            match s {
                Step::Bind { expr, var, .. } => {
                    d.push_str(&format!("      let {var} ← {}\n", expr.render()))
                }
                _ => {
                    return Err(
                        "partial_fixpoint: a right-hand side step that is not a partial call"
                            .into(),
                    );
                }
            }
        }
        d.push_str(&format!("      pure {}\n", rhs.render_arg()));
        let kw = if k == 0 { "  if" } else { "  else if" };
        if conds.is_empty() {
            // an unconditional equation ends the chain
            o.push_str(&format!("{}    {d}", if k == 0 { "" } else { "  else\n" }));
            return Ok(o);
        }
        o.push_str(&format!("{kw} {} then\n    {d}", conds.join(" ∧ ")));
    }
    let fallback = if m.anywhere.contains(f) {
        format!("some {}", anywhere_ctor(m, f, params).render_arg())
    } else {
        "none".to_string()
    };
    o.push_str(&format!("  else {fallback}\n"));
    Ok(o)
}

/// A strongly connected component of recursive functions: one `mutual` block of Option-valued
/// definitions, each cascading over its equations inline; Lean proves termination (structural
/// or well-founded on `sizeOf`, or on a measure from the `--termination` file,
/// `list_measure`, `int_measure` or `termination::plan`, in that order).
fn gen_recursive(
    m: &Model,
    fns: &Fns,
    eqs: &BTreeMap<String, Vec<Equation>>,
    scc: &[String],
    side: &Sidecar,
    list_rec_out: &mut BTreeSet<String>,
) -> Result<String, String> {
    let mut o = String::new();
    // declarations before the group: the file's `before` texts, rank functions of the measures
    let mut pre = String::new();
    let multi = scc.len() > 1;
    let ctors: BTreeMap<String, usize> = m
        .ctors
        .iter()
        .map(|(sym, ci)| (m.ctor_path(sym), ci.args.len()))
        .collect();
    for f in scc {
        let sig = fns[f].clone();
        let params: Vec<String> = (0..sig.args.len()).map(|i| format!("x{i}")).collect();
        let ps: Vec<String> = params
            .iter()
            .zip(&sig.args)
            .map(|(p, s)| format!("({p} : {s})"))
            .collect();
        let label = names::demangle(f);
        let entry = side.functions.get(&label);
        if let Some(b) = entry.and_then(|e| e.before.as_ref()) {
            pre.push_str(&format!(
                "-- termination of `{label}` (from the --termination file)\n{}\n\n",
                b.trim_end()
            ));
        }
        // lower every equation first: the measure is chosen from all of them
        let mut lowered: Lowered = Vec::new();
        let mut measure: Option<String> = None;
        let mut list_rec: Option<(String, String, bool)> = None;
        for (i, e) in eqs[f].iter().enumerate() {
            if e.args
                .iter()
                .any(|a| crate::rules::absent_sort(a, m).is_some())
            {
                continue;
            }
            let (steps, lhs_len, rhs) = lower_equation(m, fns, f, &sig, &params, e)?;
            if measure.is_none() {
                measure = int_measure(scc, &params, e, &steps);
            }
            if measure.is_none() && list_rec.is_none() {
                list_rec = list_measure(scc, &params, &steps);
            }
            lowered.push((i, steps, lhs_len, rhs));
        }
        if entry.is_some_and(|e| e.partial_fixpoint) {
            if multi {
                return Err(format!(
                    "{label}: partial_fixpoint in a mutual group is not supported"
                ));
            }
            let body =
                render_fixpoint(m, f, &params, &lowered).map_err(|e| format!("{label}: {e}"))?;
            o.push_str(&format!(
                "/-! `{label}` (recursive; least fixed point) -/\n"
            ));
            o.push_str(&format!(
                "def {} {} : Option {} :=\n{body}partial_fixpoint\n\n",
                fn_name(f),
                ps.join(" "),
                sig.result
            ));
            continue;
        }
        let side_measure =
            entry.is_some_and(|e| e.termination_by.is_some() || e.decreasing_by.is_some());
        // the list measure (on which the equations' proofs rely) or the integer bound when one
        // applies; else a synthesized one
        let plan = if multi || side_measure || list_rec.is_some() || measure.is_some() {
            None
        } else {
            let eqns: Vec<crate::termination::Eqn> = lowered
                .iter()
                .map(|(_, s, l, _)| crate::termination::Eqn {
                    steps: s,
                    lhs_len: *l,
                })
                .collect();
            crate::termination::plan(&fn_name(f), &params, &sig.args, &eqns, &ctors)
        };
        let named: BTreeSet<usize> = plan.as_ref().map(|p| p.named.clone()).unwrap_or_default();
        let mut body = String::new();
        let mut depth = 0;
        for (li, (i, steps, lhs_len, rhs)) in lowered.iter().enumerate() {
            let lhs_len = *lhs_len;
            let pad = " ".repeat(2 + 2 * depth);
            let leaf = format!("some (some {})", rhs.render_arg());
            let fail = move |k: usize| {
                if k < lhs_len {
                    "none".to_string()
                } else {
                    "some none".to_string()
                }
            };
            // named hypotheses: the termination proof needs the requires and the matched shapes
            let eb = render::exec_first(steps, true, &fail, &leaf, 4 + 2 * depth);
            body.push_str(&format!(
                "{pad}let e{} : Option (Option {}) :=\n{eb}",
                i + 1,
                sig.result
            ));
            // a failed guard-only equation is a hypothesis of the later calls (its negation)
            let h = if named.contains(&li) {
                format!("he{} : ", i + 1)
            } else {
                String::new()
            };
            body.push_str(&format!(
                "{pad}match {h}e{} with\n{pad}| some r => r\n{pad}| none =>\n",
                i + 1
            ));
            depth += 1;
        }
        let pad = " ".repeat(2 + 2 * depth);
        if m.anywhere.contains(f) {
            body.push_str(&format!(
                "{pad}some {}\n",
                anywhere_ctor(m, f, &params).render_arg()
            ));
        } else {
            body.push_str(&format!("{pad}none\n"));
        }
        if let Some(p) = &plan {
            pre.push_str(&p.rank_defs);
        }
        // inside a `mutual` block only declarations may appear, so the note is the definition's
        // docstring there
        let note = if multi { "/--" } else { "/-!" };
        o.push_str(&format!("{note} `{label}` (recursive) -/\n"));
        o.push_str(&format!(
            "def {} {} : Option {} :=\n{body}",
            fn_name(f),
            ps.join(" "),
            sig.result
        ));
        // termination: Lean's measure search (or the integer measure), with a tactic that sees
        // through the injections and the integer hooks of the recursive calls' arguments
        let mut injs: Vec<String> = body
            .split(|c: char| !(c.is_alphanumeric() || c == '_'))
            .filter(|w| {
                w.starts_with("inj_") && w.matches('_').count() >= 2 && !w.contains("inj_Bottoms")
            })
            .map(|w| w.to_string())
            .collect();
        injs.sort();
        injs.dedup();
        let injs: Vec<String> = injs
            .into_iter()
            .filter(|w| body.contains(&format!("{w} ")))
            .collect();
        let mut simp = vec![
            "KPrelude.IntHook.le".to_string(),
            "KPrelude.IntHook.lt".into(),
            "KPrelude.IntHook.add".into(),
            "KPrelude.IntHook.ge".into(),
            "KPrelude.IntHook.gt".into(),
        ];
        simp.extend(
            injs.iter()
                .filter(|w| {
                    !w.contains('.') && m.sorts.keys().any(|s| w.ends_with(names::short_sort(s)))
                })
                .cloned(),
        );
        let side_by = entry.and_then(|e| e.termination_by.as_ref());
        if let Some(t) = side_by {
            o.push_str(&format!("termination_by {t}\n"));
        } else if let Some((meas, _, _)) = &list_rec {
            o.push_str(&format!("termination_by {meas}\n"));
        } else if let (Some(meas), false) = (&measure, side_measure) {
            o.push_str(&format!("termination_by {meas}\n"));
        } else if let Some(p) = &plan {
            o.push_str(&format!("termination_by {}\n", p.measure));
        }
        if let Some(d) = entry.and_then(|e| e.decreasing_by.as_ref()) {
            // a tactic block, indented under `decreasing_by`
            o.push_str("decreasing_by\n");
            for l in d.trim().lines() {
                o.push_str(&format!("  {l}\n"));
            }
        } else if let (None, Some((_, hyp, front))) = (side_by, &list_rec) {
            list_rec_out.insert(fn_name(f));
            // the list is `ListItem(X) REST` (`REST ListItem(X)`), so `REST` is one shorter
            let lemma = if *front {
                "concat_element_of_uncons"
            } else {
                "concat_element_of_unsnoc"
            };
            o.push_str(&format!(
                "decreasing_by all_goals (simp_wf; rw [← KPrelude.ListHook.{lemma} {hyp}]; simp [KPrelude.ListHook.concat, KPrelude.ListHook.element, KPrelude.ListIso.toList_ofList])\n"
            ));
        } else {
            // the prelude's termination tactic (its facts, then `omega`; the rank functions of
            // the measure unfolded), then the earlier generic one (`sizeOf` of constructor
            // patterns, which `simp_all` unfolds)
            let ranks = plan
                .as_ref()
                .map(|p| p.rank_names.join(", "))
                .unwrap_or_default();
            o.push_str(&format!(
                "decreasing_by all_goals first\n  | k2l_decreasing [{ranks}]\n  | (simp_wf; (try subst_vars); (try simp_all [{}]); (try omega))\n",
                simp.join(", ")
            ));
        }
        o.push('\n');
    }
    if multi {
        o = format!("mutual\n{o}end\n\n");
    }
    Ok(format!("{pre}{o}"))
}

/// The length measure of a function that recurses on a builtin `List` parameter: an equation that
/// matches `ListItem(X) REST` (or `REST ListItem(X)`) directly on parameter `x_i` (one element, so
/// the rest is one shorter, by `ListHook.concat_element_of_uncons`). Lean's `sizeOf` does not see through
/// the list carrier's `ListIso`, so the measure is the length of `toList x_i`.
fn list_measure(
    scc: &[String],
    params: &[String],
    steps: &[crate::lower::Step],
) -> Option<(String, String, bool)> {
    if scc.len() != 1 {
        return None;
    }
    let elems: Vec<(&String, &String, bool)> = steps
        .iter()
        .filter_map(|s| match s {
            crate::lower::Step::ListElem {
                list, hyp, front, ..
            } => Some((list, hyp, *front)),
            _ => None,
        })
        .collect();
    match elems.as_slice() {
        [(list, hyp, front)] if params.contains(list) => Some((
            format!("(KPrelude.ListIso.toList {list}).length"),
            hyp.to_string(),
            *front,
        )),
        _ => None,
    }
}

/// An integer measure for a function that counts a parameter up to a bound: an equation whose
/// requires says `x_i <=Int x_j` (or `<Int`) and whose right-hand side calls the function with
/// `x_i +Int c` at position `i` and `x_j` unchanged at `j`. The measure is `(x_j + 1 - x_i).toNat`.
fn int_measure(
    scc: &[String],
    params: &[String],
    e: &Equation,
    _steps: &[crate::lower::Step],
) -> Option<String> {
    if scc.len() != 1 {
        return None;
    }
    let pos = |p: &P| -> Option<usize> {
        let P::Var(v, _) = p else { return None };
        e.args
            .iter()
            .position(|a| matches!(a, P::Var(w, _) if w == v))
    };
    for r in &e.requires {
        let P::Equals(_, _, l, _) = r else { continue };
        let P::App(cmp, _, args) = &**l else { continue };
        let d = names::demangle(cmp);
        if !(d.starts_with("_<=Int_") || d.starts_with("_<Int_")) || args.len() != 2 {
            continue;
        }
        if let (Some(i), Some(j)) = (pos(&args[0]), pos(&args[1])) {
            let _ = &params;
            return Some(format!("(x{j} + 1 - x{i}).toNat"));
        }
    }
    None
}

/// The adapters of `BYTES.int2bytes` and `BYTES.bytes2int` (the prelude's `BytesHook.int2bytes`
/// and `bytes2int` take the byte order and signedness as `Bool` flags), when the definition
/// declares the constructors `domains.md` gives these arguments: (Lean name, definition).
fn bytes_adapter(
    m: &Model,
    hook: Option<&str>,
    args: &[String],
    result: &str,
) -> Option<(String, String)> {
    let ctor = |k: &str| m.ctors.get(k).map(|_| m.ctor_path(k));
    let big = ctor("LblbigEndianBytes")?;
    match (hook?, args) {
        ("BYTES.int2bytes", [l, i, e]) => Some((
            "K.hook_int2bytes".into(),
            format!(
                "/-- `BYTES.int2bytes`, with the byte order compared with `bigEndianBytes`. -/
def K.hook_int2bytes (len : {l}) (i : {i}) (e : {e}) : {result} :=
  KPrelude.BytesHook.int2bytes len i (decide (e = {big}))

"
            ),
        )),
        ("BYTES.bytes2int", [b, e, sg]) => {
            let signed = ctor("LblsignedBytes")?;
            Some((
                "K.hook_bytes2int".into(),
                format!(
                    "/-- `BYTES.bytes2int`, with the byte order and signedness compared with `bigEndianBytes`
and `signedBytes`. -/
def K.hook_bytes2int (b : {b}) (e : {e}) (s : {sg}) : {result} :=
  KPrelude.BytesHook.bytes2int b (decide (e = {big})) (decide (s = {signed}))

"
                ),
            ))
        }
        _ => None,
    }
}

pub fn generate(def: &Def, m: &Model, roots: &BTreeSet<String>) -> Result<Generated, String> {
    generate_with(def, m, roots, &Sidecar::default())
}

/// `generate` with per-definition termination inputs (`Sidecar`).
pub fn generate_with(
    def: &Def,
    m: &Model,
    roots: &BTreeSet<String>,
    side: &Sidecar,
) -> Result<Generated, String> {
    let eqs = equations(def);
    // close over calls
    let mut used: BTreeSet<String> = BTreeSet::new();
    let mut todo: Vec<String> = roots.iter().cloned().collect();
    let mut calls: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    while let Some(f) = todo.pop() {
        if !used.insert(f.clone()) {
            continue;
        }
        let sym = &def.symbols[&f];
        if hooks::for_symbol(sym).is_some() {
            continue;
        }
        let mut cs = BTreeSet::new();
        for e in eqs.get(&f).into_iter().flatten() {
            applied(&e.rhs, def, &mut cs);
            for r in &e.requires {
                applied(r, def, &mut cs);
            }
            for a in &e.args {
                applied(a, def, &mut cs);
            }
            // normalized constructors (`anywhere`, overloads) are calls in right-hand sides
            applied_ctors(&e.rhs, &m.anywhere, &mut cs);
        }
        for c in &cs {
            todo.push(c.clone());
        }
        calls.insert(f, cs);
    }
    // signatures
    let mut fns: Fns = BTreeMap::new();
    let mut notes = Vec::new();
    let mut params: Vec<(String, Vec<String>, String)> = Vec::new();
    let mut helpers = String::new();
    for f in &used {
        let sym = &def.symbols[f];
        let args: Option<Vec<String>> = sym.args.iter().map(sort_name).collect();
        let result = sort_name(&sym.result);
        if let Some(h) = hooks::for_symbol(sym) {
            // parametric hooks (`#if`) get their sorts at the use site; record a generic entry
            let (args, result) = match (args, result) {
                (Some(a), Some(r)) => (a, r),
                _ => (vec!["?".into(); sym.args.len()], "?".into()),
            };
            fns.insert(
                f.clone(),
                FnSig {
                    lean: h.lean.to_string(),
                    partial: h.partial,
                    args,
                    result,
                },
            );
            continue;
        }
        let (Some(args), Some(result)) = (args, result) else {
            return Err(format!(
                "parametric function {f} without a hook implementation"
            ));
        };
        if !eqs.contains_key(f) {
            // `BYTES.int2bytes`/`bytes2int`: prelude definitions on `Bool` flags; the flags are
            // the hook's documented argument constructors (`domains.md`: `bigEndianBytes`,
            // `signedBytes`), compared with Lean's `=`
            if let Some((name, text)) = bytes_adapter(m, sym.hook().as_deref(), &args, &result) {
                fns.insert(
                    f.clone(),
                    FnSig {
                        lean: name,
                        partial: false,
                        args: args.clone(),
                        result: result.clone(),
                    },
                );
                helpers.push_str(&text);
                continue;
            }
            // a hook the library does not implement, or a function the definition gives no
            // equations: unconstrained by the definition, so a parameter of the library (every
            // theorem then holds for every implementation of it), never an axiom
            let (field, why) = match sym.hook() {
                Some(h) => (h.clone(), format!("hook {h} has no implementation")),
                None => (
                    format!("fn.{}", names::demangle(f)),
                    "no equations, no hook".to_string(),
                ),
            };
            fns.insert(
                f.clone(),
                FnSig {
                    lean: format!("Hooks.«{field}»"),
                    partial: true,
                    args: args.clone(),
                    result: result.clone(),
                },
            );
            if !params.iter().any(|(p, _, _)| *p == field) {
                params.push((field, args, result));
            }
            notes.push(format!(
                "{} is a parameter of the library ({why})",
                names::demangle(f)
            ));
            continue;
        }
        fns.insert(
            f.clone(),
            FnSig {
                lean: fn_name(f),
                partial: true,
                args,
                result,
            },
        );
    }
    // strongly connected components of the call graph, callees first
    let generated: Vec<String> = used
        .iter()
        .filter(|f| eqs.contains_key(*f) && fns[*f].lean.starts_with("K."))
        .cloned()
        .collect();
    let sccs = sccs(&generated, &calls);
    // functions on a call cycle are Option-valued (their purity is not known in advance)
    let mut recursive: BTreeSet<String> = BTreeSet::new();
    let mut list_recursive: BTreeSet<String> = BTreeSet::new();
    for c in &sccs {
        let self_loop = c.len() == 1 && calls.get(&c[0]).is_some_and(|cs| cs.contains(&c[0]));
        if c.len() > 1 || self_loop {
            recursive.extend(c.iter().cloned());
        }
    }
    let labels: BTreeSet<String> = recursive.iter().map(|f| names::demangle(f)).collect();
    let unknown = side.unknown(&labels);
    if !unknown.is_empty() {
        return Err(format!(
            "--termination: no recursive function is labelled {}",
            unknown.join(", ")
        ));
    }
    // generate, deciding purity on the way (callees first, so their purity is known)
    let mut lean = helpers;
    let mut unfold = Vec::new();
    for scc in &sccs {
        if scc.iter().any(|f| recursive.contains(f)) {
            let text = gen_recursive(m, &fns, &eqs, scc, side, &mut list_recursive)?;
            lean.push_str(&text);
            for f in scc {
                notes.push(format!(
                    "{} is recursive (well-founded recursion, Option-valued)",
                    names::demangle(f)
                ));
            }
            continue;
        }
        let f = &scc[0];
        let sig = fns[f].clone();
        let es = &eqs[f];
        let params: Vec<String> = (0..sig.args.len()).map(|i| format!("x{i}")).collect();
        let mut bodies = Vec::new(); // (name, body, rhs_partial, catch_all)
        for (i, e) in es.iter().enumerate() {
            if e.args
                .iter()
                .any(|a| crate::rules::absent_sort(a, m).is_some())
            {
                continue; // needs a sort without values: never applies
            }
            let (steps, lhs_len, rhs) = lower_equation(m, &fns, f, &sig, &params, e)?;
            let rhs_partial = steps.len() > lhs_len;
            let catch_all = lhs_len == 0;
            bodies.push((i, steps, lhs_len, rhs, rhs_partial, catch_all));
        }
        if m.anywhere.contains(f) {
            // an `anywhere` symbol is a constructor normalized by its equations: where none
            // applies, the value is the constructor itself
            let n = bodies.len();
            bodies.push((n, vec![], 0, anywhere_ctor(m, f, &params), false, true));
        }
        let any_partial = bodies.iter().any(|b| b.4);
        let last_catch = bodies.last().is_some_and(|b| b.5);
        let pure = !any_partial && last_catch;
        let res_ty = if pure {
            sig.result.clone()
        } else {
            format!("Option {}", sig.result)
        };
        let name = fn_name(f);
        let ps: Vec<String> = params
            .iter()
            .zip(&sig.args)
            .map(|(p, s)| format!("({p} : {s})"))
            .collect();
        lean.push_str(&format!("/-! `{}` -/\n", names::demangle(f)));
        let mut cascade_parts = Vec::new();
        for (idx, (i, steps, lhs_len, rhs, _rhs_partial, _)) in bodies.iter().enumerate() {
            if pure && idx == bodies.len() - 1 {
                cascade_parts.push(format!("RHS:{}", rhs.render()));
                continue;
            }
            let eq_name = format!("{name}.rule{}", i + 1);
            let eq_ty = if pure {
                sig.result.clone()
            } else {
                format!("Option {}", sig.result)
            };
            let leaf = if pure {
                format!("some {}", rhs.render_arg())
            } else {
                format!("some (some {})", rhs.render_arg())
            };
            let lhs_len = *lhs_len;
            let fail = move |k: usize| {
                if k < lhs_len {
                    "none".to_string()
                } else {
                    "some none".to_string()
                }
            };
            let body = render::exec_first(steps, false, &fail, &leaf, 2);
            lean.push_str(&format!(
                "def {eq_name} {} : Option ({eq_ty}) :=\n{body}",
                ps.join(" ")
            ));
            unfold.push(eq_name.clone());
            cascade_parts.push(format!("EQ:{eq_name}"));
        }
        // the cascade
        let call_args = params.join(" ");
        let mut body = String::new();
        let mut depth = 0;
        let mut closed = false;
        for part in &cascade_parts {
            let pad = " ".repeat(2 + 2 * depth);
            if let Some(eqn) = part.strip_prefix("EQ:") {
                body.push_str(&format!(
                    "{pad}match {eqn} {call_args} with\n{pad}| some r => r\n{pad}| none =>\n"
                ));
                depth += 1;
            } else if let Some(v) = part.strip_prefix("RHS:") {
                body.push_str(&format!("{pad}{v}\n"));
                closed = true;
            }
        }
        if !closed {
            body.push_str(&format!("{}none\n", " ".repeat(2 + 2 * depth)));
        }
        lean.push_str(&format!(
            "def {name} {} : {res_ty} :=\n{body}\n",
            ps.join(" ")
        ));
        unfold.push(name.clone());
        fns.get_mut(f).unwrap().partial = !pure;
        if !pure {
            notes.push(format!("{} is partial (Option-valued)", names::demangle(f)));
        }
    }
    let recursive = recursive.iter().map(|f| fns[f].lean.clone()).collect();
    Ok(Generated {
        fns,
        params,
        lean,
        unfold,
        recursive,
        list_recursive,
        notes,
    })
}

#[cfg(test)]
pub(crate) mod tests {
    //! Recursive-function detection: a function gets the well-founded, `Option`-valued
    //! definition and the recursive equation proof exactly when it is on a call cycle.
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};

    fn graph(edges: &[(&str, &str)]) -> BTreeMap<String, BTreeSet<String>> {
        let mut g: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (a, b) in edges {
            g.entry(a.to_string()).or_default().insert(b.to_string());
        }
        g
    }

    fn names(v: &[&str]) -> Vec<String> {
        v.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn sccs_put_callees_first_and_group_cycles() {
        // a → b → c → b, a → d, d → d
        let g = graph(&[("a", "b"), ("b", "c"), ("c", "b"), ("a", "d"), ("d", "d")]);
        let out = sccs(&names(&["a", "b", "c", "d"]), &g);
        assert_eq!(out, vec![names(&["b", "c"]), names(&["d"]), names(&["a"])]);
    }

    #[test]
    fn sccs_ignore_calls_outside_the_nodes() {
        // hooks and constructors are not nodes: a call to one is not a cycle
        let g = graph(&[("f", "hook"), ("hook", "f")]);
        assert_eq!(sccs(&names(&["f"]), &g), vec![names(&["f"])]);
    }

    pub(crate) fn fixture(name: &str) -> Def {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join(format!("../../tests/fixtures/{name}/definition.kore"));
        crate::ir::load(
            &std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display())),
        )
        .unwrap()
    }

    /// The roots `gen` uses: the functions the rewrite rules apply.
    pub(crate) fn generated(def: &Def) -> (Model, Generated) {
        let m = Model::build(def).unwrap();
        let mut roots = BTreeSet::new();
        for ax in &def.axioms {
            if let P::Rewrites(_, l, _) = &ax.pattern
                && crate::rules::absent_sort(l, &m).is_none()
            {
                applied(&ax.pattern, def, &mut roots);
            }
        }
        roots.extend(m.anywhere.iter().cloned());
        let g = generate(def, &m, &roots).unwrap();
        (m, g)
    }

    #[test]
    fn recursive_set_is_the_functions_on_a_cycle() {
        let def = fixture("peano");
        let (_, g) = generated(&def);
        let want: BTreeSet<String> = [
            "K.«even(_)_PEANO_B_Nat»",
            "K.«odd(_)_PEANO_B_Nat»",
            "K.«plus(_,_)_PEANO_Nat_Nat_Nat»",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        assert_eq!(g.recursive, want);
        // a caller of a recursive function is not recursive itself, and is unfolded by `simp`
        assert!(
            g.unfold
                .contains(&"K.«double(_)_PEANO_Nat_Nat»".to_string())
        );
        assert!(
            !g.unfold.iter().any(|n| g.recursive.contains(n)),
            "recursive functions must not be in the unfold list"
        );
        // mutual recursion is one `mutual` block; self-recursion is not
        assert_eq!(g.lean.matches("mutual\n").count(), 1);
        assert!(g.lean.contains("decreasing_by"));
    }

    #[test]
    fn no_recursion_without_a_cycle() {
        let def = fixture("counter");
        let (_, g) = generated(&def);
        assert!(g.recursive.is_empty(), "{:?}", g.recursive);
        assert!(!g.lean.contains("mutual"));
    }
}
