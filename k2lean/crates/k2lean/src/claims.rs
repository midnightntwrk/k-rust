//! `k2lean claims`: K reachability claims as Lean statements over a generated semantics.
//!
//! Input: the semantics' compiled `definition.kore` (the one `gen` read, for the term universe
//! and the hooks) and one or more `definition.kore` files compiled from specifications
//! (`krust kcompile spec.k --for-proving`, or reference `kompile`), whose `claim` sentences are
//! read. A claim sentence is the matching-logic formula
//!
//! ```text
//! \implies(\and(REQUIRES, LHS), weakAlwaysFinally(\exists ?X … \and(RHS, ENSURES)))
//! ```
//!
//! (`weakExistsFinally` for one-path claims). It is translated with the generator's own term
//! lowering (`lower::Lower::expr`), so a claim's terms are the same Lean terms the rules use:
//!
//! * the free variables are universally quantified Lean variables of their sorts' types, and a
//!   `Map` variable carries `MapHook.WF` (the domain of `Map` is the canonical maps);
//! * a partial function application in the left-hand side or the requires (a map pattern
//!   `K |-> V …` is `_Map_`, which is partial) is a universally quantified result `r` with the
//!   hypothesis `f … = some r`; in the right-hand side or the ensures it is an existential with
//!   the conjunct `f … = some r` (matching logic is strict in `⊥`);
//! * `requires R` is the hypothesis `R = true`, `ensures E` the conjunct `E = true`;
//! * `?X` is an existential of the target predicate.
//!
//! For each claim the generator writes `Claim.<label> : Prop` (the readable statement),
//! `Inst.<label> c Q` (its instances: `c` is the left-hand side under a valuation that satisfies
//! the hypotheses, `Q` the target predicate of the same valuation), the bridge
//! `Claim.<label>.of_inst`, and a generic proof attempt: the claim's own circularity
//! (`AF.circularity_inst`) and the claims proved before it as lemmas, explored by `kc_auto`.
//! Claims listed in `--open` get no generic proof (their statement stays a `Prop`).

use crate::ir::{self, P};
use crate::lower::{self, Fns, Lower, Step};
use crate::model::{self, Model};
use crate::{funcs, hooks, names, rules};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::PathBuf;

struct Args {
    kore: PathBuf,
    specs: Vec<PathBuf>,
    out: PathBuf,
    name: String,
    sem: String,
    sem_path: String,
    kclaims_path: String,
    open: Option<PathBuf>,
    hand: Vec<String>,
}

fn parse(args: &[String]) -> Args {
    let mut a = Args {
        kore: PathBuf::new(),
        specs: vec![],
        out: PathBuf::new(),
        name: "KDefClaims".into(),
        sem: "KDef".into(),
        sem_path: "../kdef".into(),
        kclaims_path: "../../lean/claims".into(),
        open: None,
        hand: vec![],
    };
    let mut it = args.iter();
    while let Some(x) = it.next() {
        let mut v = || {
            it.next()
                .unwrap_or_else(|| panic!("{x} needs a value"))
                .clone()
        };
        match x.as_str() {
            "--kore" => a.kore = v().into(),
            "--spec" => a.specs.push(v().into()),
            "--out" => a.out = v().into(),
            "--name" => a.name = v(),
            "--semantics" => a.sem = v(),
            "--semantics-path" => a.sem_path = v(),
            "--kclaims-path" => a.kclaims_path = v(),
            "--open" => a.open = Some(v().into()),
            // a hand-written module of the package (imported by the root, after the generated ones)
            "--hand" => a.hand.push(v()),
            other => panic!("claims: unknown argument {other}"),
        }
    }
    a
}

/// One claim sentence.
struct RawClaim {
    module: String,
    label: String,
    location: String,
    source: String,
    trusted: bool,
    pattern: P,
}

fn kstr(s: &k_rust_kore::kore::ast::KoreString) -> String {
    match s.as_utf8() {
        Ok(t) => t.to_string(),
        Err(_) => s.as_bytes().iter().map(|b| *b as char).collect(),
    }
}

fn attr_string(attrs: &k_rust_kore::kore::ast::Attributes, name: &str) -> Option<String> {
    for p in &attrs.0 {
        if let k_rust_kore::kore::ast::Pattern::Application { symbol, arguments } = p
            && symbol.name == name
        {
            if let Some(k_rust_kore::kore::ast::Pattern::String(s)) = arguments.first() {
                return Some(kstr(s));
            }
            return Some(String::new());
        }
    }
    None
}

fn read_claims(path: &PathBuf) -> Vec<RawClaim> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let d = k_rust_kore::kore::parser::parse_definition(&text)
        .unwrap_or_else(|e| panic!("{}: {e:?}", path.display()));
    let mut out = vec![];
    for m in &d.modules {
        for s in &m.sentences {
            if let k_rust_kore::kore::ast::Sentence::Claim {
                pattern,
                attributes,
                ..
            } = s
            {
                let label = attr_string(attributes, "label")
                    .unwrap_or_else(|| format!("claim{}", out.len()));
                out.push(RawClaim {
                    module: m.name.clone(),
                    label,
                    location: attr_string(
                        attributes,
                        "org'Stop'kframework'Stop'attributes'Stop'Location",
                    )
                    .unwrap_or_default(),
                    source: attr_string(
                        attributes,
                        "org'Stop'kframework'Stop'attributes'Stop'Source",
                    )
                    .unwrap_or_default(),
                    trusted: attr_string(attributes, "trusted").is_some(),
                    pattern: ir::pat(pattern),
                });
            }
        }
    }
    out
}

/// The parts of a claim formula.
struct Parts<'p> {
    lhs: &'p P,
    requires: Vec<&'p P>,
    all_path: bool,
    existentials: Vec<(String, String)>,
    rhs: &'p P,
    ensures: Vec<&'p P>,
}

fn is_pred(p: &P) -> bool {
    matches!(
        p,
        P::Top(_)
            | P::Equals(..)
            | P::Ceil(..)
            | P::Floor(..)
            | P::In(..)
            | P::Not(..)
            | P::Bottom(_)
    )
}

fn split_and<'p>(p: &'p P, terms: &mut Vec<&'p P>, preds: &mut Vec<&'p P>) {
    match p {
        P::And(_, ps) => {
            for q in ps {
                split_and(q, terms, preds);
            }
        }
        q if is_pred(q) => {
            if !matches!(q, P::Top(_)) {
                preds.push(q)
            }
        }
        q => terms.push(q),
    }
}

fn parts(p: &P) -> Result<Parts<'_>, String> {
    let P::Implies(_, l, r) = p else {
        return Err("claim is not an implication".into());
    };
    let (mut lt, mut lp) = (vec![], vec![]);
    split_and(l, &mut lt, &mut lp);
    let [lhs] = lt.as_slice() else {
        return Err(format!(
            "left-hand side with {} terms (a disjunction?)",
            lt.len()
        ));
    };
    let (all_path, body) = match &**r {
        P::App(f, _, args) if f == "weakAlwaysFinally" && args.len() == 1 => (true, &args[0]),
        P::App(f, _, args) if f == "weakExistsFinally" && args.len() == 1 => (false, &args[0]),
        _ => return Err("right-hand side is not weakAlwaysFinally/weakExistsFinally".into()),
    };
    let mut existentials = vec![];
    let mut body = body;
    while let P::Exists(_, v, s, b) = body {
        existentials.push((
            v.clone(),
            model::sort_name(s).ok_or("parametric existential")?,
        ));
        body = b;
    }
    let (mut rt, mut rp) = (vec![], vec![]);
    split_and(body, &mut rt, &mut rp);
    let [rhs] = rt.as_slice() else {
        return Err(format!(
            "right-hand side with {} terms (a disjunction?)",
            rt.len()
        ));
    };
    Ok(Parts {
        lhs,
        requires: lp,
        all_path,
        existentials,
        rhs,
        ensures: rp,
    })
}

fn free_vars(p: &P, out: &mut BTreeMap<String, String>, bound: &BTreeSet<String>) {
    match p {
        P::Var(v, s) => {
            if !bound.contains(v)
                && let Some(n) = model::sort_name(s)
            {
                out.entry(v.clone()).or_insert(n);
            }
        }
        P::App(_, _, args) | P::And(_, args) | P::Or(_, args) => {
            args.iter().for_each(|a| free_vars(a, out, bound))
        }
        P::Not(_, a) | P::Ceil(_, _, a) | P::Floor(_, _, a) => free_vars(a, out, bound),
        P::Implies(_, a, b)
        | P::Iff(_, a, b)
        | P::Rewrites(_, a, b)
        | P::Equals(_, _, a, b)
        | P::In(_, _, a, b) => {
            free_vars(a, out, bound);
            free_vars(b, out, bound)
        }
        P::Exists(_, v, _, b) | P::Forall(_, v, _, b) => {
            let mut bd = bound.clone();
            bd.insert(v.clone());
            free_vars(b, out, &bd)
        }
        _ => {}
    }
}

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

/// A hypothesis or conjunct from a lowering step.
fn step_prop(s: &Step) -> Result<(Option<(String, String)>, String), String> {
    Ok(match s {
        Step::Bind { expr, var, .. } => (
            Some((var.clone(), String::new())),
            format!("{} = some {var}", expr.render()),
        ),
        Step::Cond { cond, .. } => (None, format!("{} = true", cond.render())),
        Step::CondEq { lhs, rhs, .. } => (None, format!("{} = {}", lhs.render(), rhs.render())),
        other => {
            return Err(format!(
                "unexpected lowering step in a claim term: {other:?}"
            ));
        }
    })
}

/// A translated claim.
struct Claim {
    lean: String,
    label: String,
    module: String,
    doc: String,
    all_path: bool,
    trusted: bool,
    /// universally quantified variables (Lean name, type), in binding order
    univ: Vec<(String, String)>,
    /// hypotheses: left-hand-side binds, `WF` of map variables, requires
    hyps: Vec<String>,
    /// variables bound by left-hand-side binds (part of `univ`)
    lhs: String,
    /// existentials of the target: `?X`, then right-hand-side bind results
    exist: Vec<(String, String)>,
    rhs: String,
    /// conjuncts of the target after `c = rhs`: binds, ensures
    post: Vec<String>,
}

fn translate(raw: &RawClaim, m: &Model, fns: &Fns, top: &str) -> Result<Claim, String> {
    let pt = parts(&raw.pattern)?;
    let ex: BTreeSet<String> = pt.existentials.iter().map(|(v, _)| v.clone()).collect();
    let mut fv = BTreeMap::new();
    free_vars(pt.lhs, &mut fv, &ex);
    for q in &pt.requires {
        free_vars(q, &mut fv, &ex);
    }
    free_vars(pt.rhs, &mut fv, &ex);
    for q in &pt.ensures {
        free_vars(q, &mut fv, &ex);
    }
    // universals in order of first occurrence would be nicer; KORE order (sorted) is stable
    let mut low = Lower::new(
        m,
        fns,
        &[
            "Claim", "Inst", "Step", "App", "AF", "EF", "AFn", "Q", "n", "ih", "hi", "d",
        ],
    );
    let mut univ = vec![];
    for (v, s) in &fv {
        if !m.sorts.contains_key(s) {
            return Err(format!(
                "variable {v} of sort {s}, which the term universe does not have"
            ));
        }
        let n = low.param(&sanitize(v), s);
        low.vars.insert(v.clone(), n.clone());
        univ.push((n, s.clone()));
    }
    let lhs = low.expr(pt.lhs, top)?;
    for q in &pt.requires {
        low.cond(q)?;
    }
    let pre_steps = std::mem::take(&mut low.steps);
    let mut exist = vec![];
    for (v, s) in &pt.existentials {
        if !m.sorts.contains_key(s) {
            return Err(format!(
                "existential {v} of sort {s}, which the term universe does not have"
            ));
        }
        let n = low.param(&sanitize(v), s);
        low.vars.insert(v.clone(), n.clone());
        exist.push((n, s.clone()));
    }
    let rhs = low.expr(pt.rhs, top)?;
    for q in &pt.ensures {
        low.cond(q)?;
    }
    let post_steps = std::mem::take(&mut low.steps);
    let mut hyps = vec![];
    for s in &pre_steps {
        let (b, h) = step_prop(s)?;
        if let Some((var, _)) = b {
            let ty = low.ty.get(&var).cloned().unwrap_or_default();
            univ.push((var.clone(), ty));
        }
        hyps.push(h);
    }
    for (n, s) in &univ[..fv.len()] {
        if m.sorts
            .get(s)
            .is_some_and(|i| matches!(i.kind, model::Kind::Coll(model::Coll::Map)))
        {
            hyps.push(format!("KPrelude.MapHook.WF {n}"));
        }
    }
    let mut post = vec![];
    for s in &post_steps {
        let (b, h) = step_prop(s)?;
        if let Some((var, _)) = b {
            let ty = low.ty.get(&var).cloned().unwrap_or_default();
            exist.push((var.clone(), ty));
        }
        post.push(h);
    }
    // An existential of a sort that can contain a map must occur in the right-hand side term,
    // where it is a subterm of the reached configuration (canonical when the start is).
    let rhs_s = rhs.render();
    for (n, s) in &exist[..pt.existentials.len()] {
        let leafy = m
            .sorts
            .get(s)
            .is_some_and(|i| matches!(i.kind, model::Kind::Builtin(_) | model::Kind::Token));
        if !leafy
            && !rhs_s
                .split(|c: char| !c.is_alphanumeric() && c != '_')
                .any(|w| w == n)
        {
            return Err(format!(
                "existential {n} : {s} does not occur in the right-hand side"
            ));
        }
    }
    let short = raw
        .label
        .rsplit_once('.')
        .map(|(_, l)| l.to_string())
        .unwrap_or(raw.label.clone());
    let file = raw
        .source
        .trim_start_matches("Source(")
        .trim_end_matches(')');
    let file = std::path::Path::new(file)
        .file_name()
        .map(|f| f.to_string_lossy().to_string())
        .unwrap_or_default();
    let loc = raw
        .location
        .trim_start_matches("Location(")
        .trim_end_matches(')');
    Ok(Claim {
        lean: names::ident(&short),
        label: raw.label.clone(),
        module: raw.module.clone(),
        doc: format!("{file}:{}", loc.split(',').next().unwrap_or("")),
        all_path: pt.all_path,
        trusted: raw.trusted,
        univ,
        hyps,
        lhs: lhs.render(),
        exist,
        rhs: rhs_s,
        post,
    })
}

fn binders(vs: &[(String, String)]) -> String {
    vs.iter()
        .map(|(n, t)| format!("({n} : {t})"))
        .collect::<Vec<_>>()
        .join(" ")
}

fn post_lambda(c: &Claim) -> String {
    let mut body = format!("c = {}", c.rhs);
    for p in &c.post {
        body.push_str(&format!(" ∧ {p}"));
    }
    if c.exist.is_empty() {
        format!("fun c => {body}")
    } else {
        format!("fun c => ∃ {}, {body}", binders(&c.exist))
    }
}

fn module_ns(module: &str) -> String {
    module
        .split('-')
        .map(|w| {
            let mut cs = w.chars();
            match cs.next() {
                Some(f) => f.to_ascii_uppercase().to_string() + &cs.as_str().to_ascii_lowercase(),
                None => String::new(),
            }
        })
        .collect()
}

fn emit_module(
    ns: &str,
    sem: &str,
    module: &str,
    claims: &[Claim],
    open: &BTreeSet<String>,
    top: &str,
) -> (String, Vec<String>) {
    let mns = module_ns(module);
    let mut s = String::new();
    let _ = writeln!(s, "import {ns}.Basic\n");
    let _ = writeln!(
        s,
        "/-! Generated by `k2lean claims` from the compiled claims of `{module}`; do not edit.\n\n\
         `Claim.<label>` is the statement of the K claim, `Inst.<label>` its instances, and\n\
         `Inst.<label>.holds` / `Claim.<label>.holds` the generic proof (absent for claims in\n\
         the open list). -/\n"
    );
    let _ = writeln!(
        s,
        "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option linter.unusedVariables false\nset_option kc.stats true\n"
    );
    let _ = writeln!(s, "namespace {ns}.{mns}\n\nopen {sem} KPrelude KClaims\n");
    let mut proved = vec![];
    let mut lemmas: Vec<String> = vec![];
    for c in claims {
        let modality = if c.all_path {
            "KClaims.AF Step"
        } else {
            "KClaims.EF Step"
        };
        let kind = if c.all_path { "all-path" } else { "one-path" };
        let _ = writeln!(
            s,
            "/-- `claim [{}]` ({}), {kind}{}. -/",
            c.label,
            c.doc,
            if c.trusted { ", trusted" } else { "" }
        );
        let _ = write!(
            s,
            "def Claim.{} : Prop :=\n  ∀ {},",
            c.lean,
            binders(&c.univ)
        );
        for h in &c.hyps {
            let _ = write!(s, "\n    {h} →");
        }
        let _ = writeln!(
            s,
            "\n    {modality}\n      ({})\n      ({})\n",
            post_lambda(c),
            c.lhs
        );
        let _ = writeln!(
            s,
            "/-- The instances of `{}`: a left-hand side and the target of the same valuation. -/",
            c.label
        );
        let mut inst = format!("c = {} ∧ Q = ({})", c.lhs, post_lambda(c));
        for h in &c.hyps {
            inst.push_str(&format!(" ∧ {h}"));
        }
        let _ = writeln!(
            s,
            "def Inst.{} (c : {top}) (Q : {top} → Prop) : Prop :=\n  ∃ {}, {inst}\n",
            c.lean,
            binders(&c.univ)
        );
        let vs: Vec<&str> = c.univ.iter().map(|(n, _)| n.as_str()).collect();
        let hs: Vec<String> = (0..c.hyps.len()).map(|i| format!("h{i}")).collect();
        let conv = if c.all_path {
            "h _ _ "
        } else {
            "KClaims.AF.toEF (h _ _ "
        };
        let close = if c.all_path { "" } else { ")" };
        let _ = writeln!(
            s,
            "theorem Claim.{}.of_inst (h : ∀ c Q, Inst.{} c Q → KClaims.AF Step Q c) : Claim.{} :=\n  fun {} => {conv}⟨{}, rfl, rfl{}⟩{close}\n",
            c.lean,
            c.lean,
            c.lean,
            vs.iter()
                .map(|v| v.to_string())
                .chain(hs.iter().cloned())
                .collect::<Vec<_>>()
                .join(" "),
            vs.join(", "),
            hs.iter().map(|h| format!(", {h}")).collect::<String>()
        );
        let key = format!("{mns}.{}", c.label);
        if open.contains(&key) || open.contains(&c.label) {
            let _ = writeln!(s, "-- `{}`: no generic proof (open list).\n", c.label);
            continue;
        }
        let using = if lemmas.is_empty() {
            String::new()
        } else {
            format!(" using [{}]", lemmas.join(", "))
        };
        let _ = writeln!(
            s,
            "theorem Inst.{}.holds : ∀ c Q, Inst.{} c Q → KClaims.AF Step Q c := by\n  apply KClaims.AF.circularity_inst\n  intro n ih c Q hi\n  kc_intro hi\n  kc_auto circ [ih]{using}\n",
            c.lean, c.lean
        );
        let _ = writeln!(
            s,
            "theorem Claim.{}.holds : Claim.{} := Claim.{}.of_inst Inst.{}.holds\n",
            c.lean, c.lean, c.lean, c.lean
        );
        lemmas.push(format!("Inst.{}.holds", c.lean));
        proved.push(format!("{ns}.{mns}.Claim.{}.holds", c.lean));
    }
    let _ = writeln!(s, "end {ns}.{mns}");
    (s, proved)
}

fn basic(ns: &str, sem: &str, m: &Model, fgen_unfold: &[String]) -> String {
    let mut unfold: Vec<String> = fgen_unfold.iter().map(|u| format!("{sem}.{u}")).collect();
    for (x, y) in crate::terms::inj_pairs(m) {
        unfold.push(format!(
            "{sem}.proj_{}_{}",
            names::short_sort(&y),
            names::short_sort(&x)
        ));
        unfold.push(format!(
            "{sem}.inj_{}_{}",
            names::short_sort(&x),
            names::short_sort(&y)
        ));
    }
    format!(
        "import {sem}\nimport KClaims\n\n/-! Generated by `k2lean claims`; do not edit.\n\n\
         The rule matchers of `{sem}` for the symbolic-execution tactics, and the definitions the\n\
         closing tactic unfolds. -/\n\nnamespace {ns}\n\nopen {sem}\n\n\
         instance : KClaims.RuleSet App Step := ⟨rules, Step.deterministic⟩\n\n\
         instance : KClaims.ExecDet Step step := ⟨step_sound, step_complete⟩\n\n\
         attribute [kc_simp] {}\n\nend {ns}\n",
        unfold.join(" ")
    )
}

pub fn main(args: &[String]) {
    if args.first().map(|s| s.as_str()) == Some("replay") {
        // KORE JSON nests as deep as the terms; parse and drop it on a large stack
        let rest = args[1..].to_vec();
        let h = std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(move || replay(&rest))
            .unwrap();
        h.join().unwrap();
        return;
    }
    let a = parse(args);
    let def = ir::load(&std::fs::read_to_string(&a.kore).unwrap()).unwrap();
    let m = Model::build(&def).unwrap_or_else(|e| panic!("{e}"));
    let mut roots = BTreeSet::new();
    for ax in &def.axioms {
        if let P::Rewrites(..) = &ax.pattern {
            funcs::applied(&ax.pattern, &def, &mut roots);
        }
    }
    let fgen = funcs::generate(&def, &m, &roots).unwrap_or_else(|e| panic!("functions: {e}"));
    let mut fns: Fns = fgen.fns.clone();
    for (sym, d) in &def.symbols {
        if fns.contains_key(sym) || !d.params.is_empty() {
            continue;
        }
        let Some(h) = d.hook().and_then(|h| hooks::lookup(&h)) else {
            continue;
        };
        let args: Option<Vec<String>> = d.args.iter().map(model::sort_name).collect();
        let (Some(args), Some(result)) = (args, model::sort_name(&d.result)) else {
            continue;
        };
        if args
            .iter()
            .chain(std::iter::once(&result))
            .any(|s| !m.sorts.contains_key(s))
        {
            continue;
        }
        fns.insert(
            sym.clone(),
            lower::FnSig {
                lean: h.lean.to_string(),
                partial: h.partial,
                args,
                result,
            },
        );
    }
    let top = rules::top_sort(&def).unwrap();
    let open: BTreeSet<String> = match &a.open {
        Some(p) => std::fs::read_to_string(p)
            .unwrap_or_default()
            .lines()
            .map(|l| l.split('#').next().unwrap_or("").trim().to_string())
            .filter(|l| !l.is_empty())
            .collect(),
        None => Default::default(),
    };
    let ns = &a.name;
    let write = |p: PathBuf, t: &str| {
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, t).unwrap();
    };
    let mut modules = vec![];
    let mut proved_all = vec![];
    let mut report = String::from("# claims translated by `k2lean claims` (generated)\n");
    for spec in &a.specs {
        let raws = read_claims(spec);
        let mut by_module: BTreeMap<String, Vec<Claim>> = BTreeMap::new();
        for r in &raws {
            match translate(r, &m, &fns, &top) {
                Ok(c) => {
                    let _ = writeln!(
                        report,
                        "[[claim]]\nlabel = {:?}\nstated = true\nall_path = {}\n",
                        c.label, c.all_path
                    );
                    by_module.entry(c.module.clone()).or_default().push(c)
                }
                Err(e) => {
                    eprintln!("claim {}: not stated: {e}", r.label);
                    let _ = writeln!(
                        report,
                        "[[claim]]\nlabel = {:?}\nstated = false\nreason = {:?}\n",
                        r.label, e
                    );
                }
            }
        }
        for (module, cs) in by_module {
            let (text, proved) = emit_module(ns, &a.sem, &module, &cs, &open, &top);
            let mns = module_ns(&module);
            write(a.out.join(ns).join(format!("{mns}.lean")), &text);
            eprintln!(
                "{module}: {} claims stated, {} generic proofs",
                cs.len(),
                proved.len()
            );
            modules.push(mns);
            proved_all.extend(proved);
        }
    }
    write(
        a.out.join(ns).join("Basic.lean"),
        &basic(ns, &a.sem, &m, &fgen.unfold),
    );
    let mut root = String::new();
    for mns in &modules {
        let _ = writeln!(root, "import {ns}.{mns}");
    }
    for h in &a.hand {
        let _ = writeln!(root, "import {ns}.{h}");
    }
    write(a.out.join(format!("{ns}.lean")), &root);
    let mut axioms = format!(
        "import {ns}\n\n/-! Generated: the generic claim proofs use only the standard axioms. -/\n\n#k2l_assert_axioms"
    );
    for p in &proved_all {
        axioms.push_str(&format!("\n  {p}"));
    }
    axioms.push('\n');
    write(a.out.join(format!("{ns}Test")).join("Axioms.lean"), &axioms);
    write(
        a.out.join("lakefile.lean"),
        &format!(
            "import Lake\nopen Lake DSL\n\n/-- Generated by `k2lean claims`; do not edit. K claims over `{sem}`. -/\n\
             package «{ns}» where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n\n\
             require {sem} from \"{}\"\nrequire KClaims from \"{}\"\n\n@[default_target]\nlean_lib {ns}\n\n\
             /-- The axiom guard over the generic proofs. -/\nlean_lib {ns}Test where\n  roots := #[`{ns}Test.Axioms]\n",
            a.sem_path,
            a.kclaims_path,
            sem = a.sem
        ),
    );
    write(a.out.join("lean-toolchain"), crate::LEAN_TOOLCHAIN);
    write(a.out.join(".gitignore"), "/.lake\n");
    write(a.out.join("claims.toml"), &report);
}

// ---------------------------------------------------------------- replay (experimental)
//
// `k2lean claims replay --kore SEM.kore --spec SPEC.kore --claim LABEL --port P [--cut LABEL]
//   --semantics KImp --name KImpClaims --out SCRIPT.lean --skeleton SKELETON.toml`
//
// Explores one claim through a running `krust kore-rpc` server, as a client of
// its JSON-RPC protocol: `execute` from the claim's left-hand side with `log-successful-rewrites` (the rule id of
// every step), following `next-states` at a branch; at a cut-point rule (a loop head, `--cut`)
// after at least one step it asks `implies(state, left-hand side)` (is this an instance of the
// claim, usable as a circularity?); at a leaf it asks `implies(state, target)`. The proof
// skeleton becomes a Lean script of named steps (`kc_rule`, `kc_split`, `kc_claim`, `kc_done`)
// whose elaboration checks it against the generated semantics.

struct Rpc {
    stream: std::net::TcpStream,
    id: u64,
    calls: BTreeMap<String, usize>,
}

impl Rpc {
    fn call(&mut self, method: &str, params: serde_json::Value) -> serde_json::Value {
        use std::io::Write;
        self.id += 1;
        *self.calls.entry(method.to_string()).or_default() += 1;
        let req = serde_json::json!({"jsonrpc": "2.0", "id": self.id, "method": method, "params": params});
        self.stream.write_all(req.to_string().as_bytes()).unwrap();
        self.stream.write_all(b"\n").unwrap();
        let mut de = serde_json::Deserializer::from_reader(&self.stream);
        de.disable_recursion_limit();
        let v = de
            .into_iter::<serde_json::Value>()
            .next()
            .expect("rpc: connection closed")
            .expect("rpc: bad JSON");
        if let Some(e) = v.get("error") {
            panic!("rpc {method}: {e}");
        }
        v["result"].clone()
    }
}

enum End {
    Branch(Vec<(String, Node)>),
    /// A circularity application (its condition), then the exploration from its right-hand side.
    Claim(String, Box<Node>),
    Done,
    Open(String),
}

struct Node {
    steps: Vec<String>,
    end: End,
}

struct Explorer<'a> {
    rpc: Rpc,
    lhs: serde_json::Value,
    target: serde_json::Value,
    /// the target with its variables renamed apart, as the right-hand side of a circularity
    rhs_apart: serde_json::Value,
    cut: Option<String>,
    labels: &'a BTreeMap<String, String>,
    budget: usize,
}

/// Rename every element variable apart (`VarX` → `VarXCirc`): the consequent of a
/// circularity check has its own valuation.
fn rename_apart(v: &mut serde_json::Value) {
    match v {
        serde_json::Value::Object(o) => {
            if o.get("tag").and_then(|t| t.as_str()) == Some("EVar")
                && let Some(serde_json::Value::String(n)) = o.get_mut("name")
            {
                n.push_str("Circ");
            }
            for (_, x) in o.iter_mut() {
                rename_apart(x);
            }
        }
        serde_json::Value::Array(a) => a.iter_mut().for_each(rename_apart),
        _ => {}
    }
}

fn kore_text(v: &serde_json::Value) -> String {
    match k_rust_kore::kore::codec::from_value(v) {
        Ok(p) => p.to_string(),
        Err(e) => format!("<{e:?}>"),
    }
}

fn subst_text(imp: &serde_json::Value) -> String {
    let c = &imp["condition"];
    format!(
        "substitution: {}; predicate: {}",
        kore_text(&c["substitution"]),
        kore_text(&c["predicate"])
    )
}

impl Explorer<'_> {
    /// An `execute` state (`term`, `predicate`, `substitution`) as one KORE pattern.
    fn whole(&self, st: &serde_json::Value) -> serde_json::Value {
        let mut parts = vec![st["term"]["term"].clone()];
        for k in ["predicate", "substitution", "rule-predicate"] {
            if st.get(k).is_some_and(|v| !v.is_null()) {
                parts.push(st[k]["term"].clone());
            }
        }
        if parts.len() == 1 {
            return serde_json::json!({"format": "KORE", "version": 1, "term": parts.pop().unwrap()});
        }
        let sort = self.lhs["term"]["sort"].clone();
        serde_json::json!({"format": "KORE", "version": 1, "term": {"tag": "And", "sort": sort, "patterns": parts}})
    }

    /// The circularity's right-hand side under the substitution `implies` found, its `?X`
    /// existentials as fresh variables, with the current state's constraints.
    fn instantiate_rhs(
        &self,
        state: &serde_json::Value,
        imp: &serde_json::Value,
    ) -> serde_json::Value {
        let mut sub: BTreeMap<String, serde_json::Value> = BTreeMap::new();
        fn eqs(p: &serde_json::Value, out: &mut BTreeMap<String, serde_json::Value>) {
            match p["tag"].as_str() {
                Some("And") => p["patterns"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .for_each(|q| eqs(q, out)),
                Some("Equals") if p["first"]["tag"] == "EVar" => {
                    out.insert(
                        p["first"]["name"].as_str().unwrap().to_string(),
                        p["second"].clone(),
                    );
                }
                _ => {}
            }
        }
        eqs(&imp["condition"]["substitution"]["term"], &mut sub);
        fn apply(
            p: &serde_json::Value,
            sub: &BTreeMap<String, serde_json::Value>,
        ) -> serde_json::Value {
            match p {
                serde_json::Value::Object(o) => {
                    if o.get("tag").and_then(|t| t.as_str()) == Some("EVar")
                        && let Some(t) = o
                            .get("name")
                            .and_then(|n| n.as_str())
                            .and_then(|n| sub.get(n))
                    {
                        return t.clone();
                    }
                    serde_json::Value::Object(
                        o.iter().map(|(k, v)| (k.clone(), apply(v, sub))).collect(),
                    )
                }
                serde_json::Value::Array(a) => {
                    serde_json::Value::Array(a.iter().map(|x| apply(x, sub)).collect())
                }
                x => x.clone(),
            }
        }
        // strip `\exists ?X`: the existentials become fresh variables
        let mut body = self.rhs_apart["term"].clone();
        while body["tag"] == "Exists" {
            body = body["arg"].clone();
        }
        let mut parts = vec![apply(&body, &sub)];
        let st = &state["term"];
        if st["tag"] == "And" {
            parts.extend(st["patterns"].as_array().unwrap().iter().skip(1).cloned());
        }
        let sort = self.lhs["term"]["sort"].clone();
        serde_json::json!({"format": "KORE", "version": 1, "term": {"tag": "And", "sort": sort, "patterns": parts}})
    }

    fn explore(&mut self, state: serde_json::Value, depth: usize) -> Node {
        let mut steps: Vec<String> = vec![];
        let mut state = state;
        loop {
            if self.budget == 0 {
                return Node {
                    steps,
                    end: End::Open("budget".into()),
                };
            }
            self.budget -= 1;
            // the target first: a state with a symbolic continuation would otherwise be narrowed
            let imp = self.rpc.call(
                "implies",
                serde_json::json!({"antecedent": state, "consequent": self.target}),
            );
            if imp["status"] == "valid" {
                return Node {
                    steps,
                    end: End::Done,
                };
            }
            // a circularity: after at least one step, an instance of the claim's left-hand side
            if self.cut.is_some() && depth + steps.len() > 0 {
                let imp = self.rpc.call(
                    "implies",
                    serde_json::json!({"antecedent": state, "consequent": self.lhs}),
                );
                if std::env::var("K2L_DEBUG").is_ok() {
                    let mut o = imp.clone();
                    o["implication"] = serde_json::Value::Null;
                    eprintln!(
                        "implies(lhs): status {} {}",
                        imp["status"],
                        if imp.get("condition").is_some() {
                            subst_text(&imp)
                        } else {
                            String::new()
                        }
                    );
                }
                // `indeterminate` with a substitution is kept as a hint: the Lean script
                // re-checks the application (`kc_claim`)
                if imp["status"] == "valid"
                    || (imp["status"] == "indeterminate" && imp.get("condition").is_some())
                {
                    let next = self.instantiate_rhs(&state, &imp);
                    let rest = self.explore(next, depth + steps.len() + 1);
                    return Node {
                        steps,
                        end: End::Claim(
                            format!("status {}; {}", imp["status"], subst_text(&imp)),
                            Box::new(rest),
                        ),
                    };
                }
            }
            let params = serde_json::json!({"state": state, "log-successful-rewrites": true, "max-depth": 1});
            let r = self.rpc.call("execute", params);
            if std::env::var("K2L_DEBUG").is_ok() {
                eprintln!(
                    "execute: reason {} depth {} logs {} next-states {}",
                    r["reason"],
                    r["depth"],
                    r["logs"].as_array().map_or(0, |a| a.len()),
                    r["next-states"].as_array().map_or(0, |a| a.len())
                );
            }
            if let Some(logs) = r["logs"].as_array() {
                for l in logs {
                    if let Some(id) = l["result"]["rule-id"].as_str() {
                        steps.push(id.to_string());
                    }
                }
            }
            let reason = r["reason"].as_str().unwrap_or("").to_string();
            match reason.as_str() {
                "depth-bound" => state = self.whole(&r["state"]),
                "branching" => {
                    let mut kids = vec![];
                    for ns in r["next-states"].as_array().cloned().unwrap_or_default() {
                        let pred = kore_text(&ns["rule-predicate"]);
                        let next = self.whole(&ns);
                        let mut child = self.explore(next, depth + steps.len() + 1);
                        if let Some(id) = ns["rule-id"].as_str() {
                            child.steps.insert(0, id.to_string());
                        }
                        kids.push((pred, child));
                    }
                    return Node {
                        steps,
                        end: End::Branch(kids),
                    };
                }
                other => {
                    return Node {
                        steps,
                        end: End::Open(other.to_string()),
                    };
                }
            }
        }
    }

    fn label(&self, uid: &str) -> String {
        self.labels
            .get(uid)
            .cloned()
            .unwrap_or_else(|| format!("?{uid}"))
    }
}

fn render(n: &Node, sem: &str, labels: &BTreeMap<String, String>) -> String {
    let mut parts: Vec<String> = n
        .steps
        .iter()
        .map(|u| match labels.get(u) {
            Some(l) => format!("kc_rule {sem}.R.{l}"),
            None => format!("fail \"rule {u} is not a rule of the semantics\""),
        })
        .collect();
    match &n.end {
        End::Done => parts.push("kc_done".into()),
        End::Claim(_, rest) => {
            parts.push("kc_claim ih".into());
            parts.push(render(rest, sem, labels));
        }
        End::Open(r) => parts.push(format!("fail \"open leaf: {}\"", r.replace('"', "'"))),
        End::Branch(kids) => {
            parts.push("kc_split".into());
            let alts: Vec<String> = kids
                .iter()
                .map(|(_, k)| format!("({})", render(k, sem, labels)))
                .collect();
            parts.push(format!("all_goals first | {}", alts.join(" | ")));
        }
    }
    parts.join("; ")
}

fn skeleton(n: &Node, ex: &Explorer, path: &str, out: &mut String) {
    let _ = writeln!(out, "[[edge]]\npath = {path:?}\nsteps = {}", n.steps.len());
    let _ = writeln!(
        out,
        "rules = [{}]",
        n.steps
            .iter()
            .map(|u| format!("{:?}", ex.label(u)))
            .collect::<Vec<_>>()
            .join(", ")
    );
    match &n.end {
        End::Done => {
            let _ = writeln!(out, "end = \"target (implies valid)\"\n");
        }
        End::Claim(s, rest) => {
            let _ = writeln!(out, "end = \"circularity\"\ncondition = {s:?}\n");
            skeleton(rest, ex, &format!("{path}.c"), out);
        }
        End::Open(r) => {
            let _ = writeln!(out, "end = {:?}\n", format!("open: {r}"));
        }
        End::Branch(kids) => {
            let _ = writeln!(out, "end = \"branch\"\n");
            for (i, (pred, k)) in kids.iter().enumerate() {
                let p = format!("{path}.{i}");
                let _ = writeln!(out, "[[branch]]\npath = {p:?}\npredicate = {pred:?}\n");
                skeleton(k, ex, &p, out);
            }
        }
    }
}

fn replay(args: &[String]) {
    let mut kore = PathBuf::new();
    let mut spec = PathBuf::new();
    let mut claim = String::new();
    let mut port = 0u16;
    let mut cut: Option<String> = None;
    let mut sem = "KImp".to_string();
    let mut ns = "KImpClaims".to_string();
    let mut out = PathBuf::new();
    let mut skel = PathBuf::new();
    let mut it = args.iter();
    while let Some(x) = it.next() {
        let mut v = || {
            it.next()
                .unwrap_or_else(|| panic!("{x} needs a value"))
                .clone()
        };
        match x.as_str() {
            "--kore" => kore = v().into(),
            "--spec" => spec = v().into(),
            "--claim" => claim = v(),
            "--port" => port = v().parse().unwrap(),
            "--cut" => cut = Some(v()),
            "--semantics" => sem = v(),
            "--name" => ns = v(),
            "--out" => out = v().into(),
            "--skeleton" => skel = v().into(),
            other => panic!("claims replay: unknown argument {other}"),
        }
    }
    // rule unique id → the Lean name of its matcher (`R.<name>`) and its label
    let def = ir::load(&std::fs::read_to_string(&kore).unwrap()).unwrap();
    let m = Model::build(&def).unwrap();
    let mut roots = BTreeSet::new();
    for ax in &def.axioms {
        if let P::Rewrites(..) = &ax.pattern {
            funcs::applied(&ax.pattern, &def, &mut roots);
        }
    }
    let fgen = funcs::generate(&def, &m, &roots).unwrap();
    let rs = rules::collect(&def, &m, &fgen.fns, &[]).unwrap();
    let labels: BTreeMap<String, String> =
        rs.iter().map(|r| (r.uid.clone(), r.lean.clone())).collect();
    let cut_uid = cut.map(|c| {
        rs.iter()
            .find(|r| r.label.as_deref() == Some(c.as_str()) || r.uid == c)
            .unwrap_or_else(|| panic!("no rule labelled {c}"))
            .uid
            .clone()
    });
    // the claim's left-hand side and target, as KORE JSON
    let text = std::fs::read_to_string(&spec).unwrap();
    let d = k_rust_kore::kore::parser::parse_definition(&text).unwrap();
    let mut found = None;
    let mut module = String::new();
    for md in &d.modules {
        for se in &md.sentences {
            if let k_rust_kore::kore::ast::Sentence::Claim {
                pattern,
                attributes,
                ..
            } = se
                && attr_string(attributes, "label").as_deref() == Some(claim.as_str())
            {
                found = Some((**pattern).clone());
                module = md.name.clone();
            }
        }
    }
    let pattern = found.unwrap_or_else(|| panic!("no claim {claim}"));
    let k_rust_kore::kore::ast::Pattern::Implies { left, right, .. } = &pattern else {
        panic!("claim is not an implication")
    };
    let k_rust_kore::kore::ast::Pattern::Application { arguments, .. } = &**right else {
        panic!("no modality")
    };
    let lhs = k_rust_kore::kore::json::to_value(left).unwrap();
    let target = k_rust_kore::kore::json::to_value(&arguments[0]).unwrap();
    let stream = std::net::TcpStream::connect(("127.0.0.1", port)).expect("connect to kore-rpc");
    let mut lhs_apart = lhs.clone();
    rename_apart(&mut lhs_apart);
    let mut rhs_apart = target.clone();
    rename_apart(&mut rhs_apart);
    let mut ex = Explorer {
        rpc: Rpc {
            stream,
            id: 0,
            calls: BTreeMap::new(),
        },
        lhs: lhs_apart,
        target,
        rhs_apart,
        cut: cut_uid,
        labels: &labels,
        budget: 1000,
    };
    let t0 = std::time::Instant::now();
    let root = ex.explore(lhs, 0);
    let dt = t0.elapsed();
    let short = claim
        .rsplit_once('.')
        .map(|(_, l)| l.to_string())
        .unwrap_or(claim.clone());
    let mns = module_ns(&module);
    let lean_name = names::ident(&short);
    let script = render(&root, &sem, &labels);
    let lean = format!(
        "import {ns}.{mns}\n\n/-! Generated by `k2lean claims replay` from a krust kore-rpc exploration of `{claim}`:\n\
         each `kc_rule` names the rule krust applied (its `rule-id`), `kc_split` is a branch of\n\
         `execute`, `kc_claim ih` a state `implies` found to be an instance of the claim. -/\n\n\
         set_option maxHeartbeats 0\n\nopen {sem} KPrelude KClaims\n\nnamespace {ns}.{mns}.Replay\n\n\
         theorem {lean_name} : ∀ c Q, Inst.{lean_name} c Q → KClaims.AF Step Q c := by\n  apply KClaims.AF.circularity_inst\n  intro n ih c Q hi\n  kc_intro hi\n  {script}\n\n\
         end {ns}.{mns}.Replay\n"
    );
    std::fs::write(&out, lean).unwrap();
    let mut sk = format!(
        "# krust kore-rpc exploration of {claim} (generated by `k2lean claims replay`)\nclaim = {claim:?}\nseconds = {:.3}\nrpc_calls = {:?}\n\n",
        dt.as_secs_f64(),
        format!("{:?}", ex.rpc.calls)
    );
    skeleton(&root, &ex, "0", &mut sk);
    std::fs::write(&skel, sk).unwrap();
    eprintln!(
        "replay {claim}: {:.3} s, rpc calls {:?}",
        dt.as_secs_f64(),
        ex.rpc.calls
    );
}
