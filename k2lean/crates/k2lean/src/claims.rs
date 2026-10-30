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
//! Claims listed in `--open` get no generic proof (their statement stays a `Prop`). An entry
//! `NAME | refuted R` names the hand theorem `R` that refutes it, and `NAME | proved R` the one
//! that proves it; `NSTest/Hand.lean` checks each (`#k2l_refuted`, or the type and the axioms),
//! and `claims.toml` records the claim as refuted, proved by hand, or open.

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
    /// `--prelude-git URL@REV`: require the `k2lean` package by git instead (`drivers::require_line`).
    prelude_git: Option<String>,
    open: Option<PathBuf>,
    hand: Vec<String>,
    inv: Option<Inv>,
    induction: Vec<PathBuf>,
    transfers: Vec<Transfer>,
}

/// `--transfer REL`: every proved claim carried along the bisimulation `REL.bisim` that
/// `k2lean relate --ns REL` writes (`REL.R a b := REL.Inv a ∧ b = REL.tr_Top a`, in the module
/// `REL.Bisim`) to the other definition `--transfer-target B`, into the module `--transfer-out
/// FILE` (namespace `--transfer-ns`, default `RELClaims.Transfers`). With `--transfer-kind
/// stutter`, along the stuttering bisimulation `REL.bisim` that `k2lean refine --ns REL` writes
/// (`REL.Refine`, relation `Stutter.Rel REL.tr_Top X`, named `REL.R` by its hand module): one-path
/// claims carry along it, an all-path claim as its one-path weakening (`KClaims/Stutter.lean`),
/// unless `--transfer-det MODULE` names the target's determinism module: `B.Step` is then a
/// function (`B.Step.deterministic`, which `gen` states for a definition without overlapping
/// rules), on which the two modalities coincide (`AF_iff_EF_of_det`), so an all-path claim
/// carries as an all-path claim.
/// Each `--transfer` starts an entry; the other `--transfer-…` flags apply to the last one.
struct Transfer {
    rel: String,
    target: String,
    out: PathBuf,
    ns: String,
    stutter: bool,
    det: Option<String>,
}

/// `--assume-invariant NAME`: the claims are stated and proved for the configurations satisfying
/// a preserved invariant of the semantics.
struct Inv {
    /// the predicate on the top sort (a Lean name, resolved in the semantics' namespace)
    name: String,
    /// the theorem `Preserved Step NAME` (default `NAME.preserved`, as `gen --invariant` writes it)
    preserved: String,
    /// the module that declares both (default `SEM.Invariants`)
    module: String,
    /// the definitions and equations that unfold the invariant (the `kc_inv` simp set)
    unfold: Vec<String>,
}

/// The unfolding set of an invariant: the Lean names of a file such as the
/// `invariant-unfold.txt` that `gen --invariant` writes beside the library, separated by commas,
/// spaces or new lines; a line whose first character other than a space is `#` is a comment.
pub fn read_unfold(path: &PathBuf) -> Vec<String> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let list = text
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .collect::<Vec<_>>()
        .join("\n");
    split_names(&list)
}

/// Split a list of Lean names at commas and white space outside `«…»`.
fn split_names(s: &str) -> Vec<String> {
    let mut out = vec![];
    let mut cur = String::new();
    let mut quoted = false;
    for ch in s.chars() {
        match ch {
            '«' => {
                quoted = true;
                cur.push(ch)
            }
            '»' => {
                quoted = false;
                cur.push(ch)
            }
            ',' | ' ' | '\n' | '\t' if !quoted => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur))
                }
            }
            _ => cur.push(ch),
        }
    }
    if !cur.is_empty() {
        out.push(cur)
    }
    out
}

fn parse(args: &[String]) -> Args {
    let mut a = Args {
        kore: PathBuf::new(),
        specs: vec![],
        out: PathBuf::new(),
        name: "KDefClaims".into(),
        sem: "KDef".into(),
        sem_path: "../kdef".into(),
        kclaims_path: "../../lean".into(),
        prelude_git: None,
        open: None,
        hand: vec![],
        inv: None,
        induction: vec![],
        transfers: vec![],
    };
    // the `--transfer` entries: relation, target, output, namespace, stutter, determinism module
    type Tr = (
        String,
        Option<String>,
        Option<PathBuf>,
        Option<String>,
        bool,
        Option<String>,
    );
    let mut trs: Vec<Tr> = vec![];
    let (mut inv_name, mut inv_preserved, mut inv_module, mut inv_unfold) =
        (None, None, None, None);
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
            "--prelude-git" => a.prelude_git = Some(v()),
            "--open" => a.open = Some(v().into()),
            // a hand-written module of the package (imported by the root, after the generated ones)
            "--hand" => a.hand.push(v()),
            // the claims hold under a preserved invariant of the semantics
            "--assume-invariant" => inv_name = Some(v()),
            "--invariant-preserved" => inv_preserved = Some(v()),
            "--invariant-module" => inv_module = Some(v()),
            "--invariant-unfold" => inv_unfold = Some(PathBuf::from(v())),
            // a structural-induction skeleton over a syntax sort (TOML, `induction` below)
            "--induction" => a.induction.push(v().into()),
            // the claims carried along a bisimulation of `relate` (`Transfer`)
            "--transfer" => trs.push((v(), None, None, None, false, None)),
            "--transfer-target" | "--transfer-out" | "--transfer-ns" | "--transfer-kind"
            | "--transfer-det" => {
                let val = v();
                let t = trs
                    .last_mut()
                    .unwrap_or_else(|| panic!("claims: {x} comes after --transfer"));
                match x.as_str() {
                    "--transfer-target" => t.1 = Some(val),
                    "--transfer-out" => t.2 = Some(PathBuf::from(val)),
                    "--transfer-ns" => t.3 = Some(val),
                    "--transfer-det" => t.5 = Some(val),
                    _ => {
                        t.4 = match val.as_str() {
                            "bisim" => false,
                            "stutter" => true,
                            other => panic!("claims: --transfer-kind {other}: bisim or stutter"),
                        }
                    }
                }
            }
            other => panic!("claims: unknown argument {other}"),
        }
    }
    if let Some(name) = inv_name {
        a.inv =
            Some(Inv {
                preserved: inv_preserved.unwrap_or(format!("{name}.preserved")),
                module: inv_module.unwrap_or(format!("{}.Invariants", a.sem)),
                // by default, the file `gen --invariant` writes in the semantics' library
                unfold: read_unfold(&inv_unfold.unwrap_or_else(|| {
                    lexical(&a.out.join(&a.sem_path).join("invariant-unfold.txt"))
                })),
                name,
            });
    } else if inv_preserved.is_some() || inv_module.is_some() || inv_unfold.is_some() {
        panic!(
            "claims: --invariant-preserved, --invariant-module and --invariant-unfold need --assume-invariant"
        );
    }
    for (rel, target, out, ns, stutter, det) in trs {
        if a.inv.is_some() {
            panic!(
                "claims: --transfer carries claims of the semantics, not under --assume-invariant"
            );
        }
        let (Some(target), Some(out)) = (target, out) else {
            panic!("claims: --transfer {rel} needs --transfer-target and --transfer-out");
        };
        if det.is_some() && !stutter {
            // along a bisimulation every claim already carries with its own modality
            panic!("claims: --transfer-det applies to --transfer-kind stutter");
        }
        a.transfers.push(Transfer {
            ns: ns.unwrap_or(format!("{rel}Claims.Transfers")),
            rel,
            target,
            out,
            stutter,
            det,
        });
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
                // A disjunction in the left-hand side is one claim per alternative (`_ork`).
                let alternatives = ir::claim_alternatives(&ir::pat(pattern));
                let several = alternatives.len() > 1;
                for (k, pattern) in alternatives.into_iter().enumerate() {
                    out.push(RawClaim {
                        module: m.name.clone(),
                        label: if several {
                            format!("{label}_or{}", k + 1)
                        } else {
                            label.clone()
                        },
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
                        pattern: ir::inline_aliases(&pattern),
                    });
                }
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

/// The transfers of the proved claims of one module along `t.rel`'s bisimulation (`Transfer`):
/// from a left-hand side satisfying the bisimulation's invariant, the other definition, started
/// from its translation, reaches a state related to one in the claim's target
/// (`AF.image_of_bisim`, `EF.image_of_bisim`). The target is the image of the claim's, so the
/// statement needs no translation of the target predicate.
/// One transfer's output: the claim modules it imports, its text, its theorems, and how many
/// of them are all-path.
type TransferOut = (Vec<String>, String, Vec<String>, usize);

fn transfer_claims(
    out: &mut TransferOut,
    t: &Transfer,
    ns: &str,
    mns: &str,
    cs: &[Claim],
    proved: &[String],
    top: &str,
) {
    let (imports, text, names, all_paths) = out;
    for c in cs {
        let holds = format!("{ns}.{mns}.Claim.{}.holds", c.lean);
        if !proved.contains(&holds) {
            continue;
        }
        if t.stutter {
            // one-path, along the simulation alone; `Stutter.Rel tr X c (tr c)` by its first case;
            // an all-path claim back to all-path on a deterministic target
            let rel = &t.rel;
            let all = c.all_path && t.det.is_some();
            *all_paths += usize::from(all);
            let hyps: String = c.hyps.iter().map(|h| format!("\n    {h} →")).collect();
            let args: String = c
                .univ
                .iter()
                .map(|(n, _)| format!(" {n}"))
                .chain((0..c.hyps.len()).map(|i| format!(" h{i}")))
                .collect();
            let claim = if c.all_path {
                format!("(KClaims.AF.toEF ({holds}{args}))")
            } else {
                format!("({holds}{args})")
            };
            let carried =
                format!("KClaims.EF.image_of_stutter {rel}.bisim.fwd (Or.inl rfl) {claim}");
            let (modality, what, proof) = if all {
                let tg = &t.target;
                (
                    "KClaims.AF",
                    "an all-path claim (the target is deterministic)",
                    format!(
                        "(KClaims.AF_iff_EF_of_det (R := {tg}.Step)\n    (fun _ _ _ h₁ h₂ => {tg}.Step.deterministic h₁ h₂)).2\n    ({carried})"
                    ),
                )
            } else {
                ("KClaims.EF", "a one-path claim", carried)
            };
            let _ = writeln!(
                text,
                "/-- `claim [{}]` ({mns}) carried to `{}` along `{rel}.bisim`, as {what}. -/\n\
theorem {mns}.{}.transfer : ∀ {},{hyps}\n    {modality} {}.Step\n      (fun d => ∃ a, {rel}.R a d ∧ ({}) a)\n      ({rel}.tr_{top} ({})) :=\n  \
fun{args} => {proof}\n",
                c.label,
                t.target,
                c.lean,
                binders(&c.univ),
                t.target,
                post_lambda(c),
                c.lhs,
            );
            names.push(format!("{mns}.{}.transfer", c.lean));
            let m = format!("{ns}.{mns}");
            if !imports.contains(&m) {
                imports.push(m);
            }
            continue;
        }
        *all_paths += usize::from(c.all_path);
        let (modality, lemma) = if c.all_path {
            ("KClaims.AF", "KClaims.AF.image_of_bisim")
        } else {
            ("KClaims.EF", "KClaims.EF.image_of_bisim")
        };
        let rel = &t.rel;
        let hyps: String = c.hyps.iter().map(|h| format!("\n    {h} →")).collect();
        let vs: Vec<&str> = c.univ.iter().map(|(n, _)| n.as_str()).collect();
        let hs: Vec<String> = (0..c.hyps.len()).map(|i| format!("h{i}")).collect();
        let args: String = vs
            .iter()
            .map(|v| v.to_string())
            .chain(hs.iter().cloned())
            .map(|x| format!(" {x}"))
            .collect();
        let _ = writeln!(
            text,
            "/-- `claim [{}]` ({mns}) carried to `{}` along `{rel}.bisim`. -/\n\
theorem {mns}.{}.transfer : ∀ {},{hyps}\n    {rel}.Inv ({}) →\n    {modality} {}.Step\n      (fun d => ∃ a, {rel}.R a d ∧ ({}) a)\n      ({rel}.tr_{top} ({})) :=\n  \
fun{args} hinv => {lemma} {rel}.bisim ⟨hinv, rfl⟩ ({holds}{args})\n",
            c.label,
            t.target,
            c.lean,
            binders(&c.univ),
            c.lhs,
            t.target,
            post_lambda(c),
            c.lhs,
        );
        names.push(format!("{mns}.{}.transfer", c.lean));
        let m = format!("{ns}.{mns}");
        if !imports.contains(&m) {
            imports.push(m);
        }
    }
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

/// What the open list says of an entry beyond "no generic proof": the hand theorem (a name
/// relative to the package's namespace) that refutes it, or that proves it.
#[derive(Clone, Debug, PartialEq)]
enum Mark {
    Refuted(String),
    Proved(String),
}

impl Mark {
    /// The entry's status line in `claims.toml`.
    fn report(&self) -> String {
        match self {
            Mark::Refuted(r) => format!("refuted = {r:?}\n"),
            Mark::Proved(r) => format!("hand = {r:?}\n"),
        }
    }
}

/// The `--open` list: one entry per line, `NAME`, `NAME | refuted R` or `NAME | proved R`; `#`
/// starts a comment.
fn open_list(path: Option<&std::path::Path>) -> BTreeMap<String, Option<Mark>> {
    let Some(p) = path else {
        return BTreeMap::new();
    };
    let text = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
    let mut out = BTreeMap::new();
    for l in text.lines() {
        let l = l.split('#').next().unwrap_or("").trim();
        if l.is_empty() {
            continue;
        }
        let (name, mark) = match l.split_once('|') {
            None => (l, None),
            Some((n, m)) => {
                let m: Vec<&str> = m.split_whitespace().collect();
                let mark = match m.as_slice() {
                    ["refuted", r] => Mark::Refuted(r.to_string()),
                    ["proved", r] => Mark::Proved(r.to_string()),
                    _ => panic!(
                        "{}: `{l}`: the mark is `refuted THEOREM` or `proved THEOREM`",
                        p.display()
                    ),
                };
                (n.trim(), Some(mark))
            }
        };
        out.insert(name.to_string(), mark);
    }
    out
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
    inv: Option<&Inv>,
) -> (String, Vec<String>) {
    let mns = module_ns(module);
    let mut s = String::new();
    let _ = writeln!(s, "import {ns}.Basic\n");
    let _ = writeln!(
        s,
        "/-! Generated by `k2lean claims` from the compiled claims of `{module}`; do not edit.\n\n\
         `Claim.<label>` is the statement of the K claim, `Inst.<label>` its instances, and\n\
         `Inst.<label>.holds` / `Claim.<label>.holds` the generic proof (absent for claims in\n\
         the open list).{} -/\n",
        match inv {
            Some(i) => format!(
                "\n\nEvery claim is stated under the preserved invariant `{}` (`--assume-invariant`): it\n\
                 holds of the configurations satisfying `{}`, and its proof carries `{}` along every\n\
                 step (`{}`).",
                i.name, i.name, i.name, i.preserved
            ),
            None => String::new(),
        }
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
        if let Some(i) = inv {
            let _ = write!(s, "\n    {} ({}) →", i.name, c.lhs);
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
        let (inv_h, inv_bind, inv_arg) = match inv {
            Some(i) => (format!("{} c → ", i.name), " hinv", "hinv "),
            None => (String::new(), "", ""),
        };
        let _ = writeln!(
            s,
            "theorem Claim.{}.of_inst (h : ∀ c Q, {inv_h}Inst.{} c Q → KClaims.AF Step Q c) : Claim.{} :=\n  fun {}{inv_bind} => {conv}{inv_arg}⟨{}, rfl, rfl{}⟩{close}\n",
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
        match inv {
            None => {
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
            }
            Some(i) => {
                // the target is strengthened to `P ∧ Q`, so that a claim's post-state satisfies `P`
                let _ = writeln!(
                    s,
                    "theorem Inst.{l}.holds : ∀ c Q, {n} c → Inst.{l} c Q → KClaims.AF Step (fun d => {n} d ∧ Q d) c := by\n  apply KClaims.AF.circularity_inst_inv\n  intro n ih c Q hinv hi\n  kc_intro hi\n  kc_auto circ [ih]{using} inv [{p}] split\n",
                    l = c.lean,
                    n = i.name,
                    p = i.preserved
                );
                let _ = writeln!(
                    s,
                    "theorem Claim.{l}.holds : Claim.{l} :=\n  Claim.{l}.of_inst fun c Q hP hi => KClaims.AF.mono (fun _ h => h.2) (Inst.{l}.holds c Q hP hi)\n",
                    l = c.lean
                );
            }
        }
        lemmas.push(format!("Inst.{}.holds", c.lean));
        proved.push(format!("{ns}.{mns}.Claim.{}.holds", c.lean));
    }
    let _ = writeln!(s, "end {ns}.{mns}");
    (s, proved)
}

/// The `kc_inv` set of an assumed invariant (the predicate itself, its unfolding set, and the
/// `toList` of the collection sorts, so that a property of a concrete map's bindings becomes one
/// per binding) and its `kc_inv_fns` set (the non-recursive functions of the library that the
/// rules do not call: those the invariant calls, in a kind 1 invariant).
fn inv_unfold(
    sem: &str,
    m: &Model,
    i: &Inv,
    all_unfold: &[String],
    rule_unfold: &[String],
) -> (Vec<String>, Vec<String>) {
    let mut out = vec![i.name.clone()];
    out.extend(i.unfold.iter().cloned());
    for (s, info) in &m.sorts {
        if matches!(info.kind, model::Kind::Coll(_)) {
            out.push(format!("{sem}.{s}.toList"));
        }
    }
    let mut seen = BTreeSet::new();
    out.retain(|x| seen.insert(x.clone()));
    let fns = all_unfold
        .iter()
        .filter(|u| !rule_unfold.contains(u))
        .map(|u| format!("{sem}.{u}"))
        .collect();
    (out, fns)
}

type InvSets = (Vec<String>, Vec<String>);

fn basic(
    ns: &str,
    sem: &str,
    m: &Model,
    fgen_unfold: &[String],
    inv: Option<(&Inv, InvSets)>,
) -> String {
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
    let (inv_import, inv_attr) = match inv {
        Some((i, (set, fns))) => (
            format!("import {}\n", i.module),
            format!(
                "-- what opens the assumed invariant `{}`, and the functions it calls\nattribute [kc_inv] {}\n\n{}",
                i.name,
                set.join(" "),
                if fns.is_empty() {
                    String::new()
                } else {
                    format!("attribute [kc_inv_fns] {}\n\n", fns.join(" "))
                }
            ),
        ),
        None => (String::new(), String::new()),
    };
    format!(
        "import {sem}\n{inv_import}import KClaims\n\n/-! Generated by `k2lean claims`; do not edit.\n\n\
         The successors of `{sem}` and, for a deterministic semantics, its rule matchers, for the\n\
         symbolic-execution tactics, and the definitions the closing tactic unfolds. -/\n\n\
         namespace {ns}\n\nopen {sem}\n\n\
         instance : KClaims.ExecSucc Step := ⟨_, successors_iff⟩\n\n\
         kc_det_instances\n\n\
         kc_simp_attr {}\n\n{inv_attr}end {ns}\n",
        unfold.join(" ")
    )
}

/// The functions the claims of `specs` apply. A claim is a statement about the definition, so a
/// function it applies belongs in the library as one a rule applies does: `gen --spec` adds them
/// to the library's functions, and `claims` to the ones it lowers the claims with.
pub fn spec_functions(specs: &[PathBuf], def: &ir::Def) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for sp in specs {
        for c in read_claims(sp) {
            funcs::applied(&c.pattern, def, &mut out);
        }
    }
    out
}

/// `functions.txt` as `gen --spec` writes it beside the library: comment lines, then the KORE
/// symbol of each function the library defines, one per line.
pub fn functions_list<'a>(syms: impl IntoIterator<Item = &'a String>) -> String {
    let mut t = String::from(
        "# The functions this library defines (KORE symbols), written by `k2lean gen --spec`;\n\
         # `k2lean claims` checks that every function its claims apply is one of them.\n",
    );
    for sym in syms {
        t.push_str(sym);
        t.push('\n');
    }
    t
}

/// `p` with its `..` components resolved by the path's text: the library is found beside `--out`
/// through `--semantics-path` (`../kimp`) before `--out` exists, where the file system cannot
/// resolve `out/..`.
fn lexical(p: &std::path::Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in p.components() {
        match c {
            std::path::Component::ParentDir if out.file_name().is_some() => {
                out.pop();
            }
            std::path::Component::CurDir => {}
            c => out.push(c),
        }
    }
    out
}

fn read_functions(path: &PathBuf) -> Option<BTreeSet<String>> {
    let text = std::fs::read_to_string(path).ok()?;
    Some(
        text.lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .map(String::from)
            .collect(),
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
    // the functions the claims apply that no rule applies (a hooked one comes from its hook
    // model below): the library defines them only when generated with `gen --spec`, which lists
    // its functions in `functions.txt`; a claim that needs one it lacks is not stated, as any
    // claim over a function with no implementation
    let applied = spec_functions(&a.specs, &def);
    let extra: BTreeSet<String> = applied
        .difference(&roots)
        .filter(|s| def.symbols.get(*s).is_some_and(|d| d.hook().is_none()))
        .cloned()
        .collect();
    let lib_path = lexical(&a.out.join(&a.sem_path).join("functions.txt"));
    let lib = read_functions(&lib_path).unwrap_or_default();
    let missing: Vec<&str> = extra
        .iter()
        .filter(|s| !lib.contains(*s))
        .map(|s| s.as_str())
        .collect();
    if !missing.is_empty() {
        eprintln!(
            "note: the claims apply {}, which the library does not define ({}); the claims that \
             need them are not stated: generate the library with `gen --spec` for these specifications",
            missing.join(", "),
            if lib_path.exists() {
                "per its functions.txt"
            } else {
                "it has no functions.txt"
            }
        );
    }
    roots.extend(extra.into_iter().filter(|s| lib.contains(s)));
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
    let marks = open_list(a.open.as_deref());
    let open: BTreeSet<String> = marks.keys().cloned().collect();
    // the statements whose hand theorem the open list names, with that mark
    let mut checked: Vec<(String, Mark)> = vec![];
    let mut marked_used: BTreeSet<String> = BTreeSet::new();
    let ns = &a.name;
    // a semantics with parameters (`class Hooks`: hooks with no model, such as KEVM's
    // `ecdsaPubKey`): `Step` takes the instance, so every claim is stated, and every instance
    // declared, for every instance, as the library's own theorems are. The library says whether
    // it has them (its function closure, not this one's, decides); without its sources, this one
    let lib_fns = lexical(&a.out.join(&a.sem_path).join(&a.sem).join("Functions.lean"));
    let has_hooks = match std::fs::read_to_string(&lib_fns) {
        Ok(t) => t.lines().any(|l| l.starts_with("class Hooks")),
        Err(_) => !fgen.params.is_empty(),
    };
    let hooks_var = has_hooks.then(|| format!("variable [{}.Hooks]", a.sem));
    let write = |p: PathBuf, t: &str| {
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        let t = match &hooks_var {
            Some(v) => match t.find("\nnamespace ") {
                Some(i) => {
                    let j = i + 1 + t[i + 1..].find('\n').unwrap_or(t.len() - i - 1);
                    format!("{}\n\n{v}{}", &t[..j], &t[j..])
                }
                None => t.to_string(),
            },
            None => t.to_string(),
        };
        std::fs::write(p, t).unwrap();
    };
    let mut modules = vec![];
    let mut proved_all = vec![];
    // the transfers (`--transfer`): the claim modules they import, and their theorems
    let mut transfers: Vec<TransferOut> = a
        .transfers
        .iter()
        .map(|_| (vec![], String::new(), vec![], 0))
        .collect();
    let mut report = String::from("# claims translated by `k2lean claims` (generated)\n");
    for spec in &a.specs {
        let raws = read_claims(spec);
        let mut by_module: BTreeMap<String, Vec<Claim>> = BTreeMap::new();
        for r in &raws {
            match translate(r, &m, &fns, &top) {
                Ok(c) => {
                    let mns = module_ns(&c.module);
                    let key = format!("{mns}.{}", c.label);
                    let entry = [&c.label, &key].into_iter().find(|k| open.contains(*k));
                    let status = match entry.and_then(|k| marks[k].clone()) {
                        Some(mk) => {
                            marked_used.insert(entry.unwrap().clone());
                            let line = mk.report();
                            checked.push((format!("{ns}.{mns}.Claim.{}", c.lean), mk));
                            line
                        }
                        None if entry.is_some() => "open = true\n".to_string(),
                        None => String::new(),
                    };
                    let _ = writeln!(
                        report,
                        "[[claim]]\nlabel = {:?}\nstated = true\nall_path = {}\n{status}",
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
            let (text, proved) = emit_module(ns, &a.sem, &module, &cs, &open, &top, a.inv.as_ref());
            let mns = module_ns(&module);
            for (t, acc) in a.transfers.iter().zip(transfers.iter_mut()) {
                transfer_claims(acc, t, ns, &mns, &cs, &proved, &top);
            }
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
    for (t, (imports, text, names, all_paths)) in a.transfers.iter().zip(&transfers) {
        let mut f = if t.stutter {
            let mut f = format!("import {}.Refine\nimport KClaims.Stutter\n", t.rel);
            if let Some(m) = &t.det {
                let _ = writeln!(f, "import {m}");
            }
            f
        } else {
            format!("import {}.Bisim\nimport KClaims.Bisim\n", t.rel)
        };
        for i in imports {
            let _ = writeln!(f, "import {i}");
        }
        let doc = if t.stutter && t.det.is_some() {
            format!(
                "Every claim that `{ns}` proves for `{}`, carried to `{}` along the stuttering bisimulation\n\
`{}.bisim` that `k2lean refine` writes: from the translation of its left-hand side, some run of `{}`\n\
reaches a state related to one in the claim's target (`EF.image_of_stutter`). `{}.Step` is\n\
deterministic (`{}.Step.deterministic`), and on a deterministic relation every run does what some run\n\
does (`AF_iff_EF_of_det`), so an all-path claim stays all-path and a one-path claim one-path.\n\
No step of `{}` is explored.",
                a.sem, t.target, t.rel, t.target, t.target, t.target, t.target
            )
        } else if t.stutter {
            format!(
                "Every claim that `{ns}` proves for `{}`, carried to `{}` along the stuttering bisimulation\n\
`{}.bisim` that `k2lean refine` writes, as a one-path claim: from the translation of its left-hand\n\
side, some run of `{}` reaches a state related to one in the claim's target (`EF.image_of_stutter`;\n\
an all-path claim through its one-path weakening, since all-path claims do not carry along a\n\
stuttering simulation, `KClaims/Stutter.lean`). No step of `{}` is explored.",
                a.sem, t.target, t.rel, t.target, t.target
            )
        } else {
            format!(
                "Every claim that `{ns}` proves for `{}`, carried to `{}` along the bisimulation `{}.bisim` that\n\
`k2lean relate` writes: from a left-hand side satisfying the bisimulation's invariant `{}.Inv`, the\n\
other definition, started from the translation of that left-hand side, reaches a state related to\n\
one in the claim's target (`AF.image_of_bisim`, `EF.image_of_bisim`). No step of `{}` is\n\
explored.",
                a.sem, t.target, t.rel, t.rel, t.target
            )
        };
        let _ = writeln!(
            f,
            "\n/-! Generated by `k2lean claims --transfer {}`; do not edit.\n\n{doc} -/\n\nset_option linter.unusedVariables false\n\nnamespace {}\n\nopen {} KPrelude KClaims\n",
            t.rel, t.ns, a.sem
        );
        f.push_str(text);
        if !names.is_empty() {
            let _ = writeln!(f, "#k2l_assert_axioms {}\n", names.join(" "));
        }
        let _ = writeln!(f, "end {}", t.ns);
        write(t.out.clone(), &f);
        eprintln!(
            "transfer: {} claims carried along {}.bisim",
            names.len(),
            t.rel
        );
        let _ = writeln!(
            report,
            "[[transfer]]\nrelation = {:?}\nkind = {:?}\ntarget = {:?}\ncarried = {}\nall_path = {}\n",
            t.rel,
            if t.stutter { "stutter" } else { "bisim" },
            t.target,
            names.len(),
            all_paths
        );
    }
    for path in &a.induction {
        let spec = induction::read(path, &m).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let (text, proved, opened) = induction::emit(ns, &a.sem, &spec, &m, &fns, &top, &open)
            .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        write(a.out.join(ns).join(format!("{}.lean", spec.name)), &text);
        let n = spec.obligations.len() + spec.leaves.len();
        eprintln!(
            "induction {}: {n} obligations, {} generic proofs, open {:?}",
            spec.name,
            n - opened.len(),
            opened
        );
        // the obligations without a generic proof: refuted, proved by hand, or open
        let (mut refuted, mut by_hand, mut still) = (vec![], vec![], vec![]);
        for key in &opened {
            let o = key.strip_prefix(&format!("{}.", spec.name)).unwrap_or(key);
            match marks.get(key).cloned().flatten() {
                Some(mk) => {
                    marked_used.insert(key.clone());
                    match &mk {
                        Mark::Refuted(_) => refuted.push(key.clone()),
                        Mark::Proved(_) => by_hand.push(key.clone()),
                    }
                    checked.push((format!("{ns}.{}.Obl.{}", spec.name, names::ident(o)), mk));
                }
                None => still.push(key.clone()),
            }
        }
        let _ = writeln!(
            report,
            "[[induction]]\nname = {:?}\nsort = {:?}\nobligations = {}\nopen = {:?}\nrefuted = {:?}\nhand = {:?}\n",
            spec.name, spec.sort, n, still, refuted, by_hand
        );
        modules.push(spec.name.clone());
        proved_all.extend(proved);
    }
    write(
        a.out.join(ns).join("Basic.lean"),
        &basic(
            ns,
            &a.sem,
            &m,
            &fgen.unfold,
            a.inv.as_ref().map(|i| {
                // every function with equations, for those the invariant calls; a function the
                // generator cannot write is left out (then its definition is not unfolded)
                let all: BTreeSet<String> = def
                    .symbols
                    .iter()
                    .filter(|(_, d)| d.is_function() && d.params.is_empty())
                    .map(|(s, _)| s.clone())
                    .collect();
                // only those the library defines (`gen` writes the functions its rules and its
                // invariant call), read from its `Functions.lean` when it is there
                let fl = a.out.join(&a.sem_path).join(&a.sem).join("Functions.lean");
                let defined = std::fs::read_to_string(&fl).ok();
                let all_unfold: Vec<String> = funcs::generate(&def, &m, &all)
                    .map(|g| g.unfold)
                    .unwrap_or_else(|e| {
                        eprintln!("claims: the invariant's functions are not unfolded: {e}");
                        vec![]
                    })
                    .into_iter()
                    .filter(|u| {
                        defined.as_ref().is_some_and(|t| {
                            t.contains(&format!("def {u} ")) || t.contains(&format!("def {u}\n"))
                        })
                    })
                    .collect();
                (i, inv_unfold(&a.sem, &m, i, &all_unfold, &fgen.unfold))
            }),
        ),
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
    let unused: Vec<&String> = marks
        .iter()
        .filter(|(k, m)| m.is_some() && !marked_used.contains(*k))
        .map(|(k, _)| k)
        .collect();
    if !unused.is_empty() {
        panic!("claims: --open marks entries that name no claim or obligation: {unused:?}");
    }
    let mut test_roots = format!("`{ns}Test.Axioms");
    if !checked.is_empty() {
        let mut hand = format!(
            "import {ns}\n\n/-! Generated: the hand theorems that the open list names. A refutation is checked by\n\
             `#k2l_refuted` (the negation of the generated statement itself, Lean's three axioms); a hand\n\
             proof by its type and its axioms. -/\n"
        );
        for (s, mk) in &checked {
            match mk {
                Mark::Refuted(r) => {
                    let _ = write!(hand, "\n#k2l_refuted {s} {ns}.{r}\n");
                }
                Mark::Proved(r) => {
                    let _ = write!(
                        hand,
                        "\nexample : {s} := {ns}.{r}\n#k2l_assert_axioms {ns}.{r}\n"
                    );
                }
            }
        }
        write(a.out.join(format!("{ns}Test")).join("Hand.lean"), &hand);
        test_roots.push_str(&format!(", `{ns}Test.Hand"));
    }
    write(
        a.out.join("lakefile.lean"),
        &format!(
            "import Lake\nopen Lake DSL\n\n/-- Generated by `k2lean claims`; do not edit. K claims over `{sem}`. -/\n\
             package «{ns}» where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n  fixedToolchain := true\n\n\
             require {sem} from \"{}\"\n{}\n\n@[default_target]\nlean_lib {ns}\n\n\
             /-- The axiom guard over the generic proofs, and the check of the hand theorems the open list names. -/\n\
             lean_lib {ns}Test where\n  roots := #[{test_roots}]\n",
            a.sem_path,
            crate::drivers::require_line(Some(&a.kclaims_path), a.prelude_git.as_deref()),
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

// ---------------------------------------------------------------- induction skeletons
//
// `k2lean claims --induction FILE`: termination of a sublanguage, by structural induction over a
// syntax sort. FILE (TOML) names the sublanguage:
//
//   name = "ExprEval"            the Lean module (`NS/ExprEval.lean`) and namespace
//   sort = "SortExpr"            the syntax sort the induction runs over
//   [[class]]                    a class of the sublanguage and the sort of its values
//   name = "AExp"
//   value = "SortInt"
//   [[ctor]]                     one typing of a constructor of `sort`: its class and its
//   class = "AExp"               arguments' classes (a constructor may have several typings)
//   ctor = "_+_"
//   args = ["AExp", "AExp"]
//   [[leaf]]                     values of a subsort of `sort` typed by a cell (optional): `Sub x
//   class = "AExp"               cl e` takes the cell `x` (a child of the top cell with a map
//   sort = "SortId"              content) as a parameter, and `inj i` is in class `AExp` when the
//   cell = "env"                 map is well formed and binds `i` to a value of the class's sort
//
// The generated module states, for the configuration `cfg e K …` with `e` (injected into `KItem`)
// at the head of the `<k>` cell, the continuation `K` and every other cell arbitrary:
//
// * `Sub cl e`, the sublanguage, an inductive predicate: a value of the class's sort, or a listed
//   constructor applied to arguments of the listed classes;
// * one obligation per listed typing: if the arguments are in their classes and each argument,
//   in any continuation, reaches a value of its class (the induction hypotheses, as claims the
//   tactic may apply anywhere), then the constructor's term reaches a value of its class
//   (`Reach`: some finite path, total correctness), closed by `kc_auto … split` unless listed in
//   `--open` as `NAME.CLASS.CTOR`;
// * `holds`: every expression of the sublanguage reaches a value of its class, by induction on
//   `Sub`, with the open obligations as hypotheses.

mod induction {
    use super::*;

    pub struct Spec {
        pub name: String,
        pub sort: String,
        /// (class, value sort)
        pub classes: Vec<(String, String)>,
        pub obligations: Vec<Obl>,
        pub leaves: Vec<Leaf>,
    }

    pub struct Leaf {
        pub class: String,
        /// the Lean name component (`AExp.env`)
        pub name: String,
        /// the subsort of the syntax sort whose values the cell types
        pub sort: String,
        /// the cell's name (`env` for `<env>`)
        pub cell: String,
    }

    pub struct Obl {
        pub class: String,
        /// the Lean name component (`AExp._+_`, `BExp._==_.1` for a second typing)
        pub name: String,
        pub sym: String,
        pub args: Vec<String>,
        pub klabel: String,
    }

    fn strs(v: &toml::Value, key: &str) -> Result<String, String> {
        v.get(key)
            .and_then(|x| x.as_str())
            .map(|x| x.to_string())
            .ok_or(format!("missing string `{key}`"))
    }

    pub fn read(path: &PathBuf, m: &Model) -> Result<Spec, String> {
        let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
        let t: toml::Table = text.parse().map_err(|e: toml::de::Error| e.to_string())?;
        let tv = toml::Value::Table(t);
        let name = strs(&tv, "name")?;
        let sort = strs(&tv, "sort")?;
        let info = m
            .sorts
            .get(&sort)
            .ok_or(format!("sort {sort} is not in the definition"))?;
        let mut classes = vec![];
        for c in tv
            .get("class")
            .and_then(|x| x.as_array())
            .ok_or("no [[class]]")?
        {
            let (n, v) = (strs(c, "name")?, strs(c, "value")?);
            if !m.sorts.contains_key(&v) {
                return Err(format!(
                    "class {n}: value sort {v} is not in the definition"
                ));
            }
            if names::ident(&n) != n {
                return Err(format!("class name {n} is not a plain identifier"));
            }
            classes.push((n, v));
        }
        let mut obligations: Vec<Obl> = vec![];
        for c in tv
            .get("ctor")
            .and_then(|x| x.as_array())
            .ok_or("no [[ctor]]")?
        {
            let class = strs(c, "class")?;
            if !classes.iter().any(|(n, _)| *n == class) {
                return Err(format!("unknown class {class}"));
            }
            let want = strs(c, "ctor")?;
            let args: Vec<String> = c
                .get("args")
                .and_then(|x| x.as_array())
                .ok_or("ctor without `args`")?
                .iter()
                .map(|x| {
                    x.as_str()
                        .map(|s| s.to_string())
                        .ok_or("args are class names")
                })
                .collect::<Result<_, _>>()?;
            let sym = info
                .own
                .iter()
                .find(|sym| {
                    let ci = &m.ctors[*sym];
                    ci.lean.trim_start_matches('«').trim_end_matches('»') == want
                        || ci.klabel == want
                })
                .ok_or(format!("{sort} has no constructor {want}"))?
                .clone();
            let ci = &m.ctors[&sym];
            if ci.args.len() != args.len() {
                return Err(format!(
                    "{want} has {} arguments, the typing {}",
                    ci.args.len(),
                    args.len()
                ));
            }
            for (a, cl) in ci.args.iter().zip(&args) {
                if *a != sort {
                    return Err(format!("{want}: an argument of sort {a}, not {sort}"));
                }
                if !classes.iter().any(|(n, _)| n == cl) {
                    return Err(format!("{want}: unknown class {cl}"));
                }
            }
            let base = format!("{class}.{want}");
            let k = obligations
                .iter()
                .filter(|o| o.name == base || o.name.starts_with(&format!("{base}.")))
                .count();
            let name = if k == 0 { base } else { format!("{base}.{k}") };
            obligations.push(Obl {
                class,
                name,
                sym,
                args,
                klabel: ci.klabel.clone(),
            });
        }
        let mut leaves: Vec<Leaf> = vec![];
        for c in tv
            .get("leaf")
            .and_then(|x| x.as_array())
            .into_iter()
            .flatten()
        {
            let (class, lsort, cell) = (strs(c, "class")?, strs(c, "sort")?, strs(c, "cell")?);
            if !classes.iter().any(|(n, _)| *n == class) {
                return Err(format!("leaf: unknown class {class}"));
            }
            if !m.subsorts.contains(&(lsort.clone(), sort.clone())) {
                return Err(format!("leaf: {lsort} is not a subsort of {sort}"));
            }
            if let Some(l) = leaves.first()
                && l.cell != cell
            {
                return Err(format!(
                    "leaf: the leaves read the cells {} and {cell}; one cell only",
                    l.cell
                ));
            }
            let name = format!("{class}.{cell}");
            if leaves.iter().any(|l| l.name == name) {
                return Err(format!("leaf: two leaves of class {class}"));
            }
            leaves.push(Leaf {
                class,
                name,
                sort: lsort,
                cell,
            });
        }
        Ok(Spec {
            name,
            sort,
            classes,
            obligations,
            leaves,
        })
    }

    fn sv(s: &str) -> crate::ir::S {
        crate::ir::S::App(s.to_string(), vec![])
    }

    fn var(n: &str, s: &str) -> P {
        P::Var(n.to_string(), sv(s))
    }

    fn inj(from: &str, to: &str, p: P) -> P {
        P::App("inj".into(), vec![sv(from), sv(to)], vec![p])
    }

    /// The configuration with `item` at the head of `<k>` followed by `K`, and the other cells of
    /// the top cell as the variables `x1 …`: `(pattern, the other cells' (name, sort))`.
    fn config(m: &Model, top: &str, item: P) -> Result<(P, Vec<(String, String)>), String> {
        let tinfo = &m.sorts[top];
        let [tsym] = tinfo.own.as_slice() else {
            return Err(format!("{top} has {} constructors", tinfo.own.len()));
        };
        let targs = &m.ctors[tsym].args;
        let mut args = vec![];
        let mut cells = vec![];
        let mut found = false;
        for (i, a) in targs.iter().enumerate() {
            let ainfo = &m.sorts[a];
            let kseq = || {
                P::App(
                    "kseq".into(),
                    vec![],
                    vec![item.clone(), var("VarK", "SortK")],
                )
            };
            if let [csym] = ainfo.own.as_slice()
                && m.ctors[csym].args == ["SortK".to_string()]
                && !found
                && a == "SortKCell"
            {
                args.push(P::App(csym.clone(), vec![], vec![kseq()]));
                found = true;
            } else {
                let n = format!("VarX{}", i + 1);
                args.push(var(&n, a));
                cells.push((n, a.clone()));
            }
        }
        if !found {
            return Err(format!("the <k> cell is not a child of {top}"));
        }
        Ok((P::App(tsym.clone(), vec![], args), cells))
    }

    pub fn emit(
        ns: &str,
        sem: &str,
        spec: &Spec,
        m: &Model,
        fns: &Fns,
        top: &str,
        open: &BTreeSet<String>,
    ) -> Result<(String, Vec<String>, Vec<String>), String> {
        let sort = &spec.sort;
        let mut low = Lower::new(
            m,
            fns,
            &[
                "Sub", "Inst", "Target", "Obl", "cfg", "holds", "Step", "d", "cl",
            ],
        );
        let name_of = |low: &mut Lower, kv: &str, base: &str, ty: &str| {
            let n = low.param(base, ty);
            low.vars.insert(kv.to_string(), n.clone());
            n
        };
        let e = name_of(&mut low, "VarE", "e", sort);
        let k = name_of(&mut low, "VarK", "k", "SortK");
        let (cfg_p, cells) = config(m, top, inj(sort, "SortKItem", var("VarE", sort)))?;
        let mut cell_vars = vec![];
        for (kv, s) in &cells {
            cell_vars.push((
                name_of(&mut low, kv, &format!("x{}", cell_vars.len() + 1), s),
                s.clone(),
            ));
        }
        let cfg_l = low.expr(&cfg_p, top)?.render();
        let cell_bind: String = cell_vars
            .iter()
            .map(|(n, t)| format!(" ({n} : {t})"))
            .collect();
        let cell_args: String = cell_vars.iter().map(|(n, _)| format!(" {n}")).collect();
        // with leaves, the cell they read is a parameter of `Sub`, `Inst` and `holds`: `(index in
        // the cells, its constructor)`; the other cells stay quantified as before
        let par = match spec.leaves.first() {
            None => None,
            Some(l) => {
                let want = format!("<{}>", l.cell);
                let j = cells
                    .iter()
                    .position(|(_, cs)| match m.sorts[cs].own.as_slice() {
                        [c] => m.ctors[c].klabel == want && m.ctors[c].args == ["SortMap"],
                        _ => false,
                    })
                    .ok_or(format!(
                        "leaf: {top} has no cell {want} whose content is a Map"
                    ))?;
                Some((j, m.sorts[&cells[j].1].own[0].clone()))
            }
        };
        let rest: Vec<&(String, String)> = cell_vars
            .iter()
            .enumerate()
            .filter(|(i, _)| par.as_ref().map(|p| p.0) != Some(*i))
            .map(|(_, c)| c)
            .collect();
        let rest_bind: String = rest.iter().map(|(n, t)| format!(" ({n} : {t})")).collect();
        let rest_args: String = rest.iter().map(|(n, _)| format!(" {n}")).collect();
        let (par_bind, par_impl, par_intro, par_arg, sub, inst) = match &par {
            None => Default::default(),
            Some((j, _)) => {
                let (pn, pt) = &cell_vars[*j];
                (
                    format!(" ({pn} : {pt})"),
                    format!(" {{{pn} : {pt}}}"),
                    format!("{pn} "),
                    " _".to_string(),
                    format!(" {pn}"),
                    format!(" {pn}"),
                )
            }
        };
        let mut targets = vec![];
        for (cl, vs) in &spec.classes {
            let v = name_of(&mut low, &format!("VarV{cl}"), "v", vs);
            let (tp, _) = config(m, top, inj(vs, "SortKItem", var(&format!("VarV{cl}"), vs)))?;
            let tl = low.expr(&tp, top)?.render();
            let leaf = low
                .expr(&inj(vs, sort, var(&format!("VarV{cl}"), vs)), sort)?
                .render();
            targets.push((cl.clone(), v, vs.clone(), tl, leaf));
        }
        // each leaf: (name, class, the Lean names of its identifier, map and value, the leaf
        // term, the cell's term, the key and the value in the map)
        let mut leaves = vec![];
        if let Some((j, csym)) = &par {
            let li = name_of(&mut low, "VarLI", "i", &spec.leaves[0].sort);
            let lm = name_of(&mut low, "VarLM", "m", "SortMap");
            let ct = low
                .expr(
                    &P::App(csym.clone(), vec![], vec![var("VarLM", "SortMap")]),
                    &cells[*j].1,
                )?
                .render();
            for l in &spec.leaves {
                let (_, v, vs, _, _) = targets.iter().find(|t| t.0 == l.class).unwrap();
                let term = low
                    .expr(&inj(&l.sort, sort, var("VarLI", &l.sort)), sort)?
                    .render();
                let key = low
                    .expr(
                        &inj(&l.sort, "SortKItem", var("VarLI", &l.sort)),
                        "SortKItem",
                    )?
                    .render();
                let val = low
                    .expr(
                        &inj(vs, "SortKItem", var(&format!("VarV{}", l.class), vs)),
                        "SortKItem",
                    )?
                    .render();
                leaves.push((
                    l,
                    li.clone(),
                    lm.clone(),
                    v.clone(),
                    format!("{v} : {vs}"),
                    term,
                    ct.clone(),
                    key,
                    val,
                ));
            }
        }
        if !low.steps.is_empty() {
            return Err("the configuration needs a partial function".into());
        }
        let mut s = String::new();
        let _ = writeln!(s, "import {ns}.Basic\n");
        let _ = writeln!(
            s,
            "/-! Generated by `k2lean claims --induction`; do not edit.\n\n\
             Termination of a sublanguage of `{sort}`: every expression of `Sub` reaches a value of its\n\
             class, from any continuation and any other cells (`holds`, by induction on `Sub`). Each\n\
             constructor typing is one obligation (`Obl.<class>.<ctor>`), whose induction hypotheses say\n\
             that its arguments reach values, in any continuation; the claims tactic applies them\n\
             where the arguments are evaluated. `Reach` is a finite path: total correctness. -/\n"
        );
        let _ = writeln!(
            s,
            "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option linter.unusedVariables false\nset_option kc.stats true\n"
        );
        let _ = writeln!(
            s,
            "namespace {ns}.{}\n\nopen {sem} KPrelude KClaims\n",
            spec.name
        );
        let _ = writeln!(
            s,
            "/-- The classes of the sublanguage. -/\ninductive Cls where"
        );
        for (cl, _) in &spec.classes {
            let _ = writeln!(s, "  | {cl}");
        }
        let _ = writeln!(s);
        let _ = writeln!(
            s,
            "/-- The configuration with `{e}` at the head of `<k>`. -/\ndef cfg ({e} : {sort}) ({k} : SortK){cell_bind} : {top} :=\n  {cfg_l}\n"
        );
        let _ = writeln!(
            s,
            "/-- The configurations where `<k>` holds a value of class `cl`, then `{k}`, and the other cells are\nunchanged. -/\ndef Target (cl : Cls) ({k} : SortK){cell_bind} (d : {top}) : Prop :=\n  match cl with"
        );
        for (cl, v, vs, tl, _) in &targets {
            let _ = writeln!(s, "  | .{cl} => ∃ ({v} : {vs}), d = {tl}");
        }
        let _ = writeln!(s);
        let _ = writeln!(
            s,
            "/-- The instances of the claim \"`{e}` reaches a value of class `cl`\". -/\ndef Inst{par_bind} (cl : Cls) ({e} : {sort}) (c : {top}) (Q : {top} → Prop) : Prop :=\n  ∃ ({k} : SortK){rest_bind}, c = cfg {e} {k}{cell_args} ∧ Q = Target cl {k}{cell_args}\n"
        );
        let _ = writeln!(
            s,
            "theorem Inst.of_forall{par_impl} {{cl : Cls}} {{{e} : {sort}}} (h : ∀ ({k} : SortK){rest_bind}, KClaims.Reach Step (Target cl {k}{cell_args}) (cfg {e} {k}{cell_args})) :\n    ∀ c Q, Inst{inst} cl {e} c Q → KClaims.Reach Step Q c := by\n  rintro c Q ⟨{k},{} rfl, rfl⟩\n  exact h {k}{rest_args}\n",
            rest.iter()
                .map(|(n, _)| format!(" {n},"))
                .collect::<String>()
        );
        // the sublanguage
        let _ = writeln!(
            s,
            "/-- The sublanguage: values of each class, {}and the listed constructor typings. -/\ninductive Sub{par_bind} : Cls → {sort} → Prop",
            if leaves.is_empty() {
                ""
            } else {
                "the leaves the cell types, "
            }
        );
        for (cl, v, vs, _, leaf) in &targets {
            let _ = writeln!(
                s,
                "  | {} ({v} : {vs}) : Sub{sub} .{cl} ({leaf})",
                names::ident(&format!("{cl}.val"))
            );
        }
        let pn = par_intro.trim_end();
        for (l, li, lm, _, vb, term, ct, key, val) in &leaves {
            let _ = writeln!(
                s,
                "  | {} ({li} : {}) ({lm} : SortMap) ({vb}) (hc : {pn} = {ct}) (hw : KPrelude.MapHook.WF {lm})\n      (hl : KPrelude.MapHook.lookup {lm} ({key}) = some ({val})) : Sub{sub} .{} ({term})",
                names::ident(&l.name),
                l.sort,
                l.class
            );
        }
        let mut terms = vec![];
        for o in &spec.obligations {
            let mut lo = Lower::new(m, fns, &[]);
            let mut avs = vec![];
            for (i, _) in o.args.iter().enumerate() {
                let n = lo.param(&format!("a{i}"), sort);
                lo.vars.insert(format!("VarA{i}"), n.clone());
                avs.push(n);
            }
            let p = P::App(
                o.sym.clone(),
                vec![],
                (0..o.args.len())
                    .map(|i| var(&format!("VarA{i}"), sort))
                    .collect(),
            );
            let t = lo.expr(&p, sort)?.render();
            let binders: String = avs.iter().map(|a| format!("{{{a} : {sort}}} ")).collect();
            let prem: String = avs
                .iter()
                .zip(&o.args)
                .map(|(a, c)| format!("Sub{sub} .{c} {a} → "))
                .collect();
            let _ = writeln!(
                s,
                "  | {} {binders}: {prem}Sub{sub} .{} ({t})",
                names::ident(&o.name),
                o.class
            );
            terms.push((avs, t));
        }
        let _ = writeln!(s);
        let mut proved = vec![];
        let mut opened = vec![];
        for (o, (avs, t)) in spec.obligations.iter().zip(&terms) {
            let on = names::ident(&o.name);
            let abind: String = avs.iter().map(|a| format!(" ({a} : {sort})")).collect();
            let prem: String = avs
                .iter()
                .zip(&o.args)
                .map(|(a, c)| format!(" Sub{sub} .{c} {a} →"))
                .collect();
            let ihs: String = avs
                .iter()
                .zip(&o.args)
                .map(|(a, c)| {
                    format!("(∀ c Q, Inst{inst} .{c} {a} c Q → KClaims.Reach Step Q c) →\n    ")
                })
                .collect();
            let _ = writeln!(
                s,
                "/-- `{}` (`{}`) in class `{}`, from its arguments' induction hypotheses. -/\ndef Obl.{on} : Prop :=\n  ∀{par_bind}{abind},{prem}\n    {ihs}∀ ({k} : SortK){rest_bind}, KClaims.Reach Step (Target .{} {k}{cell_args}) (cfg ({t}) {k}{cell_args})\n",
                o.name, o.klabel, o.class, o.class
            );
            let key = format!("{}.{}", spec.name, o.name);
            if open.contains(&key) {
                let _ = writeln!(s, "-- `{key}`: no generic proof (open list).\n");
                opened.push(key);
                continue;
            }
            let hs: Vec<String> = (0..avs.len()).map(|i| format!("h{i}")).collect();
            let is: Vec<String> = (0..avs.len()).map(|i| format!("ih{i}")).collect();
            let intro: Vec<String> = par_intro
                .split_whitespace()
                .map(|x| x.to_string())
                .chain(avs.iter().cloned())
                .chain(hs.clone())
                .chain(is.clone())
                .chain(std::iter::once(k.clone()))
                .chain(rest.iter().map(|(n, _)| n.clone()))
                .collect();
            let using = if is.is_empty() {
                String::new()
            } else {
                format!(" using [{}]", is.join(", "))
            };
            let _ = writeln!(
                s,
                "theorem Obl.{on}.holds : Obl.{on} := by\n  intro {}\n  kc_norm\n  kc_auto{using} split\n",
                intro.join(" ")
            );
            proved.push(format!("{ns}.{}.Obl.{on}.holds", spec.name));
        }
        // the leaves: the value the cell binds, read by the semantics' lookup rule
        for (l, li, lm, _, vb, term, ct, key, val) in &leaves {
            let on = names::ident(&l.name);
            let _ = writeln!(
                s,
                "/-- `{}` read from `<{}>`: a well-formed map that binds it to a value of class `{}`. -/\ndef Obl.{on} : Prop :=\n  ∀{par_bind} ({li} : {}) ({lm} : SortMap) ({vb}), {pn} = {ct} → KPrelude.MapHook.WF {lm} →\n    KPrelude.MapHook.lookup {lm} ({key}) = some ({val}) →\n    ∀ ({k} : SortK){rest_bind}, KClaims.Reach Step (Target .{} {k}{cell_args}) (cfg ({term}) {k}{cell_args})\n",
                l.sort, l.cell, l.class, l.sort, l.class
            );
            let key = format!("{}.{}", spec.name, l.name);
            if open.contains(&key) {
                let _ = writeln!(s, "-- `{key}`: no generic proof (open list).\n");
                opened.push(key);
                continue;
            }
            // one step by the constructor of `Step` that unifies with the configuration (the
            // semantics' lookup rule, `<k> X => V …</k> <env> X |-> V …</env>`), whose map pattern
            // is the binding and the rest of a well-formed map; the value is then the target. The
            // rule's matcher, which `kc_auto` evaluates, does not reduce on a map variable.
            let v = vb.split(' ').next().unwrap();
            let _ = writeln!(
                s,
                "theorem Obl.{on}.holds : Obl.{on} := by\n  intro {par_intro}{li} {lm} {v} hc hw hl {k}{rest_args}\n  subst hc\n  apply KClaims.Reach.step\n  · constructor\n    exact KPrelude.MapHook.concat_element_remove hw hl\n  · exact KClaims.Reach.here ⟨{v}, rfl⟩\n"
            );
            proved.push(format!("{ns}.{}.Obl.{on}.holds", spec.name));
        }
        // the theorem
        let hyps: String = opened
            .iter()
            .map(|key| {
                let o = key.strip_prefix(&format!("{}.", spec.name)).unwrap();
                format!(" (o_{} : Obl.{})", sanitize(o), names::ident(o))
            })
            .collect();
        let _ = writeln!(
            s,
            "/-- Every expression of the sublanguage reaches a value of its class (the open obligations, if\nany, are hypotheses). -/\ntheorem holds{hyps}{par_impl} {{cl : Cls}} {{{e} : {sort}}} (h : Sub{sub} cl {e}) :\n    ∀ ({k} : SortK){rest_bind}, KClaims.Reach Step (Target cl {k}{cell_args}) (cfg {e} {k}{cell_args}) := by\n  induction h with"
        );
        for (cl, v, _, _, _) in &targets {
            let _ = writeln!(
                s,
                "  | {} {v} =>\n    intro {k}{rest_args}\n    refine KClaims.Reach.here ?_\n    exact ⟨{v}, rfl⟩",
                names::ident(&format!("{cl}.val"))
            );
        }
        for (l, li, lm, v, _, _, _, _, _) in &leaves {
            let key = format!("{}.{}", spec.name, l.name);
            let pf = if opened.contains(&key) {
                format!("o_{}", sanitize(&l.name))
            } else {
                format!("Obl.{}.holds", names::ident(&l.name))
            };
            let _ = writeln!(
                s,
                "  | {} {li} {lm} {v} hc hw hl =>\n    intro {k}{rest_args}\n    exact {pf} _ {li} {lm} {v} hc hw hl {k}{rest_args}",
                names::ident(&l.name)
            );
        }
        for (o, (avs, _)) in spec.obligations.iter().zip(&terms) {
            let hs: Vec<String> = (0..avs.len()).map(|i| format!("h{i}")).collect();
            let is: Vec<String> = (0..avs.len()).map(|i| format!("ih{i}")).collect();
            let key = format!("{}.{}", spec.name, o.name);
            let pf = if opened.contains(&key) {
                format!("o_{}", sanitize(&o.name))
            } else {
                format!("Obl.{}.holds", names::ident(&o.name))
            };
            let args: String = std::iter::once(par_arg.clone())
                .chain(avs.iter().map(|_| " _".to_string()))
                .chain(hs.iter().map(|h| format!(" {h}")))
                .chain(is.iter().map(|i| format!(" (Inst.of_forall {i})")))
                .collect();
            let _ = writeln!(
                s,
                "  | @{} {} {} {} =>\n    exact {pf}{args}",
                names::ident(&o.name),
                avs.join(" "),
                hs.join(" "),
                is.join(" ")
            );
        }
        let _ = writeln!(s);
        if opened.is_empty() {
            proved.push(format!("{ns}.{}.holds", spec.name));
        }
        let _ = writeln!(s, "end {ns}.{}", spec.name);
        Ok((s, proved, opened))
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Mark, functions_list, lexical, open_list, read_functions, read_unfold, split_names,
    };
    use std::path::{Path, PathBuf};

    /// The `--open` list: a plain entry, the two marks, comments, and a name with `/` and `.`.
    #[test]
    fn open_list_marks() {
        let dir = std::env::temp_dir().join(format!("k2lean-open-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let p = dir.join("open.txt");
        std::fs::write(
            &p,
            "# header\nM.a  # open\nM.b | refuted Hand.b_false  # false\n\nExprDiv.AExp._/_ | proved Hand.d\n",
        )
        .unwrap();
        let m = open_list(Some(&p));
        std::fs::remove_dir_all(&dir).unwrap();
        assert_eq!(m.len(), 3);
        assert_eq!(m["M.a"], None);
        assert_eq!(m["M.b"], Some(Mark::Refuted("Hand.b_false".into())));
        assert_eq!(m["ExprDiv.AExp._/_"], Some(Mark::Proved("Hand.d".into())));
        assert!(open_list(None).is_empty());
    }

    /// `invariant-unfold.txt` as `gen --invariant` writes it: comment lines, then one name per
    /// line; a `#` inside a name is part of it.
    #[test]
    fn unfold_file_skips_comment_lines_only() {
        let p = std::env::temp_dir().join(format!("k2lean-unfold-{}.txt", std::process::id()));
        std::fs::write(
            &p,
            "# The unfolding set …\n# one per line.\nInvariant.envOk\nEqn.«#if_#then_#else_#fi_K_1»\n",
        )
        .unwrap();
        let names = read_unfold(&p);
        let _ = std::fs::remove_file(&p);
        assert_eq!(
            names,
            vec!["Invariant.envOk", "Eqn.«#if_#then_#else_#fi_K_1»"]
        );
    }

    /// `functions.txt` as `gen --spec` writes it reads back as the same symbols.
    #[test]
    fn functions_file_round_trip() {
        let syms = [
            "Lbl'Hash'padRightToWidth".to_string(),
            "LblMerkleUpdate".to_string(),
        ];
        let p = std::env::temp_dir().join(format!("k2lean-functions-{}.txt", std::process::id()));
        std::fs::write(&p, functions_list(&syms)).unwrap();
        let back = read_functions(&p).unwrap();
        let _ = std::fs::remove_file(&p);
        assert_eq!(
            back.into_iter().collect::<Vec<_>>(),
            vec!["Lbl'Hash'padRightToWidth", "LblMerkleUpdate"]
        );
    }

    /// The library beside `--out` is found before `--out` exists.
    #[test]
    fn semantics_path_resolves_by_text() {
        assert_eq!(
            lexical(Path::new("/w/gen/kimp-claims/../kimp/f.txt")),
            PathBuf::from("/w/gen/kimp/f.txt")
        );
        assert_eq!(lexical(Path::new("out/./../lib")), PathBuf::from("lib"));
        assert_eq!(lexical(Path::new("../lib")), PathBuf::from("../lib"));
    }

    #[test]
    fn unfold_names_split_outside_guillemets() {
        assert_eq!(
            split_names(
                "Invariant.envOk, Eqn.«f(_, _)_M_Bool_Int_Int_1» Eqn.isValue_1,\nOption.bind_fun_some"
            ),
            vec![
                "Invariant.envOk",
                "Eqn.«f(_, _)_M_Bool_Int_Int_1»",
                "Eqn.isValue_1",
                "Option.bind_fun_some"
            ]
        );
    }
}
