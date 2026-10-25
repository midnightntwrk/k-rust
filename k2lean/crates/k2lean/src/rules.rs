//! Rewrite rules: the inductive relations `App` (the rule applies: its left-hand side matches and
//! its requires is `true`) and `Step` (one constructor per rewrite axiom), the proof-carrying
//! matchers, and the adequacy theorems.

use crate::ir::{Def, P};
use crate::lower::{Fns, L, Lower};
use crate::model::Model;
use crate::names;
use crate::render::{self, Rel};
use std::collections::BTreeMap;

pub struct Rule {
    pub uid: String,
    pub label: Option<String>,
    /// The rule's stable name (`rulename`), with the overload variant suffix.
    pub name: String,
    /// The source position `file:line:col`, when the KORE records it.
    pub loc: Option<String>,
    /// The source file, when the KORE records one (also without a line).
    pub source: Option<String>,
    pub priority: i64,
    pub lean: String,
    pub app: Rel,
    pub step: Rel,
    pub rhs: L,
    pub exec: String,
    /// The list-valued matcher (every match; used when some rule has several matches).
    pub exec_multi: String,
    /// Whether the left-hand side has a free-key map pattern (several matches).
    pub multi: bool,
    /// The KORE left-hand side, the conditions of a step (the requires, conjoined with the
    /// ensures when there is one) and the right-hand side of this variant (the pair
    /// classification of `det2`, which separates steps, not applicability).
    pub kore: (P, P, P),
}

/// The conditions under which a rule steps: its requires, and its ensures unless that is `\top`
/// (both are predicates at the top sort `top`).
fn step_conditions(req: &P, ens: &P, top: &str) -> P {
    match (req, ens) {
        (_, P::Top(_)) => req.clone(),
        (P::Top(_), _) => ens.clone(),
        _ => P::And(
            crate::ir::S::App(top.to_string(), vec![]),
            vec![req.clone(), ens.clone()],
        ),
    }
}

/// A sort the pattern needs that the term universe does not have (an unsupported builtin such
/// as `Float`, or an empty sort): such a left-hand side has no instance in the model.
pub fn absent_sort(p: &P, m: &Model) -> Option<String> {
    let has = |s: &crate::ir::S| s.name().is_none_or(|n| m.sorts.contains_key(n));
    match p {
        P::Var(_, s) => (!has(s)).then(|| s.to_string()),
        P::App(f, params, args) => {
            if f == "inj"
                && let Some(bad) = params.iter().find(|s| !has(s))
            {
                return Some(bad.to_string());
            }
            args.iter().find_map(|a| absent_sort(a, m))
        }
        P::Dv(s, _) => (!has(s)).then(|| s.to_string()),
        P::And(_, ps) | P::Or(_, ps) => ps.iter().find_map(|a| absent_sort(a, m)),
        P::Not(_, a) => absent_sort(a, m),
        P::Equals(_, _, a, b) | P::In(_, _, a, b) => {
            absent_sort(a, m).or_else(|| absent_sort(b, m))
        }
        _ => None,
    }
}

pub fn top_sort(def: &Def) -> Result<String, String> {
    for a in &def.axioms {
        if let P::Rewrites(s, _, _) = &a.pattern {
            return s
                .name()
                .map(|n| n.to_string())
                .ok_or("parametric top sort".into());
        }
    }
    Err("no rewrite rules".into())
}

pub fn rule_priority(a: &crate::ir::AxiomDecl) -> i64 {
    if a.attrs.has("owise") {
        200
    } else {
        a.attrs
            .string("priority")
            .and_then(|p| p.parse().ok())
            .unwrap_or(50)
    }
}

/// The distinct priorities of the rewrite rules, in order.
pub fn priorities(def: &Def) -> Vec<i64> {
    let mut v: Vec<i64> = def
        .axioms
        .iter()
        .filter(|a| matches!(a.pattern, P::Rewrites(..)))
        .map(rule_priority)
        .collect();
    v.sort();
    v.dedup();
    v
}

/// The rules as `gen` emits them, with the priority ranks and whether `Step` is stratified
/// (`App i`, `Step0 i`: several ranks, or a rule with several matches, which uses the ranked
/// emitter even with one rank): with a free-key map pattern every rule is collected for the
/// ranked relations, and only the ranks of the rules kept count.
pub fn collect_ranked(
    def: &Def,
    m: &Model,
    fns: &Fns,
    order: &[String],
) -> Result<(Vec<Rule>, Vec<i64>, bool), String> {
    let mut rs = collect(def, m, fns, order)?;
    let mut prios = priorities(def);
    let multi = rs.iter().any(|r| r.multi);
    if multi {
        rs = collect_with(def, m, fns, order, true)?;
        prios.retain(|p| rs.iter().any(|r| r.priority == *p));
    }
    let ranked = prios.len() > 1 || multi;
    Ok((rs, prios, ranked))
}

pub fn collect(def: &Def, m: &Model, fns: &Fns, order: &[String]) -> Result<Vec<Rule>, String> {
    collect_with(def, m, fns, order, false)
}

/// `ranked`: emit for the stratified relation even with one priority (rules with several
/// matches use the ranked emitter).
pub fn collect_with(
    def: &Def,
    m: &Model,
    fns: &Fns,
    order: &[String],
    ranked: bool,
) -> Result<Vec<Rule>, String> {
    let top = top_sort(def)?;
    // with more than one priority rank, matchers certify the rank-local relation `Step0`
    let step_rel = if ranked || priorities(def).len() > 1 {
        "Step0"
    } else {
        "Step"
    };
    let mut rules = Vec::new();
    let mut used_names = BTreeMap::new();
    // stable names: the label, else derived from the rule's content (`rulename`)
    let rule_names = crate::rulename::assign(def);
    for a in &def.axioms {
        let P::Rewrites(_, l, r) = &a.pattern else {
            continue;
        };
        let uid = a.attrs.string("UNIQUE'Unds'ID").unwrap_or_default();
        let label = a.attrs.string("label");
        let priority = rule_priority(a);
        let what = label.clone().unwrap_or(uid.clone());
        let (lhs, req) = match &**l {
            P::And(_, ps) if ps.len() == 2 => (&ps[0], &ps[1]),
            other => (other, &P::Top(crate::ir::S::App(top.clone(), vec![]))),
        };
        // left-hand sides match normal forms: overloaded constants normalized
        let lhs_norm = crate::funcs::normalize_consts(lhs, def);
        let lhs = &lhs_norm;
        let (rhs, ens) = match &**r {
            P::And(_, ps) if ps.len() == 2 => (&ps[0], &ps[1]),
            other => (other, &P::Top(crate::ir::S::App(top.clone(), vec![]))),
        };
        if let Some(bad) = absent_sort(lhs, m) {
            eprintln!(
                "note: rule {what} left out: its left-hand side needs sort {bad}, which has no values in the model"
            );
            continue;
        }
        // matching modulo the overload axioms: one rule variant per normal-form shape
        let mut ex = crate::overload::Expander::new(def, m);
        let variants = ex.expand(lhs);
        if variants.len() > 64 {
            return Err(format!("rule {what}: {} overload variants", variants.len()));
        }
        for (vi, (vlhs, vs)) in variants.iter().enumerate() {
            let lhs = &crate::overload::subst(vlhs, vs);
            let req = &crate::overload::subst(req, vs);
            let rhs = &crate::overload::subst(rhs, vs);
            let ens = &crate::overload::subst(ens, vs);
            let mut lw = Lower::new(m, fns, &[]);
            lw.param("c", &top);
            lw.pat(lhs, "c", &top, true)
                .map_err(|e| format!("rule {what}: {e}"))?;
            lw.finish_lhs().map_err(|e| format!("rule {what}: {e}"))?;
            lw.cond(req).map_err(|e| format!("rule {what}: {e}"))?;
            let lhs_len = lw.steps.len();
            // `ensures e`: the right-hand side is `r ∧ ⌈e = true⌉`, so the rule applies (`App`)
            // whatever `e` is, and steps only where `e` is `true`; its tests come after the
            // left-hand side's, where a failure is a rule that applies without a successor
            // (`docs/design.md`, §2, "Rules")
            lw.cond(ens)
                .map_err(|e| format!("rule {what}: ensures: {e}"))?;
            let mut rhs_l = lw
                .expr(rhs, &top)
                .map_err(|e| format!("rule {what}: {e}"))?;
            let mut steps = lw.steps.clone();
            render::inline_top(&mut steps, &mut rhs_l, "c");
            let app = render::relation(&steps[..lhs_len], "c", &lw.ty, &[]);
            let step = render::relation(&steps, "c", &lw.ty, &[]);
            let base0 = rule_names
                .get(&a.index)
                .cloned()
                .unwrap_or_else(|| format!("rule_{}", &uid[..uid.len().min(12)]));
            let base = if vi == 0 {
                base0
            } else {
                format!("{base0}_ov{vi}")
            };
            let mut name = base.clone();
            let mut k = 1;
            while used_names.contains_key(&name) {
                k += 1;
                name = format!("{base}_{k}");
            }
            used_names.insert(name.clone(), ());
            let lean = names::ident(&name);
            let app_cert = render::certificate(&format!("App.{lean}"), &steps[..lhs_len], &app);
            let step_cert = render::certificate(&format!("{step_rel}.{lean}"), &steps, &step);
            let multi = steps
                .iter()
                .any(|s| matches!(s, crate::lower::Step::MapChoose { .. }));
            let exec = if multi {
                String::new()
            } else {
                let leaf = format!(".next {} ({step_cert})", rhs_l.render_arg());
                let app_cert2 = app_cert.clone();
                let fail = move |i: usize| {
                    if i < lhs_len {
                        ".none".to_string()
                    } else {
                        format!(".undefined ({app_cert2})")
                    }
                };
                render::exec(&steps, true, &fail, &leaf, 2)
            };
            let leaf_m = format!("[.next {} ({step_cert})]", rhs_l.render_arg());
            let fail_m = move |i: usize| {
                if i < lhs_len {
                    "[]".to_string()
                } else {
                    format!("[.undefined ({app_cert})]")
                }
            };
            let exec_multi = render::exec(&steps, true, &fail_m, &leaf_m, 2);
            let loc = crate::rulename::location(a);
            let source = crate::rulename::source_file(a);
            rules.push(Rule {
                uid: uid.clone(),
                label: label.clone(),
                name: name.clone(),
                loc,
                source,
                priority,
                lean,
                app,
                step,
                rhs: rhs_l.subst(&BTreeMap::new()),
                exec,
                exec_multi,
                multi,
                kore: (lhs.clone(), step_conditions(req, ens, &top), rhs.clone()),
            });
        }
    }
    // execution order: runtime.json's `execution_rewrite_order`, within priority groups
    let pos: BTreeMap<&str, usize> = order
        .iter()
        .enumerate()
        .map(|(i, u)| (u.as_str(), i))
        .collect();
    rules.sort_by_key(|r| {
        (
            r.priority,
            pos.get(r.uid.as_str()).copied().unwrap_or(usize::MAX),
        )
    });
    Ok(rules)
}

pub fn ctor_sig(rel: &Rel) -> String {
    let mut s = String::new();
    for (b, t) in &rel.binders {
        s.push_str(&format!(" ({b} : {t})"));
    }
    for (h, p) in &rel.hyps {
        s.push_str(&format!("\n      ({h} : {p})"));
    }
    s
}

pub fn ctor_args(rel: &Rel) -> Vec<String> {
    rel.binders
        .iter()
        .map(|(b, _)| b.clone())
        .chain(rel.hyps.iter().map(|(h, _)| h.clone()))
        .collect()
}

pub fn ctor_info(m: &Model) -> crate::index::CtorInfo {
    let mut info = crate::index::CtorInfo::new();
    for (ty, ctors) in crate::terms::block_types(m) {
        for c in &ctors {
            info.insert(format!("{ty}.{}", c.name), (ctors.len(), c.args.len()));
        }
    }
    info
}

pub fn display_name(r: &Rule) -> String {
    r.name.clone()
}

/// The doc comment of a rule's `Step` constructor: its name and its source position.
pub fn doc(r: &Rule) -> String {
    match &r.loc {
        Some(l) => format!("`{}` ({l})", r.name),
        None => format!("`{}`", r.name),
    }
}

pub fn emit_rules(rules: &[Rule], top: &str, ns: &str, info: &crate::index::CtorInfo) -> String {
    let mut o = String::new();
    o.push_str(&format!(
        "import {ns}.Functions\n\n/-! Generated by k2lean from compiled KORE; do not edit.\n\n\
`App c`: some rewrite rule applies at `c` (its left-hand side matches and its requires is `true`).\n\
`Step c c'`: one constructor per rewrite axiom of the compiled definition (heating and cooling\n\
included), at the top configuration. A rule whose right-hand side is undefined (`⊥`) applies but\n\
has no `Step`. -/\n\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace {ns}\n\nopen KPrelude\n\n"
    ));
    o.push_str(&format!("inductive App : {top} → Prop where\n"));
    for r in rules {
        o.push_str(&format!(
            "  | {}{} :\n      App {}\n",
            r.lean,
            ctor_sig(&r.app),
            r.app.index.render_arg()
        ));
    }
    o.push_str(&format!("\ninductive Step : {top} → {top} → Prop where\n"));
    for r in rules {
        o.push_str(&format!(
            "  /-- {} -/\n  | {}{} :\n      Step {}\n        {}\n",
            doc(r),
            r.lean,
            ctor_sig(&r.step),
            r.step.index.render_arg(),
            r.rhs.subst(&r.step.subst).render_arg()
        ));
    }
    o.push_str("\nnamespace Rules\n\n");
    for r in rules {
        o.push_str(&format!(
            "def {} (c : {top}) : RuleResult App Step c :=\n{}\n",
            r.lean, r.exec
        ));
    }
    o.push_str("end Rules\n\n");
    for (i, r) in rules.iter().enumerate() {
        o.push_str(&format!(
            "def R.{} : Rule {top} App Step := ⟨{}, {i}, Rules.{}⟩\n",
            r.lean,
            names::string_lit(&display_name(r)),
            r.lean
        ));
    }
    o.push_str(&format!("\n/-- The rules in `krun`'s order (priority, then `execution_rewrite_order`). -/\ndef rules : List (Rule {top} App Step) := [\n"));
    let items: Vec<String> = rules.iter().map(|r| format!("  R.{}", r.lean)).collect();
    o.push_str(&items.join(",\n"));
    o.push_str("]\n\n");
    let lhs: Vec<&L> = rules.iter().map(|r| &r.app.index).collect();
    let tree = crate::index::build(&lhs, info);
    let names: Vec<String> = rules.iter().map(|r| format!("R.{}", r.lean)).collect();
    let (leaves, max, avg) = crate::index::stats(&tree);
    o.push_str(&format!(
        "/-- The rules that can apply at `c`, by a decision tree on the constructors of the left-hand\n\
sides ({leaves} buckets, at most {max} rules, {avg} on average); each in `rules` order. -/\n\
def bucketOf (c : {top}) : List (Rule {top} App Step) :=\n{}\n",
        crate::index::emit(&tree, &names, info, 2)
    ));
    o.push_str(&format!(
        "/-- One step as `krun` takes it: the first rule whose result is defined. -/\ndef step (c : {top}) : Outcome {top} := firstDefined (bucketOf c) c none\n\n\
/-- `run fuel c`: at most `fuel` steps from `c`. -/\ndef run (fuel : Nat) (c : {top}) : RunResult {top} := KPrelude.run step fuel c 0\n\n"
    ));
    o.push_str(&format!("end {ns}\n"));
    o
}

/// The per-rule `complete`/`applies` proof: the relation's map and list patterns as facts about
/// the hooks the matcher calls (`k2l_map_facts`, `k2l_list_facts`), the matcher unfolded on the
/// left-hand side, then the matcher evaluated test by test: a test that does not reduce is split,
/// and right after each split the value it bound is identified with the relation's
/// (`k2l_fundep1`, e.g. the `v` of `lookup m k = some v` with the relation's cell), so that the
/// next `match` on it reduces by `dsimp` instead of being split. Splitting a `match` on a large
/// cell pattern needs its match equations, which Lean generates for an imported matcher under
/// the default heartbeat limit whatever the importing file sets. In each remaining branch the
/// bound values are identified (`k2l_fundep`) before `simp_all`. What `simp_all` leaves has its
/// identifications as conjunctions (from a map lookup) or as equations `pattern = v`, which are
/// split and substituted; then it is a fallback branch, refuted by instantiating its "no
/// pattern matched" hypothesis with the relation's values (`k2l_absurd`), or a branch that a
/// second round of `k2l_fundep` and `simp_all` closes.
pub fn adequacy_tactic(rule: &str) -> String {
    format!(
        "  k2l_map_facts\n  k2l_list_facts\n  dsimp only [{rule}]\n  repeat' (first | (k2l_fundep1; (try dsimp only)) | split)\n  all_goals (k2l_fundep; (try simp_all))\n  all_goals (k2l_split_ands; (try subst_vars); first | k2l_absurd | (k2l_fundep; simp_all))\n\n"
    )
}

/// The membership theorems of every rule in the bucket of its own left-hand side: `mem` at the
/// applicability relation's left-hand side, `memS` at the step relation's (an instance of it, so
/// it has the same constructors at the same positions and the same path). `rs` are the rules the
/// index `bucket` was built from, in its order.
pub fn emit_mem(o: &mut String, rs: &[&Rule], bucket: &str, info: &crate::index::CtorInfo) {
    let lhs: Vec<&L> = rs.iter().map(|r| &r.app.index).collect();
    let tree = crate::index::build(&lhs, info);
    for (pos, r) in rs.iter().enumerate() {
        let tac = crate::index::mem_tactic_or_search(&tree, pos, &r.app.index, info, bucket);
        o.push_str(&format!(
            "theorem Rules.{0}.mem{1} :\n    R.{0} ∈ {bucket} {2} := by\n{tac}\n",
            r.lean,
            ctor_sig(&r.app),
            r.app.index.render_arg()
        ));
        o.push_str(&format!(
            "theorem Rules.{0}.memS{1} :\n    R.{0} ∈ {bucket} {2} := by\n{tac}\n",
            r.lean,
            ctor_sig(&r.step),
            r.step.index.render_arg()
        ));
    }
}

pub fn emit_adequacy(
    rules: &[Rule],
    top: &str,
    ns: &str,
    unfold: &[String],
    info: &crate::index::CtorInfo,
) -> String {
    let mut o = String::new();
    o.push_str(&format!(
        "import {ns}.Rules\nimport KPrelude.Tactic\n\n/-! Generated by k2lean; do not edit.\n\nAdequacy of the executable step with respect to `Step` and `App`. Soundness holds by\n\
construction (every matcher returns a proof); completeness is proved rule by rule. -/\n\n\
set_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace {ns}\n\nopen KPrelude\n\n"
    ));
    let _ = unfold;
    for r in rules {
        let rule = format!("Rules.{}", r.lean);
        let s_rhs = r.rhs.subst(&r.step.subst).render_arg();
        o.push_str(&format!(
            "theorem {rule}.complete{} :\n    ({rule} {}).next? = some {s_rhs} := by\n{}",
            ctor_sig(&r.step),
            r.step.index.render_arg(),
            adequacy_tactic(&rule)
        ));
        o.push_str(&format!(
            "theorem {rule}.applies{} :\n    ({rule} {}).applies = true := by\n{}",
            ctor_sig(&r.app),
            r.app.index.render_arg(),
            adequacy_tactic(&rule)
        ));
    }
    // Step → App
    o.push_str(&format!(
        "theorem Step.app {{c c' : {top}}} (h : Step c c') : App c := by\n  cases h with\n"
    ));
    for r in rules {
        let args = ctor_args(&r.step);
        let app_args = ctor_args(&r.app);
        o.push_str(&format!(
            "  | {} {} => exact App.{} {}\n",
            r.lean,
            args.join(" "),
            r.lean,
            app_args.join(" ")
        ));
    }
    // every rule is in the bucket of its own left-hand side
    o.push('\n');
    let all: Vec<&Rule> = rules.iter().collect();
    emit_mem(&mut o, &all, "bucketOf", info);
    o.push_str(&format!(
        "theorem bucket_complete {{c c' : {top}}} (h : Step c c') : ∃ r ∈ bucketOf c, (r.run c).next? = some c' := by\n  cases h with\n"
    ));
    for r in rules {
        let args = ctor_args(&r.step).join(" ");
        o.push_str(&format!(
            "  | {0} {args} => exact ⟨R.{0}, Rules.{0}.memS {args}, Rules.{0}.complete {args}⟩\n",
            r.lean
        ));
    }
    o.push_str(&format!(
        "\ntheorem bucket_applies {{c : {top}}} (h : App c) : ∃ r ∈ bucketOf c, (r.run c).applies = true := by\n  cases h with\n"
    ));
    for r in rules {
        let args = ctor_args(&r.app).join(" ");
        o.push_str(&format!(
            "  | {0} {args} => exact ⟨R.{0}, Rules.{0}.mem {args}, Rules.{0}.applies {args}⟩\n",
            r.lean
        ));
    }
    // completeness over the list
    o.push_str(&format!(
        "\ntheorem rules_complete {{c c' : {top}}} (h : Step c c') : ∃ r ∈ rules, (r.run c).next? = some c' := by\n  cases h with\n"
    ));
    for (i, r) in rules.iter().enumerate() {
        let args = ctor_args(&r.step);
        o.push_str(&format!(
            "  | {} {} => exact ⟨R.{}, KPrelude.mem_of_getElem? (i := {i}) rfl, Rules.{}.complete {}⟩\n",
            r.lean,
            args.join(" "),
            r.lean,
            r.lean,
            args.join(" ")
        ));
    }
    o.push_str(&format!(
        "\ntheorem rules_applies {{c : {top}}} (h : App c) : ∃ r ∈ rules, (r.run c).applies = true := by\n  cases h with\n"
    ));
    for (i, r) in rules.iter().enumerate() {
        let args = ctor_args(&r.app);
        o.push_str(&format!(
            "  | {} {} => exact ⟨R.{}, KPrelude.mem_of_getElem? (i := {i}) rfl, Rules.{}.applies {}⟩\n",
            r.lean,
            args.join(" "),
            r.lean,
            r.lean,
            args.join(" ")
        ));
    }
    o.push_str(&format!(
        r#"
/-- Soundness of the executable step. -/
theorem step_sound {{c c' : {top}}} (h : step c = .next c') : Step c c' :=
  firstDefined_sound (bucketOf c) c none c' h

/-- `successors` lists exactly the `Step` successors. -/
theorem successors_iff {{c c' : {top}}} : c' ∈ successors rules c ↔ Step c c' := by
  rw [mem_successors]
  constructor
  · rintro ⟨r, _, h⟩; exact RuleResult.sound_of_next? h
  · exact rules_complete

/-- If some rule has a successor, the step function takes a step. -/
theorem step_progress {{c c' : {top}}} (h : Step c c') : ∃ c'', step c = .next c'' := by
  obtain ⟨r, hm, hr⟩ := bucket_complete h
  exact firstDefined_next_of_mem (bucketOf c) c none r c' hm hr

/-- A stuck configuration: no rule applies. -/
theorem step_stuck {{c : {top}}} (h : step c = .stuck) : ¬ App c := by
  intro ha
  obtain ⟨r, hm, hr⟩ := bucket_applies ha
  have := firstDefined_stuck (bucketOf c) c h r hm
  rw [hr] at this
  exact Bool.noConfusion this

theorem stuck_no_step {{c : {top}}} (h : step c = .stuck) (c' : {top}) : ¬ Step c c' :=
  fun hs => step_stuck h (Step.app hs)

/-- An undefined step: a rule applies, and there is no successor. -/
theorem step_undefined {{c : {top}}} {{n : String}} (h : step c = .undefined n) :
    App c ∧ ∀ c', ¬ Step c c' := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hm, hr⟩ := firstDefined_undefined_applies (bucketOf c) c n h
    exact RuleResult.app_of_applies (fun c' hs => Step.app hs) hr
  · intro c' hs
    obtain ⟨r, hm, hr⟩ := bucket_complete hs
    have := firstDefined_undefined (bucketOf c) c none n h r hm
    rw [hr] at this
    cases this

/-- Runs are `Step` derivations. -/
theorem run_sound (fuel : Nat) (c : {top}) :
    StepsN Step (run fuel c).steps c (run fuel c).config := by
  have := (KPrelude.run_sound (step := step) (R := Step) (I := fun _ => True)
    (fun _ _ _ h => step_sound h) (fun _ _ _ _ => trivial) fuel c 0 trivial).1
  simpa [run] using this

end {ns}
"#
    ));
    o
}

pub fn emit_determinism(top: &str, ns: &str, unfold: &[String]) -> String {
    format!(
        "import {ns}.Adequacy\n\n/-! Generated by k2lean; do not edit.\n\nDeterminism of `Step`, by case analysis on pairs of rules; pairs whose left-hand sides\n\
cannot unify are discharged by `cases` itself. -/\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace {ns}\n\nopen KPrelude\n\n\
theorem Step.deterministic {{c c₁ c₂ : {top}}} (h₁ : Step c c₁) (h₂ : Step c c₂) : c₁ = c₂ := by\n  cases h₁ <;> cases h₂ <;> k2l_map_facts <;> (try simp_all [{0}]) <;>\n    (repeat' (k2l_split_hyps <;> (try simp_all [{0}])))\n\n\
/-- With determinism, the executable step is complete. -/\ntheorem step_complete {{c c' : {top}}} (h : Step c c') : step c = .next c' := by\n  obtain ⟨c'', hc⟩ := step_progress h\n  rw [hc, Step.deterministic (step_sound hc) h]\n\n\
theorem step_iff {{c c' : {top}}} : step c = .next c' ↔ Step c c' := ⟨step_sound, step_complete⟩\n\nend {ns}\n",
        unfold.join(", "),
        top = top,
        ns = ns
    )
}

#[cfg(test)]
mod tests {
    //! Rule naming (the `Step` constructor names that hand proofs and residual-case tags refer to)
    //! and the priority ranks that choose the stratified emitter.
    use super::*;
    use crate::funcs::tests::{fixture, generated};

    fn rules_of(def: &Def) -> Vec<Rule> {
        let (m, g) = generated(def);
        collect(def, &m, &g.fns, &[]).unwrap()
    }

    #[test]
    fn a_rule_is_named_by_its_label_else_by_its_content() {
        let def = fixture("peano");
        let rs = rules_of(&def);
        let names: Vec<(&str, Option<&str>)> = rs
            .iter()
            .map(|r| (r.lean.as_str(), r.label.as_deref()))
            .collect();
        assert_eq!(
            names,
            vec![("start", Some("start")), ("«done(s(s(N)))»", None)]
        );
        assert_eq!(display_name(&rs[1]), "done(s(s(N)))");
        // the source position is the constructor's doc comment
        assert_eq!(doc(&rs[1]), "`done(s(s(N)))` (peano.k:30:3)");
    }

    #[test]
    fn the_doc_position_uses_the_source_file_name_only() {
        // the same definition compiled from another directory gets the same names and positions
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/peano/definition.kore");
        let text = std::fs::read_to_string(p).unwrap();
        let start = text.find("Source(").unwrap() + "Source(".len();
        let end = start + text[start..].find("peano.k").unwrap();
        let moved = text.replace(&text[start..end], "/some/other/checkout/");
        assert_ne!(moved, text);
        let def = crate::ir::load(&moved).unwrap();
        let rs = rules_of(&def);
        assert_eq!(rs[1].lean, "«done(s(s(N)))»");
        assert_eq!(rs[1].loc.as_deref(), Some("peano.k:30:3"));
    }

    #[test]
    fn priorities_give_ranks_and_order() {
        let def = fixture("counter");
        assert_eq!(priorities(&def), vec![40, 50]);
        let rs = rules_of(&def);
        // the rules of the higher priority (lower number) come first
        assert_eq!(rs[0].priority, 40);
        assert!(
            rs.iter()
                .any(|r| r.lean == "incr" && r.label.as_deref() == Some("incr"))
        );
        assert!(rs.windows(2).all(|w| w[0].priority <= w[1].priority));
        let def = fixture("peano");
        assert_eq!(priorities(&def), vec![50]);
    }
}
