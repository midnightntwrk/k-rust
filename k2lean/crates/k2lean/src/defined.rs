//! Progress to a step (SND-20, `k2lean/docs/design.md` §3.9): `gen --progress` also writes
//! `{pfx}/DefinedDefs.lean`, `{pfx}/Defined.lean` and, beside the library, `open-defined-rules.txt`.
//!
//! `progress` concludes `App c`: some rule's left-hand side matches with a true `requires`. A rule
//! whose right-hand side is `⊥` (a partial call with no value, a map built with a key already
//! bound) or whose `ensures` fails applies and gives no successor, so `App` does not exclude a
//! stuck configuration. Its `Step` constructor has the right-hand side's premises
//! (`t = some v`, the ensures' tests) after the `App` constructor's, and nothing else.
//!
//! **The obligation, one per rule with such premises.** `Defined.r.statement`: at every instance
//! of the rule's match and `requires` that satisfies the invariant (and, with priorities, where no
//! rule of a higher rank applies), some step exists. The conclusion is any `Step`, not rule `r`'s
//! own, so a hand proof may use another rule of the rank; the generated proof obtains a value for
//! each premise in order (`def_close`: the hooks and the proved equations under the `requires`
//! and the invariant, then the totality lemmas `@[k2l_value]`) and applies `r`'s constructor.
//! A rule with no such premise needs nothing: its `Step` constructor applies as its `App` one does.
//!
//! **The outcomes.** An obligation `def_close` does not prove is listed in `open-defined-rules.txt`
//! and taken from the hand module `{pfx}/DefinedHand.lean` (written once) as `Defined.hand.r`. One
//! marked `| refuted hand` is false, a configuration that satisfies the invariant where the rule
//! applies and nothing steps (`Defined.r.refuted`, checked by `#k2l_refuted`): an undefined
//! behaviour of the definition, such as a division by zero. Such a rule is a further outcome of
//! `progress_step`, `Undefined c` (the rule applies at `c`).
//!
//! **The theorems.** `app_step : Inv c → App c → (∃ c', Step c c') ∨ Undefined c` by cases on
//! `App` (with priorities, at the least rank that applies, `Step0.lift`), and from it and
//! `progress`: `progress_step : Inv c → Ending c ∨ (∃ c', Step c c') ∨ Undefined c` (and
//! `Progress.Refuted c` where `progress` has it), `no_stuck_step` and `always_step`. They are named
//! `*_step` until every progress library has them; the rename of the `App` forms is core's CT-3
//! landing before the first release.

use crate::progress::Ctx;
use crate::rules::Rule;
use std::collections::BTreeSet;

/// What `progress` concludes, which `progress_step` extends.
pub struct Shape {
    /// `<k>` is in a cell map: `progress` takes `Progress.Keys c`.
    pub coll: bool,
    /// `progress` has the third outcome `Progress.Refuted c`.
    pub refuted: bool,
    /// The invariant's name (`Invariant` or `Progress.Inv`).
    pub inv: String,
    /// The unfolding set of `def_close`: the hooks, sort injections and projections, and the
    /// proved equations of the functions the rules' conditions call.
    pub close: Vec<String>,
}

pub struct Out {
    /// `{ns}/HooksDefined.lean`, when a right-hand side calls a parameter of the library.
    pub hooks: Option<String>,
    pub defs: String,
    pub theorems: String,
    pub open_list: String,
    pub hand_skeleton: Option<String>,
    /// Rules with an obligation, and how many of them are open (refuted included).
    pub obligations: usize,
    pub open: usize,
    /// The outcomes of `progress_step` beside an ending and a step, in its order (`Undefined`,
    /// `Unproved`, `Progress.Refuted`): what a run may also end at (`ends.rs`).
    pub outcomes: Vec<String>,
}

/// A rule's obligation: the binders and hypotheses of its `App` constructor, and the premises its
/// `Step` constructor adds.
struct Obl<'a> {
    rule: &'a Rule,
    rank: Option<usize>,
    /// `(binder, defining premise index)` for each binder the `Step` constructor adds.
    extra_binders: Vec<(String, String)>,
    extra_hyps: Vec<(String, String)>,
}

fn obligation<'a>(r: &'a Rule, rank: Option<usize>) -> Result<Obl<'a>, String> {
    let (a, s) = (&r.app, &r.step);
    if s.binders.len() < a.binders.len()
        || s.binders[..a.binders.len()] != a.binders[..]
        || s.hyps.len() < a.hyps.len()
        || s.hyps[..a.hyps.len()] != a.hyps[..]
    {
        return Err(format!(
            "--progress: rule {}: its Step constructor does not extend its App constructor",
            r.name
        ));
    }
    Ok(Obl {
        rule: r,
        rank,
        extra_binders: s.binders[a.binders.len()..].to_vec(),
        extra_hyps: s.hyps[a.hyps.len()..].to_vec(),
    })
}

fn paren(s: &str) -> String {
    if s.contains(' ') && !(s.starts_with('(') && s.ends_with(')')) {
        format!("({s})")
    } else {
        s.to_string()
    }
}

/// `Or.inr (… (Or.inl h))`: the `i`-th of `n` disjuncts.
fn inj(i: usize, n: usize, h: &str) -> String {
    let mut w = if i + 1 < n {
        format!("Or.inl {}", paren(h))
    } else {
        h.to_string()
    };
    for _ in 0..i {
        w = format!("Or.inr ({w})");
    }
    w
}

pub fn emit(
    cx: &Ctx,
    shape: &Shape,
    prios: &[i64],
    params: &[(String, Vec<String>, String)],
    open_text: &str,
    hand_exists: bool,
) -> Result<Out, String> {
    let (ns, top, pfx) = (cx.ns, cx.top, cx.module.as_str());
    let inv = shape.inv.as_str();
    let ranked = cx.ranked;
    let mut obls = Vec::new();
    for r in cx.rules {
        let rank = ranked.then(|| crate::multi::rank_of(r, prios));
        obls.push(obligation(r, rank)?);
    }
    // the open list: a bare entry is proved by hand, `| refuted hand` refuted by hand, and
    // `| unproved` neither (an outcome of `progress_step`, `Unproved`); `| unproved` is this list's
    // own marker, read here before the shared parser
    let strip = |n: &str| n.strip_prefix("Defined.").unwrap_or(n).to_string();
    let mut unproved: BTreeSet<String> = BTreeSet::new();
    let mut rest = String::new();
    for l in open_text.lines() {
        if let Some(n) = crate::refuted::name_of(l) {
            let body = l.trim()[n.len()..].split('#').next().unwrap_or("");
            if body
                .split_once('|')
                .is_some_and(|(_, m)| m.trim() == "unproved")
            {
                unproved.insert(strip(&n));
                continue;
            }
        }
        rest.push_str(l);
        rest.push('\n');
    }
    let list = crate::refuted::parse(&rest).map_err(|e| format!("open-defined-rules.txt: {e}"))?;
    let refuted: BTreeSet<String> = list.refuted.keys().map(|n| strip(n)).collect();
    let open: BTreeSet<String> = list
        .names
        .iter()
        .map(|n| strip(n))
        .filter(|n| !refuted.contains(n))
        .collect();

    let keys = |idx: &str| {
        if shape.coll {
            format!(" Progress.Keys {idx} →")
        } else {
            String::new()
        }
    };
    let higher = |o: &Obl, idx: &str| match o.rank {
        Some(i) => format!(" (∀ j, j < {i} → ¬ App j {idx}) →"),
        None => String::new(),
    };

    // the statements, and `Undefined`
    let mut defs = String::new();
    let needs: Vec<&Obl> = obls
        .iter()
        .filter(|o| !o.extra_binders.is_empty() || !o.extra_hyps.is_empty())
        .collect();
    for o in &needs {
        let r = o.rule;
        let idx = paren(&r.app.index.render_arg());
        let mut q: Vec<String> = r
            .app
            .binders
            .iter()
            .map(|(b, t)| format!("({b} : {t})"))
            .collect();
        q.extend(r.app.hyps.iter().map(|(h, p)| format!("({h} : {p})")));
        let lead = if q.is_empty() {
            String::new()
        } else {
            format!("∀ {}, ", q.join(" "))
        };
        defs.push_str(&format!(
            "/-- `{}`: where it applies under the invariant, some step exists (its right-hand side is defined). -/\n\
def Defined.{l}.statement : Prop :=\n  {lead}{inv} {idx} →{}{} ∃ c', Step {idx} c'\n\n",
            r.name,
            keys(&idx),
            higher(o, &idx),
            l = r.lean
        ));
    }
    // the outcomes of `progress_step` beside a step: the rules refuted (`Undefined`: shown to have
    // no value somewhere under the invariant) and the rules marked unproved (`Unproved`: neither)
    let groups: Vec<(&str, &str, Vec<&&Obl>)> = [
        (
            "Undefined",
            "its definedness is refuted: it has no value somewhere under the invariant",
            &refuted,
        ),
        (
            "Unproved",
            "its definedness is neither proved nor refuted (`| unproved`)",
            &unproved,
        ),
    ]
    .into_iter()
    .map(|(g, what, set)| {
        (
            g,
            what,
            needs
                .iter()
                .filter(|o| set.contains(&o.rule.lean))
                .collect::<Vec<_>>(),
        )
    })
    .filter(|(_, _, v)| !v.is_empty())
    .collect();
    for (g, what, rs) in &groups {
        for o in rs {
            let r = o.rule;
            let idx = paren(&r.app.index.render_arg());
            let bs: Vec<String> = r
                .app
                .binders
                .iter()
                .map(|(b, t)| format!("({b} : {t})"))
                .collect();
            let mut body: Vec<String> = r.app.hyps.iter().map(|(_, p)| paren(p)).collect();
            body.push(format!("c = {idx}"));
            let ex = if bs.is_empty() {
                String::new()
            } else {
                format!("∃ {}, ", bs.join(" "))
            };
            defs.push_str(&format!(
                "/-- `{}` applies at `c` ({what}). -/\ndef {g}.{} (c : {top}) : Prop :=\n  {ex}{}\n\n",
                r.name,
                r.lean,
                body.join(" ∧ ")
            ));
        }
        let ds: Vec<String> = rs
            .iter()
            .map(|o| format!("{g}.{} c", o.rule.lean))
            .collect();
        defs.push_str(&format!(
            "/-- Some rule applies at `c` of which {what}. -/\ndef {g} (c : {top}) : Prop :=\n  {}\n\n",
            ds.join(" ∨ ")
        ));
    }

    // the closers' unfolding set: `progress`'s, and the proved equations of the functions the
    // right-hand sides' premises call
    let mut close: BTreeSet<String> = shape.close.iter().cloned().collect();
    for (sym, sig) in cx.fns {
        if needs
            .iter()
            .any(|o| o.extra_hyps.iter().any(|(_, p)| p.contains(&sig.lean)))
            && let Some(es) = cx.eqns.get(sym)
        {
            close.extend(es.iter().cloned());
        }
    }
    // the hooks the premises call (a hook only a right-hand side calls is in no `requires`)
    for o in &needs {
        for (_, p) in &o.extra_hyps {
            for tok in p.split(|c: char| !(c.is_alphanumeric() || c == '.' || c == '_')) {
                if tok.starts_with("KPrelude.") && tok.contains("Hook.") {
                    close.insert(tok.trim_end_matches('.').to_string());
                }
            }
        }
    }
    let close: Vec<String> = close.into_iter().collect();

    // the library's parameters that a right-hand side calls: no proof of their definedness exists
    // for every instance, so `Hooks.Defined` states it and the step theorems assume it
    let called: Vec<&(String, Vec<String>, String)> = params
        .iter()
        .filter(|(h, _, _)| {
            needs.iter().any(|o| {
                o.extra_hyps
                    .iter()
                    .any(|(_, p)| p.contains(&format!("Hooks.«{h}»")))
            })
        })
        .collect();
    let hooks = (!called.is_empty()).then(|| {
        let mut f = String::new();
        for (h, args, _) in &called {
            let xs: Vec<String> = (0..args.len()).map(|i| format!("x{i}")).collect();
            let bs: String = xs.iter().zip(args.iter()).map(|(x, t)| format!("({x} : {t}) ")).collect();
            f.push_str(&format!(
                "  /-- `{h}` has a value at every argument. -/\n  «{h}» : ∀ {bs}, ∃ v, Hooks.«{h}» {} = some v\n",
                xs.join(" ")
            ));
        }
        format!(
            "import {ns}.Functions\n\n/-! Generated by k2lean (`gen --progress`); do not edit.\n\n\
The library's parameters that a rule's right-hand side calls, as total: no proof of it exists for every\n\
implementation, so the step forms of `progress` (`Defined.lean`) assume it, and an instance proves it\n\
(SND-20). -/\n\nnamespace {ns}\n\nvariable [Hooks]\n\n\
/-- The parameters a right-hand side calls are defined at every argument. -/\n\
class Hooks.Defined : Prop where\n{f}\nend {ns}\n"
        )
    });
    let hook_alts: String = called
        .iter()
        .map(|(h, args, _)| {
            format!(
                "\n  | exact Hooks.Defined.«{h}» {}",
                vec!["_"; args.len()].join(" ")
            )
        })
        .collect();

    // the proofs
    let mut th = format!(
        "/-- The closers' computation: the hooks, the sort injections and projections, the proved equations. -/\n\
local macro \"def_simp\" : tactic => `(tactic| simp_all [{}])\n\n\
/-- A value for a right-hand side's premise, or an ensures' test: by computing it under the `requires` and the invariant,\n\
then with the totality lemmas of the functions it reaches (`@[k2l_value]`). -/\n\
local macro \"def_close\" : tactic => `(tactic| first\n  | exact ⟨_, rfl⟩\n  | assumption{hook_alts}\n  | k2l_map_defined\n  \
| (apply Option.ne_none_iff_exists'.mp; first | (def_simp; done) | (k2l_value_all; def_simp; done))\n  \
| (def_simp; done)\n  | (k2l_value_all; def_simp; done))\n\n",
        close.join(", "),
    );
    let step_of = |o: &Obl, args: &str| -> String {
        let r = o.rule;
        match o.rank {
            Some(i) => format!(
                "Step0.lift (Step0.{} {args}) {}",
                r.lean,
                if i == 0 {
                    "(fun _ h => absurd h (Nat.not_lt_zero _))".to_string()
                } else {
                    "hmin".into()
                }
            ),
            None => format!("Step.{} {args}", r.lean),
        }
    };
    for o in &needs {
        let r = o.rule;
        let l = &r.lean;
        if refuted.contains(l) || unproved.contains(l) {
            continue;
        }
        if open.contains(l) {
            th.push_str(&format!(
                "theorem Defined.{l} : Defined.{l}.statement := Defined.hand.{l}\n\n"
            ));
            continue;
        }
        let mut intro: Vec<String> = r.app.binders.iter().map(|(b, _)| b.clone()).collect();
        intro.extend(r.app.hyps.iter().map(|(h, _)| h.clone()));
        intro.push("hI".into());
        if shape.coll {
            intro.push("hK".into());
        }
        if matches!(o.rank, Some(i) if i > 0) {
            intro.push("hmin".into());
        } else if o.rank.is_some() {
            intro.push("_".into());
        }
        let mut body = String::new();
        let mut bound: BTreeSet<&str> = BTreeSet::new();
        for (h, p) in &o.extra_hyps {
            // `t = some v` for a binder `v` the step adds: obtain the value
            let v = p
                .rsplit_once(" = some ")
                .map(|(_, v)| v.trim())
                .filter(|v| o.extra_binders.iter().any(|(b, _)| b == v) && !bound.contains(v));
            match v {
                Some(v) => {
                    let t = p.rsplit_once(" = some ").unwrap().0;
                    body.push_str(&format!(
                        "  obtain ⟨{v}, {h}⟩ : ∃ {v}, {t} = some {v} := by def_close\n"
                    ));
                    bound.insert(v);
                }
                None => body.push_str(&format!("  have {h} : {p} := by def_close\n")),
            }
        }
        if let Some((b, _)) = o
            .extra_binders
            .iter()
            .find(|(b, _)| !bound.contains(b.as_str()))
        {
            return Err(format!(
                "--progress: rule {}: the step's binder {b} has no premise `… = some {b}`",
                r.name
            ));
        }
        let mut args: Vec<String> = r.step.binders.iter().map(|(b, _)| b.clone()).collect();
        args.extend(r.step.hyps.iter().map(|(h, _)| h.clone()));
        th.push_str(&format!(
            "theorem Defined.{l} : Defined.{l}.statement := by\n  intro {}\n{body}  exact ⟨_, {}⟩\n\n",
            intro.join(" "),
            step_of(o, &args.join(" "))
        ));
    }

    // `app_step`
    let hk = if shape.coll {
        " (hK : Progress.Keys c)"
    } else {
        ""
    };
    let app_hyp = if cx.ranks > 1 {
        "Progress.App c"
    } else if ranked {
        "App 0 c"
    } else {
        "App c"
    };
    let n_out = 1 + groups.len();
    let mut parts = vec!["∃ c', Step c c'".to_string()];
    parts.extend(groups.iter().map(|(g, _, _)| format!("{g} c")));
    let concl_a = if n_out > 1 {
        parts[0] = format!("({})", parts[0]);
        parts.join(" ∨ ")
    } else {
        parts[0].clone()
    };
    let mut arms = String::new();
    for o in &obls {
        let r = o.rule;
        let l = &r.lean;
        let mut pat: Vec<String> = r.app.binders.iter().map(|(b, _)| b.clone()).collect();
        pat.extend(r.app.hyps.iter().map(|(h, _)| h.clone()));
        let pats = pat.join(" ");
        let has = !o.extra_binders.is_empty() || !o.extra_hyps.is_empty();
        let grp = groups.iter().enumerate().find_map(|(gi, (_, _, rs))| {
            rs.iter()
                .position(|u| &u.rule.lean == l)
                .map(|i| (gi, i, rs.len()))
        });
        let term = if let Some((gi, i, k)) = grp {
            let w = format!(
                "⟨{}rfl⟩",
                pat.iter().map(|p| format!("{p}, ")).collect::<String>()
            );
            inj(1 + gi, n_out, &inj(i, k, &w))
        } else if has {
            let mut a = vec![pats.clone(), "hI".into()];
            if shape.coll {
                a.push("hK".into());
            }
            if matches!(o.rank, Some(i) if i > 0) {
                a.push("hmin".into());
            } else if o.rank.is_some() {
                a.push("(fun _ h => absurd h (Nat.not_lt_zero _))".into());
            }
            inj(0, n_out, &format!("Defined.{l} {}", a.join(" ")))
        } else {
            inj(0, n_out, &format!("⟨_, {}⟩", step_of(o, &pats)))
        };
        arms.push_str(&format!("  | {l} {pats} => exact {term}\n"));
    }
    let pre = if cx.ranks > 1 {
        "  obtain ⟨i, h, hmin⟩ := Progress.App.least h\n"
    } else {
        ""
    };
    th.push_str(&format!(
        "/-- A rule that applies under the invariant steps, or is one whose definedness is refuted or unproved. -/\n\
theorem app_step (c : {top}) (hI : {inv} c){hk} (h : {app_hyp}) : {concl_a} := by\n{pre}  cases h with\n{arms}\n"
    ));

    // `progress_step`, `no_stuck_step`, `always_step`
    let mut outcomes: Vec<String> = groups.iter().map(|(g, _, _)| g.to_string()).collect();
    if shape.refuted {
        outcomes.push("Progress.Refuted".into());
    }
    let mut outs = vec!["Ending c".to_string(), "∃ c', Step c c'".to_string()];
    outs.extend(outcomes.iter().map(|g| format!("{g} c")));
    let n = outs.len();
    let concl = outs
        .iter()
        .enumerate()
        .map(|(i, o)| {
            if i == 1 && n > 2 {
                format!("({o})")
            } else {
                o.clone()
            }
        })
        .collect::<Vec<_>>()
        .join(" ∨ ");
    let kp = if shape.coll { " hK" } else { "" };
    let a_arm = if groups.is_empty() {
        format!("exact {}", inj(1, n, &format!("app_step c hI{kp} h")))
    } else {
        let alts = vec!["h"; n_out].join(" | ");
        let mut t = format!("rcases app_step c hI{kp} h with {alts}");
        for gi in 0..n_out {
            t.push_str(&format!("\n    · exact {}", inj(1 + gi, n, "h")));
        }
        t
    };
    let r_arm = if shape.refuted {
        format!("\n  · exact {}", inj(n - 1, n, "h"))
    } else {
        String::new()
    };
    let rc = if shape.refuted { "h | h | h" } else { "h | h" };
    let mut what = String::from("an ending, or steps");
    if !groups.is_empty() || shape.refuted {
        let mut w = vec!["an ending".to_string(), "steps".to_string()];
        for (g, _, _) in &groups {
            w.push(match *g {
                "Undefined" => {
                    "a rule whose definedness is refuted applies (`Undefined`)".to_string()
                }
                _ => "a rule whose definedness is unproved applies (`Unproved`)".to_string(),
            });
        }
        if shape.refuted {
            w.push("its head is one whose case of `progress` is refuted".into());
        }
        let last = w.pop().unwrap();
        what = format!("{}, or {last}", w.join(", "));
    }
    th.push_str(&format!(
        "/-- No stuck configuration: one that satisfies the invariant is {what}. -/\n\
theorem progress_step (c : {top}) (hI : {inv} c){hk} : {concl} := by\n  rcases progress c hI{kp} with {rc}\n  · exact Or.inl h\n  · {a_arm}{r_arm}\n\n"
    ));
    let concl_s = concl
        .replace(" c'", " C'")
        .replace(" c", " (s n)")
        .replace(" C'", " c'");
    if shape.coll {
        th.push_str(&format!(
            "/-- From a configuration that satisfies the invariant and `Progress.Keys`, every configuration reached is {what}. -/\n\
theorem no_stuck_step {{c0 c : {top}}} (h0 : {inv} c0) (hk0 : Progress.Keys c0) (h : Star Step c0 c) : {concl} :=\n  \
progress_step c ({inv}.preserved.star h h0) (Progress.Keys.preserved.star h hk0)\n\n\
/-- The same, on every run from `c0`. -/\n\
theorem always_step {{c0 : {top}}} (h0 : {inv} c0) (hk0 : Progress.Keys c0) :\n    ∀ s, s 0 = c0 → Paths.IsRun Step s → ∀ n, {concl_s} :=\n  \
Paths.always_iff.2 fun c h =>\n    progress_step c (Preserved.star {inv}.preserved h h0) (Preserved.star Progress.Keys.preserved h hk0)\n\n"
        ));
    } else {
        th.push_str(&format!(
            "/-- From a configuration that satisfies the invariant, every configuration reached is {what}. -/\n\
theorem no_stuck_step {{c0 c : {top}}} (h0 : {inv} c0) (h : Star Step c0 c) : {concl} :=\n  progress_step c ({inv}.preserved.star h h0)\n\n\
/-- The same, on every run from `c0`. -/\n\
theorem always_step {{c0 : {top}}} (h0 : {inv} c0) :\n    ∀ s, s 0 = c0 → Paths.IsRun Step s → ∀ n, {concl_s} :=\n  \
Paths.always_iff.2 fun c h => progress_step c (Preserved.star {inv}.preserved h h0)\n\n"
        ));
    }
    th.push_str("#k2l_assert_axioms app_step progress_step no_stuck_step always_step\n");
    for l in &refuted {
        th.push_str(&format!("#k2l_refuted Defined.{l}\n"));
    }

    // the open list and the hand module
    let mut ol = String::from(
        "# Rules whose definedness `def_close` does not prove (`k2lean gen --progress`, SND-20).\n\
# `k2lean open-from-log NS/Defined.lean BUILD.log open-defined-rules.txt` adds the rules whose proof failed.\n\
# Each entry: `Defined.r`; prove it in NS/DefinedHand.lean as `theorem Defined.hand.r : Defined.r.statement`,\n\
# or mark it `| refuted hand` with `theorem Defined.r.refuted : ¬ Defined.r.statement` there (the rule applies\n\
# and nothing steps: an undefined behaviour; `progress_step` then has the rule as an outcome, `Undefined`),\n\
# or mark it `| unproved` (neither shown; `progress_step` has the rule as an outcome, `Unproved`).\n",
    );
    for l in open_text.lines() {
        if crate::refuted::name_of(l).is_some() {
            ol.push_str(l.trim_end());
            ol.push('\n');
        }
    }
    let hand_names: Vec<&String> = needs
        .iter()
        .map(|o| &o.rule.lean)
        .filter(|l| open.contains(*l) || refuted.contains(*l))
        .collect();
    let any_hand = !hand_names.is_empty();
    let hand_skeleton = (any_hand && !hand_exists).then(|| {
        let mut s = format!(
            "import {pfx}.DefinedDefs\nimport {ns}.Adequacy\n\n/-! Hand-written proofs of the rules listed in `open-defined-rules.txt`.\n\n\
`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each rule's definedness\n\
below as the theorem it names, or refute it (`theorem Defined.r.refuted : ¬ Defined.r.statement`, marked\n\
`| refuted hand` in the list: an instance where the rule applies and no step exists). -/\n\nnamespace {ns}\n\nopen KPrelude\n\n"
        );
        for l in &hand_names {
            if refuted.contains(*l) {
                s.push_str(&format!(
                    "-- theorem Defined.{l}.refuted : ¬ Defined.{l}.statement := by\n--   …\n\n"
                ));
            } else {
                s.push_str(&format!(
                    "-- theorem Defined.hand.{l} : Defined.{l}.statement := by\n--   …\n\n"
                ));
            }
        }
        s.push_str(&format!("end {ns}\n"));
        s
    });
    let defs_mod = format!(
        "import {pfx}.ProgressDefs\n\n/-! Generated by k2lean (`gen --progress`); do not edit.\n\n\
The definedness of each rule's right-hand side where it applies under the invariant (SND-20): one statement per\n\
rule whose `Step` constructor has premises its `App` constructor lacks. Separate so that `DefinedHand.lean` can\n\
prove or refute the ones `Defined.lean` does not close. -/\n\nset_option linter.unusedVariables false\n\n\
namespace {ns}\n\nopen KPrelude\n\n{defs}end {ns}\n"
    );
    let thm_mod = format!(
        "import {pfx}.Progress\nimport {pfx}.DefinedDefs\nimport {ns}.Adequacy\nimport KPrelude.Defined\n{}{}\n/-! Generated by k2lean (`gen --progress`); do not edit.\n\n\
`progress_step`: a configuration that satisfies `{inv}` is an acceptable ending or steps, or a rule whose\n\
definedness is refuted applies (`Undefined`). `progress` gives a rule that applies; each rule's `Defined`\n\
gives a step from it ({} rules with right-hand-side premises, {} open). -/\n\n\
set_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\nnamespace {ns}\n\nopen KPrelude\n\n{}{th}\nend {ns}\n",
        if hooks.is_some() {
            format!("import {ns}.HooksDefined\n")
        } else {
            String::new()
        },
        if any_hand {
            format!("import {pfx}.DefinedHand\n")
        } else {
            String::new()
        },
        needs.len(),
        hand_names.len(),
        if hooks.is_some() {
            "variable [Hooks.Defined]\n\n"
        } else {
            ""
        }
    );
    Ok(Out {
        hooks,
        defs: defs_mod,
        theorems: thm_mod,
        open_list: ol,
        hand_skeleton,
        obligations: needs.len(),
        open: hand_names.len() + unproved.len(),
        outcomes,
    })
}
