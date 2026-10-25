//! The instances of a function with a free-key map pattern, and their agreement
//! (`docs/design.md`, §2, "Free-key map patterns in function equations").
//!
//! An equation `f(K |-> V REST) => e requires c` whose key is bound nowhere else in its left-hand
//! side is one KORE axiom instance per binding of the map at which the rest of the left-hand side
//! matches and `c` holds; the generated definition takes the first such binding in the map's order
//! (`MapHook.chooseFirst`). For each function with such an equation this module generates, after
//! every function is defined:
//!
//! - `F.instN`: the instances of equation `N` at the arguments, one per match (every binding of
//!   each free-key map pattern, in the maps' order, lexicographically for several), each the
//!   value of the right-hand side there (`none` for `⊥` when `F` is partial);
//! - `F.instances`: the instances of the first priority group of `F`'s equations that has one
//!   (the equations of one priority are all axioms where none of a higher priority applies), and
//!   the cascade's own value where none applies (an `anywhere` symbol's constructor);
//! - `F.Agrees`: every two of them are equal (`KPrelude.Agree`, decidable), which is exactly where
//!   K's axioms determine `F`'s value;
//! - `F.instN_head`: the first instance of equation `N` is the value of the equation's matcher in
//!   the definition's cascade (`F.ruleN`, or `F.eqnN`, a copy of the matcher a recursive definition
//!   inlines); `F.eq_instances`: the generated value is the first of `F.instances`; and
//!   `F.eq_of_agrees`: under `F.Agrees`, the generated value is every instance's value.

use crate::lower::{L, Step};
use crate::render;
use std::collections::BTreeSet;

/// How the definition's cascade reads an equation's matcher.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Matcher {
    /// `F.ruleN`, a definition of its own (a non-recursive function).
    Rule,
    /// Inlined into `F`'s body (a recursive function): `F.eqnN` is generated, the same text.
    Inline,
    /// The last equation of a total function, with no left-hand-side step: the cascade's value.
    CatchAll,
}

pub struct Eqn {
    /// The equation's number in the cascade (`ruleN`, `eN`).
    pub n: usize,
    pub priority: i64,
    pub steps: Vec<Step>,
    pub lhs_len: usize,
    pub rhs: L,
    pub matcher: Matcher,
    /// The cascade names the matcher's value (`match heN : eN with`).
    pub named: bool,
}

pub struct FreeKeyFn {
    pub label: String,
    /// The function's Lean name (`K.…`).
    pub lean: String,
    pub params: Vec<String>,
    pub arg_tys: Vec<String>,
    pub result: String,
    /// Total (`F : … → R`), not `Option`-valued.
    pub pure: bool,
    pub recursive: bool,
    pub eqns: Vec<Eqn>,
    /// The cascade's value where no equation applies, when it is not `none` (`some ctor` of an
    /// `anywhere` symbol of a recursive function).
    pub fallback: Option<String>,
}

/// Whether an equation's steps have a free-key map pattern.
pub fn has_free_key(steps: &[Step]) -> bool {
    steps.iter().any(|s| matches!(s, Step::MapChoose { .. }))
}

fn l_vars(l: &L, out: &mut BTreeSet<String>) {
    match l {
        L::Var(v) => {
            out.insert(v.clone());
        }
        L::App(_, args) => args.iter().for_each(|a| l_vars(a, out)),
        L::Typed(e, _) => l_vars(e, out),
        L::Raw(r) => {
            out.extend(
                r.split(|c: char| !(c.is_alphanumeric() || c == '_'))
                    .filter(|w| !w.is_empty())
                    .map(str::to_string),
            );
        }
    }
}

/// Whether every instance of the equation has one value: its right-hand side (with the partial
/// calls it evaluates) reads no variable that the choice of a binding of a free-key map pattern
/// binds, directly or through a later match on such a variable. Then all matches evaluate one
/// expression over variables every match binds alike. A sufficient condition, not a decision:
/// `false` means only that agreement is not shown.
pub fn reads_no_choice(e: &Eqn) -> bool {
    let mut chosen: BTreeSet<String> = BTreeSet::new();
    let mut started = false;
    let mut reads: BTreeSet<String> = BTreeSet::new();
    let from = |l: &L, chosen: &BTreeSet<String>| {
        let mut vs = BTreeSet::new();
        l_vars(l, &mut vs);
        vs.iter().any(|v| chosen.contains(v))
    };
    for (i, s) in e.steps.iter().enumerate() {
        if i >= e.lhs_len {
            if let Step::Bind { expr, var, .. } = s {
                l_vars(expr, &mut reads);
                if from(expr, &chosen) {
                    chosen.insert(var.clone());
                }
            }
            continue;
        }
        match s {
            Step::MapChoose { key, val, rest, .. } => {
                started = true;
                chosen.extend([key.clone(), val.clone(), rest.clone()]);
            }
            _ if !started => {}
            Step::Destruct { scrut, pat, .. } => {
                if chosen.contains(scrut) {
                    l_vars(pat, &mut chosen);
                }
            }
            Step::Bind { expr, var, .. } => {
                if from(expr, &chosen) {
                    chosen.insert(var.clone());
                }
            }
            Step::MapElem {
                map,
                key,
                val,
                rest,
                ..
            } => {
                if chosen.contains(map) || from(key, &chosen) {
                    chosen.extend([val.clone(), rest.clone()]);
                }
            }
            Step::ListElem {
                list, head, tail, ..
            } => {
                if chosen.contains(list) {
                    chosen.extend([head.clone(), tail.clone()]);
                }
            }
            Step::Cond { .. } | Step::CondEq { .. } | Step::EqVar { .. } => {}
        }
    }
    l_vars(&e.rhs, &mut reads);
    reads.is_disjoint(&chosen)
}

/// The note `gen` prints for a function with a free-key equation.
pub fn note(f: &FreeKeyFn) -> String {
    let fk: Vec<&Eqn> = f.eqns.iter().filter(|e| has_free_key(&e.steps)).collect();
    let nums: Vec<String> = fk.iter().map(|e| e.n.to_string()).collect();
    let shown = fk.iter().all(|e| reads_no_choice(e));
    let verdict = if shown {
        "every such instance reads only variables that every match binds alike, so they agree at every argument"
    } else {
        "its instances are not shown to agree: where two matching bindings give different values, K's axioms determine no value and the definition is the first in key order"
    };
    format!(
        "{} has a free-key map pattern in equation {} ({}.Agrees states where K's axioms determine its value): {verdict}",
        f.label,
        nums.join(", "),
        f.lean
    )
}

/// The value type of an instance: the result, or `Option` of it for a partial function.
fn inst_ty(f: &FreeKeyFn) -> String {
    if f.pure {
        f.result.clone()
    } else {
        format!("Option {}", f.result)
    }
}

/// The generated declarations of `f` and the names of its theorems (for the axiom guard).
pub fn emit(f: &FreeKeyFn) -> (String, Vec<String>) {
    let name = &f.lean;
    let ps: Vec<String> = f
        .params
        .iter()
        .zip(&f.arg_tys)
        .map(|(p, s)| format!("({p} : {s})"))
        .collect();
    let ps = ps.join(" ");
    let args = f.params.join(" ");
    let ty = inst_ty(f);
    let mut o = format!(
        "/-! `{}`: the instances of its equations (`docs/design.md` §2, \"Free-key map patterns\") -/\n",
        f.label
    );
    let mut thms = Vec::new();
    // a recursive definition inlines its matchers: the same text as definitions of their own
    if f.recursive {
        for e in &f.eqns {
            let lhs_len = e.lhs_len;
            let fail = move |k: usize| {
                if k < lhs_len {
                    "none".to_string()
                } else {
                    "some none".to_string()
                }
            };
            let leaf = format!("some (some {})", e.rhs.render_arg());
            let body = render::exec_first(&e.steps, true, &fail, &leaf, 2);
            o.push_str(&format!(
                "/-- The matcher of equation {} in `{}`'s cascade. -/\ndef {name}.eqn{} {ps} : Option (Option {}) :=\n{body}",
                e.n, f.label, e.n, f.result
            ));
        }
    }
    for e in f.eqns.iter().filter(|e| e.matcher != Matcher::CatchAll) {
        let lhs_len = e.lhs_len;
        let fail = move |k: usize| {
            if k < lhs_len {
                "[]".to_string()
            } else {
                "[none]".to_string()
            }
        };
        let leaf = if f.pure {
            format!("[{}]", e.rhs.render())
        } else {
            format!("[some {}]", e.rhs.render_arg())
        };
        let body = render::exec_all(&e.steps, &fail, &leaf, 2);
        o.push_str(&format!(
            "/-- The instances of equation {} of `{}` at the arguments. -/\ndef {name}.inst{} {ps} : List ({ty}) :=\n{body}",
            e.n, f.label, e.n
        ));
    }
    // the groups of one priority, in the cascade's order
    let mut groups: Vec<(i64, Vec<String>)> = Vec::new();
    for e in &f.eqns {
        let part = match e.matcher {
            Matcher::CatchAll => format!("[{}]", e.rhs.render()),
            _ => format!("{name}.inst{} {args}", e.n),
        };
        match groups.last_mut() {
            Some((p, parts)) if *p == e.priority => parts.push(part),
            _ => groups.push((e.priority, vec![part])),
        }
    }
    let mut gl: Vec<String> = groups.iter().map(|(_, ps)| ps.join(" ++ ")).collect();
    if let Some(fb) = &f.fallback {
        gl.push(format!("[{fb}]"));
    }
    o.push_str(&format!(
        "/-- The instances of `{}` at the arguments that K's axioms equate with its value: those of the\nfirst priority group of its equations that has one (one per matching binding of a free-key map\npattern, in the map's order), or the value where no equation applies. -/\ndef {name}.instances {ps} : List ({ty}) :=\n  KPrelude.firstNonempty [{}]\n",
        f.label,
        gl.join(", ")
    ));
    o.push_str(&format!(
        "/-- K's axioms determine `{}` at the arguments: its instances there agree. -/\nabbrev {name}.Agrees {ps} : Prop :=\n  KPrelude.Agree ({name}.instances {args})\n",
        f.label
    ));
    // the matcher of each equation is the first of its instances
    let matcher = |e: &Eqn| match e.matcher {
        Matcher::Rule => format!("{name}.rule{}", e.n),
        _ => format!("{name}.eqn{}", e.n),
    };
    let heads: Vec<&Eqn> = f
        .eqns
        .iter()
        .filter(|e| e.matcher != Matcher::CatchAll)
        .collect();
    for e in &heads {
        let mt = matcher(e);
        o.push_str(&format!(
            "theorem {name}.inst{}_head {ps} :\n    ({name}.inst{} {args}).head? = {mt} {args} := by\n  unfold {name}.inst{} {mt}\n  k2l_inst_head\n",
            e.n, e.n, e.n
        ));
        thms.push(format!("{name}.inst{}_head", e.n));
    }
    // the generated value is the first instance
    let stmt = if f.pure {
        format!("({name}.instances {args}).head? = some ({name} {args})")
    } else {
        format!("{name} {args} = ({name}.instances {args}).head?.join")
    };
    let mut proof = String::new();
    if f.recursive {
        let mut c = String::new();
        let mut pad = 4;
        for e in &f.eqns {
            let p = " ".repeat(pad);
            let h = if e.named {
                format!("he{} : ", e.n)
            } else {
                String::new()
            };
            c.push_str(&format!(
                "{p}match {h}{name}.eqn{} {args} with\n{p}| some r => r\n{p}| none =>\n",
                e.n
            ));
            pad += 2;
        }
        c.push_str(&format!(
            "{}{}",
            " ".repeat(pad),
            f.fallback.as_deref().unwrap_or("none")
        ));
        proof.push_str(&format!("  rw [{name}.eq_def]\n  show (\n{c}) = _\n"));
    } else {
        proof.push_str(&format!("  unfold {name}\n"));
    }
    if !heads.is_empty() {
        let rws: Vec<String> = heads
            .iter()
            .map(|e| format!("← {name}.inst{}_head {args}", e.n))
            .collect();
        proof.push_str(&format!("  rw [{}]\n", rws.join(", ")));
    }
    proof.push_str(&format!("  unfold {name}.instances\n"));
    for e in &heads {
        proof.push_str(&format!("  cases {name}.inst{} {args} <;> try rfl\n", e.n));
    }
    o.push_str(&format!(
        "/-- The value of `{}` is its first instance (`chooseFirst`: the first matching binding in the\nmap's order). -/\ntheorem {name}.eq_instances {ps} :\n    {stmt} := by\n{proof}",
        f.label
    ));
    thms.push(format!("{name}.eq_instances"));
    let use_ = if f.pure {
        format!(
            "  exact Option.some.inj (({name}.eq_instances {args}).symm.trans (KPrelude.Agree.head?_eq h hv))\n"
        )
    } else {
        format!("  exact ({name}.eq_instances {args}).trans (KPrelude.Agree.head?_join_eq h hv)\n")
    };
    o.push_str(&format!(
        "/-- Where K's axioms determine `{}` (its instances agree), the generated value is the value of\nevery instance. -/\ntheorem {name}.eq_of_agrees {ps} (h : {name}.Agrees {args}) {{v : {ty}}}\n    (hv : v ∈ {name}.instances {args}) : {name} {args} = v := by\n{use_}\n",
        f.label
    ));
    thms.push(format!("{name}.eq_of_agrees"));
    (o, thms)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn choose() -> Step {
        Step::MapChoose {
            map: "x0".into(),
            key: "k".into(),
            val: "v".into(),
            rest: "R".into(),
            wf_hyp: "hwf".into(),
            cert: "hc".into(),
            hyp: "h".into(),
        }
    }

    fn eqn(steps: Vec<Step>, lhs_len: usize, rhs: L) -> Eqn {
        Eqn {
            n: 1,
            priority: 50,
            steps,
            lhs_len,
            rhs,
            matcher: Matcher::Rule,
            named: false,
        }
    }

    /// A right-hand side that reads no variable of the chosen binding has one value at every
    /// match; one that reads the value (or a variable a later match binds from it) is not shown
    /// to agree.
    #[test]
    fn reads_no_choice_follows_the_chosen_variables() {
        let destruct = Step::Destruct {
            scrut: "v".into(),
            pat: L::app("SortKItem.inj_Int", vec![L::Var("V".into())]),
            hyp: None,
            refutable: true,
        };
        let cond = Step::Cond {
            cond: L::app(
                "KPrelude.IntHook.lt",
                vec![L::Var("V".into()), L::Raw("0".into())],
            ),
            hyp: "hc0".into(),
        };
        let steps = vec![choose(), destruct, cond];
        assert!(reads_no_choice(&eqn(
            steps.clone(),
            3,
            L::Raw("true".into())
        )));
        assert!(reads_no_choice(&eqn(steps.clone(), 3, L::Var("x1".into()))));
        assert!(!reads_no_choice(&eqn(steps.clone(), 3, L::Var("V".into()))));
        assert!(!reads_no_choice(&eqn(steps, 3, L::Var("R".into()))));
        // a partial call of the right-hand side on the rest reads it
        let bind = Step::Bind {
            expr: L::app("K.f", vec![L::Var("R".into())]),
            var: "r".into(),
            hyp: "hr".into(),
        };
        assert!(!reads_no_choice(&eqn(
            vec![choose(), bind],
            1,
            L::Var("r".into())
        )));
    }

    /// Equations of one priority form one group of `instances`; the cascade's value where none
    /// applies is the last group.
    #[test]
    fn instances_group_equations_by_priority() {
        let f = FreeKeyFn {
            label: "f".into(),
            lean: "K.f".into(),
            params: vec!["x0".into()],
            arg_tys: vec!["SortMap".into()],
            result: "SortInt".into(),
            pure: false,
            recursive: false,
            eqns: vec![
                eqn(vec![choose()], 1, L::Var("x0".into())),
                Eqn {
                    n: 2,
                    ..eqn(vec![], 0, L::Raw("0".into()))
                },
                Eqn {
                    n: 3,
                    priority: 200,
                    ..eqn(vec![], 0, L::Raw("1".into()))
                },
            ],
            fallback: None,
        };
        let (text, thms) = emit(&f);
        assert!(
            text.contains("KPrelude.firstNonempty [K.f.inst1 x0 ++ K.f.inst2 x0, K.f.inst3 x0]"),
            "{text}"
        );
        assert!(
            text.contains("KPrelude.MapHook.chooseAll x0 fun k v =>"),
            "{text}"
        );
        assert_eq!(
            thms,
            [
                "K.f.inst1_head",
                "K.f.inst2_head",
                "K.f.inst3_head",
                "K.f.eq_instances",
                "K.f.eq_of_agrees"
            ]
        );
    }
}
