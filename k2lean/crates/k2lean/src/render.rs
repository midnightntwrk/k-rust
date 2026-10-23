//! Rendering lowered match steps: as executable Lean (plain or proof-carrying), and as the
//! binders, index and hypotheses of a relation constructor.

use crate::lower::{L, Step};
use std::collections::{BTreeMap, BTreeSet};

/// The relational reading of a step sequence that starts by destructing `top`.
pub struct Rel {
    /// Constructor binders: (name, type), in introduction order.
    pub binders: Vec<(String, String)>,
    /// The index (the matched value), after substitution.
    pub index: L,
    /// Hypotheses: (name, proposition).
    pub hyps: Vec<(String, String)>,
    /// The substitution (destructed variables and merged duplicates).
    pub subst: BTreeMap<String, L>,
}

/// The variables a step introduces, in order.
fn introduced(s: &Step) -> Vec<String> {
    match s {
        Step::Destruct { pat, .. } => {
            let mut v = Vec::new();
            pat_vars_ordered(pat, &mut v);
            v
        }
        Step::Bind { var, .. } => vec![var.clone()],
        Step::MapElem { val, rest, .. } => vec![val.clone(), rest.clone()],
        Step::MapChoose { key, val, rest, .. } => vec![key.clone(), val.clone(), rest.clone()],
        Step::ListElem { head, tail, .. } => vec![head.clone(), tail.clone()],
        _ => vec![],
    }
}

fn pat_vars_ordered(l: &L, out: &mut Vec<String>) {
    match l {
        L::Var(v) => out.push(v.clone()),
        L::App(_, args) => args.iter().for_each(|a| pat_vars_ordered(a, out)),
        L::Raw(_) => {}
    }
}

pub fn relation(
    steps: &[Step],
    top: &str,
    ty: &BTreeMap<String, String>,
    extra_vars: &[String],
) -> Rel {
    let mut subst = BTreeMap::new();
    for s in steps {
        match s {
            Step::Destruct { scrut, pat, .. } => {
                subst.insert(scrut.clone(), pat.clone());
            }
            Step::EqVar { a, b, .. } => {
                subst.insert(b.clone(), L::Var(a.clone()));
            }
            _ => {}
        }
    }
    let mut binders = Vec::new();
    let mut seen = BTreeSet::new();
    for v in steps
        .iter()
        .flat_map(introduced)
        .chain(extra_vars.iter().cloned())
    {
        if subst.contains_key(&v) || !seen.insert(v.clone()) {
            continue;
        }
        let t = ty
            .get(&v)
            .cloned()
            .unwrap_or_else(|| panic!("no type for {v}"));
        binders.push((v, t));
    }
    let mut hyps = Vec::new();
    for s in steps {
        match s {
            Step::Bind { expr, var, hyp } => hyps.push((
                hyp.clone(),
                format!(
                    "{} = some {}",
                    expr.subst(&subst).render(),
                    L::Var(var.clone()).subst(&subst).render_arg()
                ),
            )),
            Step::Cond { cond, hyp } => hyps.push((
                hyp.clone(),
                format!("{} = true", cond.subst(&subst).render()),
            )),
            Step::CondEq { lhs, rhs, hyp } => hyps.push((
                hyp.clone(),
                format!(
                    "{} = {}",
                    lhs.subst(&subst).render(),
                    rhs.subst(&subst).render()
                ),
            )),
            Step::MapElem {
                map,
                key,
                val,
                rest,
                hyp,
                ..
            } => hyps.push((
                hyp.clone(),
                format!(
                    "KPrelude.MapHook.concat (KPrelude.MapHook.element {} {}) {} = some {}",
                    key.subst(&subst).render_arg(),
                    L::Var(val.clone()).subst(&subst).render_arg(),
                    L::Var(rest.clone()).subst(&subst).render_arg(),
                    L::Var(map.clone()).subst(&subst).render_arg()
                ),
            )),
            Step::MapChoose {
                map,
                key,
                val,
                rest,
                hyp,
                ..
            } => hyps.push((
                hyp.clone(),
                format!(
                    "KPrelude.MapHook.concat (KPrelude.MapHook.element {} {}) {} = some {}",
                    L::Var(key.clone()).subst(&subst).render_arg(),
                    L::Var(val.clone()).subst(&subst).render_arg(),
                    L::Var(rest.clone()).subst(&subst).render_arg(),
                    L::Var(map.clone()).subst(&subst).render_arg()
                ),
            )),
            Step::ListElem {
                list,
                head,
                tail,
                front,
                hyp,
            } => {
                let (h, t) = (
                    L::Var(head.clone()).subst(&subst).render_arg(),
                    L::Var(tail.clone()).subst(&subst).render_arg(),
                );
                let cat = if *front {
                    format!("KPrelude.ListHook.concat (KPrelude.ListHook.element {h}) {t}")
                } else {
                    format!("KPrelude.ListHook.concat {t} (KPrelude.ListHook.element {h})")
                };
                hyps.push((
                    hyp.clone(),
                    format!(
                        "{cat} = {}",
                        L::Var(list.clone()).subst(&subst).render_arg()
                    ),
                ))
            }
            _ => {}
        }
    }
    let index = L::Var(top.to_string()).subst(&subst);
    Rel {
        binders,
        index,
        hyps,
        subst,
    }
}

/// The proof term of a relation hypothesis, from the executable matcher's hypotheses.
fn hyp_proof(s: &Step) -> Option<String> {
    match s {
        Step::Bind { hyp, .. } | Step::Cond { hyp, .. } | Step::CondEq { hyp, .. } => {
            Some(hyp.clone())
        }
        Step::MapElem {
            wf_hyp, lookup_hyp, ..
        } => Some(format!(
            "(KPrelude.MapHook.concat_element_remove ((KPrelude.MapHook.wfb_iff _).1 {wf_hyp}) {lookup_hyp})"
        )),
        Step::MapChoose { cert, .. } => Some(cert.clone()),
        Step::ListElem {
            hyp, front: true, ..
        } => Some(format!(
            "(KPrelude.ListHook.concat_element_of_uncons {hyp})"
        )),
        Step::ListElem {
            hyp, front: false, ..
        } => Some(format!(
            "(KPrelude.ListHook.concat_element_of_unsnoc {hyp})"
        )),
        _ => None,
    }
}

/// In the steps after the top `match` (which generalizes `top` without naming an equation),
/// the top variable stands for the matched pattern. A call that reads the whole configuration
/// (`getTxData(TXID, C)` with `C` the top cell) must name the pattern, which the relation states:
/// inside the branch, `top` is still the matcher's argument, not the pattern, so a hypothesis
/// about it would not have the relation's type.
pub fn inline_top(steps: &mut [Step], rhs: &mut L, top: &str) {
    let pat = match steps.first() {
        Some(Step::Destruct {
            scrut,
            pat,
            hyp: None,
            ..
        }) if scrut == top => pat.clone(),
        _ => return,
    };
    let s: BTreeMap<String, L> = [(top.to_string(), pat)].into_iter().collect();
    for st in steps.iter_mut().skip(1) {
        match st {
            Step::Bind { expr, .. } => *expr = expr.subst(&s),
            Step::Cond { cond, .. } => *cond = cond.subst(&s),
            Step::CondEq { lhs, rhs, .. } => {
                *lhs = lhs.subst(&s);
                *rhs = rhs.subst(&s);
            }
            Step::MapElem { key, .. } => *key = key.subst(&s),
            _ => {}
        }
    }
    *rhs = rhs.subst(&s);
}

/// A certificate `by subst …; exact Ctor binders… hyps…` for the relation of `steps`.
pub fn certificate(ctor: &str, steps: &[Step], rel: &Rel) -> String {
    let mut tac = String::from("by ");
    // a variable is eliminated once: a nonlinear pattern variable (`EqVar b = a`) that is then
    // destructed has no `b` left for its `hd : b = pat` (that hypothesis is then about `a`'s value)
    let mut gone: BTreeSet<&str> = BTreeSet::new();
    for s in steps {
        match s {
            Step::Destruct {
                scrut,
                hyp: Some(_),
                ..
            }
            | Step::EqVar { b: scrut, .. }
                if gone.insert(scrut.as_str()) =>
            {
                tac.push_str(&format!("subst {scrut}; "));
            }
            _ => {}
        }
    }
    let mut args: Vec<String> = rel.binders.iter().map(|(b, _)| b.clone()).collect();
    args.extend(steps.iter().filter_map(hyp_proof));
    tac.push_str(&format!("exact {ctor} {}", args.join(" ")));
    tac
}

/// Render the executable matcher. `fail(i)` is the code for a failure at step `i`, `leaf` the
/// code when every step succeeded. With `certified`, every test names its hypothesis.
pub fn exec(
    steps: &[Step],
    certified: bool,
    fail: &dyn Fn(usize) -> String,
    leaf: &str,
    indent: usize,
) -> String {
    let mut out = String::new();
    render_from(steps, 0, certified, fail, leaf, indent, &mut out);
    out
}

fn pad(n: usize) -> String {
    " ".repeat(n)
}

fn render_from(
    steps: &[Step],
    i: usize,
    cert: bool,
    fail: &dyn Fn(usize) -> String,
    leaf: &str,
    ind: usize,
    out: &mut String,
) {
    let p = pad(ind);
    if i == steps.len() {
        out.push_str(&format!("{p}{leaf}\n"));
        return;
    }
    let h = |name: &str| {
        if cert {
            format!("{name} : ")
        } else {
            String::new()
        }
    };
    match &steps[i] {
        Step::Destruct {
            scrut,
            pat,
            hyp,
            refutable,
        } => {
            let hh = match hyp {
                Some(n) => h(n),
                None => String::new(),
            };
            out.push_str(&format!(
                "{p}match {hh}{scrut} with\n{p}| {} =>\n",
                pat.render()
            ));
            render_from(steps, i + 1, cert, fail, leaf, ind + 2, out);
            if *refutable {
                out.push_str(&format!("{p}| _ => {}\n", fail(i)));
            }
        }
        Step::Bind { expr, var, hyp } => {
            out.push_str(&format!(
                "{p}match {}{} with\n{p}| some {var} =>\n",
                h(hyp),
                expr.render()
            ));
            render_from(steps, i + 1, cert, fail, leaf, ind + 2, out);
            out.push_str(&format!("{p}| none => {}\n", fail(i)));
        }
        Step::Cond { cond, hyp } => {
            out.push_str(&format!("{p}if {}{} = true then\n", h(hyp), cond.render()));
            render_from(steps, i + 1, cert, fail, leaf, ind + 2, out);
            out.push_str(&format!("{p}else {}\n", fail(i)));
        }
        Step::CondEq { lhs, rhs, hyp } => {
            out.push_str(&format!(
                "{p}if {}{} = {} then\n",
                h(hyp),
                lhs.render(),
                rhs.render()
            ));
            render_from(steps, i + 1, cert, fail, leaf, ind + 2, out);
            out.push_str(&format!("{p}else {}\n", fail(i)));
        }
        Step::EqVar { a, b, hyp } => {
            out.push_str(&format!("{p}if {}{b} = {a} then\n", h(hyp)));
            render_from(steps, i + 1, cert, fail, leaf, ind + 2, out);
            out.push_str(&format!("{p}else {}\n", fail(i)));
        }
        Step::MapElem {
            map,
            key,
            val,
            rest,
            wf_hyp,
            lookup_hyp,
            ..
        } => {
            out.push_str(&format!(
                "{p}if {}KPrelude.MapHook.wfb {map} = true then\n",
                h(wf_hyp)
            ));
            out.push_str(&format!(
                "{p}  match {}KPrelude.MapHook.lookup {map} {} with\n{p}  | some {val} =>\n",
                h(lookup_hyp),
                key.render_arg()
            ));
            out.push_str(&format!(
                "{p}    let {rest} := KPrelude.MapHook.remove {map} {}\n",
                key.render_arg()
            ));
            render_from(steps, i + 1, cert, fail, leaf, ind + 4, out);
            out.push_str(&format!("{p}  | none => {}\n", fail(i)));
            out.push_str(&format!("{p}else {}\n", fail(i)));
        }
        Step::MapChoose {
            map,
            key,
            val,
            rest,
            wf_hyp,
            cert: hc,
            ..
        } => {
            assert!(
                cert,
                "a free-key map pattern needs the certified, list-valued matcher"
            );
            out.push_str(&format!(
                "{p}if {wf_hyp} : KPrelude.MapHook.wfb {map} = true then\n"
            ));
            out.push_str(&format!(
                "{p}  KPrelude.MapHook.choose {map} ((KPrelude.MapHook.wfb_iff _).1 {wf_hyp}) fun {key} {val} {hc} =>\n"
            ));
            out.push_str(&format!(
                "{p}    let {rest} := KPrelude.MapHook.remove {map} {key}\n"
            ));
            render_from(steps, i + 1, cert, fail, leaf, ind + 4, out);
            out.push_str(&format!("{p}else {}\n", fail(i)));
        }
        Step::ListElem {
            list,
            head,
            tail,
            front,
            hyp,
        } => {
            let (f, pat) = if *front {
                ("uncons", format!("({head}, {tail})"))
            } else {
                ("unsnoc", format!("({tail}, {head})"))
            };
            out.push_str(&format!(
                "{p}match {}KPrelude.ListHook.{f} {list} with\n{p}| some {pat} =>\n",
                h(hyp)
            ));
            render_from(steps, i + 1, cert, fail, leaf, ind + 2, out);
            out.push_str(&format!("{p}| none => {}\n", fail(i)));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rel() -> Rel {
        Rel {
            binders: vec![],
            index: L::Var("c".into()),
            hyps: vec![],
            subst: BTreeMap::new(),
        }
    }

    /// A nonlinear pattern variable that is then destructed is eliminated once: after
    /// `subst y` (from `y = x`), the destruct's hypothesis is about `x`, and `y` is gone.
    #[test]
    fn certificate_substitutes_each_variable_once() {
        let steps = vec![
            Step::EqVar {
                a: "x".into(),
                b: "y".into(),
                hyp: "he".into(),
            },
            Step::Destruct {
                scrut: "y".into(),
                pat: L::app("C", vec![L::Var("z".into())]),
                hyp: Some("hd".into()),
                refutable: true,
            },
        ];
        let c = certificate("R", &steps, &rel());
        assert_eq!(c.matches("subst y;").count(), 1, "{c}");
    }

    /// After the top `match` without a named equation, the top variable is the matched pattern
    /// in the later steps and the right-hand side.
    #[test]
    fn inline_top_names_the_pattern() {
        let pat = L::app("T", vec![L::Var("a".into())]);
        let mut steps = vec![
            Step::Destruct {
                scrut: "c".into(),
                pat: pat.clone(),
                hyp: None,
                refutable: false,
            },
            Step::Bind {
                expr: L::app("f", vec![L::Var("c".into())]),
                var: "r".into(),
                hyp: "hr".into(),
            },
        ];
        let mut rhs = L::app("g", vec![L::Var("c".into()), L::Var("r".into())]);
        inline_top(&mut steps, &mut rhs, "c");
        let Step::Bind { expr, .. } = &steps[1] else {
            panic!()
        };
        assert_eq!(expr.render(), "f (T a)");
        assert_eq!(rhs.render(), "g (T a) r");
    }
}
