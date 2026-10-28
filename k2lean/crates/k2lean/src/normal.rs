//! The values of the term family that are K values, modulo the overload axioms (EQ-18).
//!
//! An overload axiom `f(inj(x₁), …) = inj(f'(x₁, …))` (`symbol-overload`) makes the super
//! symbol's term at such arguments the sub symbol's: K's values are in normal form, and the
//! generated functions keep them so (each super symbol has a normalizer `K.f`). The family also
//! holds the node `f(inj(x₁), …)` itself, which is no K value. A statement whose premises say
//! that no pattern of K applies (an `owise` equation's) is about K values, and can be false at
//! such a node, where the definition's arms match the representation: it gets the premise
//! `Term.nf X = true` for each variable of a sort whose values can contain an overloaded node,
//! as a simplification gets `WF` (`design.md` §3).
//!
//! `Term.nf` is structural over the family: a node is in normal form when none of its symbol's
//! overload rules (the normalizer's `rule`s) applies, and its subterms are. The fold lemmas read
//! a value back as the normalizer's application, which the no-match premises are written in.

use crate::funcs::Equation;
use crate::ir::Def;
use crate::lower::{Fns, Lower};
use crate::model::{Coll, Model};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

/// A super symbol that the library normalizes: its normalizer, and the positions of its overload
/// rules in its equations (the normalizer's `rule{i+1}`), those that need a sort without values
/// left out.
struct Overloaded {
    sym: String,
    lean: String,
    rules: Vec<usize>,
}

fn overloaded(
    def: &Def,
    m: &Model,
    fns: &Fns,
    eqs: &BTreeMap<String, Vec<Equation>>,
) -> Vec<Overloaded> {
    let mut out = Vec::new();
    for g in crate::funcs::overload_supers(def) {
        let Some(sig) = fns
            .get(&g)
            .filter(|s| s.lean.starts_with("K.") && !s.partial)
        else {
            continue;
        };
        if !m.ctors.contains_key(&g) {
            continue;
        }
        let rules: Vec<usize> = eqs
            .get(&g)
            .into_iter()
            .flatten()
            .enumerate()
            .filter(|(_, e)| {
                e.uid.starts_with("overload-")
                    && !e
                        .args
                        .iter()
                        .any(|a| crate::rules::absent_sort(a, m).is_some())
            })
            .map(|(i, _)| i)
            .collect();
        if !rules.is_empty() {
            out.push(Overloaded {
                sym: g,
                lean: sig.lean.clone(),
                rules,
            });
        }
    }
    out
}

/// The sorts that own an overloaded constructor the library normalizes.
pub fn sorts(
    def: &Def,
    m: &Model,
    fns: &Fns,
    eqs: &BTreeMap<String, Vec<Equation>>,
) -> BTreeSet<String> {
    overloaded(def, m, fns, eqs)
        .iter()
        .map(|o| m.ctors[&o.sym].sort.clone())
        .collect()
}

/// Whether a value of sort `from` can contain a node of a sort in `to`: through its leaves, its
/// own constructors' arguments and its elements.
pub fn reaches(m: &Model, from: &str, to: &BTreeSet<String>) -> bool {
    let mut seen = BTreeSet::new();
    let mut todo = vec![from.to_string()];
    while let Some(s) = todo.pop() {
        if to.contains(&s) {
            return true;
        }
        if !seen.insert(s.clone()) {
            continue;
        }
        let Some(info) = m.sorts.get(&s) else {
            continue;
        };
        todo.extend(info.leaves.iter().filter(|l| **l != s).cloned());
        todo.extend(info.elems.iter().cloned());
        for c in &info.own {
            if let Some(ci) = m.ctors.get(c) {
                todo.extend(ci.args.iter().cloned());
            }
        }
    }
    false
}

/// The simp lemmas that decide `Term.nf` at a constructor term and fold a value back into a
/// normalizer's application, for the proofs of the statements with `Term.nf` premises.
pub fn lemmas(
    def: &Def,
    m: &Model,
    fns: &Fns,
    eqs: &BTreeMap<String, Vec<Equation>>,
) -> Vec<String> {
    let ov = overloaded(def, m, fns, eqs);
    if ov.is_empty() {
        return Vec::new();
    }
    let shape = crate::terms_arity::shape(m);
    let mut out = vec!["Bool.and_eq_true".to_string(), "Term.nf".to_string()];
    let ks: BTreeSet<usize> = ov.iter().map(|o| m.ctors[&o.sym].args.len()).collect();
    out.extend(ks.iter().map(|k| format!("Term.nfNode{k}")));
    out.extend(shape.colls.iter().map(|(s, _, _)| format!("Term.nfL_{s}")));
    for o in ov.iter().filter(|o| !m.ctors[&o.sym].args.is_empty()) {
        out.push(format!("{}.fold_own", o.lean));
        out.extend(o.rules.iter().map(|i| format!("{}.fold_{}", o.lean, i + 1)));
    }
    out
}

/// `Term.nf` and the fold lemmas, for the end of `Functions.lean`; empty when the library
/// normalizes no overloaded symbol.
pub fn emit(
    def: &Def,
    m: &Model,
    fns: &Fns,
    eqs: &BTreeMap<String, Vec<Equation>>,
) -> Result<String, String> {
    let ov = overloaded(def, m, fns, eqs);
    if ov.is_empty() {
        return Ok(String::new());
    }
    let shape = crate::terms_arity::shape(m);
    let mut o = String::from(
        "/-! Normal forms modulo the overload axioms (`symbol-overload`): K's values are the terms\n\
of the family at which no overload rule applies, at any depth (`Term.nf`). A statement whose\n\
premises say that no pattern of K applies assumes it of its variables (`normal.rs`). -/\n\n",
    );
    // the nodes of each arity: a node is normal when none of its symbol's overload rules applies
    let mut by_k: BTreeMap<usize, Vec<&Overloaded>> = BTreeMap::new();
    for x in &ov {
        by_k.entry(m.ctors[&x.sym].args.len()).or_default().push(x);
    }
    for (k, xs) in &by_k {
        let args: Vec<String> = (0..*k).map(|i| format!("a{i}")).collect();
        let tys: String = (0..*k).map(|i| format!(" → Term (A{k}_{i} s c)")).collect();
        let c = if *k == 0 {
            "C0 s".to_string()
        } else {
            format!("(c : C{k} s)")
        };
        writeln!(o, "/-- Whether a node of arity {k} is in normal form: none of its symbol's overload rules applies. -/").unwrap();
        writeln!(o, "def Term.nfNode{k} : (s : Tag) → {c}{tys} → Bool").unwrap();
        for x in xs {
            let ci = &m.ctors[&x.sym];
            let checks: Vec<String> = x
                .rules
                .iter()
                .map(|i| {
                    let call = std::iter::once(format!("{}.rule{}", x.lean, i + 1))
                        .chain(args.iter().cloned())
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("({call}).isNone")
                })
                .collect();
            let pats: String = args.iter().map(|a| format!(", {a}")).collect();
            writeln!(
                o,
                "  | .«{}», .{}{pats} => {}",
                m.own_ty(&ci.sort)
                    .trim_start_matches('«')
                    .trim_end_matches('»'),
                ci.lean,
                checks.join(" && ")
            )
            .unwrap();
        }
        // another node of this arity, when there is one
        let total: usize = shape
            .enums
            .get(k)
            .map_or(0, |v| v.iter().map(|(_, cs)| cs.len()).sum());
        if total > xs.len() {
            let w: String = (0..*k).map(|_| ", _").collect();
            writeln!(o, "  | _, _{w} => true").unwrap();
        }
        o.push('\n');
    }
    let ty_of = |e: &str| {
        if shape.builtins.contains(e) {
            e.to_string()
        } else {
            format!("Term .«{e}»")
        }
    };
    let elem_nf = |e: &str, x: &str| (!shape.builtins.contains(e)).then(|| format!("Term.nf {x}"));
    writeln!(o, "mutual").unwrap();
    writeln!(
        o,
        "/-- Whether a term is a K value: no overload rule applies at any of its nodes. -/"
    )
    .unwrap();
    writeln!(o, "def Term.nf : {{s : Tag}} → Term s → Bool").unwrap();
    for k in shape.enums.keys() {
        let args: Vec<String> = (0..*k).map(|i| format!("a{i}")).collect();
        let mut parts: Vec<String> = Vec::new();
        let s = if by_k.contains_key(k) {
            parts.push(
                std::iter::once(format!("Term.nfNode{k} s c"))
                    .chain(args.iter().cloned())
                    .collect::<Vec<_>>()
                    .join(" "),
            );
            "s c"
        } else {
            "_ _"
        };
        parts.extend(args.iter().map(|a| format!("Term.nf {a}")));
        let pat: String = args.iter().map(|a| format!(" {a}")).collect();
        writeln!(o, "  | _, @Term.c{k} {s}{pat} => {}", conj(&parts)).unwrap();
    }
    for (s, _, _) in &shape.colls {
        writeln!(o, "  | _, .«coll_{s}» l => Term.nfL_{s} l").unwrap();
    }
    writeln!(o, "  | _, @Term.inj _ _ _ _ a => Term.nf a").unwrap();
    if !shape.builtins.is_empty() {
        writeln!(o, "  | _, _ => true").unwrap();
    }
    writeln!(o, "termination_by structural _ a => a").unwrap();
    for (s, kind, es) in &shape.colls {
        let (ty, pat, parts): (String, &str, Vec<Option<String>>) = match kind {
            Coll::Map => (
                format!("({} × {})", ty_of(&es[0]), ty_of(&es[1])),
                "(k, v)",
                vec![elem_nf(&es[0], "k"), elem_nf(&es[1], "v")],
            ),
            Coll::Set => (
                format!("({} × Unit)", ty_of(&es[0])),
                "(k, ())",
                vec![elem_nf(&es[0], "k")],
            ),
            Coll::List => (
                format!("({})", ty_of(&es[0])),
                "k",
                vec![elem_nf(&es[0], "k")],
            ),
        };
        let mut parts: Vec<String> = parts.into_iter().flatten().collect();
        parts.push(format!("Term.nfL_{s} t"));
        writeln!(o, "def Term.nfL_{s} : List {ty} → Bool").unwrap();
        writeln!(o, "  | [] => true").unwrap();
        writeln!(o, "  | {pat} :: t => {}", conj(&parts)).unwrap();
        writeln!(o, "termination_by structural l => l").unwrap();
    }
    writeln!(o, "end\n").unwrap();
    // the fold lemmas; statements write a constant in its normal form already
    // (`funcs::normalize_consts`), so constants need none
    for x in ov.iter().filter(|x| !m.ctors[&x.sym].args.is_empty()) {
        let sig = &fns[&x.sym];
        let params: Vec<String> = (0..sig.args.len()).map(|i| format!("x{i}")).collect();
        let binders: String = params
            .iter()
            .zip(&sig.args)
            .map(|(p, s)| format!(" ({p} : {s})"))
            .collect();
        let app = |head: String| {
            std::iter::once(head)
                .chain(params.iter().cloned())
                .collect::<Vec<_>>()
                .join(" ")
        };
        let hyps: String = x
            .rules
            .iter()
            .enumerate()
            .map(|(j, i)| {
                format!(
                    " (h{j} : ({}).isNone = true)",
                    app(format!("{}.rule{}", x.lean, i + 1))
                )
            })
            .collect();
        let hs: Vec<String> = (0..x.rules.len()).map(|j| format!("h{j}")).collect();
        let own = crate::funcs::anywhere_ctor(m, &x.sym, &params).render();
        writeln!(
            o,
            "/-- A node of `{}` in normal form is its normalizer's value. -/\ntheorem {}.fold_own{binders}{hyps} :\n    {own} = {} := by\n  simp only [Option.isNone_iff_eq_none] at {}\n  unfold {}\n  simp only [{}]\n",
            crate::names::demangle(&x.sym),
            x.lean,
            app(x.lean.clone()),
            hs.join(" "),
            x.lean,
            hs.join(", ")
        )
        .unwrap();
        for i in &x.rules {
            let e = &eqs[&x.sym][*i];
            let mut lw = Lower::new(m, fns, &[]);
            let mut vars = BTreeMap::new();
            for a in &e.args {
                crate::eqns::vars_of(a, &mut vars);
            }
            let binders = crate::eqns::bind_vars(&mut lw, &vars, "")?;
            let mut args = Vec::new();
            for (a, s) in e.args.iter().zip(&sig.args) {
                args.push(lw.expr(a, s)?.render_arg());
            }
            let rhs = lw.expr(&e.rhs, &sig.result)?;
            if !lw.steps.is_empty() {
                return Err(format!("overload rule of {}: a partial term", x.sym));
            }
            let bs: String = binders
                .iter()
                .map(|(n, t)| format!(" ({n} : {t})"))
                .collect();
            let rules: Vec<String> = x
                .rules
                .iter()
                .map(|r| format!("{}.rule{}", x.lean, r + 1))
                .collect();
            writeln!(
                o,
                "/-- Overload rule {} of `{}`, from the value back to K's term. -/\ntheorem {}.fold_{}{bs} :\n    {} = {} {} := by\n  first\n  | rfl\n  | simp [{}, {}]\n",
                i + 1,
                crate::names::demangle(&x.sym),
                x.lean,
                i + 1,
                rhs.render(),
                x.lean,
                args.join(" "),
                x.lean,
                rules.join(", ")
            )
            .unwrap();
        }
    }
    Ok(o)
}

/// `a && (b && …)`, `true` when empty.
fn conj(parts: &[String]) -> String {
    let mut acc = parts.last().cloned().unwrap_or_else(|| "true".into());
    for p in parts.iter().rev().skip(1) {
        acc = format!("{p} && ({acc})");
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::funcs::tests::{fixture, generated};

    #[test]
    fn an_owise_statement_over_an_overloaded_sort_assumes_k_values() {
        // `hd(_) => 0 [owise]` after `hd(_:Id, _) => -1`: at the node `_,_Exps(inj(x), inj(xs))`,
        // which is no K value, the definition's arm gives -1 and no pattern of K applies
        let def = fixture("overload");
        let (m, g) = generated(&def);
        assert!(
            g.lean.contains("def Term.nf : {s : Tag} → Term s → Bool"),
            "{}",
            g.lean
        );
        assert!(
            g.lean.contains(".fold_own (x0 : SortExp) (x1 : SortExps)"),
            "{}",
            g.lean
        );
        let eqs = crate::funcs::equations_modulo_overloads(&def, &m);
        let ss = sorts(&def, &m, &g.fns, &eqs);
        assert!(reaches(&m, "SortExps", &ss) && !reaches(&m, "SortInt", &ss));
        let st = crate::eqns::equation_theorems(&def, &m, &g.fns, &eqs);
        let of = |n: &str| st.iter().find(|s| s.name == n).unwrap();
        let hd3 = of("Eqn.hd_3");
        assert!(
            hd3.statement.contains("(hnf0 : Term.nf Gen0 = true)"),
            "{}",
            hd3.statement
        );
        assert!(hd3.nf.iter().any(|l| l == "Term.nf"));
        // without no-match premises an equation holds at every carrier value: no premise
        let hd2 = of("Eqn.hd_2");
        assert!(
            !hd2.statement.contains("hnf") && hd2.nf.is_empty(),
            "{}",
            hd2.statement
        );
    }
}
