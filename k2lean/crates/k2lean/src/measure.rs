//! The generated step measure (`gen --measure NAME@CELL`, `{ns}/Measure.lean`; `docs/direction.md`
//! §5, `docs/design.md` §3.10).
//!
//! In a finite execution "every run ends" is termination of `Step`, and a measure that every step
//! lowers proves it. The author writes the measure in K, a function from a cell to `Int`, and
//! states the facts it needs about the functions it calls as K simplification rules, which `gen`
//! states as obligations like any other (`Simp.s_…`) and never assumes. This module states, per
//! rule `r`, that the rule's step lowers the measure: `Step.Rel.r (KPrelude.Measure.Lower
//! Measure.value)`, its value defined at both ends, nonnegative at the target and below its value at
//! the source. Each case is proved by `k2l_measure` with the measure's unfolding set (its projections
//! to the cell, and the proved equations of every function it calls) and the proved author lemmas
//! about those functions, or, for the cases listed in `open-measure-cases.txt`, by the hand-written
//! `Measure.hand.r` of `{ns}/MeasureHand.lean`. The measure's definition (its projections and value)
//! is `{ns}/MeasureDefs.lean`, which both import. `Measure.lower` gathers the cases (`Step.rel_of`) and
//! `Measure.terminates` is termination from every configuration (`KPrelude.Measure.terminates`).

use crate::eqns::Stated;
use crate::invariants::{Ctx, Spec, closure, find_cell, resolve};
use crate::names;
use std::collections::BTreeSet;

/// The files to write.
pub struct Out {
    pub defs: String,
    pub theorems: String,
    pub open_list: String,
    /// The skeleton of the hand module, when it does not exist and some case is open.
    pub hand_skeleton: Option<String>,
}

/// `Measure.lean` for the measure `spec` (`NAME@CELL`), with the cases of `open_in` by hand.
pub fn emit(
    cx: &Ctx,
    spec: &Spec,
    stated: &[Stated],
    open_in: &BTreeSet<String>,
    hand_exists: bool,
) -> Result<Out, String> {
    let (m, ns, top) = (cx.m, cx.ns, cx.top);
    let sym = resolve(cx.def, &spec.name).map_err(|e| e.replace("--invariant", "--measure"))?;
    let sig = cx.fns.get(&sym).ok_or_else(|| {
        format!(
            "--measure {}: {} was not generated",
            spec.name,
            names::demangle(&sym)
        )
    })?;
    if sig.result != "SortInt" || sig.args.len() != 1 {
        return Err(format!(
            "--measure {}: {} must take one argument and return Int",
            spec.name,
            names::demangle(&sym)
        ));
    }
    let arg = &sig.args[0];
    let cell = spec
        .cell
        .as_ref()
        .ok_or_else(|| format!("--measure {}: name the cell it reads (NAME@CELL)", spec.name))?;
    let path = find_cell(m, top, cell)?;
    if !path.colls.is_empty() {
        return Err(format!(
            "--measure {}@{cell}: <{cell}> is inside a cell collection; a measure reads one cell of the configuration",
            spec.name
        ));
    }
    // the function takes the cell itself, or the one value the cell holds
    let content = path.cell_args.len() == 1 && path.cell_args[0] == *arg;
    if !content && path.cell_sort != *arg {
        return Err(format!(
            "--measure {}@{cell}: {} takes a {arg}, but <{cell}> is a {} holding {:?}",
            spec.name,
            names::demangle(&sym),
            path.cell_sort,
            path.cell_args
        ));
    }

    // the projections from the configuration to the cell, and the measure's value
    let mut defs = String::new();
    let mut unfold: Vec<String> = Vec::new();
    let mut read = "c".to_string();
    let mut proj = |name: String, sort: &str, child: &str, lean: &str, arity: usize, index: usize, doc: String, read: &mut String| {
        let pats: Vec<&str> = (0..arity).map(|i| if i == index { "x" } else { "_" }).collect();
        defs.push_str(&format!(
            "/-- {doc} -/\ndef {name} : {sort} → {child}\n  | {lean} {} => x\n\n",
            pats.join(" ")
        ));
        *read = format!("{name} {}", paren_read(read));
        unfold.push(name);
    };
    for lv in &path.levels {
        proj(
            format!("Measure.cell_{}", lv.name),
            &lv.sort,
            &lv.child,
            &lv.lean,
            lv.arity,
            lv.index,
            format!("The `<{}>` cell of a `{}`.", lv.name, lv.sort),
            &mut read,
        );
    }
    if content {
        proj(
            format!("Measure.content_{cell}"),
            &path.cell_sort,
            arg,
            &path.cell_lean,
            1,
            0,
            format!("What a `<{cell}>` cell holds."),
            &mut read,
        );
    }
    let call = format!("{} {}", sig.lean, paren_read(&read));
    let value = if sig.partial {
        call
    } else {
        format!("some ({call})")
    };
    defs.push_str(&format!(
        "/-- The measure `{}` of a configuration, at its `<{cell}>` cell. -/\ndef Measure.value (c : {top}) : Option Int :=\n  {value}\n\n",
        names::demangle(&sym)
    ));
    unfold.insert(0, "Measure.value".into());

    // the proved equations of every function the measure calls, and the author's proved lemmas
    // about them (a simplification rule whose statement applies one of them)
    let proved = |n: &String| cx.stated.contains(n) && !cx.open_eqns.contains(n);
    let mut called: Vec<String> = Vec::new();
    for g in closure(cx.def, cx.eqs, &sym) {
        let Some(gs) = cx.fns.get(&g) else { continue };
        if !gs.lean.starts_with("K.") {
            continue;
        }
        called.push(gs.lean.clone());
        let n = cx.eqs.get(&g).map_or(0, |es| es.len());
        for i in 0..n {
            let e = format!(
                "Eqn.{}",
                names::ident(&format!("{}_{}", names::demangle(&g), i + 1))
            );
            if proved(&e) {
                unfold.push(e);
            }
        }
    }
    let lemmas: Vec<String> = stated
        .iter()
        .filter(|s| (s.name.starts_with("Simp.") || s.name.starts_with("Lemma.")) && proved(&s.name))
        .filter(|s| called.iter().any(|f| s.statement.contains(f.as_str())))
        .map(|s| s.name.clone())
        .collect();

    // the cases
    let open: BTreeSet<String> = cx
        .ctors
        .iter()
        .filter(|c| open_in.contains(&c.lean))
        .map(|c| c.lean.clone())
        .collect();
    let lower = "(KPrelude.Measure.Lower Measure.value)";
    let d = format!(
        "import {ns}.Equations\nimport {ns}.Preserves\nimport KPrelude.Measure\n\n\
/-! Generated by k2lean (`gen --measure {}@{cell}`); do not edit. The measure's value at a\n\
configuration; `Measure.lean` states that every rule lowers it. -/\n\n\
namespace {ns}\n\nopen KPrelude\n\n{defs}end {ns}\n",
        spec.name
    );
    let mut t = format!("import {ns}.MeasureDefs\n");
    if !open.is_empty() {
        t.push_str(&format!("import {ns}.MeasureHand\n"));
    }
    t.push('\n');
    t.push_str(&format!(
        "/-! Generated by k2lean (`gen --measure {}@{cell}`); do not edit.\n\n\
Every rule of `{ns}` lowers the measure `{}` (`Measure.value`): its value is defined at both ends of\n\
the step, nonnegative at the target and below its value at the source\n\
(`Step.Rel.r (KPrelude.Measure.Lower Measure.value)`). Each case is proved by `k2l_measure` with the\n\
measure's unfolding set and the author's proved lemmas about the functions it calls (K\n\
simplification rules), or, for the cases listed in `open-measure-cases.txt`, by the hand-written\n\
`Measure.hand.r` of `MeasureHand.lean`. So no infinite run starts anywhere\n\
(`Measure.terminates`). -/\n\n\
set_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n\n\
/-- `k2l_measure` with the measure's unfolding set and the author's lemmas. -/\n\
local macro \"k2l_meas\" : tactic => `(tactic| k2l_measure [{}] [{}])\n\nnamespace Measure.case\n\n",
        spec.name,
        names::demangle(&sym),
        unfold.join(", "),
        lemmas.join(", ")
    ));
    let mut n_auto = 0;
    for c in cx.ctors {
        if open.contains(&c.lean) {
            t.push_str(&format!(
                "/-- Rule {} lowers the measure: the hand proof. -/\ntheorem {} : Step.Rel.{} {lower} := Measure.hand.{}\n\n",
                c.doc, c.lean, c.lean, c.lean
            ));
        } else {
            n_auto += 1;
            t.push_str(&format!(
                "/-- Rule {} lowers the measure. -/\ntheorem {} : Step.Rel.{} {lower} := by k2l_meas\n\n",
                c.doc, c.lean, c.lean
            ));
        }
    }
    t.push_str("end Measure.case\n\n");
    t.push_str(&format!(
        "/-- Every step lowers the measure ({} rules: {n_auto} by `k2l_measure`, {} by hand). -/\n\
theorem Measure.lower {{c c' : {top}}} (h : Step c c') : KPrelude.Measure.Lower Measure.value c c' :=\n  Step.rel_of\n",
        cx.ctors.len(),
        cx.ctors.len() - n_auto
    ));
    for c in cx.ctors {
        t.push_str(&format!("    Measure.case.{}\n", c.lean));
    }
    t.push_str(&format!(
        "    h\n\n/-- No infinite run starts anywhere: every run ends. -/\n\
theorem Measure.terminates (c : {top}) : Paths.Terminates Step c :=\n  KPrelude.Measure.terminates Measure.value Measure.lower c\n\n\
#k2l_assert_axioms Measure.lower Measure.terminates\n\nend {ns}\n"
    ));

    // open-measure-cases.txt and the hand module's skeleton
    let mut ol = format!(
        "# Cases of the measure `{ns}.Measure.value` that `k2l_measure` does not close (`k2lean gen --measure`).\n\
# `k2lean open-from-log {ns}/Measure.lean BUILD.log open-measure-cases.txt` adds the cases whose proof failed.\n\
# Each line: the case, its statement, the rule's source position. Prove each in {ns}/MeasureHand.lean as\n\
# `theorem Measure.hand.r : Step.Rel.r (KPrelude.Measure.Lower Measure.value)` (namespace `{ns}`; `Step.Rel.r`\n\
# is stated in {ns}/Preserves.lean, `Measure.value` in {ns}/MeasureDefs.lean).\n"
    );
    let mut skel = String::new();
    for c in cx.ctors {
        if open.contains(&c.lean) {
            ol.push_str(&format!(
                "{} | Step.Rel.{} {lower} | {}\n",
                c.lean,
                c.lean,
                c.loc.clone().unwrap_or_else(|| "no position".into())
            ));
            skel.push_str(&format!(
                "-- Rule {}:\n-- theorem Measure.hand.{} : Step.Rel.{} {lower} := by\n--   …\n\n",
                c.doc, c.lean, c.lean
            ));
        }
    }
    let hand_skeleton = (!open.is_empty() && !hand_exists).then(|| {
        format!(
            "import {ns}.MeasureDefs\n\n\
/-! Hand-written proofs of the cases of the measure listed in `open-measure-cases.txt`.\n\n\
`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each case\n\
below as the theorem it names (uncomment and complete it); `Measure.lean` uses them by name. The\n\
generated proofs use `k2l_measure [{}] [{}]`. -/\n\n\
namespace {ns}\n\nopen KPrelude\n\n{skel}end {ns}\n",
            unfold.join(", "),
            lemmas.join(", ")
        )
    });
    Ok(Out {
        defs: d,
        theorems: t,
        open_list: ol,
        hand_skeleton,
    })
}

/// `e` parenthesized when it is an application.
fn paren_read(e: &str) -> String {
    if e.contains(' ') {
        format!("({e})")
    } else {
        e.to_string()
    }
}
