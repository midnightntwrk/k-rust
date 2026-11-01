//! The generated step measure (`gen --measure NAME@CELL`, `{ns}/Measure.lean`; `docs/direction.md`
//! §5, `docs/design.md` §3.10).
//!
//! In a finite execution "every run ends" is termination of `Step`, and a measure that every step
//! lowers proves it. The author writes the measure in K, a function from a cell to `Int`, and
//! states the facts it needs about the functions it calls as K simplification rules, which `gen`
//! states as obligations like any other (`Simp.s_…`) and never assumes. This module states, per
//! rule `r`, that the rule's step lowers the measure: `Step.Rel.r (KPrelude.Measure.Lower
//! Measure.value)`, where its value is defined at the source, defined at the target, nonnegative
//! there and below its value at the source. Each case is proved by `k2l_measure` with the measure's
//! unfolding set (its projections to the cell, and the proved equations of every function it calls)
//! and the proved author lemmas about those functions, or, for the cases listed in
//! `open-measure-cases.txt`, by the hand-written `Measure.hand.r` of `{ns}/MeasureHand.lean`. The
//! measure's definition (its projections and value) is `{ns}/MeasureDefs.lean`, which both import.
//! `Measure.lower` gathers the cases (`Step.rel_of`) and `Measure.terminates` is termination from
//! every configuration where the measure is defined (`KPrelude.Measure.terminates`).
//!
//! **Why "where it is defined".** A measure over a cell map (the work left in each task) is a fold
//! that adds a weight per binding, and its equations read a binding's key twice: a cell map binds
//! each element under its own id. K's maps hold that by construction; the Lean map type also holds
//! maps that bind an element under another key, and there the fold is undefined. Such a map is no
//! configuration a run reaches, but a rule's instance quantifies over every rest of the map it
//! matches, so "defined at the source" cannot be shown; from a source where it is defined, the
//! step's target is, and definedness is then preserved, which is all termination needs.
//!
//! **Sums over a map.** A function the measure calls that adds a weight per binding of a map
//! (`F(.Map) => 0`, `F((K |-> V) R) => g(K, V) +Int F(R)`, `MapFold`) has one meaning in K whatever
//! order the walk takes, since `+Int` is associative and commutative. For each, `MeasureDefs.lean`
//! states its test of a binding (`Measure.F_test`, what the patterns read twice is equal), its
//! weight (`Measure.F_g`) and `Measure.F_eq`: the fold is defined exactly on a well-formed map whose
//! every binding passes the test with a defined weight, and is then `MapHook.sumOf F_g m`
//! (`KPrelude.MeasureSum`, from the fold's instances). `k2l_measure`'s sum stage reads the fold
//! through it.

use crate::eqns::Stated;
use crate::invariants::{Ctx, FoldKind, MapFold, Spec, closure, find_cell, map_fold_of, resolve};
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

/// `Measure.lean` for the measure `spec` (`NAME@CELL`), with the cases of `open_in` by hand. With
/// `inv` (`--measure-invariant`: the unfolding set of the library's kind 1 `Invariant`), the measure
/// is under the invariant: `Measure.bound` once, and per rule `KPrelude.Measure.Dec Invariant`.
pub fn emit(
    cx: &Ctx,
    spec: &Spec,
    stated: &[Stated],
    open_in: &BTreeSet<String>,
    hand_exists: bool,
    inv: Option<&[String]>,
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
    let cell = spec.cell.as_ref().ok_or_else(|| {
        format!(
            "--measure {}: name the cell it reads (NAME@CELL)",
            spec.name
        )
    })?;
    let path = find_cell(m, top, cell)?;
    if !path.colls.is_empty() {
        return Err(format!(
            "--measure {}@{cell}: <{cell}> is inside a cell collection; a measure is one number for the \
             configuration, so over every element it is a sum over the collection: write it in K over the \
             collection's cell (`F(<c> .Bag </c>) => 0`, `F(<c> <e> ... </e> R </c>) => g(...) +Int F(<c> R </c>)`) \
             and name that cell (`--measure F@c`)",
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
    let mut own: Vec<String> = Vec::new();
    let mut read = "c".to_string();
    let mut proj = |name: String,
                    sort: &str,
                    child: &str,
                    lean: &str,
                    arity: usize,
                    index: usize,
                    doc: String,
                    read: &mut String| {
        let pats: Vec<&str> = (0..arity)
            .map(|i| if i == index { "x" } else { "_" })
            .collect();
        defs.push_str(&format!(
            "/-- {doc} -/\ndef {name} : {sort} → {child}\n  | {lean} {} => x\n\n",
            pats.join(" ")
        ));
        *read = format!("{name} {}", paren_read(read));
        own.push(name.clone());
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
    let mut sums: Vec<MapFold> = Vec::new();
    let mut projections = std::collections::BTreeMap::new();
    let mut proj_names: Vec<String> = Vec::new();
    for g in closure(cx.def, cx.eqs, &sym) {
        let Some(gs) = cx.fns.get(&g) else { continue };
        if !gs.lean.starts_with("K.") {
            continue;
        }
        called.push(gs.lean.clone());
        if cx.recursive.contains(&gs.lean)
            && let Some(f) = map_fold_of(
                cx,
                &g,
                FoldKind::Sum,
                "Measure",
                &mut projections,
                &mut proj_names,
            )
        {
            sums.push(f);
        }
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
        .filter(|s| {
            (s.name.starts_with("Simp.") || s.name.starts_with("Lemma.")) && proved(&s.name)
        })
        .filter(|s| called.iter().any(|f| s.statement.contains(f.as_str())))
        .map(|s| s.name.clone())
        .collect();

    // the sums over a map: their projections (those the measure's path does not define already),
    // tests, weights and reading as sums
    for n in &proj_names {
        if !own.contains(n) {
            defs.push_str(&projections[n]);
            defs.push('\n');
            unfold.push(n.clone());
        }
    }
    let mut sum_eqs: Vec<String> = Vec::new();
    let mut weights: Vec<String> = Vec::new();
    for f in &sums {
        defs.push_str(&sum_defs(f, "Measure"));
        let b = &f.base;
        unfold.push(format!("Measure.{b}_test"));
        unfold.push(format!("Measure.{b}_g"));
        sum_eqs.push(format!("Measure.{b}_eq"));
        weights.push(format!("Measure.{b}_g_nonneg"));
    }
    // each sum's weight nonnegative wherever it is defined, proved once for every rule's case. Not
    // under the invariant: a weight may be nonnegative only where the invariant holds (a task's
    // fuel), and a measure under it needs no bound at a rule's target (`Measure.bound` is once)
    if inv.is_some() {
        weights.clear();
    }
    let mut weight_thms = String::new();
    for f in sums.iter().filter(|_| inv.is_none()) {
        let b = &f.base;
        weight_thms.push_str(&format!(
            "/-- The weight of a binding in `{}` is nonnegative wherever it is defined, so a sum of them is
(`k2l_measure_weight`: the weight unfolded to its rules' matches, bounded by the author's lemmas). -/
theorem Measure.{b}_g_nonneg : ∀ k v a, Measure.{b}_g k v = some a → 0 ≤ a := by
  k2l_measure_weight [{}] [{}]

",
            f.lean,
            unfold.join(", "),
            lemmas.join(", ")
        ));
    }

    // under the invariant, the cases unfold it too (`Invariant`, then its own unfolding set)
    let mut us = unfold.clone();
    if let Some(iu) = inv {
        for n in std::iter::once(&"Invariant".to_string()).chain(iu.iter()) {
            if !us.contains(n) {
                us.push(n.clone());
            }
        }
    }

    // the cases
    let open: BTreeSet<String> = cx
        .ctors
        .iter()
        .filter(|c| open_in.contains(&c.lean))
        .map(|c| c.lean.clone())
        .collect();
    let lower = if inv.is_some() {
        "(KPrelude.Measure.Dec Invariant Measure.value)"
    } else {
        "(KPrelude.Measure.Lower Measure.value)"
    };
    let bound_stmt =
        "∀ c, Invariant c → (Measure.value c).isSome → ∃ v, Measure.value c = some v ∧ 0 ≤ v";
    let bound_open = inv.is_some() && open_in.contains("Measure.bound");
    let d = format!(
        "import {ns}.Equations\nimport {ns}.Preserves\nimport KPrelude.Measure\n\n\
/-! Generated by k2lean (`gen --measure {}@{cell}`); do not edit. The measure's value at a\n\
configuration; `Measure.lean` states that every rule lowers it. -/\n\n\
set_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n\n{defs}end {ns}\n",
        spec.name
    );
    let mut t = format!("import {ns}.MeasureDefs\n");
    if inv.is_some() {
        t.push_str(&format!("import {ns}.Invariants\n"));
    }
    if !open.is_empty() || bound_open {
        t.push_str(&format!("import {ns}.MeasureHand\n"));
    }
    t.push('\n');
    if inv.is_some() {
        t.push_str(&format!(
            "/-! Generated by k2lean (`gen --measure {}@{cell} --measure-invariant`); do not edit.\n\n\
Every rule of `{ns}` lowers the measure `{}` (`Measure.value`) under the invariant: where `Invariant`\n\
holds at the source of a step and the measure is defined there, it is defined at the target and\n\
below its value at the source (`Step.Rel.r (KPrelude.Measure.Dec Invariant Measure.value)`); and\n\
where `Invariant` holds, the measure is nonnegative where it is defined (`Measure.bound`, once).\n\
Each is proved by `k2l_measure` with the measure's and the invariant's unfolding sets, the author's\n\
proved lemmas about the functions it calls (K simplification rules) and the measure's sums over a\n\
map, or, for those listed in `open-measure-cases.txt`, by the hand-written `Measure.hand.r` of\n\
`MeasureHand.lean`. So no infinite run starts where the invariant holds and the measure is defined\n\
(`Measure.terminates`, by `Invariant.preserved`). -/\n\n\
set_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n\n\
/-- `k2l_measure` with the measure's and the invariant's unfolding sets, the author's lemmas and the\n\
measure's sums (declared before it: a quotation resolves its global names where it is written). -/\n\
local macro \"k2l_meas\" : tactic => `(tactic| k2l_measure [{}] [{}] [{}] [])\n\n",
            spec.name,
            names::demangle(&sym),
            us.join(", "),
            lemmas.join(", "),
            sum_eqs.join(", "),
        ));
        if bound_open {
            t.push_str(&format!(
                "/-- Where the invariant holds, the measure is nonnegative where it is defined: the hand proof. -/\n\
theorem Measure.bound : {bound_stmt} := Measure.hand.bound\n\n"
            ));
        } else {
            t.push_str(&format!(
                "/-- Where the invariant holds, the measure is nonnegative where it is defined. -/\n\
theorem Measure.bound : {bound_stmt} := by k2l_meas\n\n"
            ));
        }
        t.push_str("namespace Measure.case\n\n");
    } else {
        t.push_str(&format!(
        "/-! Generated by k2lean (`gen --measure {}@{cell}`); do not edit.\n\n\
Every rule of `{ns}` lowers the measure `{}` (`Measure.value`): where its value is defined at the\n\
source of a step, it is defined at the target, nonnegative there and below its value at the source\n\
(`Step.Rel.r (KPrelude.Measure.Lower Measure.value)`). Each case is proved by `k2l_measure` with the\n\
measure's unfolding set, the author's proved lemmas about the functions it calls (K simplification\n\
rules) and the measure's sums over a map, or, for the cases listed in `open-measure-cases.txt`, by\n\
the hand-written `Measure.hand.r` of `MeasureHand.lean`. So no infinite run starts where the measure\n\
is defined (`Measure.terminates`). -/\n\n\
set_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n\n{weight_thms}\
/-- `k2l_measure` with the measure's unfolding set, the author's lemmas, its sums and their weights\n\
(declared before it: a quotation resolves its global names where it is written). -/\n\
local macro \"k2l_meas\" : tactic => `(tactic| k2l_measure [{}] [{}] [{}] [{}])\n\nnamespace Measure.case\n\n",
        spec.name,
        names::demangle(&sym),
        unfold.join(", "),
        lemmas.join(", "),
        sum_eqs.join(", "),
        weights.join(", ")
    ));
    }
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
        "/-- Every step lowers the measure{} ({} rules: {n_auto} by `k2l_measure`, {} by hand). -/\n\
theorem Measure.lower {{c c' : {top}}} (h : Step c c') : {} c c' :=\n  Step.rel_of\n",
        if inv.is_some() { " under the invariant" } else { "" },
        cx.ctors.len(),
        cx.ctors.len() - n_auto,
        lower.trim_start_matches('(').trim_end_matches(')')
    ));
    for c in cx.ctors {
        t.push_str(&format!("    Measure.case.{}\n", c.lean));
    }
    if inv.is_some() {
        t.push_str(&format!(
            "    h\n\n/-- No infinite run starts where the invariant holds and the measure is defined: every run from\n\
there ends. -/\n\
theorem Measure.terminates (c : {top}) (hi : Invariant c) (h : (Measure.value c).isSome) :\n    \
Paths.Terminates Step c :=\n  \
KPrelude.Measure.terminates_inv Invariant.preserved Measure.value Measure.bound Measure.lower c hi h\n\n\
#k2l_assert_axioms Measure.bound Measure.lower Measure.terminates\n\nend {ns}\n"
        ));
    } else {
        t.push_str(&format!(
        "    h\n\n/-- No infinite run starts where the measure is defined: every run from there ends. -/\n\
theorem Measure.terminates (c : {top}) (h : (Measure.value c).isSome) : Paths.Terminates Step c :=\n  \
KPrelude.Measure.terminates Measure.value Measure.lower c h\n\n\
#k2l_assert_axioms Measure.lower Measure.terminates\n\nend {ns}\n"
    ));
    }

    // open-measure-cases.txt and the hand module's skeleton
    let mut ol = format!(
        "# Cases of the measure `{ns}.Measure.value` that `k2l_measure` does not close (`k2lean gen --measure`).\n\
# `k2lean open-from-log {ns}/Measure.lean BUILD.log open-measure-cases.txt` adds the cases whose proof failed.\n\
# Each line: the case, its statement, the rule's source position. Prove each in {ns}/MeasureHand.lean as\n\
# `theorem Measure.hand.r : Step.Rel.r {lower}` (namespace `{ns}`; `Step.Rel.r`\n\
# is stated in {ns}/Preserves.lean, `Measure.value` in {ns}/MeasureDefs.lean).\n"
    );
    let mut skel = String::new();
    if bound_open {
        ol.push_str(&format!(
            "Measure.bound | {bound_stmt} | the measure's definition\n"
        ));
        skel.push_str(&format!(
            "-- Where the invariant holds, the measure is nonnegative where it is defined:\n-- theorem Measure.hand.bound : {bound_stmt} := by\n--   …\n\n"
        ));
    }
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
    let hand_skeleton = ((!open.is_empty() || bound_open) && !hand_exists).then(|| {
        let inv_import = if inv.is_some() {
            format!("import {ns}.InvariantDefs\n")
        } else {
            String::new()
        };
        format!(
            "import {ns}.MeasureDefs\n{inv_import}\n\
/-! Hand-written proofs of the cases of the measure listed in `open-measure-cases.txt`.\n\n\
`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each case\n\
below as the theorem it names (uncomment and complete it); `Measure.lean` uses them by name. The\n\
generated proofs use `k2l_measure [{}] [{}] [{}] [{}]`. -/\n\n\
namespace {ns}\n\nopen KPrelude\n\n{skel}end {ns}\n",
            us.join(", "),
            lemmas.join(", "),
            sum_eqs.join(", "),
            weights.join(", ")
        )
    });
    Ok(Out {
        defs: d,
        theorems: t,
        open_list: ol,
        hand_skeleton,
    })
}

/// The definitions and theorems of a sum over a map (`MapFold`) in the namespace `p` (`Measure`, or
/// `Invariant` for an invariant that reads the sum): its test and weight of one binding, its value
/// at the empty map, and its value as the sum of the weights (`p.F_sum`, from its instances by
/// `MapHook.fold_sum`), where it is defined (`p.F_isSome`, by `MapHook.fold_sum_isSome`), and both
/// read together (`p.F_eq`). The proofs are those of a fold of claims (`invariants.rs`) with the
/// weights added rather than the claims concatenated.
pub(crate) fn sum_defs(f: &MapFold, p: &str) -> String {
    let (b, l) = (&f.base, &f.lean);
    let reads: String = f.reads.iter().map(|r| format!(", {r}")).collect();
    let insts = format!("{l}.instances, {l}.inst1, {l}.inst2");
    let cases: Vec<String> = [("k", &f.key_pat), ("v", &f.val_pat)]
        .iter()
        .filter_map(|(x, p)| p.as_ref().map(|p| format!("k2l_cases {x} with {p}")))
        .collect();
    let cases = if cases.is_empty() {
        String::new()
    } else {
        format!("    {}\n", cases.join(" <;> "))
    };
    let (key, val, map, test, part) = (&f.key, &f.val, &f.map, &f.test, &f.part);
    // a weight that matches the binding's patterns: its match split where the weight is defined
    let (split, split2) = if f.matched {
        (
            "      split at ha\n      all_goals (try (simp at ha; done))\n      all_goals\n  ",
            "  ",
        )
    } else {
        ("", "")
    };
    let unit = f.at("KPrelude.MapHook.unit");
    let at_m = f.at("m");
    format!(
        "/-- The sum `{l}`: what the patterns of one binding `k |-> v` read twice is equal. -/\n\
def {p}.{b}_test (k : {key}) (v : {val}) : Prop :=\n  {test}\n\n\
/-- The sum `{l}`: the weight of one binding `k |-> v`. -/\n\
def {p}.{b}_g (k : {key}) (v : {val}) : Option Int :=\n  {part}\n\n\
theorem {p}.{b}_unit : {unit} = some 0 := by\n  \
rw [{l}.eq_instances]\n  simp [{insts}, KPrelude.firstNonempty_singleton]\n\n\
/-- The sum `{l}`'s value is the sum of every binding's weight, each binding matching the patterns\n\
with its weight defined (`MapHook.fold_sum`, from its instances). -/\n\
theorem {p}.{b}_sum (m : {map}) (s : Int) (h : {at_m} = some s) :\n    \
KPrelude.MapHook.ClaimsDef {p}.{b}_test {p}.{b}_g m ∧ s = KPrelude.MapHook.sumOf {p}.{b}_g m := by\n  \
refine KPrelude.MapHook.fold_sum (F := fun m => {at_m}) (T := {p}.{b}_test)\n    {p}.{b}_unit ?_ m s h\n  \
intro m s hu h\n  rw [{l}.eq_instances] at h\n  \
simp only [{insts}, hu, ite_false, List.nil_append, KPrelude.firstNonempty_singleton] at h\n  \
split at h\n  · rename_i hw\n    \
obtain ⟨k, v, hk, hb⟩ := KPrelude.MapHook.mem_of_head?_chooseAll (Option.join_eq_some_iff.1 h)\n    \
refine ⟨(KPrelude.MapHook.wfb_iff _).1 hw, k, v, ?_⟩\n    repeat' (split at hb)\n    \
all_goals (simp only [List.mem_singleton, List.not_mem_nil, Option.some.injEq, reduceCtorEq] at hb)\n    \
all_goals\n      subst hb\n      subst_vars\n      apply Exists.intro; apply Exists.intro\n      \
refine ⟨hk, ?_, ?_, ?_, ?_⟩\n      · simp_all [{p}.{b}_test{reads}]\n      \
· simp only [{p}.{b}_g{reads}]; first | assumption | rfl\n      · assumption\n      \
· first | rfl | (simp only [KPrelude.IntHook.add_eq]; done) | (simp only [KPrelude.IntHook.add_eq]; k2l_int_omega)\n  \
· simp at h\n\n\
/-- The sum `{l}` is defined where every binding matches its patterns with a defined weight\n\
(`MapHook.fold_sum_isSome`, from its instances). -/\n\
theorem {p}.{b}_isSome (m : {map}) (hw : KPrelude.MapHook.WF m)\n    \
(hd : KPrelude.MapHook.ClaimsDef {p}.{b}_test {p}.{b}_g m) : ({at_m}).isSome := by\n  \
refine KPrelude.MapHook.fold_sum_isSome (F := fun m => {at_m}) (T := {p}.{b}_test)\n    \
(g := {p}.{b}_g) {p}.{b}_unit ?_ m hw hd\n  intro m hu hw h\n  rw [{l}.eq_instances]\n  \
simp only [{insts}, hu, ite_false, List.nil_append,\n    \
KPrelude.firstNonempty_singleton, (KPrelude.MapHook.wfb_iff m).2 hw, ite_true]\n  \
unfold KPrelude.MapHook.chooseAll\n  cases hl : KPrelude.ListIso.toList m with\n  \
| nil => exact absurd hl (KPrelude.MapHook.toList_ne_nil_of_ne_unit hu)\n  | cons p t =>\n    \
obtain ⟨⟨ht, hg⟩, hr⟩ := h p.1 p.2 (by rw [hl]; exact List.mem_cons_self ..)\n    \
obtain ⟨k, v⟩ := p\n    rw [List.flatMap_cons]\n{cases}    all_goals\n      \
simp only [{p}.{b}_test, {p}.{b}_g{reads}, Option.isSome_iff_exists] at ht hg hr\n      \
obtain ⟨a, ha⟩ := hg\n{split}      obtain ⟨r, hr'⟩ := hr\n{split2}      simp [ht, ha, hr']\n\n\
/-- The sum `{l}` read as a sum: defined exactly at a well-formed map whose every binding matches\n\
the patterns with a defined weight, and then the sum of the weights. -/\n\
theorem {p}.{b}_eq (m : {map}) (s : Int) :\n    {at_m} = some s ↔\n      \
KPrelude.MapHook.WF m ∧ KPrelude.MapHook.ClaimsDef {p}.{b}_test {p}.{b}_g m ∧\n        \
s = KPrelude.MapHook.sumOf {p}.{b}_g m := by\n  \
constructor\n  · intro h\n    refine ⟨?_, {p}.{b}_sum m s h⟩\n    \
by_cases hu : m = KPrelude.MapHook.unit\n    · subst hu; exact KPrelude.MapHook.wf_unit\n    \
· rw [{l}.eq_instances] at h\n      \
simp only [{insts}, hu, ite_false, List.nil_append, KPrelude.firstNonempty_singleton] at h\n      \
split at h\n      · exact (KPrelude.MapHook.wfb_iff _).1 ‹_›\n      · simp at h\n  \
· rintro ⟨hw, hd, rfl⟩\n    \
exact KPrelude.MapHook.fold_sum_eq (fun m s h => {p}.{b}_sum m s h)\n      \
(fun m hw hd => {p}.{b}_isSome m hw hd) hw hd\n\n"
    )
}

/// `e` parenthesized when it is an application.
fn paren_read(e: &str) -> String {
    if e.contains(' ') {
        format!("({e})")
    } else {
        e.to_string()
    }
}
