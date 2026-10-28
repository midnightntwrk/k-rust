//! Fuel twins (`NS/Fuel.lean`): a step function the kernel can evaluate through well-founded
//! functions, proved to take only `Step`s.
//!
//! A function defined by well-founded recursion (`decreasing_by`) reduces in the kernel only
//! through `Acc.rec` on its accessibility proof, which does not reduce, so `decide +kernel` stops
//! at the first call of one, and with it any concrete run of `successors` that reaches it (SIMPLE's
//! `mkDecls`, `_[_]`, `_..._|->_`, `append`). Each such function `f` gets a twin
//! `f.fuel : Nat → … → Option _`, structural on the fuel: `f`'s cascade, with every call of a
//! well-founded function `g` replaced by `g.fuel n`, and `none` when the fuel runs out. One
//! induction proves `f.fuel n xs = some v → f xs = some v` for all of them (`fuelSoundAll`).
//!
//! Each rule whose matcher calls a twinned function gets a twin matcher `RulesF.x n`, the same
//! code with those calls replaced and their equations recovered from the twins' soundness. An
//! exhausted fuel takes the matcher's own branch for an undefined call, so a twin matcher
//! applies exactly where the rule's does (`RulesF.x.applies`, proved as `Rules.x.applies` is),
//! and the twin buckets `(bucketOf_i c).map (twinR_i n)` are stuck exactly where no rule of the
//! rank applies (`rank_i_stuckF`). Hence `successorsF_sound : c' ∈ successorsF n c → Step c c'`,
//! with no completeness claim: with too little fuel a successor is missing or undefined.
//!
//! This is derived code (`contract.md` §2): it states nothing new, and each definition is tied to
//! the generated one by a theorem, so a wrong twin is a build error of this module, never a false
//! fact. It is written only for definitions with several-match rules (`multi.rs`), only when every
//! call of a twinned function in a rule is on the right-hand side (a call in a `requires` would
//! decide applicability, which an exhausted fuel must not change), and only when the twinned
//! functions are exactly the well-founded ones (no other function calls one).

use crate::multi;
use crate::rules::{self, Rule};
use std::collections::BTreeSet;

/// A generated function's definition, read from `Functions.lean`.
#[derive(Debug)]
struct FnDef {
    name: String,
    params: Vec<(String, String)>,
    result: String,
    body: Vec<String>,
}

/// The definitions `def NAME (x0 : A) … : R :=` of `lean` whose name is in `names`, with their
/// body (up to the termination clause or the next blank line).
fn read_defs(lean: &str, names: &BTreeSet<String>) -> Result<Vec<FnDef>, String> {
    let lines: Vec<&str> = lean.lines().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let l = lines[i];
        let Some(rest) = l.strip_prefix("def ") else {
            i += 1;
            continue;
        };
        let Some(name) = names.iter().find(|n| {
            rest.strip_prefix(n.as_str())
                .is_some_and(|t| t.starts_with(' '))
        }) else {
            i += 1;
            continue;
        };
        let sig = rest[name.len()..].trim();
        let sig = sig
            .strip_suffix(":=")
            .ok_or(format!("{name}: a definition not ending in `:=`"))?;
        let (params, result) = split_sig(sig).ok_or(format!("{name}: unreadable signature"))?;
        if !result.starts_with("Option ") {
            return Err(format!("{name} is not `Option`-valued"));
        }
        let mut body = Vec::new();
        i += 1;
        while i < lines.len() {
            let b = lines[i];
            if b.is_empty()
                || b.starts_with("termination_by")
                || b.starts_with("decreasing_by")
                || b.starts_with("partial_fixpoint")
                || !b.starts_with(' ')
            {
                break;
            }
            body.push(b.to_string());
            i += 1;
        }
        out.push(FnDef {
            name: name.clone(),
            params,
            result: result.to_string(),
            body,
        });
    }
    Ok(out)
}

/// `(x0 : A) (x1 : B) : R` into the parameters and `R`.
fn split_sig(sig: &str) -> Option<(Vec<(String, String)>, &str)> {
    let mut params = Vec::new();
    let mut rest = sig.trim_start();
    while let Some(r) = rest.strip_prefix('(') {
        let mut depth = 1;
        let mut end = None;
        for (k, ch) in r.char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(k);
                        break;
                    }
                }
                _ => {}
            }
        }
        let inner = &r[..end?];
        let (x, t) = inner.split_once(" : ")?;
        params.push((x.trim().to_string(), t.trim().to_string()));
        rest = r[end? + 1..].trim_start();
    }
    Some((params, rest.strip_prefix(": ")?.trim()))
}

/// Whether line `l` is `match h : CALL with` of a twinned function: `(indent, h, f, args)`.
fn twin_call<'a>(l: &'a str, twins: &[String]) -> Option<(&'a str, &'a str, String, &'a str)> {
    let t = l.trim_start();
    let ind = &l[..l.len() - t.len()];
    let rest = t.strip_prefix("match ")?.strip_suffix(" with")?;
    let (h, e) = rest.split_once(" : ")?;
    let f = twins.iter().find(|f| {
        e.strip_prefix(f.as_str())
            .is_some_and(|a| a.is_empty() || a.starts_with(' '))
    })?;
    Some((ind, h, f.clone(), e[f.len()..].trim_start()))
}

/// Replace every call `f args` of a twinned function by `f.fuel n args` (a word boundary after
/// the name: `K.f` must not match `K.f.rule1`, nor `K.append` match `K.appendAll`).
fn twin_calls(line: &str, twins: &[String]) -> String {
    let mut s = line.to_string();
    for f in twins {
        let mut out = String::new();
        let mut rest = s.as_str();
        while let Some(k) = rest.find(f.as_str()) {
            let after = &rest[k + f.len()..];
            out.push_str(&rest[..k]);
            if after.starts_with(' ') {
                out.push_str(&format!("{f}.fuel n"));
            } else {
                out.push_str(f);
            }
            rest = after;
        }
        out.push_str(rest);
        s = out;
    }
    s
}

/// The generic proof script of one twin's soundness, in the induction step: unfold both, split the
/// twin's cascade, lift each twin call's value to the function's (`k2l_fuel_lift`), then reduce the
/// function's cascade along it.
/// `bullet`: one goal of several (`· …`), else the only goal.
fn sound_case(f: &FnDef, ihs: &str, bullet: bool) -> String {
    let xs: Vec<&str> = f.params.iter().map(|(x, _)| x.as_str()).collect();
    let (first, rest) = if bullet {
        ("    · ", "      ")
    } else {
        ("    ", "    ")
    };
    format!(
        "{first}intro {} v h\n{rest}rw [{}.eq_def]\n{rest}simp only [{}.fuel] at h\n{rest}repeat' (first | split at h | k2l_split_hyps)\n{rest}all_goals (k2l_fuel_lift [{ihs}]; repeat' (first | (simp_all; done) | simp only [] | split | k2l_split_hyps))\n",
        xs.join(" "),
        f.name,
        f.name
    )
}

/// `NS/Fuel.lean`, or why it is not written (a note), for a definition with several-match rules.
/// `None` when the definition has no well-founded function.
#[allow(clippy::too_many_arguments)]
pub fn emit(
    functions: &str,
    recursive: &BTreeSet<String>,
    groups: &[Vec<String>],
    rules: &[Rule],
    prios: &[i64],
    top: &str,
    ns: &str,
) -> Option<Result<String, String>> {
    if recursive.is_empty() {
        return None;
    }
    Some(emit_inner(
        functions, recursive, groups, rules, prios, top, ns,
    ))
}

fn emit_inner(
    functions: &str,
    recursive: &BTreeSet<String>,
    groups: &[Vec<String>],
    rules: &[Rule],
    prios: &[i64],
    top: &str,
    ns: &str,
) -> Result<String, String> {
    let defs = read_defs(functions, recursive)?;
    // definition order (callees first), as `Functions.lean` has them
    let order: Vec<&String> = groups
        .iter()
        .flatten()
        .filter(|f| recursive.contains(*f))
        .collect();
    let mut fs: Vec<&FnDef> = Vec::new();
    for n in &order {
        if let Some(d) = defs.iter().find(|d| &&d.name == n) {
            fs.push(d);
        }
    }
    if fs.len() != recursive.len() {
        return Err(format!(
            "not every well-founded function is a single definition ({} of {})",
            fs.len(),
            recursive.len()
        ));
    }
    let twins: Vec<String> = fs.iter().map(|d| d.name.clone()).collect();
    // another function calling a twinned one would need a twin too (not generated)
    let mut current: Option<&str> = None;
    for l in functions.lines() {
        if let Some(rest) = l.strip_prefix("def ") {
            current = rest.split(' ').next();
        } else if !l.starts_with(' ') {
            current = None;
        } else if let Some(name) = current
            && !twins.iter().any(|t| t == name)
            && twin_calls(l, &twins) != l
        {
            return Err(format!("{name} calls a well-founded function"));
        }
    }
    let mut o = format!(
        "import {ns}.Adequacy\nimport KPrelude.Tactic\n\n/-! Generated by k2lean; do not edit.\n\n\
Fuel twins of the well-founded functions and of the rules that call them, so that the kernel can\n\
evaluate `successorsF` on a closed configuration (`decide +kernel`) where `successors` stops at a\n\
well-founded function. Derived: `successorsF_sound` proves that every successor it lists is a\n\
`Step` successor; with too little fuel one is missing or undefined. -/\n\n\
set_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\nset_option maxRecDepth 100000\n\nnamespace {ns}\n\nopen KPrelude\n\n"
    );
    // the twins, a `mutual` block per strongly connected group of several functions
    for g in groups {
        let members: Vec<&&FnDef> = fs.iter().filter(|d| g.contains(&d.name)).collect();
        if members.is_empty() {
            continue;
        }
        let mutual = members.len() > 1;
        if mutual {
            o.push_str("mutual\n");
        }
        for d in members {
            let tys: Vec<&str> = d.params.iter().map(|(_, t)| t.as_str()).collect();
            let xs: Vec<&str> = d.params.iter().map(|(x, _)| x.as_str()).collect();
            let blanks: Vec<&str> = d.params.iter().map(|_| "_").collect();
            let mut zero = vec!["0"];
            zero.extend(&blanks);
            let mut succ = vec!["n + 1"];
            succ.extend(&xs);
            o.push_str(&format!(
                "/-- `{}` with fuel: structural on the first argument. -/\ndef {}.fuel : Nat → {} → {}\n  | {} => none\n  | {} =>\n",
                d.name,
                d.name,
                tys.join(" → "),
                d.result,
                zero.join(", "),
                succ.join(", ")
            ));
            for b in &d.body {
                o.push_str(&format!("  {}\n", twin_calls(b, &twins)));
            }
            o.push('\n');
        }
        if mutual {
            o.push_str("end\n\n");
        }
    }
    // soundness, one induction for all twins
    let stmts: Vec<String> = fs
        .iter()
        .map(|d| {
            let xs: Vec<&str> = d.params.iter().map(|(x, _)| x.as_str()).collect();
            let xs = xs.join(" ");
            format!(
                "(∀ {xs} v, {}.fuel n {xs} = some v → {} {xs} = some v)",
                d.name, d.name
            )
        })
        .collect();
    let k = fs.len();
    let ihs: Vec<String> = (0..k).map(|i| format!("ih{i}")).collect();
    let fuels: Vec<String> = fs.iter().map(|d| format!("{}.fuel", d.name)).collect();
    o.push_str(&format!(
        "/-- Every twin's value is its function's. -/\ntheorem fuelSoundAll : ∀ n,\n    {} := by\n  intro n\n  induction n with\n",
        stmts.join(" ∧\n    ")
    ));
    if k == 1 {
        o.push_str(&format!(
            "  | zero => intros; simp_all [{}]\n  | succ n ih0 =>\n",
            fuels.join(", ")
        ));
        o.push_str(&sound_case(fs[0], "ih0", false));
    } else {
        let holes: Vec<&str> = (0..k).map(|_| "?_").collect();
        o.push_str(&format!(
            "  | zero => refine ⟨{}⟩ <;> (intros; simp_all [{}])\n  | succ n ih =>\n    obtain ⟨{}⟩ := ih\n    refine ⟨{}⟩\n",
            holes.join(", "),
            fuels.join(", "),
            ihs.join(", "),
            holes.join(", ")
        ));
        for d in &fs {
            o.push_str(&sound_case(d, &ihs.join(", "), true));
        }
    }
    for (i, d) in fs.iter().enumerate() {
        let xs: Vec<&str> = d.params.iter().map(|(x, _)| x.as_str()).collect();
        let xs = xs.join(" ");
        let proj = if k == 1 {
            String::new()
        } else if i + 1 < k {
            format!("{}.1", ".2".repeat(i))
        } else {
            ".2".repeat(i)
        };
        o.push_str(&format!(
            "\ntheorem {}.fuel_sound {{n : Nat}} {{{xs}}} {{v}} (h : {}.fuel n {xs} = some v) : {} {xs} = some v :=\n  (fuelSoundAll n){proj} {xs} v h\n",
            d.name, d.name, d.name
        ));
    }
    // the twin matchers
    let mut twinned: Vec<&Rule> = Vec::new();
    for r in rules {
        let lines: Vec<&str> = r.exec_multi.lines().collect();
        if !lines.iter().any(|l| twin_calls(l, &twins) != *l) {
            continue;
        }
        let i = multi::rank_of(r, prios);
        let mut body = String::new();
        let mut pending: Option<(String, String, String)> = None;
        let mut calls: Vec<String> = Vec::new();
        for l in &lines {
            if let Some((ind, h, f, args)) = twin_call(l, &twins) {
                body.push_str(&format!("{ind}match {h}F : {f}.fuel n {args} with\n"));
                pending = Some((ind.to_string(), h.to_string(), f));
                calls.push(ind.to_string());
                continue;
            }
            // the `none` arm of a twin call: a call on the right-hand side is undefined there; one in
            // a condition decides whether the rule applies, which an exhausted fuel must not change
            if let Some(ind) = calls
                .iter()
                .find(|ind| l.starts_with(ind.as_str()) && l[ind.len()..].starts_with("| none =>"))
            {
                if !l.contains(".undefined") {
                    return Err(format!(
                        "rule {}: a well-founded function in a condition of the rule",
                        r.name
                    ));
                }
                let ind = ind.clone();
                calls.retain(|x| *x != ind);
            }
            if twin_calls(l, &twins) != *l {
                return Err(format!(
                    "rule {}: a well-founded function called outside a `match` on its value",
                    r.name
                ));
            }
            body.push_str(l);
            body.push('\n');
            if let Some((ind, h, f)) = &pending
                && l.trim_start().starts_with("| some ")
                && l.starts_with(ind.as_str())
            {
                body.push_str(&format!("{ind}  have {h} := {f}.fuel_sound {h}F\n"));
                pending = None;
            }
        }
        o.push_str(&format!(
            "\ndef RulesF.{} (n : Nat) (c : {top}) : List (RuleResult (App {i}) (Step0 {i}) c) :=\n{}",
            r.lean,
            body.trim_end()
        ));
        o.push('\n');
        twinned.push(r);
    }
    for r in &twinned {
        let rule = format!("RulesF.{}", r.lean);
        let tac = multi::MATCH_TAC.replace("{rule}", &rule);
        o.push_str(&format!(
            "\ntheorem {rule}.applies (n : Nat){} :\n    ∃ ρ ∈ {rule} n {}, ρ.applies = true := by\n{tac}",
            rules::ctor_sig(&r.app),
            r.app.index.render_arg()
        ));
    }
    let pos = |r: &Rule| rules.iter().position(|x| x.lean == r.lean).unwrap_or(0);
    for r in &twinned {
        let i = multi::rank_of(r, prios);
        o.push_str(&format!(
            "\ndef RF.{} (n : Nat) : Rule {top} (App {i}) (Step0 {i}) := ⟨{}, {}, fun c => pick (RulesF.{} n c)⟩\n",
            r.lean,
            crate::names::string_lit(&rules::display_name(r)),
            pos(r),
            r.lean
        ));
    }
    let ranks = prios.len();
    o.push_str(&format!(
        "\ntheorem firstDefined_stuck_map {{i : Nat}} {{f : Rule {top} (App i) (Step0 i) → Rule {top} (App i) (Step0 i)}}\n    {{rs : List (Rule {top} (App i) (Step0 i))}} {{c : {top}}}\n    (h : firstDefined (rs.map f) c none = .stuck) {{r : Rule {top} (App i) (Step0 i)}} (hm : r ∈ rs)\n    (ha : ((f r).run c).applies = true) : False := by\n  have := firstDefined_stuck (rs.map f) c h (f r) (List.mem_map_of_mem hm)\n  rw [ha] at this\n  exact Bool.noConfusion this\n"
    ));
    let is_twin = |r: &Rule| twinned.iter().any(|t| t.lean == r.lean);
    for i in 0..ranks {
        let rs: Vec<&Rule> = rules
            .iter()
            .filter(|r| multi::rank_of(r, prios) == i)
            .collect();
        let mut disp = "r".to_string();
        for r in rs.iter().rev() {
            if is_twin(r) {
                disp = format!("if r.rank = {} then RF.{} n else {disp}", pos(r), r.lean);
            }
        }
        let ms: Vec<String> = rs
            .iter()
            .map(|r| {
                if is_twin(r) {
                    format!("  RulesF.{} n", r.lean)
                } else {
                    format!("  Rules.{}", r.lean)
                }
            })
            .collect();
        o.push_str(&format!(
            "\ndef twinR{i} (n : Nat) (r : Rule {top} (App {i}) (Step0 {i})) : Rule {top} (App {i}) (Step0 {i}) :=\n  {disp}\n\
def bucketOfF{i} (n : Nat) (c : {top}) : List (Rule {top} (App {i}) (Step0 {i})) := (bucketOf{i} c).map (twinR{i} n)\n\
def matchersF{i} (n : Nat) : List ((c : {top}) → List (RuleResult (App {i}) (Step0 {i}) c)) := [\n{}]\n\
def succF{i} (n : Nat) (c : {top}) : List {top} := (matchersF{i} n).flatMap fun f => nexts (f c)\n",
            ms.join(",\n")
        ));
        o.push_str(&format!(
            "\ntheorem rank{i}_stuckF {{n : Nat}} {{c : {top}}} (h : firstDefined (bucketOfF{i} n c) c none = .stuck) : ¬ App {i} c := by\n  intro ha\n  cases ha with\n"
        ));
        for r in &rs {
            let args = rules::ctor_args(&r.app).join(" ");
            let ap = if is_twin(r) {
                format!("RulesF.{}.applies n {args}", r.lean)
            } else {
                format!("Rules.{}.applies {args}", r.lean)
            };
            o.push_str(&format!(
                "  | {0} {args} => exact firstDefined_stuck_map h (Rules.{0}.mem {args}) (pick_applies_of_exists ({ap}))\n",
                r.lean
            ));
        }
        o.push_str(&format!(
            "\ntheorem succF{i}_sound {{n : Nat}} {{c c' : {top}}} (h : c' ∈ succF{i} n c) : Step0 {i} c c' := by\n  simp only [succF{i}, List.mem_flatMap] at h\n  obtain ⟨f, _, hf⟩ := h\n  exact sound_of_mem_nexts hf\n"
        ));
    }
    let mut succ = format!("succF{} n c", ranks - 1);
    for i in (0..ranks - 1).rev() {
        succ = format!(
            "if isStuck (firstDefined (bucketOfF{i} n c) c none) = true then {succ} else succF{i} n c"
        );
    }
    o.push_str(&format!(
        "\n/-- `successors` through the fuel twins. -/\ndef successorsF (n : Nat) (c : {top}) : List {top} :=\n  {succ}\n"
    ));
    // soundness: the first rank whose twin bucket is not stuck
    let mut proof = String::new();
    let stuck = |j: usize| format!("rank{j}_stuckF (isStuck_iff.1 s{j})");
    for i in 0..ranks {
        let ind = "  ".repeat(i + 1);
        if i + 1 < ranks {
            proof.push_str(&format!(
                "{ind}by_cases s{i} : isStuck (firstDefined (bucketOfF{i} n c) c none) = true\n{ind}· rw [ite_eq_left s{i}] at h\n"
            ));
        } else {
            proof.push_str(&format!(
                "{ind}exact Step0.lift (succF{i}_sound h) {}\n",
                multi::below(i, &stuck)
            ));
        }
    }
    for i in (0..ranks - 1).rev() {
        let ind = "  ".repeat(i + 1);
        proof.push_str(&format!(
            "{ind}· rw [ite_eq_right s{i}] at h\n{ind}  exact Step0.lift (succF{i}_sound h) {}\n",
            multi::below(i, &stuck)
        ));
    }
    o.push_str(&format!(
        "\n/-- Every successor `successorsF` lists is a `Step` successor. -/\ntheorem successorsF_sound {{n : Nat}} {{c c' : {top}}} (h : c' ∈ successorsF n c) : Step c c' := by\n  unfold successorsF at h\n{proof}\n#k2l_assert_axioms fuelSoundAll successorsF_sound\n\nend {ns}\n"
    ));
    Ok(o)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signature_of_a_definition() {
        let (ps, r) =
            split_sig("(x0 : SortIds) (x1 : Option (List Nat)) : Option SortStmt").unwrap();
        assert_eq!(
            ps,
            vec![
                ("x0".to_string(), "SortIds".to_string()),
                ("x1".to_string(), "Option (List Nat)".to_string())
            ]
        );
        assert_eq!(r, "Option SortStmt");
    }

    /// A call is renamed only at a word boundary: not `K.f.rule1`, not `K.ff`.
    #[test]
    fn calls_are_renamed_at_a_word_boundary() {
        let tw = vec!["K.f".to_string()];
        assert_eq!(
            twin_calls("  match hr : K.f x (K.f.rule1 y) (K.ff z) with", &tw),
            "  match hr : K.f.fuel n x (K.f.rule1 y) (K.ff z) with"
        );
        let (ind, h, f, args) = twin_call("    match hr_3 : K.f x y with", &tw).unwrap();
        assert_eq!((ind, h, f.as_str(), args), ("    ", "hr_3", "K.f", "x y"));
        assert!(twin_call("    match hr : K.ff x with", &tw).is_none());
    }

    #[test]
    fn definitions_and_their_bodies() {
        let lean = "def K.f (x0 : A) : Option B :=\n  match x0 with\n  | a => some b\ndecreasing_by all_goals simp\n\ndef K.g (x0 : A) : B :=\n  b\n";
        let names: BTreeSet<String> = ["K.f".to_string()].into();
        let ds = read_defs(lean, &names).unwrap();
        assert_eq!(ds.len(), 1);
        assert_eq!(ds[0].body, vec!["  match x0 with", "  | a => some b"]);
        let names: BTreeSet<String> = ["K.g".to_string()].into();
        assert!(
            read_defs(lean, &names)
                .unwrap_err()
                .contains("not `Option`-valued")
        );
    }
}
