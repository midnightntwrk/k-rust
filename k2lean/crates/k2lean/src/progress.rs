//! No stuck states (SND-13, `k2lean/docs/design.md` §3.9): `k2lean gen --progress` writes
//! `{ns}/ProgressDefs.lean` and `{ns}/Progress.lean`, and beside the library
//! `open-progress-cases.txt`.
//!
//! **The theorem.** `progress c : Inv c → Ending c ∨ App c`: a configuration that satisfies the
//! well-formedness property (`Invariant`, the kind 1 invariant of `--invariant`; `True` without one)
//! is an acceptable ending (`--ending NAME@CELL`, a `Bool` K function of a cell's content; without
//! it, `<k>` is empty) or some rule applies (`App`, the library's own: its left-hand side matches
//! and its `requires` is true). A rule whose right-hand side is undefined applies, so the theorem
//! excludes stuck configurations, not undefined results, as type soundness does
//! (`product.md` §3.2). `no_stuck` composes it with `Invariant.preserved`: from a configuration
//! that satisfies the invariant, every configuration reached is an ending or can step; `always`
//! states the same of every run (`KPrelude.Paths`).
//!
//! **The cases.** One obligation per head of `<k>`: `.K`, and each constructor of a sort injected
//! into `KItem` (a builtin sort's values are one head). `<k>` is K's computation, so the head is
//! where a definition's rules read it; the name of a head's case is its K symbol, so an edit to the
//! rules of one head reopens that head's case only. The case states, for every configuration with
//! that head (the other cells and the rest of `<k>` variables), `Inv c → ¬ Ending c → App c`, and
//! is proved by `k2l_progress` (`KPrelude.Progress`) among the rules whose left-hand side has that
//! head (or a variable there), then, where no rule applies, from the invariant or the ending by
//! `simp_all` with their unfolding sets. A case that fails is listed in `open-progress-cases.txt`
//! (`k2lean open-from-log NS/Progress.lean BUILD.log open-progress-cases.txt`) and taken from the
//! hand-written `{ns}/ProgressHand.lean` as `Progress.hand.h`; one marked `| refuted hand` is false
//! (a stuck configuration the invariant allows), its refutation `Progress.case.h.refuted` is in the
//! hand module and checked by `#k2l_refuted`, and `progress` has the configurations with its head as a
//! third outcome (`Progress.Refuted`).

use crate::invariants::find_cell;
use crate::lower::{Fns, L};
use crate::model::Model;
use crate::names;
use crate::rules::Rule;
use std::collections::{BTreeMap, BTreeSet};

pub struct Ctx<'a> {
    pub m: &'a Model,
    pub rules: &'a [Rule],
    pub fns: &'a Fns,
    pub top: &'a str,
    pub ns: &'a str,
    /// The invariant's unfolding set (`invariant-unfold.txt`), when the library has an invariant.
    pub invariant: Option<Vec<String>>,
    /// The ending: the K function's symbol and the cell whose content it reads.
    pub ending: Option<(String, String)>,
    /// The library's `Step` is ranked (priorities, or rules with several matches).
    pub ranked: bool,
    /// The proved equations of each function (`Eqn.…`), by symbol.
    pub eqns: BTreeMap<String, Vec<String>>,
    /// The library's hook definitions and sort injections and projections, which a side condition
    /// unfolds into.
    pub unfold: Vec<String>,
}

pub struct Out {
    pub defs: String,
    pub theorems: String,
    pub open_list: String,
    pub hand_skeleton: Option<String>,
    pub cases: usize,
}

/// A head of `<k>`: its case's name, the binders of its arguments, the content of `<k>` with that
/// head (the rest `R`), how the dispatch of `progress` recognizes it, and the rules that can
/// apply there.
struct Head {
    name: String,
    binders: Vec<(String, String)>,
    k: String,
    /// `None` for `.K`; otherwise the injection into `KItem`, and whether the injected sort has
    /// constructors (a second case split) or is a builtin value
    dispatch: Option<(String, bool)>,
    /// the constructor at the head (`ctor_path`), for an injected sort with constructors
    ctor: Option<String>,
    rules: Vec<String>,
}

fn paren(s: &str) -> String {
    if s.contains(' ') && !(s.starts_with('(') && s.ends_with(')')) {
        format!("({s})")
    } else {
        s.to_string()
    }
}

/// The head of `<k>` in a rule's left-hand side: `Err(())` when the rule reads `<k>` through a
/// variable (it can apply at any head), `Ok(None)` for `.K`, `Ok(Some((inj, ctor)))` for an item
/// (`ctor` `None` when the injected value is a variable).
type RuleHead = Result<Option<(String, Option<String>)>, ()>;

fn rule_head(l: &L, path: &[(String, usize)], cell_lean: &str) -> RuleHead {
    let mut cur = l;
    for (lean, idx) in path {
        match cur {
            L::App(h, args) if h == lean => cur = &args[*idx],
            _ => return Err(()),
        }
    }
    let L::App(h, args) = cur else { return Err(()) };
    if h != cell_lean || args.len() != 1 {
        return Err(());
    }
    match &args[0] {
        L::App(h, _) if h == "SortK.dotk" => Ok(None),
        L::App(h, a) if h == "SortK.kseq" && a.len() == 2 => match &a[0] {
            L::App(inj, x) if x.len() == 1 => match &x[0] {
                L::App(c, _) => Ok(Some((inj.clone(), Some(c.clone())))),
                _ => Ok(Some((inj.clone(), None))),
            },
            _ => Err(()),
        },
        _ => Err(()),
    }
}

pub fn emit(cx: &Ctx, open_text: &str, hand_exists: bool) -> Result<Out, String> {
    let (m, ns, top) = (cx.m, cx.ns, cx.top);
    let kpath = find_cell(m, top, "k")?;
    if !kpath.colls.is_empty() {
        return Err(
            "--progress: `<k>` is inside a cell collection (threads); not supported yet (SND-13 slice 2)"
                .into(),
        );
    }
    if cx.ranked {
        return Err("--progress: a ranked Step (priorities, or rules with several matches) is not supported yet (SND-13 slice 3)".into());
    }
    if cx.rules.iter().any(|r| r.multi) {
        return Err("--progress: rules with several matches (free-key map patterns) are not supported yet (SND-13 slice 2)".into());
    }
    let path: Vec<(String, usize)> = kpath
        .levels
        .iter()
        .map(|lv| (lv.lean.clone(), lv.index))
        .collect();

    // the configuration with `<k>` holding `k`, the other cells variables
    let mut sib_binders: Vec<(String, String)> = Vec::new();
    let mut pats: Vec<Vec<String>> = Vec::new();
    for (i, lv) in kpath.levels.iter().enumerate() {
        let args = &m.ctors[&lv.sym].args;
        let mut p = Vec::new();
        for (j, a) in args.iter().enumerate() {
            if j == lv.index {
                p.push(String::new());
            } else {
                let x = format!("x{i}_{j}");
                sib_binders.push((x.clone(), a.clone()));
                p.push(x);
            }
        }
        pats.push(p);
    }
    let cfg = |k: &str| -> String {
        let mut inner = format!("{} {}", kpath.cell_lean, paren(k));
        for (i, lv) in kpath.levels.iter().enumerate().rev() {
            let args: Vec<String> = pats[i]
                .iter()
                .enumerate()
                .map(|(j, x)| {
                    if j == lv.index {
                        paren(&inner)
                    } else {
                        x.clone()
                    }
                })
                .collect();
            inner = format!("{} {}", lv.lean, args.join(" "));
        }
        inner
    };
    // the destructuring pattern of `progress`, down to the content `k` of `<k>`
    let mut dpat = "⟨k⟩".to_string();
    for (i, lv) in kpath.levels.iter().enumerate().rev() {
        let ps: Vec<String> = pats[i]
            .iter()
            .enumerate()
            .map(|(j, x)| {
                if j == lv.index {
                    dpat.clone()
                } else {
                    x.clone()
                }
            })
            .collect();
        dpat = format!("⟨{}⟩", ps.join(", "));
    }

    // the heads
    let kitem = m.sort("SortKItem");
    let mut heads: Vec<Head> = vec![Head {
        name: "dotk".into(),
        binders: vec![],
        k: "SortK.dotk".into(),
        dispatch: None,
        ctor: None,
        rules: vec![],
    }];
    for l in &kitem.leaves {
        let inj = format!("{ns}.{}", m.leaf_ctor("SortKItem", l));
        let inj_short = m.leaf_ctor("SortKItem", l);
        let sl = m.sort(l);
        if sl.own.is_empty() {
            heads.push(Head {
                name: format!("inj_{}", names::short_sort(l)),
                binders: vec![("v".into(), l.clone())],
                k: format!("SortK.kseq ({inj_short} v) R"),
                dispatch: Some((inj.clone(), false)),
                ctor: None,
                rules: vec![],
            });
            continue;
        }
        for sym in &sl.own {
            let c = &m.ctors[sym];
            let binders: Vec<(String, String)> = c
                .args
                .iter()
                .enumerate()
                .map(|(i, a)| (format!("a{i}"), a.clone()))
                .collect();
            let args: Vec<String> = binders.iter().map(|(b, _)| b.clone()).collect();
            let item = if args.is_empty() {
                m.ctor_path(sym)
            } else {
                format!("({} {})", m.ctor_path(sym), args.join(" "))
            };
            let base = c.lean.trim_start_matches('«').trim_end_matches('»');
            heads.push(Head {
                name: names::ident(&format!("{}.{base}", names::short_sort(l))),
                binders,
                k: format!("SortK.kseq ({inj_short} {item}) R"),
                dispatch: Some((inj.clone(), true)),
                ctor: Some(m.ctor_path(sym)),
                rules: vec![],
            });
        }
    }
    // the rules of each head: the rules whose `<k>` has that head, or a variable there
    for r in cx.rules {
        let h = rule_head(&r.app.index, &path, &kpath.cell_lean);
        let app = format!("App.{}", r.lean);
        for hd in heads.iter_mut() {
            let fits = match (&h, &hd.dispatch) {
                (Err(()), _) => true,
                (Ok(None), None) => true,
                (Ok(Some((inj, c))), Some((hinj, _))) => {
                    let hinj_short = hinj.strip_prefix(&format!("{ns}.")).unwrap_or(hinj);
                    inj == hinj_short && (c.is_none() || *c == hd.ctor)
                }
                _ => false,
            };
            if fits {
                hd.rules.push(app.clone());
            }
        }
    }

    // the unfolding sets: a side condition's functions and hooks; the invariant; the ending
    let mut close: BTreeSet<String> = cx.unfold.iter().cloned().collect();
    for (sym, sig) in cx.fns {
        if cx
            .rules
            .iter()
            .any(|r| r.app.hyps.iter().any(|(_, p)| p.contains(&sig.lean)))
            && let Some(es) = cx.eqns.get(sym)
        {
            close.extend(es.iter().cloned());
        }
    }
    let mut stuck: BTreeSet<String> = close.clone();
    if let Some(u) = &cx.invariant {
        stuck.insert("Invariant".into());
        stuck.extend(u.iter().cloned());
    }
    let mut defs = String::new();
    let ending_def;
    match &cx.ending {
        Some((sym, cell)) => {
            let sig = cx
                .fns
                .get(sym)
                .ok_or_else(|| format!("--ending: the function {sym} is not generated"))?;
            let ep = find_cell(m, top, cell)?;
            if !ep.colls.is_empty() {
                return Err(format!(
                    "--ending {cell}: inside a cell collection, not supported yet"
                ));
            }
            // one projection, by a nested pattern down to the cell's content
            let mut pat = format!("{} x", ep.cell_lean);
            for lv in ep.levels.iter().rev() {
                let args: Vec<String> = (0..lv.arity)
                    .map(|j| {
                        if j == lv.index {
                            paren(&pat)
                        } else {
                            "_".into()
                        }
                    })
                    .collect();
                pat = format!("{} {}", lv.lean, args.join(" "));
            }
            let content_sort = &ep.cell_args[0];
            defs.push_str(&format!(
                "/-- The content of the `<{cell}>` cell. -/\ndef Ending.content : {top} → {content_sort}\n  | {pat} => x\n\n"
            ));
            let rhs = if sig.partial { "some true" } else { "true" };
            ending_def = format!(
                "/-- The acceptable endings: the K function `{}` is `true` of the `<{cell}>` cell. -/\ndef Ending (c : {top}) : Prop :=\n  {} (Ending.content c) = {rhs}\n",
                names::demangle(sym),
                sig.lean
            );
            stuck.insert("Ending".into());
            stuck.insert("Ending.content".into());
            if let Some(es) = cx.eqns.get(sym) {
                stuck.extend(es.iter().cloned());
            }
        }
        None => {
            let mut pat = format!("{} x", kpath.cell_lean);
            for lv in kpath.levels.iter().rev() {
                let args: Vec<String> = (0..lv.arity)
                    .map(|j| {
                        if j == lv.index {
                            paren(&pat)
                        } else {
                            "_".into()
                        }
                    })
                    .collect();
                pat = format!("{} {}", lv.lean, args.join(" "));
            }
            defs.push_str(&format!(
                "/-- The content of the `<k>` cell. -/\ndef Ending.content : {top} → SortK\n  | {pat} => x\n\n"
            ));
            ending_def = format!(
                "/-- The acceptable endings: `<k>` is empty (no `--ending`). -/\ndef Ending (c : {top}) : Prop :=\n  Ending.content c = SortK.dotk\n"
            );
            stuck.insert("Ending".into());
            stuck.insert("Ending.content".into());
        }
    }
    defs.push_str(&ending_def);
    let inv = if cx.invariant.is_some() {
        "Invariant".to_string()
    } else {
        defs.push_str(&format!(
            "\n/-- The well-formedness property: none (no `--invariant`). -/\ndef Invariant (c : {top}) : Prop := True\n\n\
theorem Invariant.preserved : Preserved Step Invariant := by\n  intro _ _ _ _; trivial\n"
        ));
        "Invariant".to_string()
    };

    // the open list: `Progress.case.h` names, with `| refuted hand`
    let list =
        crate::refuted::parse(open_text).map_err(|e| format!("open-progress-cases.txt: {e}"))?;
    let strip = |n: &str| -> String {
        let n = n.strip_prefix("Progress.case.").unwrap_or(n);
        n.to_string()
    };
    let open: BTreeSet<String> = list.names.iter().map(|n| strip(n)).collect();
    let refuted: BTreeSet<String> = list.refuted.keys().map(|n| strip(n)).collect();

    // the statements
    defs.push('\n');
    for hd in &heads {
        let binders: Vec<String> = hd
            .binders
            .iter()
            .chain(
                if hd.dispatch.is_some() {
                    Some(("R".to_string(), "SortK".to_string()))
                } else {
                    None
                }
                .iter(),
            )
            .chain(sib_binders.iter())
            .map(|(b, t)| format!("({b} : {t})"))
            .collect();
        let c = cfg(&hd.k);
        defs.push_str(&format!(
            "/-- The head `{}` of `<k>`: a configuration with it that satisfies the invariant and is not an ending has a rule that applies. -/\ndef Progress.case.{}.statement : Prop :=\n  ∀ {}, {inv} ({c}) → ¬ Ending ({c}) → App ({c})\n\n",
            hd.name,
            hd.name,
            binders.join(" ")
        ));
    }

    // the proofs
    let n_args =
        |hd: &Head| hd.binders.len() + usize::from(hd.dispatch.is_some()) + sib_binders.len();
    let mut th = String::new();
    let close_list: Vec<String> = close.iter().cloned().collect();
    let stuck_list: Vec<String> = stuck.iter().cloned().collect();
    th.push_str(&format!(
        "/-- A rule's remaining goals: its `requires` and collection facts, by unification, an assumption, or computing them. -/\n\
local macro \"prog_close\" : tactic => `(tactic| first | rfl | assumption | (simp_all [{}]; done))\n\n\
/-- No rule of the head applies: the invariant or the ending is false. -/\n\
local macro \"prog_stuck\" : tactic => `(tactic| (exfalso; simp_all [{}]; done))\n\n",
        close_list.join(", "),
        stuck_list.join(", ")
    ));
    for hd in &heads {
        if refuted.contains(&hd.name) {
            continue;
        }
        if open.contains(&hd.name) {
            th.push_str(&format!(
                "theorem Progress.case.{n} : Progress.case.{n}.statement := Progress.hand.{n}\n\n",
                n = hd.name
            ));
            continue;
        }
        let xs: Vec<String> = (0..n_args(hd)).map(|i| format!("y{i}")).collect();
        let tac = if hd.rules.is_empty() {
            "  first | prog_stuck | fail \"no rule of this head applies, and the invariant and the ending do not exclude it\"".to_string()
        } else {
            format!(
                "  k2l_progress [{}] => prog_close else prog_stuck\n  all_goals first | prog_stuck | fail \"no rule of this head applies, and the invariant and the ending do not exclude it\"",
                hd.rules.join(", ")
            )
        };
        th.push_str(&format!(
            "theorem Progress.case.{n} : Progress.case.{n}.statement := by\n  intro {} hI hE\n{tac}\n\n",
            xs.join(" "),
            n = hd.name
        ));
    }
    // `progress`: a refuted case's head is a third outcome, `Progress.Refuted c` (the configuration
    // has one of those heads), so the theorem still says that every other configuration steps
    let refuted_heads: Vec<&Head> = heads.iter().filter(|h| refuted.contains(&h.name)).collect();
    let all_binders = |hd: &Head| -> Vec<String> {
        hd.binders
            .iter()
            .chain(
                if hd.dispatch.is_some() {
                    Some(("R".to_string(), "SortK".to_string()))
                } else {
                    None
                }
                .iter(),
            )
            .chain(sib_binders.iter())
            .map(|(b, t)| format!("({b} : {t})"))
            .collect()
    };
    let concl = if refuted_heads.is_empty() {
        "Ending c ∨ App c".to_string()
    } else {
        for hd in &refuted_heads {
            defs.push_str(&format!(
                "/-- The configurations whose head of `<k>` is `{}` (a refuted case). -/\ndef Progress.case.{}.at (c : {top}) : Prop :=\n  ∃ {}, c = {}\n\n",
                hd.name,
                hd.name,
                all_binders(hd).join(" "),
                cfg(&hd.k)
            ));
        }
        let ats: Vec<String> = refuted_heads
            .iter()
            .map(|h| format!("Progress.case.{}.at c", h.name))
            .collect();
        defs.push_str(&format!(
            "/-- The configurations at the heads whose case is refuted: stuck configurations the invariant allows. -/\ndef Progress.Refuted (c : {top}) : Prop :=\n  {}\n\n",
            ats.join(" ∨ ")
        ));
        "Ending c ∨ App c ∨ Progress.Refuted c".to_string()
    };
    let case_term = |hd: &Head| -> String {
        let us = vec!["_"; n_args(hd)].join(" ");
        match refuted_heads.iter().position(|h| h.name == hd.name) {
            Some(i) => {
                let k = refuted_heads.len();
                let mut w = format!("⟨{}, rfl⟩", vec!["_"; n_args(hd)].join(", "));
                if i + 1 < k {
                    w = format!("Or.inl {w}");
                }
                for _ in 0..i {
                    w = format!("Or.inr ({w})");
                }
                format!("Or.inr ({w})")
            }
            None if refuted_heads.is_empty() => format!("Progress.case.{} {us} hI hE", hd.name),
            None => format!("Or.inl (Progress.case.{} {us} hI hE)", hd.name),
        }
    };
    let mut leaf_arms: Vec<String> = Vec::new();
    let mut by_inj: BTreeMap<String, Vec<&Head>> = BTreeMap::new();
    for hd in &heads {
        if let Some((inj, _)) = &hd.dispatch {
            by_inj.entry(inj.clone()).or_default().push(hd);
        }
    }
    for (inj, hs) in &by_inj {
        let own = hs[0].dispatch.as_ref().unwrap().1;
        if own {
            let arms: Vec<String> = hs
                .iter()
                .map(|h| format!("| exact {}", case_term(h)))
                .collect();
            leaf_arms.push(format!(
                "| (k2l_has_ctor [{inj}]\n             k2l_cases x <;> k2l_norm_idx\n             all_goals first\n               {}\n             done)",
                arms.join("\n               ")
            ));
        } else {
            leaf_arms.push(format!(
                "| (k2l_has_ctor [{inj}]\n             exact {})",
                case_term(hs[0])
            ));
        }
    }
    let dotk = heads.iter().find(|h| h.dispatch.is_none()).unwrap();
    let what = if refuted_heads.is_empty() {
        "an ending, or some rule applies"
    } else {
        "an ending, some rule applies, or its head is one whose case is refuted (`Progress.Refuted`)"
    };
    th.push_str(&format!(
        "/-- No stuck configuration: one that satisfies the invariant is {what}. -/\n\
theorem progress (c : {top}) (hI : {inv} c) : {concl} := by\n  by_cases hE : Ending c\n  · exact Or.inl hE\n  right\n  k2l_cases c with {dpat}\n  k2l_cases k with ⟨it, R⟩\n  all_goals k2l_norm_idx\n  all_goals first\n    | exact {}\n    | (k2l_cases it with ⟨x⟩\n       all_goals k2l_norm_idx\n       all_goals first\n          {}\n       done)\n\n",
        case_term(dotk),
        leaf_arms.join("\n          ")
    ));
    let (preserved, star) = (
        "Invariant.preserved".to_string(),
        "Invariant.preserved.star h h0".to_string(),
    );
    let concl_s = concl.replace(" c", " (s n)");
    th.push_str(&format!(
        "/-- From a configuration that satisfies the invariant, every configuration reached is {what}. -/\n\
theorem no_stuck {{c0 c : {top}}} (h0 : {inv} c0) (h : Star Step c0 c) : {concl} :=\n  progress c ({star})\n\n\
/-- The same, on every run from `c0` (`KPrelude.Paths`: a run that halts repeats its last configuration). -/\n\
theorem always {{c0 : {top}}} (h0 : {inv} c0) :\n    ∀ s, s 0 = c0 → Paths.IsRun Step s → ∀ n, {concl_s} :=\n  Paths.always_iff.2 fun c h => progress c (Preserved.star {preserved} h h0)\n\n#k2l_assert_axioms progress no_stuck always\n{}",
        refuted_heads
            .iter()
            .map(|h| format!("#k2l_refuted Progress.case.{}\n", h.name))
            .collect::<String>(),
    ));

    // the open list
    let mut ol = String::from(
        "# Cases of `progress` that `k2l_progress` does not close (`k2lean gen --progress`).\n\
# `k2lean open-from-log NS/Progress.lean BUILD.log open-progress-cases.txt` adds the cases whose proof failed.\n\
# Each entry: `Progress.case.h`; prove it in NS/ProgressHand.lean as `theorem Progress.hand.h : Progress.case.h.statement`,\n\
# or mark it `| refuted hand` with `theorem Progress.case.h.refuted : ¬ Progress.case.h.statement` there (a stuck\n\
# configuration the invariant allows; `progress` then has that head as a third outcome, `Progress.Refuted`).\n",
    );
    for l in open_text.lines() {
        if crate::refuted::name_of(l).is_some() {
            ol.push_str(l.trim_end());
            ol.push('\n');
        }
    }
    let any_hand = !open.is_empty();
    let hand_skeleton = (any_hand && !hand_exists).then(|| {
        let mut s = format!(
            "import {ns}.ProgressDefs\nimport {ns}.Adequacy\n\n/-! Hand-written proofs of the cases of `progress` listed in `open-progress-cases.txt`.\n\n\
`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each case below as the\n\
theorem it names, or refute it (`theorem Progress.case.h.refuted : ¬ Progress.case.h.statement`, marked\n\
`| refuted hand` in the list; a witness configuration, with `step_stuck` for its last part). The generated proofs use `k2l_progress [rules] => prog_close`, then\n\
`exfalso; simp_all [{}]`. -/\n\nnamespace {ns}\n\nopen KPrelude\n\n",
            stuck_list.join(", ")
        );
        for n in &open {
            if refuted.contains(n) {
                s.push_str(&format!(
                    "-- theorem Progress.case.{n}.refuted : ¬ Progress.case.{n}.statement := by\n--   …\n\n"
                ));
            } else {
                s.push_str(&format!(
                    "-- theorem Progress.hand.{n} : Progress.case.{n}.statement := by\n--   …\n\n"
                ));
            }
        }
        s.push_str(&format!("end {ns}\n"));
        s
    });

    let n_heads = heads.len();
    let defs_mod = format!(
        "import {ns}.Rules\nimport {ns}.Equations\n{}import KPrelude.Progress\nimport KPrelude.Paths\n\n\
/-! Generated by k2lean (`gen --progress`); do not edit.\n\n\
The acceptable endings `Ending` and the statement of each case of `progress` (`Progress.lean`): one per head\n\
of `<k>`. This module is separate so that the hand-written `ProgressHand.lean` can prove the cases the\n\
generic tactic does not close. -/\n\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n\n{defs}\nend {ns}\n",
        if cx.invariant.is_some() {
            format!("import {ns}.Invariants\n")
        } else {
            String::new()
        }
    );
    let thm_mod = format!(
        "import {ns}.ProgressDefs\n{}\n\
/-! Generated by k2lean (`gen --progress`); do not edit.\n\n\
`progress`: a configuration that satisfies `{inv}` is an acceptable ending (`Ending`) or some rule applies\n\
(`App`), so no such configuration is stuck. One case per head of `<k>` ({n_heads} heads), each by\n\
`k2l_progress` among the rules of that head, then from the invariant or the ending where none applies;\n\
the cases listed in `open-progress-cases.txt` come from `ProgressHand.lean`. `no_stuck` and `always`\n\
extend it to every configuration reached from one that satisfies the invariant. -/\n\n\
set_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\nnamespace {ns}\n\nopen KPrelude\n\n{th}\nend {ns}\n",
        if any_hand {
            format!("import {ns}.ProgressHand\n")
        } else {
            String::new()
        }
    );
    Ok(Out {
        defs: defs_mod,
        theorems: thm_mod,
        open_list: ol,
        hand_skeleton,
        cases: n_heads,
    })
}
