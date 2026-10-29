//! No stuck states (SND-13, `k2lean/docs/design.md` §3.9): `k2lean gen --progress` writes
//! `{ns}/ProgressDefs.lean` and `{ns}/Progress.lean`, and beside the library
//! `open-progress-cases.txt`; under a kind 2 invariant, which the library cannot import, into the
//! package that holds it instead (`--progress-out DIR --progress-prefix PFX`: `PFX/…`).
//!
//! **The theorem.** `progress c : Inv c → Ending c ∨ App c`: a configuration that satisfies the
//! well-formedness property (`Invariant`, the kind 1 invariant of `--invariant`, or a kind 2 one,
//! a Lean predicate, with `--assume-invariant`; `True` without one)
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

use crate::invariants::{CellPath, find_cell};
use crate::ir::P;
use crate::lower::{Fns, L};
use crate::model::{Coll, Model};
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
    /// The library's `Step` is ranked (priorities, or rules with several matches): `App` is
    /// indexed by the rank.
    pub ranked: bool,
    /// The number of priority ranks.
    pub ranks: usize,
    /// The proved equations of each function (`Eqn.…`), by symbol.
    pub eqns: BTreeMap<String, Vec<String>>,
    /// The library's hook definitions and sort injections and projections, which a side condition
    /// unfolds into.
    pub unfold: Vec<String>,
    /// A kind 2 invariant (`--assume-invariant`), in place of the kind 1 `Invariant`.
    pub kind2: Option<Kind2>,
    /// The prefix of the progress modules' names: the library's namespace, or the package that
    /// holds a kind 2 invariant (`--progress-out`), which the library cannot import.
    pub module: String,
    /// `--element-fact NAME`: what the invariant says of each element of the cell map, added to
    /// every case.
    pub element_fact: Option<String>,
    /// `--rank NAME`: the rank of an element, a Lean function of the cell map, the key and the
    /// element.
    pub rank: Option<String>,
}

/// A kind 2 invariant, spelled as `claims --assume-invariant` takes it: the predicate, the module
/// that defines it, its preservation theorem, and the names the stuck closer unfolds.
pub struct Kind2 {
    pub name: String,
    pub module: String,
    pub preserved: String,
    pub unfold: Vec<String>,
}

/// `Invariant` when the library has no kind 1 invariant: the kind 2 one, or `True`.
fn inv_def(cx: &Ctx, top: &str) -> String {
    match &cx.kind2 {
        Some(k) => format!(
            "\n/-- The well-formedness property: `{n}` (`--assume-invariant`, a Lean predicate of `{m}`). -/\n\
def Invariant (c : {top}) : Prop := {n} c\n\n\
theorem Invariant.preserved : Preserved Step Invariant := {p}\n",
            n = k.name,
            m = k.module,
            p = k.preserved
        ),
        None => format!(
            "\n/-- The well-formedness property: none (no `--invariant`). -/\ndef Invariant (c : {top}) : Prop := True\n\n\
theorem Invariant.preserved : Preserved Step Invariant := by\n  intro _ _ _ _; trivial\n"
        ),
    }
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
    /// the head's K symbol (a constructor head) and the leaf sort of `KItem` it is in
    sym: Option<String>,
    leaf: Option<String>,
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

/// The heads of `<k>`: `.K`, then each constructor of a sort injected into `KItem` (a builtin
/// sort's values are one head).
fn heads_of(m: &Model, ns: &str) -> Vec<Head> {
    let kitem = m.sort("SortKItem");
    let mut heads: Vec<Head> = vec![Head {
        name: "dotk".into(),
        binders: vec![],
        k: "SortK.dotk".into(),
        dispatch: None,
        ctor: None,
        sym: None,
        leaf: None,
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
                sym: None,
                leaf: Some(l.clone()),
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
                sym: Some(sym.clone()),
                leaf: Some(l.clone()),
                rules: vec![],
            });
        }
    }
    heads
}

pub fn emit(cx: &Ctx, open_text: &str, hand_exists: bool) -> Result<Out, String> {
    let (m, ns, top) = (cx.m, cx.ns, cx.top);
    let kpath = find_cell(m, top, "k")?;
    if !kpath.colls.is_empty() {
        return emit_coll(cx, open_text, hand_exists, &kpath);
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

    let mut heads = heads_of(m, ns);
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
    if let Some(k) = &cx.kind2 {
        stuck.insert("Invariant".into());
        stuck.extend(k.unfold.iter().cloned());
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
    if cx.invariant.is_none() {
        defs.push_str(&inv_def(cx, top));
    }
    let inv = "Invariant";

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

    finish(
        cx,
        Finish {
            defs,
            th,
            open_text,
            open: &open,
            refuted: &refuted,
            stuck_list: &stuck_list,
            hand_exists,
            n_heads: heads.len(),
            coll: false,
            doc: format!(
                "`progress`: a configuration that satisfies `{inv}` is an acceptable ending (`Ending`) or some rule applies\n\
(`App`), so no such configuration is stuck. One case per head of `<k>` ({} heads), each by\n\
`k2l_progress` among the rules of that head, then from the invariant or the ending where none applies;\n\
the cases listed in `open-progress-cases.txt` come from `ProgressHand.lean`. `no_stuck` and `always`\n\
extend it to every configuration reached from one that satisfies the invariant.",
                heads.len()
            ),
        },
    )
}

/// What `finish` writes around a mode's definitions and theorems.
struct Finish<'a> {
    defs: String,
    th: String,
    open_text: &'a str,
    open: &'a BTreeSet<String>,
    refuted: &'a BTreeSet<String>,
    stuck_list: &'a [String],
    hand_exists: bool,
    n_heads: usize,
    /// `<k>` is in a cell map: `Progress.Keys` is proved with `k2l_preserve` over `Step.Case`
    coll: bool,
    /// the module documentation of `Progress.lean`
    doc: String,
}

/// The open list, the hand skeleton and the two modules.
fn finish(cx: &Ctx, f: Finish) -> Result<Out, String> {
    let (ns, pfx) = (cx.ns, cx.module.as_str());
    let (defs, th, open_text, open, refuted, stuck_list, hand_exists, n_heads) = (
        f.defs,
        f.th,
        f.open_text,
        f.open,
        f.refuted,
        f.stuck_list,
        f.hand_exists,
        f.n_heads,
    );
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
            "import {pfx}.ProgressDefs\nimport {ns}.Adequacy\n\n/-! Hand-written proofs of the cases of `progress` listed in `open-progress-cases.txt`.\n\n\
`k2lean gen` wrote this file once, because it did not exist, and never changes it. Prove each case below as the\n\
theorem it names, or refute it (`theorem Progress.case.h.refuted : ¬ Progress.case.h.statement`, marked\n\
`| refuted hand` in the list; a witness configuration, with `step_stuck` for its last part). The generated proofs use `k2l_progress [rules] => prog_close`, then\n\
`exfalso; simp_all [{}]`. -/\n\nnamespace {ns}\n\nopen KPrelude\n\n",
            stuck_list.join(", ")
        );
        for n in open {
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

    let defs_mod = format!(
        "import {ns}.Rules\nimport {ns}.Equations\n{}import KPrelude.Progress\nimport KPrelude.Paths\n\n\
/-! Generated by k2lean (`gen --progress`); do not edit.\n\n\
The acceptable endings `Ending` and the statement of each case of `progress` (`Progress.lean`): one per head\n\
of `<k>`. This module is separate so that the hand-written `ProgressHand.lean` can prove the cases the\n\
generic tactic does not close. -/\n\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n\n{defs}\nend {ns}\n",
        match (&cx.invariant, &cx.kind2) {
            (Some(_), _) => format!("import {ns}.Invariants\n"),
            // `Progress.Keys` is proved over `Step.Case` by `k2l_preserve`, which the invariant's
            // modules import otherwise
            (None, k) => format!(
                "{}{}",
                if f.coll {
                    format!(
                        "import {ns}.Preserves\nimport KPrelude.InvTactic\n{}",
                        if cx.element_fact.is_some() {
                            "import KPrelude.PendingTactic\n"
                        } else {
                            ""
                        }
                    )
                } else {
                    String::new()
                },
                k.as_ref()
                    .map(|k| format!("import {}\n", k.module))
                    .unwrap_or_default()
            ),
        }
    );
    let thm_mod = format!(
        "import {pfx}.ProgressDefs\n{}\n\
/-! Generated by k2lean (`gen --progress`); do not edit.\n\n{} -/\n\n\
set_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\nnamespace {ns}\n\nopen KPrelude\n\n{th}\nend {ns}\n",
        if any_hand {
            format!("import {pfx}.ProgressHand\n")
        } else {
            String::new()
        },
        f.doc
    );
    Ok(Out {
        defs: defs_mod,
        theorems: thm_mod,
        open_list: ol,
        hand_skeleton,
        cases: n_heads,
    })
}

/// The heartbeat budget of a case at a cell map: a case that waits on a partner splits the
/// partner's `<k>` as well (measured: `coro`'s `resume` needs between 400,000 and 700,000).
const CASE_BUDGET: u32 = 2_000_000;

/// A rule's head of `<k>`, read off its KORE left-hand side: in the first element of its cell map
/// pattern, which its `App` constructor matches first (the element of a case).
enum HeadPat {
    /// `<k>` is a variable there, or the rule does not read it
    Any,
    Dotk,
    /// a constructor, by its K symbol
    Sym(String),
    /// a value of a sort injected into `KItem` (a builtin value, or a variable of the sort)
    Leaf(String),
}

fn first_k<'a>(p: &'a P, ksym: &str) -> Option<&'a P> {
    match p {
        P::App(s, _, args) if s == ksym && args.len() == 1 => Some(&args[0]),
        P::App(_, _, args) | P::And(_, args) => args.iter().find_map(|a| first_k(a, ksym)),
        _ => None,
    }
}

fn kore_head(p: &P, ksym: &str, m: &Model) -> HeadPat {
    let Some(c) = first_k(p, ksym) else {
        return HeadPat::Any;
    };
    match c {
        P::App(s, _, a) if s == "dotk" && a.is_empty() => HeadPat::Dotk,
        P::App(s, _, a) if s == "kseq" && a.len() == 2 => match &a[0] {
            P::App(i, sorts, x) if i == "inj" && x.len() == 1 => match &x[0] {
                P::App(cs, _, _) if m.ctors.contains_key(cs) => HeadPat::Sym(cs.clone()),
                _ => match sorts.first().and_then(|s| s.name()) {
                    Some(sub) => HeadPat::Leaf(sub.to_string()),
                    None => HeadPat::Any,
                },
            },
            P::App(cs, _, _) if m.ctors.contains_key(cs) => HeadPat::Sym(cs.clone()),
            _ => HeadPat::Any,
        },
        _ => HeadPat::Any,
    }
}

impl HeadPat {
    fn fits(&self, hd: &Head) -> bool {
        match self {
            HeadPat::Any => true,
            HeadPat::Dotk => hd.dispatch.is_none(),
            HeadPat::Sym(s) => hd.sym.as_deref() == Some(s.as_str()),
            HeadPat::Leaf(l) => hd.leaf.as_deref() == Some(l.as_str()),
        }
    }
}

/// `k` inside the cells `levels` (outermost first) down to the cell `cell_lean`: each level's other
/// arguments named by `name(level, argument)`.
fn nest(
    levels: &[crate::invariants::Level],
    cell_lean: &str,
    k: &str,
    name: &dyn Fn(usize, usize) -> String,
) -> String {
    let mut inner = format!("{cell_lean} {}", paren(k));
    for (i, lv) in levels.iter().enumerate().rev() {
        let args: Vec<String> = (0..lv.arity)
            .map(|j| {
                if j == lv.index {
                    paren(&inner)
                } else {
                    name(i, j)
                }
            })
            .collect();
        inner = format!("{} {}", lv.lean, args.join(" "));
    }
    inner
}

/// The same as a `k2l_cases` pattern, with `inner` at the cell's content.
fn nest_pat(
    levels: &[crate::invariants::Level],
    inner: &str,
    name: &dyn Fn(usize, usize) -> String,
) -> String {
    let mut p = format!("⟨{inner}⟩");
    for (i, lv) in levels.iter().enumerate().rev() {
        let ps: Vec<String> = (0..lv.arity)
            .map(|j| if j == lv.index { p.clone() } else { name(i, j) })
            .collect();
        p = format!("⟨{}⟩", ps.join(", "));
    }
    p
}

/// `--progress` with `<k>` in the elements of a cell map (SND-14, `design.md` §3.9): one case per
/// head of an element's `<k>`. The case's element `e` is matched as the rules match it,
/// `concat (element kc e) rest = some m`; besides the invariant, the case assumes `Progress.Keys`
/// (every binding at its element's key cell, as in every K configuration; preserved by every
/// rule) and `Progress.Above` (every element of a higher rank is an ending). `progress` takes,
/// among the elements that are not endings, one of maximal rank (`MapHook.exists_maximal`), so a
/// case may read the state of an element it waits on when that element ranks higher; the rank (the
/// size of the key) is internal to the proof, and `progress` holds whatever it is.
fn emit_coll(
    cx: &Ctx,
    open_text: &str,
    hand_exists: bool,
    kpath: &CellPath,
) -> Result<Out, String> {
    let (m, ns, top) = (cx.m, cx.ns, cx.top);
    if kpath.colls.len() != 1 {
        return Err(
            "--progress: `<k>` is inside nested cell collections; not supported yet (SND-14)"
                .into(),
        );
    }
    let (coll, inner) = &kpath.colls[0];
    if coll.kind != Coll::Map {
        return Err(format!(
            "--progress: `<k>` is inside a cell collection that is not a cell map ({:?}); not supported yet (SND-14)",
            coll.kind
        ));
    }
    if cx.ranks > 1 {
        return Err("--progress: priority ranks are not supported yet (SND-15)".into());
    }
    let app = if cx.ranked { "App 0" } else { "App" };
    let (key_sort, elem_sort, map_sort) = (&coll.elems[0], &coll.elems[1], &coll.sort);
    let Some(el0) = inner.first() else {
        return Err("--progress: `<k>` is the element of its cell map".into());
    };
    let ector = &m.ctors[&el0.sym];
    let keyposs: Vec<usize> = ector
        .args
        .iter()
        .enumerate()
        .filter(|(j, a)| *a == key_sort && *j != el0.index)
        .map(|(j, _)| j)
        .collect();
    let [keypos] = keyposs.as_slice() else {
        return Err(format!(
            "--progress: the element {} has no single key cell {key_sort}",
            el0.lean
        ));
    };
    let keypos = *keypos;

    // the configuration with the cell map `m`, its other cells variables
    let mut sib_binders: Vec<(String, String)> = Vec::new();
    for (i, lv) in kpath.levels.iter().enumerate() {
        for (j, a) in m.ctors[&lv.sym].args.iter().enumerate() {
            if j != lv.index {
                sib_binders.push((format!("x{i}_{j}"), a.clone()));
            }
        }
    }
    let hargs = &m.ctors[&coll.holder_sym].args;
    for (j, a) in hargs.iter().enumerate() {
        if j != coll.index {
            sib_binders.push((format!("h_{j}"), a.clone()));
        }
    }
    let holder = |name: &dyn Fn(usize) -> String| -> String {
        let a: Vec<String> = (0..coll.holder_arity)
            .map(|j| {
                if j == coll.index {
                    "m".to_string()
                } else {
                    name(j)
                }
            })
            .collect();
        format!("{} {}", coll.holder_lean, a.join(" "))
    };
    let wrap = |inner_s: String, name: &dyn Fn(usize, usize) -> String| -> String {
        let mut cur = inner_s;
        for (i, lv) in kpath.levels.iter().enumerate().rev() {
            let args: Vec<String> = (0..lv.arity)
                .map(|j| {
                    if j == lv.index {
                        paren(&cur)
                    } else {
                        name(i, j)
                    }
                })
                .collect();
            cur = format!("{} {}", lv.lean, args.join(" "));
        }
        cur
    };
    let cfg = wrap(holder(&|j| format!("h_{j}")), &|i, j| format!("x{i}_{j}"));
    let cfg_pat = wrap(holder(&|_| "_".into()), &|_, _| "_".into());
    let mut dpat = {
        let a: Vec<String> = (0..coll.holder_arity)
            .map(|j| {
                if j == coll.index {
                    "m".to_string()
                } else {
                    format!("h_{j}")
                }
            })
            .collect();
        format!("⟨{}⟩", a.join(", "))
    };
    for (i, lv) in kpath.levels.iter().enumerate().rev() {
        let ps: Vec<String> = (0..lv.arity)
            .map(|j| {
                if j == lv.index {
                    dpat.clone()
                } else {
                    format!("x{i}_{j}")
                }
            })
            .collect();
        dpat = format!("⟨{}⟩", ps.join(", "));
    }
    // the element with `<k>` holding `k`, its key `kc`
    let mut elem_binders: Vec<(String, String)> = Vec::new();
    for (i, lv) in inner.iter().enumerate() {
        for (j, a) in m.ctors[&lv.sym].args.iter().enumerate() {
            if j != lv.index && !(i == 0 && j == keypos) {
                elem_binders.push((format!("e{i}_{j}"), a.clone()));
            }
        }
    }
    let ename = |i: usize, j: usize| -> String {
        if i == 0 && j == keypos {
            "kc".into()
        } else {
            format!("e{i}_{j}")
        }
    };
    let elem = |k: &str| nest(inner, &kpath.cell_lean, k, &ename);
    let edpat = nest_pat(inner, "kk", &ename);

    // the heads, and the rules whose first element has each
    let mut heads = heads_of(m, ns);
    for r in cx.rules {
        let h = kore_head(&r.kore.0, &kpath.cell_sym, m);
        for hd in heads.iter_mut() {
            if h.fits(hd) {
                hd.rules.push(format!("App.{}", r.lean));
            }
        }
    }

    // the unfolding sets
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
    if let Some(k) = &cx.kind2 {
        stuck.insert("Invariant".into());
        stuck.extend(k.unfold.iter().cloned());
    }
    stuck.insert("Ending.elem".into());
    stuck.insert("Ending.content".into());

    let mut defs = String::new();
    defs.push_str(&format!(
        "/-- The cell map of the `<{}>` cell. -/\ndef Progress.map : {top} → {map_sort}\n  | {cfg_pat} => m\n\n",
        coll.holder_name
    ));
    let key_pat: Vec<String> = (0..el0.arity)
        .map(|j| {
            if j == keypos {
                "k".to_string()
            } else {
                "_".to_string()
            }
        })
        .collect();
    defs.push_str(&format!(
        "/-- An element's key cell. -/\ndef Progress.key : {elem_sort} → {key_sort}\n  | {} {} => k\n\n\
/-- Every binding of the cell map is at its element's key cell, as in every K configuration (a rule matches a second\n\
element at the key it computes, then reads that element's cells). -/\n\
def Progress.Keys (c : {top}) : Prop :=\n  MapHook.EntriesOn (fun p => p.1 = Progress.key p.2) (Progress.map c)\n\n",
        el0.lean,
        key_pat.join(" ")
    ));
    // the ending of an element: the K function of a cell of the element, or `<k>` empty
    let (epath, ecell_lean, econtent, erhs) = match &cx.ending {
        Some((sym, cell)) => {
            let sig = cx
                .fns
                .get(sym)
                .ok_or_else(|| format!("--ending: the function {sym} is not generated"))?;
            let ep = find_cell(m, top, cell)?;
            if ep.colls.len() != 1 || ep.colls[0].0.holder_sym != coll.holder_sym {
                return Err(format!(
                    "--ending {cell}: with `<k>` in a cell map, the ending's cell must be in the same elements"
                ));
            }
            if let Some(es) = cx.eqns.get(sym) {
                stuck.extend(es.iter().cloned());
            }
            let rhs = if sig.partial { "some true" } else { "true" };
            (
                ep.colls[0].1.clone(),
                ep.cell_lean.clone(),
                ep.cell_args[0].clone(),
                format!("{} (Ending.content e) = {rhs}", sig.lean),
            )
        }
        None => (
            inner.clone(),
            kpath.cell_lean.clone(),
            "SortK".to_string(),
            "Ending.content e = SortK.dotk".to_string(),
        ),
    };
    let epat = nest(&epath, &ecell_lean, "x", &|_, _| "_".into());
    let rank_def = match &cx.rank {
        Some(r) => format!(
            "/-- The rank of an element in the proof of `progress` (not in its statement, which holds whatever the rank is):\n\
`{r}` (`--rank`), which reads the cell map. -/\n\
noncomputable def Progress.rank (m : {map_sort}) (k : {key_sort}) (e : {elem_sort}) : Nat := {r} m k e"
        ),
        None => format!(
            "/-- The rank of an element in the proof of `progress` (not in its statement, which holds whatever the rank is): the size\n\
of its key, so that an element is below the elements whose keys contain its key (ids derived from content). -/\n\
noncomputable def Progress.rank (_ : {map_sort}) (k : {key_sort}) (_ : {elem_sort}) : Nat := sizeOf k"
        ),
    };
    let what_end = match &cx.ending {
        Some((sym, cell)) => format!(
            "the K function `{}` is `true` of its `<{cell}>` cell",
            names::demangle(sym)
        ),
        None => "its `<k>` is empty (no `--ending`)".to_string(),
    };
    defs.push_str(&format!(
        "/-- The content of an element's cell that the ending reads. -/\ndef Ending.content : {elem_sort} → {econtent}\n  | {epat} => x\n\n\
/-- An element is an acceptable ending: {what_end}. -/\ndef Ending.elem (e : {elem_sort}) : Prop :=\n  {erhs}\n\n\
/-- The acceptable endings: every element of the cell map is one (stated over the matches `K |-> E REST` a rule sees). -/\n\
def Ending (c : {top}) : Prop :=\n  ∀ k e r, MapHook.concat (MapHook.element k e) r = some (Progress.map c) → Ending.elem e\n\n\
{rank_def}\n\n\
/-- Every element of a higher rank than `e` (at `k`) is an ending. -/\n\
def Progress.Above (m : {map_sort}) (k : {key_sort}) (e : {elem_sort}) : Prop :=\n  ∀ k' e' r', MapHook.concat (MapHook.element k' e') r' = some m → Progress.rank m k e < Progress.rank m k' e' → Ending.elem e'\n"
    ));
    if cx.invariant.is_none() {
        defs.push_str(&inv_def(cx, top));
    }
    let inv = "Invariant";

    let list =
        crate::refuted::parse(open_text).map_err(|e| format!("open-progress-cases.txt: {e}"))?;
    let strip = |n: &str| -> String { n.strip_prefix("Progress.case.").unwrap_or(n).to_string() };
    let open: BTreeSet<String> = list.names.iter().map(|n| strip(n)).collect();
    let refuted: BTreeSet<String> = list.refuted.keys().map(|n| strip(n)).collect();

    // the statements
    let all_binders = |hd: &Head| -> Vec<(String, String)> {
        let mut b: Vec<(String, String)> = hd.binders.clone();
        if hd.dispatch.is_some() {
            b.push(("R".into(), "SortK".into()));
        }
        b.extend(elem_binders.iter().cloned());
        b.push(("kc".into(), key_sort.clone()));
        b.push(("rest".into(), map_sort.clone()));
        b.push(("m".into(), map_sort.clone()));
        b.extend(sib_binders.iter().cloned());
        b
    };
    defs.push('\n');
    for hd in &heads {
        let bs: Vec<String> = all_binders(hd)
            .iter()
            .map(|(b, t)| format!("({b} : {t})"))
            .collect();
        let e = elem(&hd.k);
        defs.push_str(&format!(
            "/-- The head `{n}` of an element's `<k>`: a configuration with such an element that satisfies the invariant, where\n\
the element is not an ending and every element of a higher rank is, has a rule that applies. -/\n\
def Progress.case.{n}.statement : Prop :=\n  ∀ {}, MapHook.concat (MapHook.element kc ({e})) rest = some m →\n    {inv} ({cfg}) → ¬ Ending.elem ({e}) → Progress.Keys ({cfg}) → Progress.Above m kc ({e}) →\n    {app} ({cfg})\n\n",
            bs.join(" "),
            n = hd.name
        ));
    }

    // the proofs
    let close_list: Vec<String> = close.iter().cloned().collect();
    let stuck_list: Vec<String> = stuck.iter().cloned().collect();
    let mut rank_list: Vec<String> = Vec::new();
    for c in &m.sort(key_sort).own {
        rank_list.push(m.ctor_path(c));
        for a in &m.ctors[c].args {
            for c2 in &m.sort(a).own {
                rank_list.push(m.ctor_path(c2));
            }
        }
    }
    let other: Vec<String> = (0..el0.arity)
        .filter(|j| *j != keypos)
        .map(|j| format!("b{j}"))
        .collect();
    let partner_elem = {
        let a: Vec<String> = (0..el0.arity)
            .map(|j| {
                if j == keypos {
                    "k'".to_string()
                } else {
                    format!("b{j}")
                }
            })
            .collect();
        format!("{} {}", el0.lean, a.join(" "))
    };
    let partner_binders: Vec<String> = (0..el0.arity)
        .filter(|j| *j != keypos)
        .map(|j| format!("(b{j} : {})", ector.args[j]))
        .collect();
    let w_pat: Vec<String> = (0..el0.arity).map(|j| format!("b{j}")).collect();
    let sib_impl: Vec<String> = sib_binders
        .iter()
        .map(|(b, t)| format!("{{{b} : {t}}}"))
        .collect();
    let mut th = String::new();
    th.push_str(&format!(
        "set_option hygiene false in\n\
/-- A rule's remaining goals: its `requires` and collection facts, by unification, an assumption, or computing them\n\
(those without metavariables, and without the case's `Above` and `Keys`). -/\n\
local macro \"prog_close\" : tactic => `(tactic| first | rfl | assumption | (k2l_ground; clear hA hK; simp_all [{}]; done))\n\n\
set_option hygiene false in\n\
/-- No rule of the head applies: the invariant or the ending (the element's, or a partner's) is false. -/\n\
local macro \"prog_stuck\" : tactic => `(tactic| (exfalso; clear hA hK; simp_all [{}]; done))\n\n\
/-- A partner's key contains the case's key, so it ranks higher. -/\n\
local macro \"prog_rank\" : tactic => `(tactic| (simp only [Progress.rank]; simp [{}]; omega))\n\n\
/-- `k2l_preserve` with the unfolding set of `Progress.Keys`. -/\n\
local macro \"k2l_keys\" : tactic => `(tactic| k2l_preserve [Progress.Keys, Progress.map, Progress.key])\n\n\
{}/-- Every rule keeps `Progress.Keys`: its right-hand side binds each element at its key cell. -/\n\
theorem Progress.Keys.preserved : Preserved Step Progress.Keys :=\n  Step.preserves_of{}\n\n\
/-- A key bound in the rest of the case's match is a partner: its match in the rest, at its own key cell, and, when it\n\
ranks higher, that it is an ending. -/\n\
theorem Progress.partner {{kc k' : {key_sort}}} {{e : {elem_sort}}} {{rest m : {map_sort}}} {}\n    \
(hm : MapHook.concat (MapHook.element kc e) rest = some m) (hK : Progress.Keys ({cfg}))\n    \
(hA : Progress.Above m kc e) (hin : MapHook.inKeys k' rest = true) :\n    \
∃ {} (r1 : {map_sort}), MapHook.concat (MapHook.element k' ({partner_elem})) r1 = some rest ∧\n      \
(Progress.rank m kc e < Progress.rank m k' ({partner_elem}) → Ending.elem ({partner_elem})) := by\n  \
obtain ⟨w, r1, r2, h1, h2⟩ := MapHook.concat_element_of_inKeys_rest hm hin\n  \
have hk := MapHook.entry_of_concat_element h2 hK\n  \
k2l_cases w with ⟨{}⟩\n  all_goals k2l_norm_idx\n  simp only [Progress.key] at hk\n  subst hk\n  \
exact ⟨{}, r1, h1, fun h => hA _ _ _ h2 h⟩\n\n",
        close_list.join(", "),
        stuck_list.join(", "),
        rank_list.join(", "),
        cx.rules
            .iter()
            .map(|r| format!(
                "/-- Rule `{}` keeps `Progress.Keys`. -/\ntheorem Progress.Keys.case.{} : Step.Case.{} Progress.Keys := by k2l_keys\n\n",
                r.name, r.lean, r.lean
            ))
            .collect::<String>(),
        cx.rules
            .iter()
            .map(|r| format!("\n    Progress.Keys.case.{}", r.lean))
            .collect::<String>(),
        sib_impl.join(" "),
        partner_binders.join(" "),
        w_pat.join(", "),
        other.join(", "),
    ));
    let fail = "fail \"no rule of this head applies, and the invariant and the endings do not exclude it\"";
    // the element's fact from the invariant (`--element-fact`): unfolded, split, its equations
    // substituted, so that the search and the stuck closer read it
    let fact = cx.element_fact.as_ref().map(|f| {
        let u: Vec<String> = cx.kind2.iter().flat_map(|k| k.unfold.iter().cloned()).collect();
        format!(
            "  have hF := {f} hI hm\n  try simp [{}] at hF\n  k2l_destruct\n  all_goals try subst_vars",
            u.join(", ")
        )
    });
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
        let xs: Vec<String> = (0..all_binders(hd).len())
            .map(|i| format!("y{i}"))
            .collect();
        let tac = if hd.rules.is_empty() {
            format!("  first | prog_stuck | {fail}")
        } else {
            format!(
                "  k2l_progress [{}] => prog_close else prog_stuck partner (Progress.partner hm hK hA) rank prog_rank\n  all_goals first | prog_stuck | {fail}",
                hd.rules.join(", ")
            )
        };
        th.push_str(&format!(
            "set_option maxHeartbeats {CASE_BUDGET} in\ntheorem Progress.case.{n} : Progress.case.{n}.statement := by\n  intro {} hm hI hE hK hA\n  k2l_entries hm [hI]\n{}\n\n",
            xs.join(" "),
            match &fact {
                Some(f) => format!("{f}\n  all_goals (\n  {}\n  )", tac.trim_start()),
                None => tac,
            },
            n = hd.name
        ));
    }

    // `progress`
    let refuted_heads: Vec<&Head> = heads.iter().filter(|h| refuted.contains(&h.name)).collect();
    let concl = if refuted_heads.is_empty() {
        format!("Ending c ∨ {app} c")
    } else {
        for hd in &refuted_heads {
            let bs: Vec<String> = all_binders(hd)
                .iter()
                .map(|(b, t)| format!("({b} : {t})"))
                .collect();
            defs.push_str(&format!(
                "\n/-- The configurations with an element whose head of `<k>` is `{n}` (a refuted case). -/\ndef Progress.case.{n}.at (c : {top}) : Prop :=\n  ∃ {}, c = {cfg} ∧ MapHook.concat (MapHook.element kc ({})) rest = some m\n",
                bs.join(" "),
                elem(&hd.k),
                n = hd.name
            ));
        }
        let ats: Vec<String> = refuted_heads
            .iter()
            .map(|h| format!("Progress.case.{}.at c", h.name))
            .collect();
        defs.push_str(&format!(
            "\n/-- The configurations at the heads whose case is refuted: stuck configurations the invariant allows. -/\ndef Progress.Refuted (c : {top}) : Prop :=\n  {}\n",
            ats.join(" ∨ ")
        ));
        format!("Ending c ∨ {app} c ∨ Progress.Refuted c")
    };
    let case_term = |hd: &Head| -> String {
        let n = all_binders(hd).len();
        match refuted_heads.iter().position(|h| h.name == hd.name) {
            Some(i) => {
                let mut w = format!("⟨{}, rfl, hm⟩", vec!["_"; n].join(", "));
                if i + 1 < refuted_heads.len() {
                    w = format!("Or.inl {w}");
                }
                for _ in 0..i {
                    w = format!("Or.inr ({w})");
                }
                format!("Or.inr ({w})")
            }
            None => {
                let t = format!(
                    "Progress.case.{} {} hm hI hne hK hA",
                    hd.name,
                    vec!["_"; n].join(" ")
                );
                if refuted_heads.is_empty() {
                    t
                } else {
                    format!("Or.inl ({t})")
                }
            }
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
        if hs[0].dispatch.as_ref().unwrap().1 {
            let arms: Vec<String> = hs
                .iter()
                .map(|h| format!("| exact {}", case_term(h)))
                .collect();
            leaf_arms.push(format!(
                "| (k2l_has_ctor_at hm [{inj}]\n             k2l_cases x <;> k2l_norm_idx\n             all_goals first\n               {}\n             done)",
                arms.join("\n               ")
            ));
        } else {
            leaf_arms.push(format!(
                "| (k2l_has_ctor_at hm [{inj}]\n             exact {})",
                case_term(hs[0])
            ));
        }
    }
    let dotk = heads.iter().find(|h| h.dispatch.is_none()).unwrap();
    let what = if refuted_heads.is_empty() {
        "an ending, or some rule applies"
    } else {
        "an ending, some rule applies, or it has an element at a head whose case is refuted (`Progress.Refuted`)"
    };
    th.push_str(&format!(
        "/-- No stuck configuration: one that satisfies the invariant (and whose bindings are at their key cells) is {what}.\n\
Among the elements that are not endings, the case of one of maximal rank applies. -/\n\
theorem progress (c : {top}) (hI : {inv} c) (hK : Progress.Keys c) : {concl} := by\n  \
by_cases hE : Ending c\n  · exact Or.inl hE\n  right\n  \
have hx : ∃ k e r, MapHook.concat (MapHook.element k e) r = some (Progress.map c) ∧ ¬ Ending.elem e := by\n    \
simp only [Ending, Classical.not_forall] at hE\n    obtain ⟨k, e, r, h, hn⟩ := hE\n    exact ⟨k, e, r, h, hn⟩\n  \
obtain ⟨k, e, r, hm, hne, hA⟩ := MapHook.exists_maximal (P := fun _ e => Ending.elem e) (Progress.rank (Progress.map c)) hx\n  \
have hk := MapHook.entry_of_concat_element hm hK\n  \
k2l_cases c with {dpat}\n  all_goals k2l_norm_idx\n  \
k2l_cases e with {edpat}\n  all_goals k2l_norm_idx\n  \
simp only [Progress.key] at hk\n  subst hk\n  \
k2l_cases kk with ⟨it, R⟩\n  all_goals k2l_norm_idx\n  all_goals first\n    | exact {}\n    | (k2l_cases it with ⟨x⟩\n       all_goals k2l_norm_idx\n       all_goals first\n          {}\n       done)\n\n",
        case_term(dotk),
        leaf_arms.join("\n          ")
    ));
    let concl_s = concl.replace(" c", " (s n)");
    th.push_str(&format!(
        "/-- From a configuration that satisfies the invariant and `Progress.Keys`, every configuration reached is {what}. -/\n\
theorem no_stuck {{c0 c : {top}}} (h0 : {inv} c0) (hk0 : Progress.Keys c0) (h : Star Step c0 c) : {concl} :=\n  \
progress c (Invariant.preserved.star h h0) (Progress.Keys.preserved.star h hk0)\n\n\
/-- The same, on every run from `c0` (`KPrelude.Paths`: a run that halts repeats its last configuration). -/\n\
theorem always {{c0 : {top}}} (h0 : {inv} c0) (hk0 : Progress.Keys c0) :\n    ∀ s, s 0 = c0 → Paths.IsRun Step s → ∀ n, {concl_s} :=\n  \
Paths.always_iff.2 fun c h =>\n    progress c (Preserved.star Invariant.preserved h h0) (Preserved.star Progress.Keys.preserved h hk0)\n\n\
#k2l_assert_axioms progress no_stuck always\n{}",
        refuted_heads.iter().map(|h| format!("#k2l_refuted Progress.case.{}\n", h.name)).collect::<String>(),
    ));
    let n_heads = heads.len();
    finish(
        cx,
        Finish {
            defs,
            th,
            open_text,
            open: &open,
            refuted: &refuted,
            stuck_list: &stuck_list,
            hand_exists,
            n_heads,
            coll: true,
            doc: format!(
                "`progress`: a configuration that satisfies `{inv}` (and whose cell map binds each element at its key cell,\n\
`Progress.Keys`) is an acceptable ending (`Ending`: every element is one) or some rule applies (`App`), so no such\n\
configuration is stuck, and in particular no set of elements waits on each other. One case per head of an element's\n\
`<k>` ({n_heads} heads), each by `k2l_progress` among the rules whose first element has that head, reading the state of\n\
an element it waits on (a partner) where that element ranks higher; the cases listed in `open-progress-cases.txt` come\n\
from `ProgressHand.lean`. `no_stuck` and `always` extend it to every configuration reached."
            ),
        },
    )
}
