//! The functions part of `k2lean diff` (`casediff.rs`): the generated functions whose definitions
//! changed between two generations, and the rules whose cases call them.
//!
//! **What is compared.** A rule's case `Step.Case.r P` (`{ns}/Preserves.lean`) mentions the
//! generated functions its side conditions and right-hand side call (`K.f …`); what the case says
//! depends on their definitions in `{ns}/Functions.lean`, which `gen` writes from the function's
//! K equations. So a case whose text is equal in two generations means something else when a
//! function it calls, directly or through other generated functions, is defined differently.
//! Each function is the text of its declarations (`def K.f`, the equation steps `K.f.ruleN`, its
//! termination measure), compared after trimming trailing white space; the generator writes
//! them deterministically from the equations, so equal equations give equal text, and a changed
//! equation, an added or removed one, or a changed priority changes it. The comparison is of text:
//! renaming a variable of an equation also reports its function as changed.
//!
//! **Who calls a function.** Function `g` calls `f` when the declarations of `g` mention a name
//! that `f`'s declarations define; a rule calls `f` when its case mentions such a name, or calls
//! a function that calls `f`, transitively (in the new generation; in the old one for a
//! removed function). A kind 1 invariant (`{ns}/InvariantDefs.lean`, when present) calls the
//! functions its definitions mention: when one of them changed, the meaning of `Invariant`
//! changed, so every case of it did.
//!
//! Hooked functions are the prelude's (`KPrelude`) and the parameters of `class Hooks` have no
//! definition; neither is compared.

use crate::casediff::tokens;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// One generated function.
#[derive(Clone, Debug)]
pub struct Func {
    /// The Lean name of its value (`K.isId`, `K.«typeOf(_,_)_…»`).
    pub name: String,
    /// The K label the generated header prints (`isId`, `typeOf(_,_)_IMP-TYPING_Type_Expr_Map`).
    pub label: String,
    /// Its declarations' text, each line's trailing white space trimmed.
    pub text: String,
    /// The names its declarations define (`K.f`, `K.f.rule1`, `K.f.rank0`).
    pub defs: BTreeSet<String>,
    /// The other functions it mentions (their `name`s).
    pub calls: BTreeSet<String>,
}

/// The function `name` of a generated definition name: `K.f.rule1` and `K.f.rank0` are `K.f`'s
/// equation steps and termination ranks.
fn base(name: &str) -> String {
    for suffix in [".rule", ".rank"] {
        if let Some(k) = name.rfind(suffix) {
            let tail = &name[k + suffix.len()..];
            if !tail.is_empty() && tail.chars().all(|c| c.is_ascii_digit()) {
                return name[..k].to_string();
            }
        }
    }
    name.to_string()
}

/// A line that starts a top-level declaration or command of a generated module.
fn starts_decl(l: &str) -> bool {
    const KW: [&str; 21] = [
        "def ",
        "theorem ",
        "lemma ",
        "abbrev ",
        "instance ",
        "class ",
        "structure ",
        "inductive ",
        "noncomputable ",
        "private ",
        "partial ",
        "@[",
        "/-",
        "mutual",
        "end",
        "variable ",
        "set_option ",
        "namespace ",
        "open ",
        "import ",
        "--",
    ];
    KW.iter().any(|k| l.starts_with(k))
}

/// The label of a header comment: ``/-! `label` … -/`` or ``/-- `label` (recursive) -/``.
fn header_label(l: &str) -> Option<String> {
    let r = l.strip_prefix("/-!").or_else(|| l.strip_prefix("/--"))?;
    let r = r.trim_start().strip_prefix('`')?;
    r.find('`').map(|e| r[..e].to_string())
}

/// The functions of a `Functions.lean`, by name.
pub fn parse_functions(text: &str) -> BTreeMap<String, Func> {
    let mut out: BTreeMap<String, Func> = BTreeMap::new();
    let mut label: Option<String> = None;
    // the function the current declaration belongs to (`None`: not a function's)
    let mut cur: Option<String> = None;
    for l in text.lines() {
        if starts_decl(l) {
            cur = None;
            if let Some(h) = header_label(l) {
                label = Some(h);
                continue;
            }
            let after = l
                .strip_prefix("def ")
                .or_else(|| l.strip_prefix("noncomputable def "))
                .or_else(|| l.strip_prefix("partial def "));
            if let Some(rest) = after {
                let n = tokens(rest).into_iter().next().unwrap_or_default();
                if n.starts_with("K.") {
                    let b = base(&n);
                    let f = out.entry(b.clone()).or_insert_with(|| Func {
                        name: b.clone(),
                        label: label.clone().unwrap_or_else(|| b.clone()),
                        text: String::new(),
                        defs: BTreeSet::new(),
                        calls: BTreeSet::new(),
                    });
                    f.defs.insert(n);
                    cur = Some(b);
                }
            }
        }
        if let Some(b) = &cur {
            let f = out.get_mut(b).expect("current function");
            f.text.push_str(l.trim_end());
            f.text.push('\n');
        }
    }
    let owner = owners(&out);
    let calls: Vec<(String, BTreeSet<String>)> = out
        .values()
        .map(|f| {
            let mut c = mentioned(&f.text, &owner);
            c.remove(&f.name);
            (f.name.clone(), c)
        })
        .collect();
    for (n, c) in calls {
        out.get_mut(&n).unwrap().calls = c;
    }
    out
}

/// Every defined name, to the function that defines it.
pub fn owners(fs: &BTreeMap<String, Func>) -> BTreeMap<String, String> {
    fs.values()
        .flat_map(|f| f.defs.iter().map(move |d| (d.clone(), f.name.clone())))
        .collect()
}

/// The functions `text` mentions: tokens equal to a defined name, or ending in `.` and one (a
/// name qualified by the library's namespace).
pub fn mentioned(text: &str, owner: &BTreeMap<String, String>) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for t in tokens(text) {
        if !t.contains("K.") {
            continue;
        }
        if let Some(f) = owner.get(&t) {
            out.insert(f.clone());
            continue;
        }
        // `NS.K.f`: try every suffix that starts after a `.`
        let mut from = 0;
        while let Some(k) = t[from..].find(".K.") {
            let at = from + k + 1;
            if let Some(f) = owner.get(&t[at..]) {
                out.insert(f.clone());
                break;
            }
            from = at;
        }
    }
    out
}

/// The functions reachable from `roots` along `calls`.
pub fn reach(fs: &BTreeMap<String, Func>, roots: &BTreeSet<String>) -> BTreeSet<String> {
    let mut seen = BTreeSet::new();
    let mut todo: Vec<String> = roots.iter().cloned().collect();
    while let Some(f) = todo.pop() {
        if !seen.insert(f.clone()) {
            continue;
        }
        if let Some(x) = fs.get(&f) {
            todo.extend(x.calls.iter().filter(|c| !seen.contains(*c)).cloned());
        }
    }
    seen
}

/// The functions of a library directory (`NS/Functions.lean` next to `NS/Preserves.lean`), and
/// those its kind 1 invariant mentions (`NS/InvariantDefs.lean`), when the files exist.
pub fn load(preserves: &Path) -> (BTreeMap<String, Func>, Option<BTreeSet<String>>) {
    let dir = preserves
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_default();
    let fs = std::fs::read_to_string(dir.join("Functions.lean"))
        .map(|t| parse_functions(&t))
        .unwrap_or_default();
    let inv = std::fs::read_to_string(dir.join("InvariantDefs.lean"))
        .ok()
        .map(|t| reach(&fs, &mentioned(&t, &owners(&fs))));
    (fs, inv)
}

/// What happened to one function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnStatus {
    Changed,
    Added,
    Removed,
}

/// A function that differs, and the rules (of the generation it is in: the new one, the old one
/// for a removed function) whose cases call it.
#[derive(Clone, Debug)]
pub struct FnEntry {
    pub name: String,
    pub label: String,
    pub status: FnStatus,
    pub rules: Vec<String>,
    /// The kind 1 invariant calls it.
    pub invariant: bool,
}

/// One rule's case as the comparison reads it: its name and the text of its statement.
pub struct RuleText<'a> {
    pub name: &'a str,
    pub text: String,
}

/// Compare the functions of two generations; `old_rules` and `new_rules` are the rules' cases.
pub fn compare(
    old: &BTreeMap<String, Func>,
    new: &BTreeMap<String, Func>,
    old_inv: &Option<BTreeSet<String>>,
    new_inv: &Option<BTreeSet<String>>,
    old_rules: &[RuleText],
    new_rules: &[RuleText],
) -> (Vec<FnEntry>, usize) {
    // the functions each rule calls, transitively
    let callers = |fs: &BTreeMap<String, Func>, rules: &[RuleText]| {
        let owner = owners(fs);
        let mut by_fn: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for r in rules {
            for f in reach(fs, &mentioned(&r.text, &owner)) {
                by_fn.entry(f).or_default().push(r.name.to_string());
            }
        }
        by_fn
    };
    let (oc, nc) = (callers(old, old_rules), callers(new, new_rules));
    let mut out = Vec::new();
    let mut unchanged = 0;
    for (n, f) in new {
        let status = match old.get(n) {
            Some(o) if o.text == f.text => {
                unchanged += 1;
                continue;
            }
            Some(_) => FnStatus::Changed,
            None => FnStatus::Added,
        };
        out.push(FnEntry {
            name: n.clone(),
            label: f.label.clone(),
            status,
            rules: nc.get(n).cloned().unwrap_or_default(),
            invariant: new_inv.as_ref().is_some_and(|s| s.contains(n)),
        });
    }
    for (n, f) in old {
        if !new.contains_key(n) {
            out.push(FnEntry {
                name: n.clone(),
                label: f.label.clone(),
                status: FnStatus::Removed,
                rules: oc.get(n).cloned().unwrap_or_default(),
                invariant: old_inv.as_ref().is_some_and(|s| s.contains(n)),
            });
        }
    }
    (out, unchanged)
}

/// A hand-written mention of a function that differs: its K function (`K.f`) or one of its
/// generated K equations (`Eqn.«f_1»`).
#[derive(Clone, Debug)]
pub struct FnRef {
    pub func: String,
    pub file: PathBuf,
    pub line: usize,
}

/// The mentions of the functions `fs` (that differ) in `files`.
pub fn hand_refs(files: &[(PathBuf, String)], fs: &[&FnEntry]) -> Vec<FnRef> {
    // `Eqn.«label_N»`: the equation theorems are named by the K label and the equation's number
    let eqn_of = |t: &str| -> Option<String> {
        let r = t.rsplit_once("Eqn.").map(|(_, r)| r)?;
        let r = r.trim_start_matches('«').trim_end_matches('»');
        let (l, n) = r.rsplit_once('_')?;
        (!n.is_empty() && n.chars().all(|c| c.is_ascii_digit())).then(|| l.to_string())
    };
    let mut out = Vec::new();
    for (file, text) in files {
        for (ln, line) in text.lines().enumerate() {
            let toks = tokens(line);
            for f in fs {
                // `K.f`, qualified (`NS.K.f`) or not, or one of its declarations (`K.f.rule1`,
                // `K.f.eq_def`)
                let names_it = |t: &str| {
                    t.match_indices(f.name.as_str()).any(|(at, m)| {
                        (at == 0 || t[..at].ends_with('.'))
                            && (at + m.len() == t.len() || t[at + m.len()..].starts_with('.'))
                    })
                };
                let hit = toks.iter().any(|t| {
                    names_it(t)
                        || eqn_of(t)
                            .is_some_and(|l| l == f.label || crate::names::ident(&f.label) == l)
                });
                if hit {
                    out.push(FnRef {
                        func: f.name.clone(),
                        file: file.clone(),
                        line: ln + 1,
                    });
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const OLD: &str = "import X.Terms\n\nnamespace X\n\n/-! `inc` -/\ndef K.inc.rule1 (x0 : SortNat) : Option SortNat :=\n  some (SortNat.s x0)\ndef K.inc (x0 : SortNat) : Option SortNat :=\n  K.inc.rule1 x0\n\n/-! `twice` -/\ndef K.twice (x0 : SortNat) : Option SortNat :=\n  (K.inc x0).bind K.inc\n\n/-! `«len»` (recursive) -/\ndef K.«len(_)» (x0 : SortNat) : Option SortNat :=\n  match x0 with\n  | _ => none\ntermination_by x0\n\nend X\n";

    #[test]
    fn functions_are_their_declarations_and_calls() {
        let fs = parse_functions(OLD);
        assert_eq!(
            fs.keys().cloned().collect::<Vec<_>>(),
            ["K.inc", "K.twice", "K.«len(_)»"]
        );
        assert_eq!(fs["K.inc"].label, "inc");
        assert!(fs["K.inc"].defs.contains("K.inc.rule1"));
        assert!(fs["K.inc"].calls.is_empty(), "{:?}", fs["K.inc"].calls);
        assert_eq!(fs["K.twice"].calls, BTreeSet::from(["K.inc".to_string()]));
        assert!(fs["K.«len(_)»"].text.contains("termination_by x0"));
        assert!(!fs["K.twice"].text.contains("end X"));
    }

    #[test]
    fn a_changed_function_names_the_rules_that_call_it_transitively() {
        let new = OLD.replace("some (SortNat.s x0)", "some (SortNat.s (SortNat.s x0))");
        let (o, n) = (parse_functions(OLD), parse_functions(&new));
        let rules = [
            RuleText {
                name: "a",
                text: "P (c (K.twice X))".into(),
            },
            RuleText {
                name: "b",
                text: "P (c X)".into(),
            },
            RuleText {
                name: "c",
                text: "hr : X.K.inc Y = some Z".into(),
            },
        ];
        let inv = Some(BTreeSet::from(["K.twice".to_string(), "K.inc".to_string()]));
        let (es, unchanged) = compare(&o, &n, &inv, &inv, &rules, &rules);
        assert_eq!(unchanged, 2);
        assert_eq!(es.len(), 1);
        assert_eq!(es[0].name, "K.inc");
        assert_eq!(es[0].status, FnStatus::Changed);
        assert_eq!(es[0].rules, ["a", "c"]);
        assert!(es[0].invariant);
        let refs = hand_refs(
            &[(
                PathBuf::from("H.lean"),
                "simp [Eqn.inc_1]\nexact K.twice\nrw [X.K.inc.rule1]\n".into(),
            )],
            &es.iter().collect::<Vec<_>>(),
        );
        assert_eq!(refs.iter().map(|r| r.line).collect::<Vec<_>>(), [1, 3]);
    }
}
