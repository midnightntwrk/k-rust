//! `k2lean confluence`: the determinism of observations modulo scheduling, as a scaffold
//! (`k2lean/docs/design.md`, section 3.6).
//!
//! Statement, for a program hypothesis `H` (a preserved predicate the hand module supplies) and
//! an observation `obs` (a projection of configuration cells, `--obs`):
//! `H c → Star Step c n₁ → Terminal Step n₁ → Star Step c n₂ → Terminal Step n₂ → n₁ = n₂`, hence
//! `obs n₁ = obs n₂`. It follows from the diamond property (`KPrelude.terminal_unique_of_diamond`,
//! no termination hypothesis) or, with `--join local`, from local confluence and a measure every
//! step decreases (Newman's lemma, `terminal_unique_of_local`; the hand module supplies `μ` and
//! `μ_dec`).
//!
//! The joins are one obligation per ordered pair of rules (`pair.r₁.r₂`): two instances of the
//! rules whose left-hand sides are one configuration have successors that join. Each is
//! attempted by generic arguments, in order: the instances are refuted (the left-hand sides do
//! not unify, `cases`), or are one instance (the same successor), or act at two bindings of a cell
//! map matched at a free key (threads) and commute (`MapHook.concat_element_same_or_comm`), or
//! one updates a binding and the other inserts a fresh one (`concat_element_comm_insert`), or
//! each applies after the other unchanged; the two final states are closed by `k2l_join_eq`
//! (equal up to the commutativity of integer addition). The pairs listed in `--open` are the hand
//! module's (`hand.pair.r₁.r₂`, of the same type).
//!
//! The report (`--report`) classifies the pairs without Lean: by the pair classifier of
//! `pairs.rs` with two free-key matches taken as one binding (`clash`, `exclusive`, `joinable`,
//! `overlap`), and, for two rules that match one cell map at free keys, by their footprints on
//! the other cells (`independent`: neither writes a cell the other reads or writes, so they
//! commute by the map lemma; `conflict`: the cells they race on). `--report-only` writes only
//! the report (definitions whose `Lean` module of n² pairs is beyond a gate's budget, SIMPLE).

use crate::ir::{self, Def, P};
use crate::lower::L;
use crate::model::Model;
use crate::rules::{self, Rule};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

fn fail(msg: &str) -> ! {
    eprintln!("confluence: {msg}");
    std::process::exit(2)
}

fn write_file(path: &str, text: &str) {
    let p = std::path::Path::new(path);
    if let Some(d) = p.parent().filter(|d| !d.as_os_str().is_empty()) {
        std::fs::create_dir_all(d)
            .unwrap_or_else(|e| fail(&format!("cannot create {}: {e}", d.display())));
    }
    std::fs::write(p, text).unwrap_or_else(|e| fail(&format!("cannot write {path}: {e}")));
}

pub(crate) struct Lib {
    pub def: Def,
    pub m: Model,
    pub rules: Vec<Rule>,
    pub prios: Vec<i64>,
    pub ranked: bool,
    pub top: String,
}

pub(crate) fn load(kore: &str) -> Lib {
    let text = std::fs::read_to_string(kore).unwrap_or_else(|e| fail(&format!("{kore}: {e}")));
    let def = ir::load(&text).unwrap_or_else(|e| fail(&format!("{kore}: {e:?}")));
    let m = Model::build(&def).unwrap_or_else(|e| fail(&e));
    let mut roots = BTreeSet::new();
    for ax in &def.axioms {
        if let P::Rewrites(_, l, _) = &ax.pattern
            && rules::absent_sort(l, &m).is_none()
        {
            crate::funcs::applied(&ax.pattern, &def, &mut roots);
        }
    }
    roots.extend(m.anywhere.iter().cloned());
    let fgen = crate::funcs::generate(&def, &m, &roots)
        .unwrap_or_else(|e| fail(&format!("functions: {e}")));
    let (rules, prios, ranked) =
        rules::collect_ranked(&def, &m, &fgen.fns, &[]).unwrap_or_else(|e| fail(&e));
    let top = rules::top_sort(&def).unwrap_or_else(|e| fail(&e));
    Lib {
        def,
        m,
        rules,
        prios,
        ranked,
        top,
    }
}

const MAP_HYP: &str = "KPrelude.MapHook.concat (KPrelude.MapHook.element";

/// A map hypothesis `concat (element K V) REST = some X`: (REST, X).
fn map_hyp(h: &str) -> Option<(String, String)> {
    if !h.starts_with(MAP_HYP) {
        return None;
    }
    let (lhs, x) = h.rsplit_once(" = some ")?;
    let rest = lhs.rsplit(' ').next()?;
    let ok = |t: &str| !t.is_empty() && !t.contains(['(', ')']);
    (ok(rest) && ok(x)).then(|| (rest.to_string(), x.trim().to_string()))
}

/// How a rule uses a cell map matched at a free key.
#[derive(Clone, Debug, PartialEq)]
enum MapRole {
    /// `hm : (K ↦ V) R = some m` on the left, `hr : (K ↦ W) R = some r` on the right: an update
    /// of one binding.
    Update { hm: String, hr: String },
    /// `hr : (K ↦ W) M = some r` with `M` the cell's content on the left: an insertion.
    Insert { hr: String },
    None,
}

fn map_role(r: &Rule) -> MapRole {
    let lhs_hyps: BTreeSet<&String> = r.app.hyps.iter().map(|(h, _)| h).collect();
    // only maps that are a cell's whole content: the free-key cell maps of the configuration,
    // not maps matched inside a binding (an environment, a store at a bound key)
    let in_lhs = cell_vars(&r.step.index);
    let in_rhs = cell_vars(&r.rhs.subst(&r.step.subst));
    let mut matches = vec![];
    let mut results = vec![];
    for (h, p) in &r.step.hyps {
        let Some((rest, x)) = map_hyp(p) else {
            continue;
        };
        if lhs_hyps.contains(h) {
            if in_lhs.contains(&x) && free_key(r, h, p) {
                matches.push((h.clone(), rest, x));
            }
        } else if in_rhs.contains(&x) {
            results.push((h.clone(), rest, x));
        }
    }
    if let [(hm, rest, _)] = matches.as_slice() {
        let rs: Vec<&(String, String, String)> = results.iter().filter(|(_, r2, _)| r2 == rest).collect();
        return match rs.as_slice() {
            [(hr, _, _)] => MapRole::Update {
                hm: hm.clone(),
                hr: hr.clone(),
            },
            _ => MapRole::None,
        };
    }
    match results.as_slice() {
        [(hr, rest, _)] if matches.is_empty() && in_lhs.contains(rest) => {
            MapRole::Insert { hr: hr.clone() }
        }
        _ => MapRole::None,
    }
}

/// Whether the key of a map hypothesis is free: none of its variables occurs in the left-hand
/// side's index or in another left-hand-side hypothesis (a key bound elsewhere, such as a store
/// location read off `<k>`, makes the match unique).
fn free_key(r: &Rule, h: &str, p: &str) -> bool {
    let Some(rest) = p.strip_prefix(MAP_HYP) else {
        return false;
    };
    let key = first_arg(rest.trim_start());
    let words = |t: &str| -> BTreeSet<String> {
        t.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
            .filter(|w| !w.is_empty() && w.chars().next().is_some_and(|c| c.is_lowercase() || c.is_uppercase()))
            .map(String::from)
            .collect()
    };
    let binders: BTreeSet<&String> = r.step.binders.iter().map(|(b, _)| b).collect();
    let kv: BTreeSet<String> = words(key).into_iter().filter(|w| binders.contains(w)).collect();
    if kv.is_empty() {
        return false;
    }
    let mut elsewhere = r.step.index.render();
    for (h2, p2) in &r.app.hyps {
        if h2 != h {
            elsewhere.push(' ');
            elsewhere.push_str(p2);
        }
    }
    let ew = words(&elsewhere);
    kv.iter().all(|v| !ew.contains(v))
}

/// The first argument of an application's argument list (`(a b) c` → `(a b)`, `k c` → `k`).
fn first_arg(t: &str) -> &str {
    if t.starts_with('(') {
        let mut d = 0;
        for (i, ch) in t.char_indices() {
            match ch {
                '(' => d += 1,
                ')' => {
                    d -= 1;
                    if d == 0 {
                        return &t[..=i];
                    }
                }
                _ => {}
            }
        }
        t
    } else {
        t.split(' ').next().unwrap_or(t)
    }
}

/// The variables that are the whole content of a cell.
fn cell_vars(l: &L) -> BTreeSet<String> {
    fn go(l: &L, out: &mut BTreeSet<String>) {
        if let L::App(h, a) = l {
            if is_cell(h).is_some()
                && let [L::Var(v)] = a.as_slice()
            {
                out.insert(v.clone());
            }
            a.iter().for_each(|x| go(x, out));
        }
    }
    let mut out = BTreeSet::new();
    go(l, &mut out);
    out
}

fn is_cell(head: &str) -> Option<String> {
    let i = head.find(".«<")?;
    let name = head[i + ".«<".len()..].strip_suffix(">»")?;
    Some(name.to_string())
}

/// The cells a rule reads and writes, outside the bindings of free-key cell maps: a leaf cell
/// is written when its right-hand side differs from its left-hand side, and read when its
/// left-hand side is not a variable or its variable occurs elsewhere (another cell, a side
/// condition). A cell map's content is reported under the map cell's name.
fn footprint(r: &Rule) -> BTreeMap<String, (bool, bool)> {
    let lhs = &r.step.index;
    let rhs = r.rhs.subst(&r.step.subst);
    let hyps: String = r
        .step
        .hyps
        .iter()
        .map(|(_, p)| p.as_str())
        .collect::<Vec<_>>()
        .join(" ");
    let mut leaves: Vec<(String, L, L)> = vec![];
    fn walk(a: &L, b: &L, out: &mut Vec<(String, L, L)>, name: Option<String>) {
        if let (L::App(ha, xa), L::App(hb, xb)) = (a, b)
            && ha == hb
            && xa.len() == xb.len()
            && xa.iter().any(|x| matches!(x, L::App(h, _) if is_cell(h).is_some()))
        {
            for (x, y) in xa.iter().zip(xb) {
                let n = match x {
                    L::App(h, _) => is_cell(h),
                    _ => None,
                };
                walk(x, y, out, n);
            }
            return;
        }
        out.push((name.unwrap_or_else(|| "?".into()), a.clone(), b.clone()));
    }
    walk(lhs, &rhs, &mut leaves, None);
    let rendered: Vec<String> = leaves
        .iter()
        .map(|(_, a, b)| format!("{} {}", a.render(), b.render()))
        .collect();
    let mut out: BTreeMap<String, (bool, bool)> = BTreeMap::new();
    for (i, (name, a, b)) in leaves.iter().enumerate() {
        // a leaf that is a variable standing for a whole cell: name it by the variable's type
        let name = if name == "?" {
            match a {
                L::Var(v) => r
                    .step
                    .binders
                    .iter()
                    .find(|(x, _)| x == v)
                    .map(|(_, t)| t.trim_start_matches("Sort").to_string())
                    .unwrap_or_else(|| "?".into()),
                _ => "?".into(),
            }
        } else {
            name.clone()
        };
        let write = a.render() != b.render();
        let elsewhere = |v: &String| {
            let occurs = |t: &str| {
                t.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
                    .any(|w| w == v)
            };
            occurs(&hyps)
                || rendered
                    .iter()
                    .enumerate()
                    .any(|(j, t)| j != i && occurs(t))
        };
        let read = match a {
            L::Var(v) => elsewhere(v),
            _ => true,
        };
        let e = out.entry(name).or_default();
        e.0 |= read;
        e.1 |= write;
    }
    out
}

/// The cells two rules race on: one writes what the other reads or writes, outside `map`.
fn conflicts(
    a: &BTreeMap<String, (bool, bool)>,
    b: &BTreeMap<String, (bool, bool)>,
    map: &BTreeSet<String>,
) -> Vec<String> {
    a.iter()
        .filter(|(c, _)| !map.contains(*c))
        .filter_map(|(c, (ra, wa))| {
            let (rb, wb) = b.get(c).copied().unwrap_or((false, false));
            ((*wa && (rb || wb)) || (wb && *ra)).then(|| c.clone())
        })
        .collect()
}

/// The cell holding a free-key map: the cell (by name) whose content is the variable a map
/// hypothesis matches.
fn map_cells(r: &Rule) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let lhs = &r.step.index;
    let mut targets = BTreeSet::new();
    for (_, p) in &r.step.hyps {
        if let Some((rest, x)) = map_hyp(p) {
            targets.insert(rest);
            targets.insert(x);
        }
    }
    fn go(l: &L, t: &BTreeSet<String>, out: &mut BTreeSet<String>) {
        if let L::App(h, a) = l {
            if let Some(n) = is_cell(h)
                && a.len() == 1
                && matches!(&a[0], L::Var(v) if t.contains(v))
            {
                out.insert(n);
            }
            a.iter().for_each(|x| go(x, t, out));
        }
    }
    go(lhs, &targets, &mut out);
    out
}

/// The observation: the path to each named cell in a rule's left-hand side, as a match pattern.
pub(crate) fn proj_def(
    lib: &Lib,
    name: &str,
    def: &str,
    cells: &[String],
    content: Option<&str>,
) -> String {
    let mut pats: Vec<(String, String)> = vec![]; // (cell type, path)
    // the pattern of the top configuration with `x{i}` at each observed cell
    fn find(l: &L, cell: &str, path: &mut Vec<usize>) -> Option<String> {
        if let L::App(h, a) = l {
            if is_cell(h).as_deref() == Some(cell) {
                return Some(h.split(".«").next().unwrap_or(h).to_string());
            }
            for (i, x) in a.iter().enumerate() {
                path.push(i);
                if let Some(t) = find(x, cell, path) {
                    return Some(t);
                }
                path.pop();
            }
        }
        None
    }
    let mut shape: Option<L> = None;
    let mut paths = vec![];
    for c in cells {
        let mut found = None;
        for r in &lib.rules {
            let mut p = vec![];
            if let Some(t) = find(&r.step.index, c, &mut p) {
                found = Some((t, p));
                shape.get_or_insert_with(|| r.step.index.clone());
                break;
            }
        }
        let Some((t, p)) = found else {
            fail(&format!("--obs: no rule's left-hand side shows the cell <{c}>"))
        };
        pats.push((t, String::new()));
        paths.push(p);
    }
    // build the pattern: walk the shape, keeping constructors on the paths, `_` elsewhere
    fn pat(
        l: &L,
        paths: &[(usize, Vec<usize>)],
        depth: usize,
        ns: &str,
        content: bool,
    ) -> String {
        if let Some((i, _)) = paths.iter().find(|(_, p)| p.len() == depth) {
            return match (content, l) {
                (true, L::App(h, _)) => format!("({ns}.{h} x{i})"),
                _ => format!("x{i}"),
            };
        }
        match l {
            L::App(h, a) => {
                let args: Vec<String> = a
                    .iter()
                    .enumerate()
                    .map(|(k, x)| {
                        let sub: Vec<(usize, Vec<usize>)> = paths
                            .iter()
                            .filter(|(_, p)| p.len() > depth && p[depth] == k)
                            .cloned()
                            .collect();
                        if sub.is_empty() {
                            "_".to_string()
                        } else {
                            pat(x, &sub, depth + 1, ns, content)
                        }
                    })
                    .collect();
                format!("({ns}.{h} {})", args.join(" "))
            }
            _ => "_".into(),
        }
    }
    let shape = shape.unwrap();
    let indexed: Vec<(usize, Vec<usize>)> = paths.into_iter().enumerate().collect();
    let p = pat(&shape, &indexed, 0, name, content.is_some());
    let tys: Vec<String> = match content {
        Some(t) => vec![format!("{name}.{t}"); cells.len()],
        None => pats.iter().map(|(t, _)| format!("{name}.{t}")).collect(),
    };
    let xs: Vec<String> = (0..cells.len()).map(|i| format!("x{i}")).collect();
    let (ty, val) = if cells.len() == 1 {
        (tys[0].clone(), xs[0].clone())
    } else {
        (tys.join(" × "), format!("({})", xs.join(", ")))
    };
    let cells_doc: Vec<String> = cells.iter().map(|c| format!("`<{c}>`")).collect();
    format!(
        "/-- The projection to the cell{} {}. -/\ndef {def} : {name}.{} → {ty}\n  | {p} => {val}\n",
        if cells.len() == 1 { "" } else { "s" },
        cells_doc.join(", "),
        lib.top
    )
}

fn intro(xs: &[String]) -> String {
    if xs.is_empty() {
        String::new()
    } else {
        format!("  intro {}\n", xs.join(" "))
    }
}

pub fn main(args: &[String]) {
    let mut opt: BTreeMap<String, String> = BTreeMap::new();
    let mut it = args.iter();
    while let Some(k) = it.next() {
        let v = it
            .next()
            .unwrap_or_else(|| fail(&format!("{k} needs a value")));
        opt.insert(k.trim_start_matches("--").to_string(), v.clone());
    }
    let get = |k: &str| {
        opt.get(k)
            .cloned()
            .unwrap_or_else(|| fail(&format!("--{k} is required")))
    };
    let lib = load(&get("kore"));
    let name = get("name");
    let report_only = opt.get("report-only").is_some_and(|v| v == "true");
    let local = match opt.get("join").map(|s| s.as_str()) {
        None | Some("diamond") => false,
        Some("local") => true,
        Some(o) => fail(&format!("--join {o}: expected diamond or local")),
    };
    let rs = &lib.rules;
    let rank = |r: &Rule| lib.prios.iter().position(|p| *p == r.priority).unwrap_or(0);
    // the classes of the unordered pairs, two free-key matches taken as one binding
    let same = crate::pairs::classify_same_rank(&lib.def, &lib.m, rs, &rank, true);
    let roles: Vec<MapRole> = rs.iter().map(map_role).collect();
    let feet: Vec<_> = rs.iter().map(footprint).collect();
    let maps: Vec<BTreeSet<String>> = rs.iter().map(map_cells).collect();
    // the report
    let mut by_class: BTreeMap<String, usize> = BTreeMap::new();
    let mut distinct: BTreeMap<String, usize> = BTreeMap::new();
    let mut races: BTreeMap<String, usize> = BTreeMap::new();
    let mut critical: Vec<String> = vec![];
    let n = rs.len();
    for i in 0..n {
        for j in i..n {
            if rank(&rs[i]) != rank(&rs[j]) {
                *by_class.entry("priority".into()).or_default() += 1;
                continue;
            }
            // one binding (or no free-key match)
            if i != j {
                let o = &same[&(i, j)];
                // an overlap of rules that write disjoint cells commutes
                let c = conflicts(&feet[i], &feet[j], &BTreeSet::new());
                let class = match o.class.as_str() {
                    "overlap" if c.is_empty() => "overlap-independent".to_string(),
                    "overlap" => "overlap-conflict".to_string(),
                    x => x.to_string(),
                };
                *by_class.entry(class.clone()).or_default() += 1;
                if class == "overlap-conflict" {
                    critical.push(format!(
                        "{} | {} (one binding: {}; cells {})",
                        rules::display_name(&rs[i]),
                        rules::display_name(&rs[j]),
                        o.detail,
                        c.join(", ")
                    ));
                }
            }
            // two bindings of one cell map
            let shared: BTreeSet<String> = maps[i].intersection(&maps[j]).cloned().collect();
            if rs[i].multi && rs[j].multi && !shared.is_empty() {
                let c = conflicts(&feet[i], &feet[j], &shared);
                let both_update = matches!(roles[i], MapRole::Update { .. })
                    && matches!(roles[j], MapRole::Update { .. });
                let class = if !both_update {
                    "map-structure"
                } else if c.is_empty() {
                    "independent"
                } else {
                    "conflict"
                };
                *distinct.entry(class.into()).or_default() += 1;
                for x in &c {
                    *races.entry(x.clone()).or_default() += 1;
                }
                if class != "independent" {
                    critical.push(format!(
                        "{} | {} (two bindings: {})",
                        rules::display_name(&rs[i]),
                        rules::display_name(&rs[j]),
                        if c.is_empty() {
                            "the map's bindings change".to_string()
                        } else {
                            c.join(", ")
                        }
                    ));
                }
            }
        }
    }
    let mut rep = format!(
        "# k2lean confluence: the pairs of rules of {name}\n\nrules = {n}\nmulti = {}\nranks = {}\nunordered_pairs = {}\ncritical = {}\n\n[one_binding]\n",
        rs.iter().filter(|r| r.multi).count(),
        if lib.ranked { lib.prios.len().max(1) } else { 1 },
        n * (n + 1) / 2,
        critical.len()
    );
    for (k, v) in &by_class {
        writeln!(rep, "{k} = {v}").unwrap();
    }
    writeln!(rep, "\n[two_bindings]").unwrap();
    for (k, v) in &distinct {
        writeln!(rep, "{k} = {v}").unwrap();
    }
    writeln!(rep, "\n[races]  # pairs at two bindings that both touch the cell, one writing").unwrap();
    for (k, v) in &races {
        writeln!(rep, "{:?} = {v}", k).unwrap();
    }
    writeln!(rep, "\n[critical]\npairs = [").unwrap();
    for c in &critical {
        writeln!(rep, "  {c:?},").unwrap();
    }
    writeln!(rep, "]").unwrap();
    if report_only {
        if let Some(p) = opt.get("report") {
            write_file(p, &rep);
        }
        eprintln!(
            "confluence: {n} rules, {} unordered pairs, {} critical (report only)",
            n * (n + 1) / 2,
            critical.len()
        );
        return;
    }
    if lib.ranked && lib.prios.len() > 1 {
        fail("the Lean scaffold supports definitions without priority ranks (use --report-only)");
    }
    let ns = get("ns");
    let hand = opt
        .get("hand-module")
        .cloned()
        .unwrap_or(format!("{ns}.Hand"));
    let h = opt.get("hyp").cloned().unwrap_or("H".into());
    let open: BTreeSet<(String, String)> = match opt.get("open") {
        Some(p) => std::fs::read_to_string(p)
            .unwrap_or_else(|e| fail(&format!("{p}: {e}")))
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .map(|l| match l.split_once(" | ") {
                Some((a, b)) => (a.trim().to_string(), b.trim().to_string()),
                None => fail(&format!("{p}: `{l}` is not `RULE | RULE`")),
            })
            .collect(),
        None => BTreeSet::new(),
    };
    let names: BTreeSet<String> = rs.iter().map(rules::display_name).collect();
    for (a, b) in &open {
        if !names.contains(a) || !names.contains(b) {
            fail(&format!("open pair {a} | {b}: no such rule"));
        }
    }
    let cells: Vec<String> = get("obs").split(',').map(|s| s.to_string()).collect();
    let (j, refl, step) = if local {
        ("JoinMod", ".refl _", "Star.single")
    } else {
        ("DiamondMod", "Or.inl rfl", "Or.inr")
    };
    let top = format!("{name}.{}", lib.top);
    let mut o = String::new();
    writeln!(o, "import {hand}\nimport KPrelude.Tactic\n").unwrap();
    writeln!(
        o,
        "/-! Generated by `k2lean confluence`; do not edit.\n\n\
Under the hypothesis `{h}` of `{hand}`, every two runs of `{name}.Step` from one configuration that\n\
end in terminal configurations end in the same one, so in particular they observe the same\n\
`obs`. One obligation per ordered pair of rules (`pair.r₁.r₂`, {} of them): the successors of two\n\
instances of the rules at one configuration {}. The pairs the generic arguments do not close\n\
are the hand module's (`hand.pair.r₁.r₂`). -/\n",
        n * n,
        if local {
            "join (`JoinMod`; with the measure `μ` of the hand module, Newman's lemma)"
        } else {
            "join in at most one step each (`DiamondMod`)"
        }
    )
    .unwrap();
    writeln!(o, "set_option maxHeartbeats 0\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n").unwrap();
    o.push_str(&proj_def(&lib, &name, "obs", &cells, None));
    o.push('\n');
    let args_of = |r: &Rule| rules::ctor_args(&r.step);
    let mut guard = vec![];
    let mut counts = (0usize, 0usize);
    let mut hand_pairs = vec![];
    for (i, r1) in rs.iter().enumerate() {
        let a1 = args_of(r1);
        let taken: BTreeSet<&String> = a1.iter().collect();
        for (k, r2) in rs.iter().enumerate() {
            let mut suf = "_r".to_string();
            while args_of(r2)
                .iter()
                .any(|x| taken.contains(&format!("{x}{suf}")))
            {
                suf.push('\'');
            }
            let a2: Vec<String> = args_of(r2).iter().map(|x| format!("{x}{suf}")).collect();
            let hyps1: Vec<(String, String)> = r1
                .step
                .hyps
                .iter()
                .map(|(x, _)| (x.clone(), x.clone()))
                .collect();
            let hyps2: Vec<(String, String)> = r2
                .step
                .hyps
                .iter()
                .map(|(x, _)| (x.clone(), format!("{x}{suf}")))
                .collect();
            let (l1, l2) = (&r1.lean, &r2.lean);
            let ty = format!(
                "{name}.Step.Rel.{l1} (fun c c₁ => {name}.Step.Rel.{l2} (fun c' c₂ => c' = c → {h} c → {j} {name}.Step Eq c₁ c₂))"
            );
            let mut xs = a1.clone();
            xs.extend(a2.iter().cloned());
            xs.extend(["hc".to_string(), "hH".to_string()]);
            writeln!(o, "theorem pair.{l1}.{l2} :\n    {ty} := by\n{}", intro(&xs)).unwrap();
            let listed = open.contains(&(rules::display_name(r1), rules::display_name(r2)));
            if listed {
                counts.1 += 1;
                hand_pairs.push(format!(
                    "{} | {}",
                    rules::display_name(r1),
                    rules::display_name(r2)
                ));
                writeln!(o, "  exact hand.pair.{l1}.{l2} {}\n", xs.join(" ")).unwrap();
                guard.push(format!("pair.{l1}.{l2}"));
                continue;
            }
            counts.0 += 1;
            // a step of `r` with the hypotheses `named` (constructor binder := value)
            let ctor = |r: &Rule, named: &[(String, String)]| {
                let mut s = format!("{name}.Step.{}", r.lean);
                for (b, v) in named {
                    write!(s, " ({b} := {v})").unwrap();
                }
                s.push_str(" ..");
                format!("{step} ({s})")
            };
            let replace = |hs: &[(String, String)], with: &[(&String, String)]| {
                hs.iter()
                    .map(|(b, v)| {
                        with.iter()
                            .find(|(x, _)| *x == b)
                            .map(|(x, w)| ((*x).clone(), w.clone()))
                            .unwrap_or((b.clone(), v.clone()))
                    })
                    .collect::<Vec<_>>()
            };
            let mut alts = vec![format!("exact ⟨_, _, {refl}, {refl}, rfl⟩")];
            if i == k {
                // one instance: its right-hand-side hypotheses determine the same values
                let lhs_hyps: BTreeSet<&String> = r1.app.hyps.iter().map(|(x, _)| x).collect();
                let unify: Vec<String> = r1
                    .step
                    .hyps
                    .iter()
                    .filter(|(x, p)| !lhs_hyps.contains(x) && p.contains("= some "))
                    .map(|(x, _)| format!("cases {x}.symm.trans {x}{suf}"))
                    .collect();
                if !unify.is_empty() {
                    alts.push(format!(
                        "({}; exact ⟨_, _, {refl}, {refl}, rfl⟩)",
                        unify.join("; ")
                    ));
                }
            }
            let sfx = |x: &String| format!("{x}{suf}");
            match (&roles[i], &roles[k]) {
                (MapRole::Update { hm, hr }, MapRole::Update { hm: hm2, hr: hr2 }) => {
                    let s2 = replace(&hyps2, &[(hm2, "a₁".into()), (hr2, "a₂".into())]);
                    let s1 = replace(&hyps1, &[(hm, "a₃".into()), (hr, "a₄".into())]);
                    alts.push(format!(
                        "(rcases MapHook.concat_element_same_or_comm {hm} {} {hr} {} with ⟨hk, hv, hR⟩ | ⟨R₁₂, R₂₁, m', a₁, a₂, a₃, a₄⟩\n       · cases hk; cases hv; cases hR; cases {hr}.symm.trans {}\n         first | exact ⟨_, _, {refl}, {refl}, rfl⟩ | (exfalso; simp_all) | omega\n       · exact ⟨_, _, {}, {}, by k2l_join_eq⟩)",
                        sfx(hm2),
                        sfx(hr2),
                        sfx(hr2),
                        ctor(r2, &s2),
                        ctor(r1, &s1)
                    ));
                }
                (MapRole::Update { hm, hr }, MapRole::Insert { hr: hr2 }) => {
                    let s2 = replace(&hyps2, &[(hr2, "a₃".into())]);
                    let s1 = replace(&hyps1, &[(hm, "a₁".into()), (hr, "a₂".into())]);
                    alts.push(format!(
                        "(obtain ⟨R₂₁, m', a₁, a₂, a₃⟩ := MapHook.concat_element_comm_insert {hm} {hr} {}\n       exact ⟨_, _, {}, {}, by k2l_join_eq⟩)",
                        sfx(hr2),
                        ctor(r2, &s2),
                        ctor(r1, &s1)
                    ));
                }
                (MapRole::Insert { hr }, MapRole::Update { hm: hm2, hr: hr2 }) => {
                    let s2 = replace(&hyps2, &[(hm2, "a₁".into()), (hr2, "a₂".into())]);
                    let s1 = replace(&hyps1, &[(hr, "a₃".into())]);
                    alts.push(format!(
                        "(obtain ⟨R₂₁, m', a₁, a₂, a₃⟩ := MapHook.concat_element_comm_insert {} {} {hr}\n       exact ⟨_, _, {}, {}, by k2l_join_eq⟩)",
                        sfx(hm2),
                        sfx(hr2),
                        ctor(r2, &s2),
                        ctor(r1, &s1)
                    ));
                }
                _ => {}
            }
            alts.push(format!(
                "exact ⟨_, _, {}, {}, by k2l_join_eq⟩",
                ctor(r2, &hyps2),
                ctor(r1, &hyps1)
            ));
            writeln!(o, "  cases hc\n  all_goals first").unwrap();
            for a in &alts {
                writeln!(o, "    | {a}").unwrap();
            }
            writeln!(o).unwrap();
            guard.push(format!("pair.{l1}.{l2}"));
        }
    }
    // assembly
    writeln!(o, "/-! ## Every two steps from one configuration join -/\n").unwrap();
    for r1 in rs {
        let l1 = &r1.lean;
        let a1 = args_of(r1);
        let mut xs = a1.clone();
        xs.extend(["c₂".to_string(), "h₂".to_string()]);
        let parts: Vec<String> = rs
            .iter()
            .map(|r2| format!("(pair.{l1}.{} {})", r2.lean, a1.join(" ")))
            .collect();
        writeln!(
            o,
            "theorem left.{l1} :\n    {name}.Step.Rel.{l1} (fun c c₁ => ∀ c₂, {name}.Step c c₂ → {h} c → {j} {name}.Step Eq c₁ c₂) := by\n{}  exact {name}.Step.rel_of {} h₂ rfl\n",
            intro(&xs),
            parts.join(" ")
        )
        .unwrap();
    }
    let lefts: Vec<String> = rs.iter().map(|r| format!("left.{}", r.lean)).collect();
    writeln!(
        o,
        "theorem joins {{c c₁ c₂ : {top}}} (hH : {h} c) (h₁ : {name}.Step c c₁) (h₂ : {name}.Step c c₂) :\n    {j} {name}.Step Eq c₁ c₂ :=\n  {name}.Step.rel_of {} h₁ c₂ h₂ hH\n",
        lefts.join(" ")
    )
    .unwrap();
    let uniq = if local {
        format!("terminal_unique_of_local StepEquiv.eq {h}.preserved μ μ_dec joins")
    } else {
        format!("terminal_unique_of_diamond StepEquiv.eq {h}.preserved joins")
    };
    writeln!(
        o,
        "/-- Two runs from a configuration satisfying `{h}` that end in terminal configurations end in the same one. -/\n\
theorem terminal_unique {{c n₁ n₂ : {top}}} (hc : {h} c) (h₁ : Star {name}.Step c n₁) (t₁ : Terminal {name}.Step n₁)\n    (h₂ : Star {name}.Step c n₂) (t₂ : Terminal {name}.Step n₂) : n₁ = n₂ :=\n  {uniq} hc h₁ t₁ h₂ t₂\n\n\
/-- The observation is determined: whatever the schedule, a terminal configuration observes the same `obs`. -/\n\
theorem obs_confluent {{c n₁ n₂ : {top}}} (hc : {h} c) (h₁ : Star {name}.Step c n₁) (t₁ : Terminal {name}.Step n₁)\n    (h₂ : Star {name}.Step c n₂) (t₂ : Terminal {name}.Step n₂) : obs n₁ = obs n₂ :=\n  congrArg obs (terminal_unique hc h₁ t₁ h₂ t₂)\n"
    )
    .unwrap();
    guard.extend(["joins".into(), "terminal_unique".into(), "obs_confluent".into()]);
    writeln!(o, "#k2l_assert_axioms {}\n\nend {ns}", guard.join(" ")).unwrap();
    write_file(&get("out"), &o);
    writeln!(
        rep,
        "\n[lean]\nordered_pairs = {}\ngenerated = {}\nhand = {}\nhand_pairs = {hand_pairs:?}",
        n * n,
        counts.0,
        counts.1
    )
    .unwrap();
    if let Some(p) = opt.get("report") {
        write_file(p, &rep);
    }
    eprintln!(
        "confluence: {n} rules, {} ordered pairs, {} generated, {} by hand; {} critical unordered pairs",
        n * n,
        counts.0,
        counts.1,
        critical.len()
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_hypotheses_name_their_rest_and_map() {
        let h = "KPrelude.MapHook.concat (KPrelude.MapHook.element (SortWidCell.«<wid>» Gen0) (SortWorkerCell.«<worker>» (SortWidCell.«<wid>» Gen0) (SortTodoCell.«<todo>» C))) DotVar2 = some m";
        assert_eq!(map_hyp(h), Some(("DotVar2".into(), "m".into())));
        assert_eq!(map_hyp("KPrelude.IntHook.gt C (0 : Int) = true"), None);
    }

    #[test]
    fn cell_heads_are_recognized() {
        assert_eq!(is_cell("SortAccCell.«<acc>»"), Some("acc".into()));
        assert_eq!(is_cell("SortK.kseq"), None);
    }
}
