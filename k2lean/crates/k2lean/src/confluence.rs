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
    Update {
        hm: String,
        hr: String,
    },
    /// `hr : (K ↦ W) M = some r` with `M` the cell's content on the left: an insertion.
    Insert {
        hr: String,
    },
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
        let rs: Vec<&(String, String, String)> =
            results.iter().filter(|(_, r2, _)| r2 == rest).collect();
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
            .filter(|w| {
                !w.is_empty()
                    && w.chars()
                        .next()
                        .is_some_and(|c| c.is_lowercase() || c.is_uppercase())
            })
            .map(String::from)
            .collect()
    };
    let binders: BTreeSet<&String> = r.step.binders.iter().map(|(b, _)| b).collect();
    let kv: BTreeSet<String> = words(key)
        .into_iter()
        .filter(|w| binders.contains(w))
        .collect();
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
            && xa
                .iter()
                .any(|x| matches!(x, L::App(h, _) if is_cell(h).is_some()))
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
            fail(&format!(
                "--obs: no rule's left-hand side shows the cell <{c}>"
            ))
        };
        pats.push((t, String::new()));
        paths.push(p);
    }
    // build the pattern: walk the shape, keeping constructors on the paths, `_` elsewhere
    fn pat(l: &L, paths: &[(usize, Vec<usize>)], depth: usize, ns: &str, content: bool) -> String {
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
        if lib.ranked {
            lib.prios.len().max(1)
        } else {
            1
        },
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
    writeln!(
        rep,
        "\n[races]  # pairs at two bindings that both touch the cell, one writing"
    )
    .unwrap();
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
    if let Some(threads) = opt.get("threads") {
        let ns = get("ns");
        let out = views::emit(&lib, &name, &ns, threads, &roles, &feet, &rank);
        write_file(&get("out"), &out);
        if let Some(p) = opt.get("report") {
            write_file(p, &rep);
        }
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
            writeln!(
                o,
                "theorem pair.{l1}.{l2} :\n    {ty} := by\n{}",
                intro(&xs)
            )
            .unwrap();
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
    guard.extend([
        "joins".into(),
        "terminal_unique".into(),
        "obs_confluent".into(),
    ]);
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


/// `--threads CELL`: the joins of a definition whose threads are the bindings of a cell map
/// (SIMPLE's `<threads>`), proved through one view per rule instead of one obligation per pair
/// (`k2lean/docs/design.md`, §3.6).
mod views {
    use super::{Lib, MapRole};
    use crate::model::Model;
    use crate::names;
    use crate::rules::{self, Rule};
    use std::collections::BTreeMap;
    use std::fmt::Write as _;

    /// A leaf cell of the configuration: its label, its sort, and its field name.
    pub(super) struct Leaf {
        pub label: String,
        pub sort: String,
        pub field: String,
    }

    fn is_cell_sort(m: &Model, s: &str) -> Option<String> {
        let info = m.sorts.get(s)?;
        let [c] = info.own.as_slice() else { return None };
        let k = &m.ctors[c].klabel;
        (k.starts_with('<') && k.ends_with('>')).then(|| c.clone())
    }

    /// The configuration's cells: the leaves under nested cells, in order, and the Lean term of
    /// the top cell with `leaf(i)` at each leaf.
    pub(super) fn tree(lib: &Lib, name: &str) -> (Vec<Leaf>, Box<dyn Fn(&dyn Fn(usize) -> String) -> String>) {
        enum Node {
            Inner(String, Vec<Node>),
            Leaf(usize),
        }
        fn walk(m: &Model, s: &str, leaves: &mut Vec<Leaf>, name: &str) -> Node {
            let c = is_cell_sort(m, s).unwrap_or_else(|| super::fail(&format!("{s} is not a cell")));
            let args = m.ctors[&c].args.clone();
            if !args.is_empty() && args.iter().all(|a| is_cell_sort(m, a).is_some()) {
                Node::Inner(
                    format!("{name}.{}", m.ctor_path(&c)),
                    args.iter().map(|a| walk(m, a, leaves, name)).collect(),
                )
            } else {
                let label = m.ctors[&c].klabel.trim_start_matches('<').trim_end_matches('>').to_string();
                leaves.push(Leaf {
                    field: names::ident(&label.replace('-', "_")),
                    label,
                    sort: s.to_string(),
                });
                Node::Leaf(leaves.len() - 1)
            }
        }
        let mut leaves = vec![];
        let root = walk(&lib.m, &lib.top, &mut leaves, name);
        fn render(n: &Node, f: &dyn Fn(usize) -> String) -> String {
            match n {
                Node::Leaf(i) => f(*i),
                Node::Inner(c, a) => {
                    let xs: Vec<String> = a.iter().map(|x| render(x, f)).collect();
                    format!("({c} {})", xs.join(" "))
                }
            }
        }
        (leaves, Box::new(move |f| render(&root, f)))
    }

    /// How a rule touches a shared cell.
    #[derive(Clone, Copy, PartialEq, Debug)]
    pub(super) enum Touch {
        None,
        Read,
        Write,
    }


    /// A key pattern, as `KPrelude.KeyPat`.
    #[derive(Clone, PartialEq)]
    pub(super) enum KeyP {
        Any,
        Dotk,
        Item(Option<String>, Option<String>),
    }

    impl KeyP {
        fn lean(&self) -> String {
            match self {
                KeyP::Any => "KeyPat.any".into(),
                KeyP::Dotk => "KeyPat.dotk".into(),
                KeyP::Item(i, o) => format!(
                    "KeyPat.item {} {}",
                    i.as_ref().map(|x| format!("(some {x:?})")).unwrap_or("none".into()),
                    o.as_ref().map(|x| format!("(some {x:?})")).unwrap_or("none".into())
                ),
            }
        }
        /// `KeyPat.disj`.
        fn disj(&self, other: &KeyP) -> bool {
            match (self, other) {
                (KeyP::Dotk, KeyP::Item(..)) | (KeyP::Item(..), KeyP::Dotk) => true,
                (KeyP::Item(Some(i1), o1), KeyP::Item(Some(i2), o2)) => {
                    i1 != i2 || matches!((o1, o2), (Some(a), Some(b)) if a != b)
                }
                _ => false,
            }
        }
    }

    /// The key of a thread rule, read off its map hypothesis: the first item of the thread's `<k>`
    /// (its injection, and the constructor under it when that is an application).
    fn key_pat(hyp: &str) -> KeyP {
        let Some(i) = hyp.find("«<k>» ") else { return KeyP::Any };
        let rest = &hyp[i + "«<k>» ".len()..];
        if rest.starts_with("SortK.dotk") {
            return KeyP::Dotk;
        }
        let Some(rest) = rest.strip_prefix("(SortK.kseq ") else { return KeyP::Any };
        let Some(rest) = rest.strip_prefix('(') else { return KeyP::Any };
        let head: String = rest.chars().take_while(|c| *c != ' ' && *c != ')').collect();
        let Some(inj) = head.strip_prefix("SortKItem.") else { return KeyP::Any };
        let after = &rest[head.len()..];
        let own = after.strip_prefix(" (").and_then(|r| {
            let o = own_name(r);
            (!o.is_empty() && !o.chars().next().unwrap().is_lowercase() || r.starts_with("Sort")).then_some(o)
        });
        KeyP::Item(Some(inj.to_string()), own)
    }

    /// The constructor name heading `r`: `SortExp.Own.«_+_» …` → `«_+_»`, `SortExp.Own.f x` → `f`.
    fn own_name(r: &str) -> String {
        let mut tok = String::new();
        let mut quoted = false;
        for ch in r.chars() {
            if !quoted && (ch == ' ' || ch == ')') {
                break;
            }
            if ch == '«' {
                quoted = true;
            } else if ch == '»' {
                quoted = false;
            }
            tok.push(ch);
        }
        match tok.rfind('«') {
            Some(i) if tok.ends_with('»') => tok[i..].to_string(),
            _ => tok.rsplit('.').next().unwrap_or(&tok).to_string(),
        }
    }

    pub(super) fn emit(
        lib: &Lib,
        name: &str,
        ns: &str,
        threads: &str,
        roles: &[MapRole],
        feet: &[BTreeMap<String, (bool, bool)>],
        rank: &dyn Fn(&Rule) -> usize,
    ) -> String {
        let (leaves, top) = tree(lib, name);
        let ti = leaves
            .iter()
            .position(|l| l.label == threads)
            .unwrap_or_else(|| super::fail(&format!("--threads: no cell <{threads}>")));
        let tcell = &leaves[ti];
        let tctor = is_cell_sort(&lib.m, &tcell.sort).unwrap();
        let tmap = lib.m.ctors[&tctor].args[0].clone();
        let shared: Vec<&Leaf> = leaves.iter().enumerate().filter(|(i, _)| *i != ti).map(|(_, l)| l).collect();
        let topt = format!("{name}.{}", lib.top);
        let ty = |s: &str| format!("{name}.{s}");
        let mut o = String::new();
        writeln!(o, "import {name}.Preserves\nimport KPrelude.Scaffold\nimport KPrelude.Tactic\n").unwrap();
        writeln!(o, "/-! Generated by `k2lean confluence --threads {threads}`; do not edit. -/\n").unwrap();
        writeln!(o, "set_option maxHeartbeats 0\nset_option linter.unusedVariables false\n\nnamespace {ns}\n\nopen KPrelude\n").unwrap();
        // the shared cells, the configuration from the threads and them, and their changes
        writeln!(o, "/-- The cells of a configuration other than `<{threads}>`. -/\nstructure Shared where").unwrap();
        for l in &shared {
            writeln!(o, "  {} : {}", l.field, ty(&l.sort)).unwrap();
        }
        let mk_body = top(&|i| {
            if i == ti {
                "tc".to_string()
            } else {
                format!("s.{}", leaves[i].field)
            }
        });
        writeln!(o, "\n/-- The configuration of the cell `<{threads}>` `tc` and the shared cells `s`. -/\ndef mkc (tc : {}) (s : Shared) : {topt} :=\n  {mk_body}\n", ty(&tcell.sort)).unwrap();
        writeln!(o, "/-- The configuration of the threads `m` and the shared cells `s`. -/\nabbrev mk (m : {}) (s : Shared) : {topt} := mkc ({name}.{} m) s\n", ty(&tmap), lib.m.ctor_path(&tctor)).unwrap();
        writeln!(o, "/-- A change of the shared cells: per cell, none, or the value it has and the value it gets. -/\nstructure Change where").unwrap();
        for l in &shared {
            writeln!(o, "  {} : Ch {} := none", l.field, ty(&l.sort)).unwrap();
        }
        let conj = |f: &dyn Fn(&str) -> String| -> String {
            shared.iter().map(|l| f(&l.field)).collect::<Vec<_>>().join(" ∧ ")
        };
        let anon = |f: &dyn Fn(&str) -> String| -> String {
            format!("⟨{}⟩", shared.iter().map(|l| f(&l.field)).collect::<Vec<_>>().join(", "))
        };
        // projections of the n-fold conjunction
        let n = shared.len();
        let proj = |h: &str, i: usize| -> String {
            let mut t = h.to_string();
            for _ in 0..i {
                t.push_str(".2");
            }
            if i + 1 < n {
                t.push_str(".1");
            }
            t
        };
        writeln!(o, "\ndef Change.pre (c : Change) (s : Shared) : Prop :=\n  {}", conj(&|f| format!("c.{f}.pre s.{f}"))).unwrap();
        writeln!(o, "def Change.apply (c : Change) (s : Shared) : Shared :=\n  {}", anon(&|f| format!("c.{f}.apply s.{f}"))).unwrap();
        writeln!(o, "def Change.Compat (a b : Change) : Prop :=\n  {}", conj(&|f| format!("a.{f}.Compat b.{f}"))).unwrap();
        let pa: Vec<String> = (0..n).map(|i| format!("Ch.pre_apply {} {} {}", proj("h", i), proj("ha", i), proj("hb", i))).collect();
        writeln!(o, "\ntheorem Change.pre_apply {{a b : Change}} {{s : Shared}} (h : a.Compat b) (ha : a.pre s) (hb : b.pre s) :\n    b.pre (a.apply s) :=\n  ⟨{}⟩", pa.join(",\n    ")).unwrap();
        let sy: Vec<String> = (0..n).map(|i| format!("{}.symm", proj("h", i))).collect();
        writeln!(o, "\ntheorem Change.Compat.symm {{a b : Change}} (h : a.Compat b) : b.Compat a :=\n  ⟨{}⟩", sy.join(", ")).unwrap();
        let ac: Vec<String> = (0..n).map(|i| format!("Ch.apply_comm {} {} {}", proj("h", i), proj("ha", i), proj("hb", i))).collect();
        writeln!(o, "\ntheorem Change.apply_comm {{a b : Change}} {{s : Shared}} (h : a.Compat b) (ha : a.pre s) (hb : b.pre s) :\n    b.apply (a.apply s) = a.apply (b.apply s) := by\n  simp only [Change.apply, {}]", ac.join(",\n    ")).unwrap();
        // a step of one thread, and its frame
        let els = lib.m.sort(&tmap).elems.clone();
        let (kt, vt) = (ty(&els[0]), ty(&els[1]));
        writeln!(o, "\n/-- A step of the thread at binding `k`, from `t` to `t'`, changing the shared cells by `ch`. -/\ndef TStep (k : {kt}) (t t' : {vt}) (ch : Change) (c c' : {topt}) : Prop :=\n  ∃ m R r s, c = mk m s ∧ MapHook.concat (MapHook.element k t) R = some m ∧\n    MapHook.concat (MapHook.element k t') R = some r ∧ ch.pre s ∧ c' = mk r (ch.apply s)").unwrap();
        writeln!(o, "\n/-- The thread step is a step of `Step` wherever no rule of a rank before `i` applies. -/\ndef Local (i : Nat) (k : {kt}) (t t' : {vt}) (ch : Change) : Prop :=\n  ∀ d d', TStep k t t' ch d d' → (∀ j, j < i → ¬ {name}.App j d) → {name}.Step d d'").unwrap();
        // mk is injective
        let svars: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
        let svars2: Vec<String> = (0..n).map(|i| format!("y{i}")).collect();
        let _ = (&svars, &svars2);
        writeln!(o, "\ntheorem mkc_inj {{tc tc' s s'}} (h : mkc tc s = mkc tc' s') : tc = tc' ∧ s = s' := by\n  cases s; cases s'; cases h; exact ⟨rfl, rfl⟩").unwrap();
        writeln!(o, "\ntheorem mk_inj {{m m' s s'}} (h : mk m s = mk m' s') : m = m' ∧ s = s' := by\n  cases s; cases s'; cases h; exact ⟨rfl, rfl⟩").unwrap();
        writeln!(o, "\ntheorem tstep_comm {{k₁ k₂ t₁ t₁' t₂ t₂' ch₁ ch₂}} {{c c₁ c₂ : {topt}}}\n    (h₁ : TStep k₁ t₁ t₁' ch₁ c c₁) (h₂ : TStep k₂ t₂ t₂' ch₂ c c₂) (hk : k₁ ≠ k₂) (hc : ch₁.Compat ch₂) :\n    ∃ c₁₂, TStep k₂ t₂ t₂' ch₂ c₁ c₁₂ ∧ TStep k₁ t₁ t₁' ch₁ c₂ c₁₂ := by\n  obtain ⟨m, R₁, r₁, s, rfl, hm₁, hr₁, hp₁, rfl⟩ := h₁\n  obtain ⟨m₂, R₂, r₂, s₂, he, hm₂, hr₂, hp₂, rfl⟩ := h₂\n  obtain ⟨rfl, rfl⟩ := mk_inj he\n  rcases MapHook.concat_element_same_or_comm hm₁ hm₂ hr₁ hr₂ with ⟨hk', -, -⟩ | ⟨R₁₂, R₂₁, m', a₁, a₂, a₃, a₄⟩\n  · exact absurd hk' hk\n  · refine ⟨mk m' (ch₂.apply (ch₁.apply s)), ⟨_, _, _, _, rfl, a₁, a₂, Change.pre_apply hc hp₁ hp₂, rfl⟩,\n      ⟨_, _, _, _, rfl, a₃, a₄, Change.pre_apply hc.symm hp₂ hp₁, ?_⟩⟩\n    rw [Change.apply_comm hc hp₁ hp₂]").unwrap();
        // shared-only steps (the threads unchanged)
        writeln!(o, "\n/-- A step that leaves the threads alone and changes the shared cells by `ch`. -/\ndef SStep (ch : Change) (c c' : {topt}) : Prop :=\n  ∃ tc s, c = mkc tc s ∧ ch.pre s ∧ c' = mkc tc (ch.apply s)").unwrap();
        writeln!(o, "\ndef LocalS (i : Nat) (ch : Change) : Prop :=\n  ∀ d d', SStep ch d d' → (∀ j, j < i → ¬ {name}.App j d) → {name}.Step d d'").unwrap();
        writeln!(o, "\ntheorem tstep_sstep_comm {{k₁ t₁ t₁' ch₁ ch₂}} {{c c₁ c₂ : {topt}}}\n    (h₁ : TStep k₁ t₁ t₁' ch₁ c c₁) (h₂ : SStep ch₂ c c₂) (hc : ch₁.Compat ch₂) :\n    ∃ c₁₂, SStep ch₂ c₁ c₁₂ ∧ TStep k₁ t₁ t₁' ch₁ c₂ c₁₂ := by\n  obtain ⟨m, R₁, r₁, s, rfl, hm₁, hr₁, hp₁, rfl⟩ := h₁\n  obtain ⟨tc₂, s₂, he, hp₂, rfl⟩ := h₂\n  obtain ⟨rfl, rfl⟩ := mkc_inj he\n  refine ⟨mk r₁ (ch₂.apply (ch₁.apply s)), ⟨_, _, rfl, Change.pre_apply hc hp₁ hp₂, rfl⟩,\n    ⟨_, _, _, _, rfl, hm₁, hr₁, Change.pre_apply hc.symm hp₂ hp₁, ?_⟩⟩\n  rw [Change.apply_comm hc hp₁ hp₂]").unwrap();
        writeln!(o, "\ntheorem sstep_comm {{ch₁ ch₂}} {{c c₁ c₂ : {topt}}}\n    (h₁ : SStep ch₁ c c₁) (h₂ : SStep ch₂ c c₂) (hc : ch₁.Compat ch₂) :\n    ∃ c₁₂, SStep ch₂ c₁ c₁₂ ∧ SStep ch₁ c₂ c₁₂ := by\n  obtain ⟨tc, s, rfl, hp₁, rfl⟩ := h₁\n  obtain ⟨tc₂, s₂, he, hp₂, rfl⟩ := h₂\n  obtain ⟨rfl, rfl⟩ := mkc_inj he\n  refine ⟨mkc tc (ch₂.apply (ch₁.apply s)), ⟨_, _, rfl, Change.pre_apply hc hp₁ hp₂, rfl⟩,\n    ⟨_, _, rfl, Change.pre_apply hc.symm hp₂ hp₁, ?_⟩⟩\n  rw [Change.apply_comm hc hp₁ hp₂]").unwrap();
        writeln!(o, "\n/-- Two threads at one binding are one thread. -/\ntheorem tstep_same {{k t₁ t₁' t₂ t₂' ch₁ ch₂}} {{c c₁ c₂ : {topt}}}\n    (h₁ : TStep k t₁ t₁' ch₁ c c₁) (h₂ : TStep k t₂ t₂' ch₂ c c₂) : t₁ = t₂ := by\n  obtain ⟨m, R₁, r₁, s, rfl, hm₁, -, -, rfl⟩ := h₁\n  obtain ⟨m₂, R₂, r₂, s₂, he, hm₂, -, -, rfl⟩ := h₂\n  obtain ⟨rfl, rfl⟩ := mk_inj he\n  have := (MapHook.lookup_of_concat_element hm₁).symm.trans (MapHook.lookup_of_concat_element hm₂)\n  cases this; rfl").unwrap();
        // the key of a thread: its first `<k>` item
        let vctor = is_cell_sort(&lib.m, &els[1]);
        let kpos = vctor.as_ref().and_then(|c| {
            lib.m.ctors[c].args.iter().position(|a| {
                is_cell_sort(&lib.m, a).is_some_and(|kc| lib.m.ctors[&kc].klabel == "<k>")
            })
        });
        let (Some(vc), Some(kpos)) = (vctor, kpos) else {
            super::fail("--threads: the threads are expected to be cells with a <k> cell");
        };
        let kcell = lib.m.ctors[&vc].args[kpos].clone();
        let kctor = is_cell_sort(&lib.m, &kcell).unwrap();
        let kitem = lib.m.sort("SortKItem");
        let mut own_arms = String::new();
        for l in &kitem.leaves {
            let st = lib.m.sort(l);
            let inj = lib.m.leaf_ctor("SortKItem", l);
            let short = inj.rsplit('.').next().unwrap_or(&inj).to_string();
            if l == "SortKItem" && !kitem.own.is_empty() {
                continue;
            }
            if st.own.is_empty() || l == "SortKItem" {
                writeln!(own_arms, "    | .{short} _ => ({:?}, \"\")", short).unwrap();
                continue;
            }
            let mut inner = String::new();
            for c in &st.own {
                let cl = lib.m.ctors[c].lean.clone();
                writeln!(inner, "      | .{cl} .. => {:?}", cl).unwrap();
            }
            writeln!(own_arms, "    | .{short} x => ({:?}, match x with\n{inner}      )", short).unwrap();
        }
        // the own constructors of KItem itself (freezers)
        if !kitem.own.is_empty() {
            let mut inner = String::new();
            for c in &kitem.own {
                let cl = lib.m.ctors[c].lean.clone();
                writeln!(inner, "      | .{cl} .. => {:?}", cl).unwrap();
            }
            writeln!(own_arms, "    | .inj_KItem x => (\"inj_KItem\", match x with\n{inner}      )").unwrap();
        }
        let vargs: Vec<String> = (0..lib.m.ctors[&vc].args.len()).map(|i| if i == kpos { "kc".to_string() } else { "_".to_string() }).collect();
        writeln!(o, "\n/-- The first item of a thread's `<k>`: its injection into `KItem` and the constructor of the\ninjected value (`(\"dotk\", \"\")` when `<k>` is empty). -/\ndef tkey (t : {vt}) : String × String :=\n  match t with\n  | {name}.{} {} =>\n    match kc with\n    | {name}.{} k =>\n      match k with\n      | .dotk => (\"dotk\", \"\")\n      | .kseq it _ =>\n        match it with\n{own_arms}",
            lib.m.ctor_path(&vc), vargs.join(" "), lib.m.ctor_path(&kctor)).unwrap();
        // the rules: their kind, rank, class and key
        let field_of = |key: &str| -> Option<usize> {
            shared.iter().position(|l| l.label == key || l.sort.trim_start_matches("Sort") == key)
        };
        #[derive(PartialEq, Clone, Copy, Debug)]
        enum Kind { Thread, Shared, Global }
        let mut kinds = vec![];
        let mut touches: Vec<Vec<Touch>> = vec![];
        let mut keys: Vec<String> = vec![];
        let mut keyps: Vec<KeyP> = vec![];
        for (ri, r) in lib.rules.iter().enumerate() {
            let mut touch = vec![Touch::None; n];
            let mut unknown = false;
            let mut threads_touched = false;
            for (key, (rd, wr)) in &feet[ri] {
                if key == &tcell.label || key == tcell.sort.trim_start_matches("Sort") {
                    threads_touched = *rd || *wr;
                    continue;
                }
                match field_of(key) {
                    Some(f) => touch[f] = if *wr { Touch::Write } else if *rd { Touch::Read } else { Touch::None },
                    None => unknown = true,
                }
            }
            let kind = match (&roles[ri], unknown, threads_touched) {
                (MapRole::Update { .. }, false, _) => Kind::Thread,
                (MapRole::None, false, false) if !r.multi => Kind::Shared,
                _ => Kind::Global,
            };
            kinds.push(kind);
            touches.push(touch);
            let kp = match &roles[ri] {
                MapRole::Update { hm, .. } if kind == Kind::Thread => {
                    let p = &r.step.hyps.iter().find(|(h, _)| h == hm).unwrap().1;
                    key_pat(p)
                }
                _ => KeyP::Any,
            };
            keys.push(kp.lean());
            keyps.push(kp);
        }
        // the classes: the distinct ways of touching the shared cells
        let mut classes: Vec<Vec<Touch>> = vec![];
        let cls: Vec<usize> = touches.iter().map(|t| {
            if let Some(i) = classes.iter().position(|c| c == t) { i } else { classes.push(t.clone()); classes.len() - 1 }
        }).collect();
        writeln!(o, "\n/-- The ways a rule touches the shared cells. -/\ninductive Cls where\n  {}\n  deriving DecidableEq", (0..classes.len()).map(|i| format!("| c{i}")).collect::<Vec<_>>().join(" ")).unwrap();
        writeln!(o, "\ndef InClass : Cls → Change → Prop").unwrap();
        for (ci, c) in classes.iter().enumerate() {
            let parts: Vec<String> = (0..n).filter_map(|f| match c[f] {
                Touch::None => Some(format!("ch.{} = none", shared[f].field)),
                Touch::Read => Some(format!("(∃ x, ch.{} = some (x, x))", shared[f].field)),
                Touch::Write => None,
            }).collect();
            writeln!(o, "  | .c{ci}, ch => {}", if parts.is_empty() { "True".into() } else { parts.join(" ∧ ") }).unwrap();
        }
        let compat = |a: &[Touch], b: &[Touch]| (0..n).all(|f| a[f] == Touch::None || b[f] == Touch::None || (a[f] == Touch::Read && b[f] == Touch::Read));
        writeln!(o, "\ndef compatTbl : Cls → Cls → Bool").unwrap();
        for (i, a) in classes.iter().enumerate() {
            for (j, b) in classes.iter().enumerate() {
                writeln!(o, "  | .c{i}, .c{j} => {}", compat(a, b)).unwrap();
            }
        }
        // compat_of: by cases on the two classes; each compatible pair field by field
        let idx = |i: usize, k: usize| -> String {
            // the i-th component of an InClass conjunction of k parts
            if k <= 1 { return String::new(); }
            let mut t = String::new();
            for _ in 0..i { t.push_str(".2"); }
            if i + 1 < k { t.push_str(".1"); }
            t
        };
        let mut arms = String::new();
        for (i, a) in classes.iter().enumerate() {
            for (j, b) in classes.iter().enumerate() {
                if !compat(a, b) {
                    writeln!(arms, "  | .c{i}, .c{j}, h, _, _, _, _ => by simp [compatTbl] at h").unwrap();
                    continue;
                }
                let ka = a.iter().filter(|t| **t != Touch::Write).count();
                let kb = b.iter().filter(|t| **t != Touch::Write).count();
                let pos = |c: &[Touch], f: usize| c[..f].iter().filter(|t| **t != Touch::Write).count();
                let fs: Vec<String> = (0..n).map(|f| {
                    if a[f] == Touch::None {
                        format!("Or.inl h₁{}", idx(pos(a, f), ka))
                    } else if b[f] == Touch::None {
                        format!("Or.inr (Or.inl h₂{})", idx(pos(b, f), kb))
                    } else {
                        format!("Or.inr (Or.inr ⟨h₁{}, h₂{}⟩)", idx(pos(a, f), ka), idx(pos(b, f), kb))
                    }
                }).collect();
                writeln!(arms, "  | .c{i}, .c{j}, _, _, _, h₁, h₂ => ⟨{}⟩", fs.join(", ")).unwrap();
            }
        }
        writeln!(o, "\ntheorem compat_of : ∀ (a b : Cls), compatTbl a b = true → ∀ (ch₁ ch₂ : Change),\n    InClass a ch₁ → InClass b ch₂ → ch₁.Compat ch₂\n{arms}").unwrap();
        // priorities: which cells the rules of each rank read, and that a step leaving them alone
        // keeps a rule of that rank from applying where it did not
        let max_rank = lib.rules.iter().zip(&kinds).filter(|(_, k)| **k != Kind::Global).map(|(r, _)| rank(r)).max().unwrap_or(0);
        let mut reads: Vec<Option<Vec<usize>>> = vec![]; // per rank below max_rank: the fields, or None if threads
        for j in 0..max_rank {
            let mut fs: Vec<usize> = vec![];
            let mut threads_read = false;
            for (ri, r) in lib.rules.iter().enumerate() {
                if rank(r) != j {
                    continue;
                }
                if kinds[ri] == Kind::Thread || kinds[ri] == Kind::Global && !matches!(roles[ri], MapRole::None) {
                    threads_read = true;
                }
                for (key, (rd, wr)) in &feet[ri] {
                    if key == &tcell.label || key == tcell.sort.trim_start_matches("Sort") {
                        if *rd || *wr { threads_read = true; }
                        continue;
                    }
                    match field_of(key) {
                        Some(f) => if (*rd || *wr) && !fs.contains(&f) { fs.push(f) },
                        None => threads_read = true,
                    }
                }
            }
            fs.sort();
            reads.push((!threads_read).then_some(fs));
        }
        let safe_tbl = |j: usize, c: usize| -> bool {
            reads[j].as_ref().is_some_and(|fs| fs.iter().all(|&f| classes[c][f] == Touch::None))
        };
        for j in 0..max_rank {
            if reads[j].is_none() {
                writeln!(o, "\n/-- The rules of rank {j} read the threads. -/\ndef appSafe{j} (_ : Cls) : Bool := false").unwrap();
                continue;
            }
            writeln!(o, "\ndef appSafe{j} : Cls → Bool").unwrap();
            for c in 0..classes.len() {
                writeln!(o, "  | .c{c} => {}", safe_tbl(j, c)).unwrap();
            }
        }
        let mut ite = "false".to_string();
        for j in (0..max_rank).rev() {
            ite = format!("if j = {j} then appSafe{j} c else {ite}");
        }
        writeln!(o, "\n/-- A step of the class leaves alone every cell the rules of rank `j` read. -/\ndef appSafe (j : Nat) (c : Cls) : Bool :=\n  {ite}").unwrap();
        let app = |j: &str, c: &str| format!("{name}.App {j} {c}");
        for (j, fs) in reads.iter().enumerate() {
            let Some(fs) = fs else { continue };
            let hyps: Vec<String> = fs.iter().map(|&f| format!("ch.{} = none", shared[f].field)).collect();
            let hyp = if hyps.is_empty() { "True".to_string() } else { hyps.join(" ∧ ") };
            let rules_j: Vec<&Rule> = lib.rules.iter().filter(|r| rank(r) == j).collect();
            let alts: Vec<String> = rules_j.iter().map(|r| format!("    | (apply {name}.App.{} <;> assumption)", r.lean)).collect();
            let hs: Vec<String> = (0..fs.len()).map(|i| format!("hf{i}")).collect();
            let pat = if hs.is_empty() { "-".to_string() } else if hs.len() == 1 { format!("⟨{}⟩", hs[0]) } else { format!("⟨{}⟩", hs.join(", ")) };
            for (nm, def) in [("app_back", "TStep k t t' ch c c'"), ("app_back_s", "SStep ch c c'")] {
                let binders = if nm == "app_back" { "{k t t' ch}" } else { "{ch}" };
                let (destr, s1) = if nm == "app_back" { ("⟨m, R, r, s, rfl, -, -, -, rfl⟩", "r") } else { ("⟨tc, s, rfl, -, rfl⟩", "tc") };
                let _ = s1;
                let mut body = if hs.len() == 1 {
                    format!("  have hf0 := hf\n  obtain {destr} := h\n")
                } else {
                    format!("  obtain {pat} := hf\n  obtain {destr} := h\n")
                };
                for (i, &f) in fs.iter().enumerate() {
                    writeln!(body, "  have e{i} : (ch.apply s).{} = s.{} := by simp only [Change.apply, Ch.apply, {}]", shared[f].field, shared[f].field, hs[i]).unwrap();
                }
                let es: Vec<String> = (0..fs.len()).map(|i| format!("e{i}")).collect();
                writeln!(body, "  generalize ch.apply s = s' at ha{}\n  cases s; cases s'\n  simp only [mk, mkc] at ha{} ⊢", es.iter().map(|e| format!(" {e}")).collect::<String>(), es.iter().map(|e| format!(" {e}")).collect::<String>()).unwrap();
                if !es.is_empty() {
                    writeln!(body, "  subst {}", es.join(" ")).unwrap();
                }
                writeln!(body, "  cases ha\n  all_goals first\n{}", if alts.is_empty() { "    | skip".into() } else { alts.join("\n") }).unwrap();
                writeln!(o, "\ntheorem {nm}_{j} {binders} {{c c' : {topt}}} (h : {def}) (hf : {hyp})\n    (ha : {}) : {} := by\n{body}", app(&j.to_string(), "c'"), app(&j.to_string(), "c")).unwrap();
            }
            // the cells, from the class
            let arms: Vec<String> = (0..classes.len()).map(|c| {
                if safe_tbl(j, c) {
                    let parts: Vec<String> = fs.iter().map(|&f| {
                        let k = classes[c].iter().filter(|t| **t != Touch::Write).count();
                        let pos = classes[c][..f].iter().filter(|t| **t != Touch::Write).count();
                        format!("hc{}", idx(pos, k))
                    }).collect();
                    let v = if parts.is_empty() { "trivial".into() } else if parts.len() == 1 { parts[0].clone() } else { format!("⟨{}⟩", parts.join(", ")) };
                    format!("  | .c{c}, _, _, hc => {v}")
                } else {
                    format!("  | .c{c}, _, h, _ => by simp [appSafe, appSafe{j}] at h")
                }
            }).collect();
            writeln!(o, "\ntheorem none_of_class_{j} : ∀ (c : Cls) (ch : Change), appSafe {j} c = true → InClass c ch → {hyp}\n{}", arms.join("\n")).unwrap();
        }
        // app_back for every rank
        let mut arms_t = String::new();
        let mut arms_s = String::new();
        for (j, fs) in reads.iter().enumerate() {
            if fs.is_some() {
                writeln!(arms_t, "  | {j}, c, h, hc, ht, ha => app_back_{j} ht (none_of_class_{j} c _ h hc) ha").unwrap();
                writeln!(arms_s, "  | {j}, c, h, hc, ht, ha => app_back_s_{j} ht (none_of_class_{j} c _ h hc) ha").unwrap();
            } else {
                writeln!(arms_t, "  | {j}, c, h, _, _, _ => by simp [appSafe, appSafe{j}] at h").unwrap();
                writeln!(arms_s, "  | {j}, c, h, _, _, _ => by simp [appSafe, appSafe{j}] at h").unwrap();
            }
        }
        writeln!(arms_t, "  | _ + {max_rank}, _, h, _, _, _ => by simp [appSafe] at h").unwrap();
        writeln!(arms_s, "  | _ + {max_rank}, _, h, _, _, _ => by simp [appSafe] at h").unwrap();
        writeln!(o, "\ntheorem app_back {{k t t' ch}} {{c c' : {topt}}} : ∀ (j : Nat) (cl : Cls), appSafe j cl = true → InClass cl ch →\n    TStep k t t' ch c c' → {} → {}\n{arms_t}", app("j", "c'"), app("j", "c")).unwrap();
        writeln!(o, "\ntheorem app_back_s {{ch}} {{c c' : {topt}}} : ∀ (j : Nat) (cl : Cls), appSafe j cl = true → InClass cl ch →\n    SStep ch c c' → {} → {}\n{arms_s}", app("j", "c'"), app("j", "c")).unwrap();
        writeln!(o, "\ndef safe (cl : Cls) (i : Nat) : Bool := (List.range i).all (fun j => appSafe j cl)\n\ntheorem safe_spec {{cl : Cls}} {{i j : Nat}} (h : safe cl i = true) (hj : j < i) : appSafe j cl = true := by\n  unfold safe at h\n  rw [List.all_eq_true] at h\n  exact h j (List.mem_range.2 hj)").unwrap();
        // the rules
        let rs = &lib.rules;
        writeln!(o, "\n/-- The rules. -/\ninductive Rule where\n{}\n  deriving DecidableEq", rs.iter().map(|r| format!("  | {}", r.lean)).collect::<Vec<_>>().join("\n")).unwrap();
        writeln!(o, "\ninductive RKind where\n  | thread | shared | global\n  deriving DecidableEq").unwrap();
        writeln!(o, "\ndef Rule.rank : Rule → Nat\n{}", rs.iter().map(|r| format!("  | .{} => {}", r.lean, rank(r))).collect::<Vec<_>>().join("\n")).unwrap();
        writeln!(o, "\ndef Rule.kind : Rule → RKind\n{}", rs.iter().zip(&kinds).map(|(r, k)| format!("  | .{} => .{}", r.lean, match k { Kind::Thread => "thread", Kind::Shared => "shared", Kind::Global => "global" })).collect::<Vec<_>>().join("\n")).unwrap();
        writeln!(o, "\ndef Rule.cls : Rule → Cls\n{}", rs.iter().zip(&cls).map(|(r, c)| format!("  | .{} => .c{c}", r.lean)).collect::<Vec<_>>().join("\n")).unwrap();
        writeln!(o, "\ndef Rule.key : Rule → KeyPat\n{}", rs.iter().zip(&keys).map(|(r, k)| format!("  | .{} => {k}", r.lean)).collect::<Vec<_>>().join("\n")).unwrap();
        writeln!(o, "\n/-- A step by rule `r`: every per-rule property of `r` holds of it. -/\ndef StepBy : Rule → {topt} → {topt} → Prop\n{}", rs.iter().map(|r| format!("  | .{l}, c, c' => ∀ Q, {name}.Step.Rel.{l} Q → Q c c'", l = r.lean)).collect::<Vec<_>>().join("\n")).unwrap();
        writeln!(o, "\n/-- What a step by `r` is, beyond `Step`: one thread's step, a step of the shared cells, or nothing\nmore (`global`). -/\ndef VPart (r : Rule) (c c' : {topt}) : Prop :=\n  match r.kind with\n  | .thread => ∃ k t t' ch, TStep k t t' ch c c' ∧ Local r.rank k t t' ch ∧ InClass r.cls ch ∧ r.key.matches (tkey t) = true\n  | .shared => ∃ ch, SStep ch c c' ∧ LocalS r.rank ch ∧ InClass r.cls ch\n  | .global => True").unwrap();
        writeln!(o, "\ndef ViewOf (r : Rule) (c c' : {topt}) : Prop :=\n  {name}.App r.rank c ∧ (∀ j, j < r.rank → ¬ {name}.App j c) ∧ StepBy r c c' ∧ VPart r c c'").unwrap();
        // the frames
        let mut frame_names = vec![];
        for (ri, r) in rs.iter().enumerate() {
            let l = &r.lean;
            let rk = rank(r);
            let mut args = rules::ctor_args(&r.step);
            if rk > 0 && !args.iter().any(|a| a == "hpri") {
                args.push("hpri".into());
            }
            let app_named: String = r.app.hyps.iter().map(|(h, _)| format!(" ({h} := {h})")).collect();
            let pri = if rk > 0 { "hpri".to_string() } else { "fun j hj => absurd hj (Nat.not_lt_zero j)".to_string() };
            let touch = &touches[ri];
            let c = &classes[cls[ri]];
            let k = c.iter().filter(|t| **t != Touch::Write).count();
            let inclass = {
                let parts: Vec<&str> = (0..n).filter_map(|f| match touch[f] { Touch::None => Some("rfl"), Touch::Read => Some("⟨_, rfl⟩"), Touch::Write => None }).collect();
                if parts.is_empty() { "trivial".to_string() } else if parts.len() == 1 { parts[0].to_string() } else { format!("⟨{}⟩", parts.join(", ")) }
            };
            let _ = k;
            let chlit = {
                let fs: Vec<String> = (0..n).filter(|&i| touch[i] != Touch::None).map(|i| format!("{} := some (_, _)", shared[i].field)).collect();
                if fs.is_empty() { "{}".to_string() } else { format!("{{ {} }}", fs.join(", ")) }
            };
            let pres: Vec<&str> = (0..n).map(|i| if touch[i] == Touch::None { "Ch.pre_none" } else { "Ch.pre_self" }).collect();
            let unders = vec!["_"; n].join(", ");
            let vars: Vec<String> = (0..n).map(|i| format!("v{i}")).collect();
            let cases_pre: String = (0..n).filter(|&i| touch[i] != Touch::None).map(|i| format!("    cases ({} _ rfl)\n", proj("hpre", i))).collect();
            let vpart = match kinds[ri] {
                Kind::Thread => {
                    let MapRole::Update { hm, hr } = &roles[ri] else { unreachable!() };
                    let mut named = format!("({hm} := hm') ({hr} := hr')");
                    if rk > 0 { named.push_str(" (hpri := hpri')"); }
                    for (h, _) in &r.step.hyps {
                        if h != hm && h != hr && h != "hpri" { write!(named, " ({h} := {h})").unwrap(); }
                    }
                    format!("  simp only [VPart, Rule.kind, Rule.rank, Rule.cls, Rule.key, InClass]\n  refine ⟨_, _, _, {chlit}, ⟨_, _, _, ⟨{unders}⟩, rfl, {hm}, {hr}, ⟨{}⟩, rfl⟩, ?_, {inclass}, rfl⟩\n  rintro d d' ⟨_, _, _, ⟨{}⟩, rfl, hm', hr', hpre, rfl⟩ hpri'\n{}  exact {name}.Step.{l} {named} ..",
                        pres.join(", "), vars.join(", "), cases_pre.replace("    cases", "  cases"))
                }
                Kind::Shared => {
                    let mut named = String::new();
                    if rk > 0 { named.push_str(" (hpri := hpri')"); }
                    for (h, _) in &r.step.hyps {
                        if h != "hpri" { write!(named, " ({h} := {h})").unwrap(); }
                    }
                    format!("  simp only [VPart, Rule.kind, Rule.rank, Rule.cls, InClass]\n  refine ⟨{chlit}, ⟨_, ⟨{unders}⟩, rfl, ⟨{}⟩, rfl⟩, ?_, {inclass}⟩\n  rintro d d' ⟨_, ⟨{}⟩, rfl, hpre, rfl⟩ hpri'\n{}  exact {name}.Step.{l}{named} ..",
                        pres.join(", "), vars.join(", "), cases_pre.replace("    cases", "  cases"))
                }
                Kind::Global => "  simp only [VPart, Rule.kind]".to_string(),
            };
            writeln!(o, "\ntheorem frame.{l} : {name}.Step.Rel.{l} (fun c c' => ∃ r, ViewOf r c c') := by\n  intro {}\n  refine ⟨.{l}, {name}.App.{l}{app_named} .., {pri}, fun Q hQ => hQ {}, ?_⟩\n{vpart}",
                args.join(" "), args.join(" ")).unwrap();
            frame_names.push(format!("frame.{l}"));
        }
        writeln!(o, "\ntheorem view_of {{c c' : {topt}}} (h : {name}.Step c c') : ∃ r, ViewOf r c c' :=\n  {name}.Step.rel_of {} h", frame_names.join(" ")).unwrap();
        // the pairs decided without looking at them
        writeln!(o, "\ntheorem compatTbl_symm : ∀ a b : Cls, compatTbl a b = compatTbl b a := by\n  intro a b; cases a <;> cases b <;> rfl").unwrap();
        writeln!(o, "\n/-- Two rules whose steps from one configuration join by the generic arguments, unless both step
one thread: of different ranks (they never both apply), or each stepping one thread or the
shared cells, touching compatible cells and not enabling a rule of a rank before the other's. -/
def staticOK (r₁ r₂ : Rule) : Bool :=
  r₁.rank != r₂.rank ||
    (match r₁.kind, r₂.kind with
     | .thread, .thread | .thread, .shared | .shared, .thread | .shared, .shared =>
       compatTbl r₁.cls r₂.cls && safe r₁.cls r₂.rank && safe r₂.cls r₁.rank
     | _, _ => false)").unwrap();
        writeln!(o, "\n/-- The joins of two steps of one thread by two rules of one rank whose keys (the first item of
the thread's `<k>`) may be equal. Nothing generic decides them: they are the determinism of one
thread. -/
def SameThreadJoins : Prop :=
  ∀ r₁ r₂, r₁.kind = .thread → r₂.kind = .thread → r₁.rank = r₂.rank → r₁.key.disj r₂.key = false →
    ∀ {{c c₁ c₂ : {topt}}} {{k t₁ t₁' ch₁ t₂ t₂' ch₂}}, StepBy r₁ c c₁ → StepBy r₂ c c₂ →
      TStep k t₁ t₁' ch₁ c c₁ → TStep k t₂ t₂' ch₂ c c₂ → DiamondMod {name}.Step Eq c₁ c₂").unwrap();
        writeln!(o, "\ntheorem join_static (S : SameThreadJoins) {{r₁ r₂ : Rule}} {{c c₁ c₂ : {topt}}} (hs : staticOK r₁ r₂ = true)
    (v₁ : ViewOf r₁ c c₁) (v₂ : ViewOf r₂ c c₂) : DiamondMod {name}.Step Eq c₁ c₂ := by
  obtain ⟨a₁, p₁, b₁, w₁⟩ := v₁
  obtain ⟨a₂, p₂, b₂, w₂⟩ := v₂
  by_cases hr : r₁.rank ≠ r₂.rank
  · rcases Nat.lt_or_gt_of_ne hr with h | h
    · exact absurd a₁ (p₂ _ h)
    · exact absurd a₂ (p₁ _ h)
  have hr := Decidable.of_not_not hr
  have hne : (r₁.rank != r₂.rank) = false := by simp only [hr, bne_self_eq_false]
  simp only [staticOK, hne, Bool.false_or] at hs
  unfold VPart at w₁ w₂
  revert w₁ w₂ hs
  cases hk₁ : r₁.kind <;> cases hk₂ : r₂.kind <;> intro w₁ w₂ hs <;> simp only [Bool.and_eq_true, Bool.false_eq_true] at hs
  · obtain ⟨k₁, t₁, t₁', ch₁, ts₁, l₁, i₁, m₁⟩ := w₁
    obtain ⟨k₂, t₂, t₂', ch₂, ts₂, l₂, i₂, m₂⟩ := w₂
    obtain ⟨⟨hc, hs₁⟩, hs₂⟩ := hs
    by_cases hk : k₁ = k₂
    · subst hk
      cases hd : r₁.key.disj r₂.key
      · exact S r₁ r₂ hk₁ hk₂ hr hd b₁ b₂ ts₁ ts₂
      · have ht := tstep_same ts₁ ts₂
        subst ht
        exact (KeyPat.disj_sound hd m₁ m₂).elim
    · obtain ⟨c₁₂, x, y⟩ := tstep_comm ts₁ ts₂ hk (compat_of _ _ hc _ _ i₁ i₂)
      refine ⟨c₁₂, c₁₂, Or.inr (l₂ _ _ x ?_), Or.inr (l₁ _ _ y ?_), rfl⟩
      · intro j hj ha; exact p₂ j hj (app_back j _ (safe_spec hs₁ hj) i₁ ts₁ ha)
      · intro j hj ha; exact p₁ j hj (app_back j _ (safe_spec hs₂ hj) i₂ ts₂ ha)
  · obtain ⟨k₁, t₁, t₁', ch₁, ts₁, l₁, i₁, -⟩ := w₁
    obtain ⟨ch₂, ss₂, l₂, i₂⟩ := w₂
    obtain ⟨⟨hc, hs₁⟩, hs₂⟩ := hs
    obtain ⟨c₁₂, x, y⟩ := tstep_sstep_comm ts₁ ss₂ (compat_of _ _ hc _ _ i₁ i₂)
    refine ⟨c₁₂, c₁₂, Or.inr (l₂ _ _ x ?_), Or.inr (l₁ _ _ y ?_), rfl⟩
    · intro j hj ha; exact p₂ j hj (app_back j _ (safe_spec hs₁ hj) i₁ ts₁ ha)
    · intro j hj ha; exact p₁ j hj (app_back_s j _ (safe_spec hs₂ hj) i₂ ss₂ ha)
  · obtain ⟨ch₁, ss₁, l₁, i₁⟩ := w₁
    obtain ⟨k₂, t₂, t₂', ch₂, ts₂, l₂, i₂, -⟩ := w₂
    obtain ⟨⟨hc, hs₁⟩, hs₂⟩ := hs
    obtain ⟨c₁₂, x, y⟩ := tstep_sstep_comm ts₂ ss₁ (compat_of _ _ ((compatTbl_symm _ _).trans hc) _ _ i₂ i₁)
    refine ⟨c₁₂, c₁₂, Or.inr (l₂ _ _ y ?_), Or.inr (l₁ _ _ x ?_), rfl⟩
    · intro j hj ha; exact p₂ j hj (app_back_s j _ (safe_spec hs₁ hj) i₁ ss₁ ha)
    · intro j hj ha; exact p₁ j hj (app_back j _ (safe_spec hs₂ hj) i₂ ts₂ ha)
  · obtain ⟨ch₁, ss₁, l₁, i₁⟩ := w₁
    obtain ⟨ch₂, ss₂, l₂, i₂⟩ := w₂
    obtain ⟨⟨hc, hs₁⟩, hs₂⟩ := hs
    obtain ⟨c₁₂, x, y⟩ := sstep_comm ss₁ ss₂ (compat_of _ _ hc _ _ i₁ i₂)
    refine ⟨c₁₂, c₁₂, Or.inr (l₂ _ _ x ?_), Or.inr (l₁ _ _ y ?_), rfl⟩
    · intro j hj ha; exact p₂ j hj (app_back_s j _ (safe_spec hs₁ hj) i₁ ss₁ ha)
    · intro j hj ha; exact p₁ j hj (app_back_s j _ (safe_spec hs₂ hj) i₂ ss₂ ha)").unwrap();
        writeln!(o, "\n/-- The joins the generic arguments leave in every configuration: one per ordered pair of rules that
`staticOK` rejects. -/\ndef OpenJoins : Prop :=\n  ∀ r₁ r₂, staticOK r₁ r₂ = false → ∀ {{c c₁ c₂ : {topt}}}, StepBy r₁ c c₁ → StepBy r₂ c c₂ →\n    DiamondMod {name}.Step Eq c₁ c₂").unwrap();
        writeln!(o, "\ntheorem joins_of (O : OpenJoins) (S : SameThreadJoins) {{c c₁ c₂ : {topt}}} (h₁ : {name}.Step c c₁)\n    (h₂ : {name}.Step c c₂) : DiamondMod {name}.Step Eq c₁ c₂ := by\n  obtain ⟨r₁, v₁⟩ := view_of h₁\n  obtain ⟨r₂, v₂⟩ := view_of h₂\n  cases hs : staticOK r₁ r₂\n  · exact O r₁ r₂ hs v₁.2.2.1 v₂.2.2.1\n  · exact join_static S hs v₁ v₂").unwrap();
        writeln!(o, "\n/-- Given the joins left open, two runs that end in terminal configurations end in the same one. -/\ntheorem terminal_unique_of (O : OpenJoins) (S : SameThreadJoins) {{c n₁ n₂ : {topt}}}\n    (h₁ : Star {name}.Step c n₁) (t₁ : Terminal {name}.Step n₁) (h₂ : Star {name}.Step c n₂)\n    (t₂ : Terminal {name}.Step n₂) : n₁ = n₂ :=\n  terminal_unique_of_diamond (H := fun _ => True) StepEquiv.eq (fun _ _ _ _ => trivial)\n    (fun _ h₁ h₂ => joins_of O S h₁ h₂) trivial h₁ t₁ h₂ t₂").unwrap();
        writeln!(o, "\n#k2l_assert_axioms tstep_comm compat_of app_back app_back_s view_of join_static joins_of terminal_unique_of").unwrap();
        // the count
        let safe = |c: usize, i: usize| (0..i).all(|j| j < max_rank && safe_tbl(j, c));
        let mut open = 0usize;
        let mut same = 0usize;
        for (i, r1) in rs.iter().enumerate() {
            for (j, r2) in rs.iter().enumerate() {
                if rank(r1) == rank(r2) && kinds[i] == Kind::Thread && kinds[j] == Kind::Thread && !keyps[i].disj(&keyps[j]) {
                    same += 1;
                }
                let ok = rank(r1) != rank(r2) || match (kinds[i], kinds[j]) {
                    (Kind::Global, _) | (_, Kind::Global) => false,
                    _ => compat(&classes[cls[i]], &classes[cls[j]]) && safe(cls[i], rank(r2)) && safe(cls[j], rank(r1)),
                };
                if !ok {
                    open += 1;
                    if std::env::var("K2L_CNF_DEBUG").is_ok() {
                        let why = match (kinds[i], kinds[j]) {
                            (Kind::Global, _) | (_, Kind::Global) => "global".to_string(),
                            _ => format!("compat={} disj={} safe12={} safe21={} kinds={:?}/{:?}",
                                compat(&classes[cls[i]], &classes[cls[j]]), keyps[i].disj(&keyps[j]),
                                safe(cls[i], rank(r2)), safe(cls[j], rank(r1)), kinds[i], kinds[j]),
                        };
                        eprintln!("open\t{}\t{}\t{}\t{}\t{}", rank(r1), why, keys[i], keys[j], cls[i]);
                    }
                }
            }
        }
        eprintln!("confluence: {} rules ({} thread, {} shared, {} global), {} classes; of {} ordered pairs, {} left open, {} same-thread pairs left open", rs.len(),
            kinds.iter().filter(|k| **k == Kind::Thread).count(), kinds.iter().filter(|k| **k == Kind::Shared).count(),
            kinds.iter().filter(|k| **k == Kind::Global).count(), classes.len(), rs.len() * rs.len(), open, same);
        writeln!(o, "\nend {ns}").unwrap();
        o
    }
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
