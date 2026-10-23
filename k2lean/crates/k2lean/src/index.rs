//! Rule indexing: a decision tree over constructor positions of the left-hand sides, so that a
//! step tries only the rules whose left-hand side can match (`bucketOf c`). Correctness needs
//! only that every rule that applies at `c` is in `bucketOf c` (proved per rule); the order of
//! rules in a bucket is the order of `rules`.

use crate::lower::L;
use std::collections::{BTreeMap, BTreeSet};

/// For each fully qualified Lean constructor: (number of constructors of its type, arity).
pub type CtorInfo = BTreeMap<String, (usize, usize)>;

/// A node of a left-hand side: the constructors and argument positions from the root.
type Path = Vec<(String, usize)>;

enum At<'a> {
    Ctor(&'a str, usize),
    Var,
    Absent,
}

fn at<'a>(l: &'a L, path: &[(String, usize)], info: &CtorInfo) -> At<'a> {
    let mut cur = l;
    for (ctor, pos) in path {
        match cur {
            L::App(h, args) if info.contains_key(h) => {
                if h != ctor {
                    return At::Absent;
                }
                cur = &args[*pos];
            }
            _ => return At::Var,
        }
    }
    match cur {
        L::App(h, args) if info.contains_key(h) => At::Ctor(h, args.len()),
        _ => At::Var,
    }
}

pub enum Tree {
    Leaf(Vec<usize>),
    /// Observe the node at `path` (its ancestors' constructors are `facts`): the rules with a
    /// constructor there are in `branches`; the rules with a variable there are in `rest`,
    /// which is consulted for every configuration (no rule is copied into two subtrees).
    Node {
        facts: BTreeMap<Path, String>,
        path: Path,
        branches: Vec<(String, usize, Tree)>,
        rest: Box<Tree>,
    },
}

pub fn build(lhs: &[&L], info: &CtorInfo) -> Tree {
    let all: Vec<usize> = (0..lhs.len()).collect();
    go(lhs, info, &all, &BTreeMap::new(), 0)
}

const MAX_DEPTH: usize = 12;
const LEAF: usize = 3;

fn candidates(facts: &BTreeMap<Path, String>, info: &CtorInfo) -> BTreeSet<Path> {
    let mut cands: BTreeSet<Path> = BTreeSet::new();
    if !facts.contains_key(&vec![]) {
        cands.insert(vec![]);
    }
    for (p, c) in facts {
        let (_, arity) = info[c];
        for i in 0..arity {
            let mut q = p.clone();
            q.push((c.clone(), i));
            if !facts.contains_key(&q) {
                cands.insert(q);
            }
        }
    }
    cands
}

fn go(
    lhs: &[&L],
    info: &CtorInfo,
    rules: &[usize],
    facts0: &BTreeMap<Path, String>,
    depth: usize,
) -> Tree {
    if rules.len() <= LEAF || depth >= MAX_DEPTH {
        return Tree::Leaf(rules.to_vec());
    }
    // nodes of single-constructor types are known without a test: add them to the facts
    let mut facts = facts0.clone();
    loop {
        let mut changed = false;
        for p in candidates(&facts, info) {
            let mut seen: BTreeSet<&str> = BTreeSet::new();
            for &r in rules {
                if let At::Ctor(h, _) = at(lhs[r], &p, info) {
                    seen.insert(h);
                }
            }
            if seen.len() == 1 {
                let c = *seen.iter().next().unwrap();
                if info[c].0 == 1 {
                    facts.insert(p, c.to_string());
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    // the node that splits the rules with a constructor there into the most groups (ties: more
    // such rules, shallower)
    let mut best: Option<(usize, usize, usize, Path)> = None;
    for p in candidates(&facts, info) {
        let mut by: BTreeMap<String, usize> = BTreeMap::new();
        let mut has_args = false;
        for &r in rules {
            if let At::Ctor(h, a) = at(lhs[r], &p, info) {
                *by.entry(h.to_string()).or_default() += 1;
                has_args |= a > 0;
            }
        }
        let with_ctor: usize = by.values().sum();
        if with_ctor == 0 || (by.len() == 1 && !has_args) {
            continue;
        }
        // a node with one constructor only helps by opening deeper nodes
        let key = (by.len().min(2), with_ctor, usize::MAX - p.len(), p.clone());
        if best
            .as_ref()
            .is_none_or(|b| (key.0, key.1, key.2) > (b.0, b.1, b.2))
        {
            best = Some(key);
        }
    }
    let Some((_, _, _, path)) = best else {
        return Tree::Leaf(rules.to_vec());
    };
    let mut ctors: Vec<(String, usize)> = Vec::new();
    for &r in rules {
        if let At::Ctor(h, a) = at(lhs[r], &path, info)
            && !ctors.iter().any(|(c, _)| c == h)
        {
            ctors.push((h.to_string(), a));
        }
    }
    let mut branches = Vec::new();
    for (c, a) in &ctors {
        let sub: Vec<usize> = rules
            .iter()
            .copied()
            .filter(|&r| matches!(at(lhs[r], &path, info), At::Ctor(h, _) if h == c))
            .collect();
        let mut f = facts.clone();
        f.insert(path.clone(), c.clone());
        branches.push((c.clone(), *a, go(lhs, info, &sub, &f, depth + 1)));
    }
    let rest: Vec<usize> = rules
        .iter()
        .copied()
        .filter(|&r| matches!(at(lhs[r], &path, info), At::Var))
        .collect();
    let rest = Box::new(go(lhs, info, &rest, &facts, depth + 1));
    Tree::Node {
        facts,
        path,
        branches,
        rest,
    }
}

/// The pattern for the root with the known constructors, `x` at `target`, `_` elsewhere.
fn prefix_pattern(
    facts: &BTreeMap<Path, String>,
    target: &Path,
    info: &CtorInfo,
    at: &Path,
) -> String {
    if at == target {
        return "x".to_string();
    }
    if !target.starts_with(at) {
        return "_".to_string();
    }
    match facts.get(at) {
        None => "_".to_string(),
        Some(c) => {
            let (_, arity) = info[c];
            let mut s = c.clone();
            for i in 0..arity {
                let mut q = at.clone();
                q.push((c.clone(), i));
                let sub = prefix_pattern(facts, target, info, &q);
                if sub.contains(' ') {
                    s.push_str(&format!(" ({sub})"));
                } else {
                    s.push_str(&format!(" {sub}"));
                }
            }
            s
        }
    }
}

fn refutable(facts: &BTreeMap<Path, String>, target: &Path, info: &CtorInfo) -> bool {
    // only the facts on the way to the target are in the pattern
    facts
        .iter()
        .any(|(p, c)| target.starts_with(p) && p != target && info[c].0 > 1)
}

/// Lean code of `bucketOf`: `names[i]` is the Lean constant of rule `i`.
pub fn emit(t: &Tree, names: &[String], info: &CtorInfo, ind: usize) -> String {
    let pad = " ".repeat(ind);
    match t {
        Tree::Leaf(rs) => {
            let items: Vec<&str> = rs.iter().map(|&i| names[i].as_str()).collect();
            format!("{pad}[{}]\n", items.join(", "))
        }
        Tree::Node {
            facts,
            path,
            branches,
            rest,
        } => {
            let rest_empty = matches!(&**rest, Tree::Leaf(v) if v.is_empty());
            let mut o = String::new();
            let ind = if rest_empty {
                ind
            } else {
                o.push_str(&format!("{pad}mergeRank\n{pad}  (\n"));
                ind + 4
            };
            let pad2 = " ".repeat(ind);
            let pat = prefix_pattern(facts, path, info, &vec![]);
            let inner = if pat == "x" { ind } else { ind + 2 };
            let ipad = " ".repeat(inner);
            if pat == "x" {
                o.push_str(&format!("{pad2}match c with\n"));
            } else {
                o.push_str(&format!(
                    "{pad2}match c with\n{pad2}| {pat} =>\n{ipad}match x with\n"
                ));
            }
            let mut ncons = 0;
            for (c, a, sub) in branches {
                ncons = info[c].0;
                let wild = vec!["_"; *a].join(" ");
                o.push_str(&format!("{ipad}| {c} {wild} =>\n"));
                o.push_str(&emit(sub, names, info, inner + 2));
            }
            if branches.len() < ncons {
                o.push_str(&format!("{ipad}| _ => []\n"));
            }
            if pat != "x" && refutable(facts, path, info) {
                o.push_str(&format!("{pad2}| _ => []\n"));
            }
            if !rest_empty {
                o.push_str(&format!("{pad}  )\n{pad}  (\n"));
                o.push_str(&emit(rest, names, info, ind));
                o.push_str(&format!("{pad}  )\n"));
            }
            o
        }
    }
}

/// One step from a bucket expression to a smaller one that holds rule `r` (`mem_tactic`).
#[derive(Clone, Copy)]
enum MemStep {
    /// `mergeRank (branches) rest`, `r` in the branch taken at its own constructor
    Left,
    /// `mergeRank (branches) rest`, `r` in `rest` (its left-hand side has a variable there)
    Right,
    /// a list literal, `r` at this position
    Elem(usize),
}

fn mem_path(t: &Tree, r: usize, lhs: &L, info: &CtorInfo, out: &mut Vec<MemStep>) -> bool {
    match t {
        Tree::Leaf(rs) => match rs.iter().position(|&x| x == r) {
            Some(k) => {
                out.push(MemStep::Elem(k));
                true
            }
            None => false,
        },
        Tree::Node {
            path,
            branches,
            rest,
            ..
        } => {
            let rest_empty = matches!(&**rest, Tree::Leaf(v) if v.is_empty());
            match at(lhs, path, info) {
                At::Ctor(h, _) => {
                    let Some((_, _, sub)) = branches.iter().find(|(c, _, _)| c == h) else {
                        return false;
                    };
                    if !rest_empty {
                        out.push(MemStep::Left);
                    }
                    mem_path(sub, r, lhs, info, out)
                }
                At::Var if !rest_empty => {
                    out.push(MemStep::Right);
                    mem_path(rest, r, lhs, info, out)
                }
                _ => false,
            }
        }
    }
}

/// The proof that rule `r` of the left-hand sides `t` was built from is in the bucket of its own
/// left-hand side `lhs`, or of an instance of it: the path through the tree, one `apply` per
/// node. Each `apply` unifies with the bucket expression at that node, which reduces by one
/// `match` on a constructor of the left-hand side (or is a `mergeRank`), so no tactic traverses
/// the off-path parts of the index. `None` if `r` is not where its left-hand side leads, which
/// would be a bug of `build`.
pub fn mem_tactic(t: &Tree, r: usize, lhs: &L, info: &CtorInfo) -> Option<String> {
    let mut steps = Vec::new();
    if !mem_path(t, r, lhs, info, &mut steps) {
        return None;
    }
    let mut o = String::new();
    for s in steps {
        match s {
            MemStep::Left => o.push_str("  apply KPrelude.mem_mergeRank_left\n"),
            MemStep::Right => o.push_str("  apply KPrelude.mem_mergeRank_right\n"),
            MemStep::Elem(k) => {
                for _ in 0..k {
                    o.push_str("  apply List.mem_cons_of_mem\n");
                }
                o.push_str("  exact List.mem_cons_self\n");
            }
        }
    }
    Some(o)
}

/// The membership proof of rule `r` of `lhs`, along its path, or (if no path is found, a bug of
/// `build`) by search in the bucket `bucket` reduced on the left-hand side.
pub fn mem_tactic_or_search(t: &Tree, r: usize, lhs: &L, info: &CtorInfo, bucket: &str) -> String {
    mem_tactic(t, r, lhs, info).unwrap_or_else(|| format!("  dsimp only [{bucket}]\n  k2l_mem\n"))
}

/// Statistics for the report: (number of leaves, largest leaf, average leaf size).
pub fn stats(t: &Tree) -> (usize, usize, usize) {
    fn walk(t: &Tree, out: &mut Vec<usize>) {
        match t {
            Tree::Leaf(r) => out.push(r.len()),
            Tree::Node { branches, rest, .. } => {
                for (_, _, b) in branches {
                    walk(b, out);
                }
                walk(rest, out);
            }
        }
    }
    let mut v = Vec::new();
    walk(t, &mut v);
    let max = v.iter().max().copied().unwrap_or(0);
    let sum: usize = v.iter().sum();
    (v.len(), max, if v.is_empty() { 0 } else { sum / v.len() })
}
