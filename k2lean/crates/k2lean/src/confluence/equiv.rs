//! `confluence --equiv CELL=REL,…`: the theorem modulo an equivalence the author states, per leaf
//! cell of the configuration (`k2lean/docs/design.md`, §3.6, "Modulo an equivalence"). Every cell
//! is compared by equality but those named: `any`, not compared, or `perm`, a list compared up to
//! the order of its items (`KPrelude.ListHook.Perm`).
//!
//! The module states `Equiv` (a conjunction over the cells' contents, `cell.X`), its laws, and that
//! it is a strong bisimulation of `Step` (`equiv_stepEquiv`), from one lemma per rule
//! (`equiv.sim.r`): the rule applies at a related configuration, and the two results are related.
//! That holds generically when the rule reads no relaxed cell (its left-hand side has a variable
//! there, used nowhere else) and, for `perm`, rebuilds the list from that variable by the list
//! hooks; a rule that does not is refused by name. With priority ranks, a rule of a later rank owes
//! at the related configuration that no rule of an earlier rank applies there: such a rule reads
//! no relaxed cell either, so it would apply at the first configuration too (`k2l_pri_other`,
//! `KPrelude/OtherRun.lean`). The views' and slots' statements are then
//! moved onto `Equiv` (`apply`): the joins are modulo `Equiv`, the theorem is `Equiv n₁ n₂`, and the
//! observation's corollary follows by `obs_of_equiv`.

use super::{Lib, fail, is_cell};
use crate::lower::L;
use crate::model::{Coll, Kind, Model};
use crate::names;
use crate::rules::{self, Rule};
use std::fmt::Write as _;

/// How a relaxed cell is compared.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Rel {
    /// Not compared.
    Any,
    /// A list, up to the order of its items.
    Perm,
}

impl Rel {
    fn name(self) -> &'static str {
        match self {
            Rel::Any => "any",
            Rel::Perm => "perm",
        }
    }
}

/// A node of the configuration's tree of cells: its sort, its constructor, and its children
/// (inner) or the sorts of its content (leaf).
struct Node {
    sort: String,
    ctor: String,
    kids: Vec<Node>,
    /// a leaf: its label and the sort of its content
    leaf: Option<(String, String)>,
}

/// A leaf cell: its label, its field name, the sort of its content, the path of argument
/// positions to it, and how it is compared (`None`: by equality).
pub(crate) struct Cell {
    pub label: String,
    field: String,
    content: String,
    path: Vec<(String, usize, usize)>,
    pub rel: Option<Rel>,
}

/// The equivalence `--equiv` states.
pub(crate) struct Equiv {
    root: Node,
    pub cells: Vec<Cell>,
}

fn cell_sort(m: &Model, s: &str) -> Option<String> {
    let info = m.sorts.get(s)?;
    let [c] = info.own.as_slice() else {
        return None;
    };
    let k = &m.ctors[c].klabel;
    (k.starts_with('<') && k.ends_with('>')).then(|| c.clone())
}

fn walk(m: &Model, s: &str, name: &str) -> Node {
    let c = cell_sort(m, s).unwrap_or_else(|| fail(&format!("--equiv: {s} is not a cell")));
    let args = m.ctors[&c].args.clone();
    let ctor = format!("{name}.{}", m.ctor_path(&c));
    if !args.is_empty() && args.iter().all(|a| cell_sort(m, a).is_some()) {
        Node {
            sort: s.to_string(),
            ctor,
            kids: args.iter().map(|a| walk(m, a, name)).collect(),
            leaf: None,
        }
    } else {
        let label = m.ctors[&c]
            .klabel
            .trim_start_matches('<')
            .trim_end_matches('>')
            .to_string();
        let [content] = args.as_slice() else {
            fail(&format!(
                "--equiv: the cell <{label}> has {} arguments, not one content",
                args.len()
            ))
        };
        Node {
            sort: s.to_string(),
            ctor,
            kids: vec![],
            leaf: Some((label, content.clone())),
        }
    }
}

/// `--equiv CELL=REL,…`, against the configuration of `lib`.
pub(crate) fn parse(spec: &str, lib: &Lib, name: &str) -> Equiv {
    let root = walk(&lib.m, &lib.top, name);
    let mut cells = vec![];
    fn leaves(n: &Node, path: &mut Vec<(String, usize, usize)>, out: &mut Vec<Cell>) {
        if let Some((label, content)) = &n.leaf {
            out.push(Cell {
                field: names::ident(&label.replace('-', "_")),
                label: label.clone(),
                content: content.clone(),
                path: path.clone(),
                rel: None,
            });
            return;
        }
        for (i, k) in n.kids.iter().enumerate() {
            path.push((n.ctor.clone(), n.kids.len(), i));
            leaves(k, path, out);
            path.pop();
        }
    }
    leaves(&root, &mut vec![], &mut cells);
    for item in spec.split(',') {
        let Some((c, r)) = item.split_once('=') else {
            fail(&format!("--equiv: `{item}` is not CELL=REL"))
        };
        let rel = match r {
            "any" => Rel::Any,
            "perm" => Rel::Perm,
            _ => fail(&format!(
                "--equiv: `{r}` is not a relation (`any`: not compared; `perm`: a list up to order)"
            )),
        };
        let Some(cell) = cells.iter_mut().find(|x| x.label == c) else {
            fail(&format!(
                "--equiv: <{c}> is not a leaf cell of the configuration (cells holding other cells, and the cells of a cell map's bindings, are not compared on their own)"
            ))
        };
        if cell.rel.is_some() {
            fail(&format!("--equiv: <{c}> is named twice"));
        }
        if rel == Rel::Perm
            && !matches!(
                lib.m.sorts.get(&cell.content).map(|s| &s.kind),
                Some(Kind::Coll(Coll::List))
            )
        {
            fail(&format!(
                "--equiv: <{c}> holds a {}, not a list: `perm` compares a list up to the order of its items",
                cell.content
            ));
        }
        cell.rel = Some(rel);
    }
    if cells.iter().all(|c| c.rel == Some(Rel::Any)) {
        fail("--equiv: every cell is `any`: the equivalence relates every two configurations");
    }
    Equiv { root, cells }
}

/// The free variables of a term, by name.
fn occurs(l: &L, v: &str) -> bool {
    match l {
        L::Var(x) => x == v,
        L::App(_, a) => a.iter().any(|x| occurs(x, v)),
        L::Raw(r) => r
            .split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
            .any(|w| w == v),
        L::Typed(x, _) => occurs(x, v),
    }
}

/// The left- and right-hand sides of a rule at each leaf cell, by label: the walk of
/// `footprint`, a leaf being a cell term or a variable standing for a whole cell (named by its
/// sort).
fn rule_leaves(eq: &Equiv, r: &Rule) -> Vec<(String, L, L)> {
    let rhs = r.rhs.subst(&r.step.subst);
    let mut out = vec![];
    fn go(a: &L, b: &L, out: &mut Vec<(String, L, L)>) {
        if let (L::App(ha, xa), L::App(hb, xb)) = (a, b)
            && ha == hb
            && xa.len() == xb.len()
            && xa
                .iter()
                .any(|x| matches!(x, L::App(h, _) if is_cell(h).is_some()))
        {
            for (x, y) in xa.iter().zip(xb) {
                go(x, y, out);
            }
            return;
        }
        let name = match a {
            L::App(h, _) => is_cell(h).unwrap_or_else(|| "?".into()),
            _ => "?".into(),
        };
        out.push((name, a.clone(), b.clone()));
    }
    go(&r.step.index, &rhs, &mut out);
    // a variable standing for a whole cell: its cell, by its sort
    for (name, a, _) in out.iter_mut() {
        if name == "?"
            && let L::Var(v) = a
            && let Some((_, t)) = r.step.binders.iter().find(|(x, _)| x == v)
        {
            let mut found = None;
            fn find<'a>(n: &'a Node, t: &str, found: &mut Option<&'a str>) {
                if n.sort == t
                    && let Some((label, _)) = &n.leaf
                {
                    *found = Some(label);
                }
                n.kids.iter().for_each(|k| find(k, t, found));
            }
            find(&eq.root, t, &mut found);
            if let Some(l) = found {
                *name = l.to_string();
            }
        }
    }
    out
}

/// A list built by the list hooks around `v` (and terms without `v`): `perm` relates two such
/// lists when it relates the two values of `v` (the items' counts).
fn list_of(l: &L, v: &str) -> bool {
    if !occurs(l, v) {
        return true;
    }
    match l {
        L::Var(x) => x == v,
        L::App(h, a) => {
            matches!(
                h.as_str(),
                "KPrelude.ListHook.concat" | "KPrelude.ListHook.push"
            ) && a.iter().all(|x| list_of(x, v))
        }
        _ => false,
    }
}

/// Why rule `r` is not generically a bisimulation step of `Equiv`, if it is not: it reads a
/// relaxed cell (not a variable there, or its variable used in a side condition or another
/// cell), or, for `perm`, does not rebuild the list from it by the list hooks.
pub(crate) fn check(eq: &Equiv, r: &Rule) -> Result<(), String> {
    let leaves = rule_leaves(eq, r);
    let hyps: Vec<&str> = r.step.hyps.iter().map(|(_, p)| p.as_str()).collect();
    for c in eq.cells.iter().filter(|c| c.rel.is_some()) {
        let Some(i) = leaves.iter().position(|(n, _, _)| *n == c.label) else {
            return Err(format!(
                "the cell <{}> is not a leaf of its left-hand side",
                c.label
            ));
        };
        let (_, a, b) = &leaves[i];
        // the variable at the cell: a whole cell, or its content
        let (v, whole) = match a {
            L::Var(v) => (v.clone(), true),
            L::App(_, x) => match x.as_slice() {
                [L::Var(v)] => (v.clone(), false),
                _ => {
                    return Err(format!(
                        "it matches <{}> by a pattern (it reads it)",
                        c.label
                    ));
                }
            },
            _ => {
                return Err(format!(
                    "it matches <{}> by a pattern (it reads it)",
                    c.label
                ));
            }
        };
        let raw = |t: &str| {
            t.split(|ch: char| !(ch.is_alphanumeric() || ch == '_' || ch == '\''))
                .any(|w| w == v)
        };
        if hyps.iter().any(|h| raw(h)) {
            return Err(format!(
                "a hypothesis of its step (a side condition, or a match of a map or a list) reads <{}>",
                c.label
            ));
        }
        if let Some((n, _, _)) = leaves
            .iter()
            .enumerate()
            .find(|(j, (_, x, y))| *j != i && (occurs(x, &v) || occurs(y, &v)))
            .map(|(_, l)| l)
        {
            return Err(format!("its step at <{n}> reads <{}>", c.label));
        }
        if c.rel == Some(Rel::Perm) {
            let ok = match b {
                L::Var(x) => whole && *x == v,
                L::App(_, x) => match x.as_slice() {
                    [y] => !whole && list_of(y, &v) || whole && !occurs(y, &v),
                    _ => false,
                },
                _ => false,
            };
            if !ok {
                return Err(format!(
                    "its right-hand side at <{}> is not the list rebuilt by the list hooks (`ListHook.concat`, `element`, `push`, `unit`)",
                    c.label
                ));
            }
        }
    }
    Ok(())
}

impl Equiv {
    fn n_vars(n: &Node) -> usize {
        if n.leaf.is_some() {
            1
        } else {
            n.kids.iter().map(Self::n_vars).sum()
        }
    }

    /// The pattern of node `n` with a variable `{x}{i}` at each leaf's content, from `next`.
    fn pat(n: &Node, x: &str, next: &mut usize) -> String {
        if n.leaf.is_some() {
            *next += 1;
            return format!("({} {x}{})", n.ctor, *next - 1);
        }
        let ks: Vec<String> = n.kids.iter().map(|k| Self::pat(k, x, next)).collect();
        format!("({} {})", n.ctor, ks.join(" "))
    }

    fn nodes(n: &Node) -> Vec<&Node> {
        let mut v = vec![n];
        for k in &n.kids {
            v.extend(Self::nodes(k));
        }
        v
    }

    /// The compared cells, in order: their field and relation.
    fn conj(&self) -> Vec<(&Cell, bool)> {
        self.cells
            .iter()
            .filter(|c| c.rel != Some(Rel::Any))
            .map(|c| (c, c.rel == Some(Rel::Perm)))
            .collect()
    }

    fn tuple(xs: &[String]) -> String {
        if xs.len() == 1 {
            xs[0].clone()
        } else {
            format!("⟨{}⟩", xs.join(", "))
        }
    }

    /// `obtain ⟨_, …, rfl⟩ := shape.S v`.
    fn destruct(n: &Node, v: &str) -> String {
        let k = Self::n_vars(n);
        format!(
            "  obtain ⟨{}rfl⟩ := shape.{} {v}\n",
            "_, ".repeat(k),
            n.sort
        )
    }

    /// The doc of `Equiv`: which cells are relaxed, and how.
    pub(crate) fn doc(&self) -> String {
        let parts: Vec<String> = self
            .cells
            .iter()
            .filter_map(|c| {
                c.rel.map(|r| match r {
                    Rel::Any => format!("`<{}>` not compared", c.label),
                    Rel::Perm => format!("`<{}>` up to the order of its items", c.label),
                })
            })
            .collect();
        parts.join(", ")
    }

    /// The report's section.
    pub(crate) fn report(&self, rules: usize) -> String {
        let cells: Vec<String> = self
            .cells
            .iter()
            .filter_map(|c| c.rel.map(|r| format!("{:?} = {:?}", c.label, r.name())))
            .collect();
        format!(
            "\n[equiv]  # the cells compared otherwise than by equality (`--equiv`), and the rules shown to\n# keep the equivalence (`equiv.sim.r`, generic)\ncells = {{ {} }}\nsim = {rules}\n",
            cells.join(", ")
        )
    }

    /// The equivalence's section of the views: the cells' contents, `Equiv` and its laws, the
    /// shapes of the cells, and the bisimulation, one lemma per rule.
    pub(crate) fn emit(&self, lib: &Lib, name: &str, topt: &str) -> String {
        let mut o = String::new();
        writeln!(
            o,
            "\n/-! ## The equivalence (`--equiv`): the configurations equal but in {} -/\n",
            self.doc()
        )
        .unwrap();
        // the contents of the leaves, one match per level
        for c in &self.cells {
            let mut body = String::from("  match c with\n");
            let mut ind = String::from("  ");
            for (ctor, n, i) in &c.path {
                let us: Vec<&str> = (0..*n).map(|j| if j == *i { "x" } else { "_" }).collect();
                writeln!(body, "{ind}| {ctor} {} => match x with", us.join(" ")).unwrap();
                ind.push_str("  ");
            }
            let leaf_ctor = Self::nodes(&self.root)
                .into_iter()
                .find(|n| n.leaf.as_ref().is_some_and(|(l, _)| *l == c.label))
                .map(|n| n.ctor.clone())
                .unwrap();
            write!(body, "{ind}| {leaf_ctor} y => y").unwrap();
            // the top cell itself is matched first: its level is the first of the path
            let body = if c.path.is_empty() {
                format!("  match c with\n  | {leaf_ctor} y => y")
            } else {
                body
            };
            writeln!(
                o,
                "/-- The content of the cell `<{}>`. -/\n@[reducible] def cell.{} (c : {topt}) : {name}.{} :=\n{body}\n",
                c.label, c.field, c.content
            )
            .unwrap();
        }
        let conj = self.conj();
        let terms: Vec<String> = conj
            .iter()
            .map(|(c, p)| {
                if *p {
                    format!("ListHook.Perm (cell.{0} a) (cell.{0} b)", c.field)
                } else {
                    format!("cell.{0} a = cell.{0} b", c.field)
                }
            })
            .collect();
        writeln!(
            o,
            "/-- The configurations the theorem identifies: equal but in {}. -/\n@[reducible] def Equiv (a b : {topt}) : Prop :=\n  {}\n",
            self.doc(),
            terms.join(" ∧\n    ")
        )
        .unwrap();
        let es: Vec<String> = (0..conj.len()).map(|i| format!("e{i}")).collect();
        let fs: Vec<String> = (0..conj.len()).map(|i| format!("f{i}")).collect();
        let refl: Vec<String> = conj
            .iter()
            .map(|(_, p)| {
                if *p {
                    "ListHook.Perm.refl _".into()
                } else {
                    "rfl".into()
                }
            })
            .collect();
        let symm: Vec<String> = conj
            .iter()
            .enumerate()
            .map(|(i, (_, p))| {
                if *p {
                    format!("ListHook.Perm.symm e{i}")
                } else {
                    format!("e{i}.symm")
                }
            })
            .collect();
        let trans: Vec<String> = conj
            .iter()
            .enumerate()
            .map(|(i, (_, p))| {
                if *p {
                    format!("ListHook.Perm.trans e{i} f{i}")
                } else {
                    format!("e{i}.trans f{i}")
                }
            })
            .collect();
        writeln!(
            o,
            "theorem Equiv.refl' (a : {topt}) : Equiv a a := {}\n\ntheorem Equiv.symm' {{a b : {topt}}} (h : Equiv a b) : Equiv b a := by\n  obtain {} := h\n  exact {}\n\ntheorem Equiv.trans' {{a b c : {topt}}} (h₁ : Equiv a b) (h₂ : Equiv b c) : Equiv a c := by\n  obtain {} := h₁\n  obtain {} := h₂\n  exact {}\n",
            Self::tuple(&refl),
            Self::tuple(&es),
            Self::tuple(&symm),
            Self::tuple(&es),
            Self::tuple(&fs),
            Self::tuple(&trans)
        )
        .unwrap();
        // the shapes of the cells: every value of a cell sort is its constructor, down to the
        // leaves' contents
        for n in Self::nodes(&self.root) {
            let k = Self::n_vars(n);
            let xs: Vec<String> = (0..k).map(|i| format!("x{i}")).collect();
            let p = Self::pat(n, "x", &mut 0);
            writeln!(
                o,
                "/-- A value of `{0}` is its constructor. -/\ntheorem shape.{0} (c : {name}.{0}) : ∃ {1}, c = {p} := by\n  match c with\n  | {p} => exact ⟨{2}rfl⟩\n",
                n.sort,
                xs.join(" "),
                "_, ".repeat(k)
            )
            .unwrap();
        }
        // the bisimulation, rule by rule
        let nodes = Self::nodes(&self.root);
        let he: Vec<String> = conj
            .iter()
            .map(|(_, p)| if *p { "_".into() } else { "rfl".into() })
            .collect();
        let mut sims = vec![];
        for r in &lib.rules {
            let l = &r.lean;
            let mut args = rules::ctor_args(&r.step);
            // a rule of a later rank owes, at `b`, that no rule of a rank before applies: such a
            // rule reads no relaxed cell (`check`), so it would apply at `a` too (`k2l_pri_other`)
            let ranked = crate::multi::rank_of(r, &lib.prios) > 0;
            if ranked {
                args.push("hpri".into());
            }
            let mut d = String::new();
            for (b, t) in &r.step.binders {
                if let Some(n) = nodes.iter().find(|n| n.sort == *t) {
                    d.push_str(&Self::destruct(n, b));
                }
            }
            let named: String = r
                .step
                .hyps
                .iter()
                .map(|(h, _)| format!(" ({h} := {h})"))
                .chain(ranked.then(|| " (hpri := by k2l_pri_other)".to_string()))
                .collect();
            writeln!(
                o,
                "theorem equiv.sim.{l} : {name}.Step.Rel.{l}\n    (fun a a' => ∀ b, Equiv a b → ∃ b', {name}.Step b b' ∧ Equiv a' b') := by\n  intro {} b he\n{d}{}  obtain {} := he\n  exact ⟨_, {name}.Step.{l}{named} .., by k2l_equiv_close⟩\n",
                args.join(" "),
                Self::destruct(&self.root, "b"),
                Self::tuple(&he)
            )
            .unwrap();
            sims.push(format!("equiv.sim.{l}"));
        }
        writeln!(
            o,
            "/-- `Equiv` is a strong bisimulation of `Step` with itself. -/\ntheorem equiv_stepEquiv : StepEquiv {name}.Step Equiv where\n  refl := Equiv.refl'\n  symm := Equiv.symm'\n  trans := Equiv.trans'\n  sim he hs := {name}.Step.rel_of {} hs _ he\n",
            sims.join(" ")
        )
        .unwrap();
        writeln!(
            o,
            "#k2l_assert_axioms Equiv.refl' Equiv.symm' Equiv.trans' {} equiv_stepEquiv",
            sims.join(" ")
        )
        .unwrap();
        o
    }

    /// `obs_of_equiv`: related configurations have one observation, the observed cells being
    /// compared by equality.
    pub(crate) fn obs_lemma(&self, topt: &str) -> String {
        let he: Vec<String> = self
            .conj()
            .iter()
            .map(|(_, p)| if *p { "_".into() } else { "rfl".into() })
            .collect();
        format!(
            "\n/-- Configurations related by `Equiv` have one observation. -/\ntheorem obs_of_equiv {{a b : {topt}}} (h : Equiv a b) : obs a = obs b := by\n{}{}  obtain {} := h\n  rfl\n",
            Self::destruct(&self.root, "a"),
            Self::destruct(&self.root, "b"),
            Self::tuple(&he)
        )
    }

    /// Whether the observed cells are compared by equality.
    pub(crate) fn check_obs(&self, obs: &[String]) {
        for o in obs {
            if let Some(c) = self.cells.iter().find(|c| c.label == *o && c.rel.is_some()) {
                fail(&format!(
                    "--obs: <{o}> is compared by `{}` in --equiv: an observation is of cells compared by equality (`terminal_unique` states `Equiv`)",
                    c.rel.unwrap().name()
                ));
            }
        }
    }
}

/// Move the statements of the views or the slots onto `Equiv`: the joins modulo `Equiv`, the
/// generic joins' equal configurations related by `Equiv.refl'`, the generic attempts closing by
/// `k2l_equiv_close`, the theorem `Equiv n₁ n₂`, the observation's by `obs_of_equiv`.
pub(crate) fn apply(o: &str, name: &str) -> String {
    o.replace(
        &format!("DiamondMod {name}.Step Eq "),
        &format!("DiamondMod {name}.Step Equiv "),
    )
    .replace("?_), rfl⟩", "?_), Equiv.refl' _⟩")
    .replace(
        "Or.inl rfl, Or.inl rfl, rfl⟩",
        "Or.inl rfl, Or.inl rfl, Equiv.refl' _⟩",
    )
    .replace("by k2l_join_eq⟩", "by k2l_equiv_close⟩")
    .replace(") : n₁ = n₂ :=", ") : Equiv n₁ n₂ :=")
    .replace("StepEquiv.eq", "equiv_stepEquiv")
    .replace("congrArg obs (", "obs_of_equiv (")
    .replace(
        "end in terminal configurations end in the same one",
        "end in terminal configurations end in related ones (`Equiv`)",
    )
    .replace(
        "the observed cells of the two terminal configurations agree",
        "the observed cells of the two terminal configurations agree (`obs_of_equiv`)",
    )
}

/// The views under `--equiv`: `apply`, with the prelude's module, the equivalence's section after
/// the module's `open KPrelude`, and `obs_of_equiv` after the observation.
pub(crate) fn views(o: &str, e: &Equiv, lib: &Lib, name: &str) -> String {
    let topt = format!("{name}.{}", lib.top);
    let mut o = apply(o, name);
    let i = o
        .find("\nopen KPrelude\n")
        .map(|i| i + "\nopen KPrelude\n".len())
        .unwrap_or_else(|| fail("--equiv: the views have no `open KPrelude`"));
    o.insert_str(i, &e.emit(lib, name, &topt));
    if let Some(j) = o.find("\ndef obs : ") {
        let k = o[j + 1..]
            .find("\n\n")
            .map(|k| j + 1 + k + 1)
            .unwrap_or(o.len());
        o.insert_str(k, &e.obs_lemma(&topt));
    }
    let k = o
        .find("import KPrelude.Scaffold\n")
        .map(|k| k + "import KPrelude.Scaffold\n".len())
        .unwrap_or(0);
    // with ranks, `equiv.sim.r`'s priority premise at `b` (`k2l_pri_other`)
    let pri = if lib.prios.len() > 1 && !o.contains("import KPrelude.OtherRun\n") {
        "import KPrelude.OtherRun\n"
    } else {
        ""
    };
    o.insert_str(k, &format!("import KPrelude.Equiv\n{pri}"));
    o
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(x: &str) -> L {
        L::Var(x.into())
    }
    fn app(h: &str, a: Vec<L>) -> L {
        L::App(h.into(), a)
    }

    #[test]
    fn a_list_rebuilt_by_the_list_hooks_around_its_variable_keeps_perm() {
        let item = app("KPrelude.ListHook.element", vec![var("W")]);
        let appended = app("KPrelude.ListHook.concat", vec![var("L"), item.clone()]);
        assert!(list_of(&appended, "L"));
        assert!(list_of(
            &app("KPrelude.ListHook.push", vec![var("W"), appended.clone()]),
            "L"
        ));
        // a list that does not mention the variable: the same on both sides
        assert!(list_of(&item, "L"));
        // the variable under another function reads the list
        assert!(!list_of(
            &app("KPrelude.ListHook.element", vec![var("L")]),
            "L"
        ));
        assert!(!list_of(&app("f", vec![var("L")]), "L"));
    }
}
