//! The term universe of a compiled K definition, as the generator encodes it.
//!
//! Encoding, justified by the theory KORE states:
//! - each sort is a carrier; its constructors are free (KORE `constructor` symbols carry the
//!   no-confusion axioms, and the `\or` "no junk" axiom of each sort lists exactly its
//!   constructors and the injections of its subsorts);
//! - injections compose (`inj{B,C}(inj{A,B}(x)) = inj{A,C}(x)`), so a value of sort `S` is
//!   determined by its *leaf*: the most specific sort that built it, which is a sort with its own
//!   constructors or a builtin/token/collection sort. A sort with more than one leaf is encoded as
//!   a sum over its leaves (`S.inj_L`), and a sort whose only leaf is itself is encoded directly.
//!   Every K value then has exactly one Lean representation (no junk, unlike nested injections).

use crate::ir::{Def, P, S};
use crate::names;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Builtin {
    Int,
    Bool,
    String,
    /// `BYTES.Bytes`, as `List UInt8`
    Bytes,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Coll {
    Map,
    Set,
    List,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
    Builtin(Builtin),
    Token,
    Coll(Coll),
    Plain,
}

#[derive(Clone, Debug)]
pub struct SortInfo {
    pub name: String,
    pub kind: Kind,
    /// Own constructor symbols, in declaration order.
    pub own: Vec<String>,
    /// Leaf sorts, in a deterministic order (by name).
    pub leaves: Vec<String>,
    /// For a collection: the element sorts (`[key, value]` for a map, `[element]` for a set or a
    /// list), from the arguments of its `element` hook symbol (`SortKItem` when it has none).
    pub elems: Vec<String>,
}

impl SortInfo {
    /// A sort whose only leaf is itself: its Lean type holds its own values directly.
    pub fn is_simple(&self) -> bool {
        self.leaves.len() == 1 && self.leaves[0] == self.name
    }
    pub fn in_block(&self) -> bool {
        matches!(self.kind, Kind::Plain | Kind::Coll(_))
    }
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct CtorInfo {
    pub sym: String,
    /// The sort whose own constructor this is.
    pub sort: String,
    pub args: Vec<String>,
    /// Lean constructor name component (quoted if needed).
    pub lean: String,
    /// Position among the owner's constructors (the serialization tag).
    pub tag: usize,
    /// The K label, for printing.
    pub klabel: String,
}

#[derive(Debug)]
pub struct Model {
    pub sorts: BTreeMap<String, SortInfo>,
    pub ctors: BTreeMap<String, CtorInfo>,
    /// Direct subsort pairs (sub, super).
    pub subsorts: BTreeSet<(String, String)>,
    /// Sorts in the mutual block, in a fixed order.
    pub block: Vec<String>,
    pub unsupported: Vec<String>,
    /// Function symbol → hook name.
    pub hooks: BTreeMap<String, String>,
    /// `anywhere` function symbols, which the model keeps as constructors (their equations
    /// normalize, see `funcs`).
    pub anywhere: BTreeSet<String>,
    /// Notes on declarations the model leaves out (macros, constructors of builtin sorts).
    pub notes: Vec<String>,
}

pub fn sort_name(s: &S) -> Option<String> {
    s.name().map(|n| n.to_string())
}

impl Model {
    pub fn build(def: &Def) -> Result<Model, String> {
        let mut sorts = BTreeMap::new();
        let mut unsupported = Vec::new();
        for (name, d) in &def.sorts {
            if !d.params.is_empty() {
                continue;
            }
            let kind = if d.hooked {
                match d.attrs.string("hook").as_deref() {
                    Some("INT.Int") => Kind::Builtin(Builtin::Int),
                    Some("BOOL.Bool") => Kind::Builtin(Builtin::Bool),
                    Some("STRING.String") => Kind::Builtin(Builtin::String),
                    Some("BYTES.Bytes") => Kind::Builtin(Builtin::Bytes),
                    Some("MAP.Map") => Kind::Coll(Coll::Map),
                    Some("SET.Set") => Kind::Coll(Coll::Set),
                    Some("LIST.List") => Kind::Coll(Coll::List),
                    other => {
                        unsupported.push(format!("{name} (hook {other:?})"));
                        continue;
                    }
                }
            } else if d.attrs.has("token") || d.attrs.has("hasDomainValues") {
                Kind::Token
            } else {
                Kind::Plain
            };
            sorts.insert(
                name.clone(),
                SortInfo {
                    name: name.clone(),
                    kind,
                    own: vec![],
                    leaves: vec![],
                    elems: vec![],
                },
            );
        }
        // collection element sorts, from the `element` hook symbols
        for d in def.symbols.values() {
            let elem_hook = matches!(
                d.hook().as_deref(),
                Some("MAP.element" | "SET.element" | "LIST.element")
            );
            if !elem_hook {
                continue;
            }
            let (Some(res), Some(args)) = (
                sort_name(&d.result),
                d.args.iter().map(sort_name).collect::<Option<Vec<_>>>(),
            ) else {
                continue;
            };
            if let Some(s) = sorts.get_mut(&res)
                && matches!(s.kind, Kind::Coll(_))
            {
                s.elems = args;
            }
        }
        for s in sorts.values_mut() {
            if s.elems.is_empty() {
                s.elems = match s.kind {
                    Kind::Coll(Coll::Map) => vec!["SortKItem".into(), "SortKItem".into()],
                    Kind::Coll(_) => vec!["SortKItem".into()],
                    _ => vec![],
                };
            }
        }
        // constructors (and `anywhere` functions, which the model keeps as constructors);
        // macros and aliases are expanded by kompile and never occur in compiled terms
        let mut ctors = BTreeMap::new();
        let mut notes = Vec::new();
        let mut anywhere: BTreeSet<String> = def
            .symbols
            .iter()
            .filter(|(_, d)| d.attrs.has("anywhere") && d.is_function() && d.params.is_empty())
            .map(|(n, _)| n.clone())
            .collect();
        // the super symbols of overload axioms are normalized like `anywhere` functions
        anywhere.extend(crate::funcs::overload_supers(def));
        for (sym, d) in &def.symbols {
            if !d.params.is_empty()
                || d.attrs.has("sortInjection")
                || (d.is_function() && !anywhere.contains(sym))
            {
                continue;
            }
            if d.attrs.has("macro")
                || d.attrs.has("macro-rec")
                || d.attrs.has("alias")
                || d.attrs.has("alias-rec")
                || d.attrs.has("alias'Kywd'")
            {
                notes.push(format!("macro symbol {} left out", names::demangle(sym)));
                continue;
            }
            let Some(res) = sort_name(&d.result) else {
                continue;
            };
            let args: Option<Vec<String>> = d.args.iter().map(sort_name).collect();
            let Some(args) = args else { continue };
            if !sorts.contains_key(&res) || args.iter().any(|a| !sorts.contains_key(a)) {
                continue;
            }
            if sorts[&res].kind != Kind::Plain {
                notes.push(format!(
                    "constructor {} of builtin sort {res} left out",
                    names::demangle(sym)
                ));
                continue;
            }
            sorts.get_mut(&res).unwrap().own.push(sym.clone());
            ctors.insert(
                sym.clone(),
                CtorInfo {
                    sym: sym.clone(),
                    sort: res.clone(),
                    args,
                    lean: String::new(),
                    tag: 0,
                    klabel: names::demangle(sym),
                },
            );
        }
        // own constructors in declaration order (BTreeMap iteration is by name; keep it, it is
        // deterministic and independent of file layout)
        // subsorts
        let mut subsorts = BTreeSet::new();
        for a in &def.axioms {
            if let Some(P::App(_, params, _)) = a.attrs.get("subsort")
                && let (Some(sub), Some(sup)) = (
                    params.first().and_then(sort_name),
                    params.get(1).and_then(sort_name),
                )
            {
                // a collection's carrier holds only its own values: K declares the cell sort a
                // subsort of its cell collection (`ThreadCell < ThreadCellMap`), but the
                // collection hooks never build such an injection
                if sorts.contains_key(&sub) && sorts.contains_key(&sup) {
                    if matches!(sorts[&sup].kind, Kind::Coll(_)) {
                        notes.push(format!("subsort {sub} < {sup} (a collection) left out"));
                    } else {
                        subsorts.insert((sub, sup));
                    }
                }
            }
        }
        // leaves: fixpoint over the subsort graph
        let names: Vec<String> = sorts.keys().cloned().collect();
        let mut leaves: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for n in &names {
            let s = &sorts[n];
            let mut set = BTreeSet::new();
            if !s.own.is_empty() || s.kind != Kind::Plain {
                set.insert(n.clone());
            }
            leaves.insert(n.clone(), set);
        }
        loop {
            let mut changed = false;
            for (sub, sup) in &subsorts {
                let add: Vec<String> = leaves[sub].iter().cloned().collect();
                let target = leaves.get_mut(sup).unwrap();
                for l in add {
                    changed |= target.insert(l);
                }
            }
            if !changed {
                break;
            }
        }
        for n in &names {
            let s = sorts.get_mut(n).unwrap();
            s.leaves = leaves[n].iter().cloned().collect();
        }
        // a sort with no leaves is empty; keep it out of the universe
        let empty: Vec<String> = sorts
            .values()
            .filter(|s| s.leaves.is_empty())
            .map(|s| s.name.clone())
            .collect();
        for e in &empty {
            sorts.remove(e);
        }
        ctors.retain(|_, c| c.args.iter().all(|a| sorts.contains_key(a)));
        // a collection whose element sort is not in the universe is left out
        let bad: Vec<String> = sorts
            .values()
            .filter(|s| s.elems.iter().any(|e| !sorts.contains_key(e)))
            .map(|s| s.name.clone())
            .collect();
        for b in &bad {
            notes.push(format!(
                "collection {b} left out (element sort not in the universe)"
            ));
            sorts.remove(b);
        }
        for s in sorts.values_mut() {
            s.leaves.retain(|l| !bad.contains(l));
        }
        ctors.retain(|_, c| c.args.iter().all(|a| sorts.contains_key(a)));
        for s in sorts.values_mut() {
            s.own.retain(|c| ctors.contains_key(c));
        }
        subsorts.retain(|(a, b)| sorts.contains_key(a) && sorts.contains_key(b));
        // Lean names and tags for constructors, unique within their owner type
        for s in sorts.values() {
            let mut used = BTreeSet::new();
            let mut chosen = Vec::new();
            for (i, c) in s.own.iter().enumerate() {
                let ci = &ctors[c];
                let label = names::demangle(c);
                let short = names::short_label(&label, &ci.sort, &ci.args).unwrap_or(label.clone());
                chosen.push((c.clone(), i, short, label));
            }
            // shorten only where the short form is unique
            let mut counts: BTreeMap<String, usize> = BTreeMap::new();
            for (_, _, short, _) in &chosen {
                *counts.entry(short.clone()).or_default() += 1;
            }
            for (c, i, short, label) in chosen {
                let mut name = if counts[&short] == 1 { short } else { label };
                if name.starts_with("inj_") {
                    name = format!("c_{name}");
                }
                if !used.insert(name.clone()) {
                    return Err(format!("constructor name collision {name} in {}", s.name));
                }
                let ci = ctors.get_mut(&c).unwrap();
                ci.lean = names::ident(&name);
                ci.tag = i;
            }
        }
        let block: Vec<String> = sorts
            .values()
            .filter(|s| s.in_block())
            .map(|s| s.name.clone())
            .collect();
        let hooks = def
            .symbols
            .iter()
            .filter_map(|(n, d)| d.hook().map(|h| (n.clone(), h)))
            .collect();
        // an overloaded symbol whose overload axioms all need sorts without values is a plain
        // constructor (no equation can ever apply)
        fn sorts_ok(p: &P, sorts: &BTreeMap<String, SortInfo>) -> bool {
            let ok = |s: &S| s.name().is_none_or(|n| sorts.contains_key(n));
            match p {
                P::Var(_, s) | P::Dv(s, _) => ok(s),
                P::App(_, ps, args) => ps.iter().all(ok) && args.iter().all(|a| sorts_ok(a, sorts)),
                P::And(_, ps) => ps.iter().all(|a| sorts_ok(a, sorts)),
                _ => true,
            }
        }
        let usable: BTreeSet<String> = def
            .axioms
            .iter()
            .filter(|a| a.attrs.has("symbol-overload"))
            .filter_map(|a| match &a.pattern {
                P::Equals(_, _, l, r) if sorts_ok(l, &sorts) && sorts_ok(r, &sorts) => {
                    l.app_name().map(|x| x.to_string())
                }
                _ => None,
            })
            .collect();
        anywhere
            .retain(|f| def.symbols.get(f).is_some_and(|d| d.is_function()) || usable.contains(f));
        Ok(Model {
            sorts,
            ctors,
            subsorts,
            block,
            unsupported,
            hooks,
            anywhere,
            notes,
        })
    }

    pub fn sort(&self, n: &str) -> &SortInfo {
        self.sorts
            .get(n)
            .unwrap_or_else(|| panic!("unknown sort {n}"))
    }

    /// The element sorts of a collection sort.
    pub fn elems(&self, n: &str) -> &[String] {
        &self.sort(n).elems
    }

    /// The Lean type holding the own values of leaf sort `l` (its constructors' type).
    pub fn own_ty(&self, l: &str) -> String {
        let s = self.sort(l);
        if s.is_simple() {
            l.to_string()
        } else {
            format!("{l}.Own")
        }
    }

    /// The constructor of compound sort `s` that injects leaf `l`.
    pub fn leaf_ctor(&self, s: &str, l: &str) -> String {
        format!("{}.inj_{}", s, names::short_sort(l))
    }

    /// The fully qualified Lean constructor of a K constructor symbol, as a value of its own type.
    pub fn ctor_path(&self, sym: &str) -> String {
        let c = &self.ctors[sym];
        format!("{}.{}", self.own_ty(&c.sort), c.lean)
    }

    /// Whether `(a, b)` is in the transitive closure of the declared subsort pairs.
    pub fn subsort_closure(&self, a: &str, b: &str) -> bool {
        let mut seen = BTreeSet::new();
        let mut todo = vec![a.to_string()];
        while let Some(x) = todo.pop() {
            for (s, t) in &self.subsorts {
                if *s == x && seen.insert(t.clone()) {
                    if t == b {
                        return true;
                    }
                    todo.push(t.clone());
                }
            }
        }
        false
    }

    /// Whether `a` ≤ `b` in the subsort order (reflexive, transitive).
    pub fn is_subsort(&self, a: &str, b: &str) -> bool {
        if a == b {
            return true;
        }
        let la = &self.sort(a).leaves;
        let lb = &self.sort(b).leaves;
        la.iter().all(|l| lb.contains(l))
    }
}
