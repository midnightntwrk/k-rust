//! `k2lean kcore-claims`: one K reachability claim, as its KORE sentence states it, written as a
//! Lean proposition over the `Step` of a package `kcore gen` wrote.
//!
//! ```text
//! k2lean kcore-claims --spec SPEC.kore --syntax PKG/NS/Syntax.lean --claim MODULE.LABEL --out FILE.lean
//! ```
//!
//! The claim sentence (selected by its whole `label` attribute) is read as `k2lean claims` reads
//! it, `\implies(\and(REQUIRES, LHS), weakAlwaysFinally(\exists ?X … \and(RHS, ENSURES)))`; its
//! terms are lowered by [`crate::kcore_terms`] with the name table of `Syntax.lean`. The file
//! holds `def NS.Claims.Generated.«LABEL» : Prop`, LABEL the part of the label after the module's
//! name:
//!
//! ```text
//! ∀ (H : HookParams) BINDERS (_hreq : P),
//!   AllPath (Step (NS.defn.sem.withHooks H))
//!     (fun x => x.val = (LHS).val)
//!     (fun z => ∃ X' : T, …, z.val = (RHS).val)
//! ```
//!
//! * Binders, in this order: the named variables (`X` not beginning with `_`) by first occurrence
//!   in the left configuration (depth first, arguments left to right), then those occurring only
//!   in the requires; then the anonymous ones (`_DotVarN`, `_GenN`) by first occurrence in the
//!   left configuration. Consecutive binders of one type are grouped.
//! * Names: a named variable keeps its K name. An anonymous variable is named by the innermost
//!   cell enclosing its first occurrence: the cell name's first letter, upper case, a leading
//!   `generated` dropped (`<k>` gives `K`, `<generatedCounter>` gives `C`), with `1`, `2`, …
//!   appended to a name already taken. An existential variable is named by the same rule from its
//!   first occurrence in the right side, with `'` appended where a universal variable has that
//!   name. `H`, `x` and `z` are taken by the statement itself.
//! * Types: sort `Int` is `Int` (used as `Tm.int X`), `Bool` is `Bool` (`Tm.bool X`), another
//!   sort `s` is `Tm s` (used bare).
//! * Requires: `\equals(B, \dv{SortBool}("true"))` is the hypothesis `(_hreq : P)`, `P` the Lean
//!   fact of `B`; `\top` gives none.
//! * Each existential is one `∃` inside the target predicate, in the order `\exists` binds them.
//!
//! Hooked function terms are folded to the Lean function where the hook has one value, the same
//! for every interpretation `H`, at every argument the statement admits ([`FOLDS`]); the file
//! carries, for each fold used, an `example` that the package's `hookRes` at that symbol is the
//! folded value under every `H`, and that the symbol is the KORE symbol read. Anything else
//! (`weakExistsFinally`, an `ensures` other than `\top`, another requires, a symbol without a
//! constructor or a fold, a variable no rule names) stops with a message naming it.

use crate::claims;
use crate::ir::{P, S};
use crate::kcore_terms::{self, Lower, Table, int_lit, int_token, node};
use crate::names;
use sha2::{Digest, Sha256};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

/// The folded hooked symbols: KORE name, KCore's symbol, and the fold.
pub const FOLDS: &[(&str, &str, Fold)] = &[
    ("Lbl'UndsPlus'Int'Unds'", "intAdd", Fold::Infix("+")),
    ("Lbl'UndsStar'Int'Unds'", "intMul", Fold::Infix("*")),
    ("Lbl'UndsSlsh'Int'Unds'", "intTDiv", Fold::TDivLit),
    ("Lbl'Unds-GT-Eqls'Int'Unds'", "intGe", Fold::Ge),
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fold {
    /// `a op b` on `Int` (the hook is total).
    Infix(&'static str),
    /// `(a).tdiv b` where `b` is a literal other than 0 (at 0 the hook has no one value).
    TDivLit,
    /// `a ≥ b`, only as the fact of `\equals(_>=Int_(a, b), true)`.
    Ge,
}

/// A fold used, for its `example`: the row, and for `TDivLit` the divisor.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Used {
    row: usize,
    divisor: Option<String>,
}

/// An integer expression, and its shape: an operator application is parenthesised as an operand
/// of an operator or as a method receiver, a method call (`.tdiv`, which binds as an application)
/// as a method receiver only.
struct IntExpr {
    text: String,
    shape: Shape,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    Atom,
    Method,
    Op,
}

impl IntExpr {
    fn operand(&self) -> String {
        if self.shape == Shape::Op {
            format!("({})", self.text)
        } else {
            self.text.clone()
        }
    }

    fn receiver(&self) -> String {
        if self.shape == Shape::Atom {
            self.text.clone()
        } else {
            format!("({})", self.text)
        }
    }
}

struct Folder<'a> {
    env: &'a BTreeMap<String, String>,
    used: RefCell<BTreeSet<Used>>,
}

fn row_of(p: &P) -> Option<(usize, &'static str, Fold, &[P])> {
    let P::App(f, ss, args) = p else { return None };
    if !ss.is_empty() {
        return None;
    }
    FOLDS
        .iter()
        .enumerate()
        .find(|(_, (k, _, _))| k == f)
        .map(|(i, (_, s, fold))| (i, *s, *fold, args.as_slice()))
}

fn is_int(s: &S) -> bool {
    s.name() == Some("SortInt")
}

impl Folder<'_> {
    /// An `Int`-sorted term as a Lean integer expression.
    fn int(&self, p: &P) -> Result<IntExpr, String> {
        match p {
            P::Var(v, s) if is_int(s) => Ok(IntExpr {
                text: self
                    .env
                    .get(v)
                    .ok_or_else(|| format!("variable {v}: not bound"))?
                    .clone(),
                shape: Shape::Atom,
            }),
            P::Dv(s, v) if is_int(s) => Ok(IntExpr {
                text: int_lit(&int_token(v)?),
                shape: Shape::Atom,
            }),
            _ => match row_of(p) {
                Some((i, _, Fold::Infix(op), [a, b])) => {
                    let (a, b) = (self.int(a)?, self.int(b)?);
                    self.used.borrow_mut().insert(Used {
                        row: i,
                        divisor: None,
                    });
                    Ok(IntExpr {
                        text: format!("{} {op} {}", a.operand(), b.operand()),
                        shape: Shape::Op,
                    })
                }
                Some((i, _, Fold::TDivLit, [a, b])) => {
                    let P::Dv(s, v) = b else {
                        return Err(format!(
                            "{}: a divisor that is not a literal has no fold",
                            node(p)
                        ));
                    };
                    let d = int_token(v)?;
                    if !is_int(s) || d == 0.into() {
                        return Err(format!("{}: the divisor 0 has no fold", node(p)));
                    }
                    let a = self.int(a)?;
                    let d = int_lit(&d);
                    self.used.borrow_mut().insert(Used {
                        row: i,
                        divisor: Some(d.clone()),
                    });
                    Ok(IntExpr {
                        text: format!("{}.tdiv {d}", a.receiver()),
                        shape: Shape::Method,
                    })
                }
                _ => Err(format!("{}: no rule for an Int operand", node(p))),
            },
        }
    }

    /// The Lean fact of `\equals(B, true)`.
    fn fact(&self, b: &P) -> Result<String, String> {
        match row_of(b) {
            Some((i, _, Fold::Ge, [x, y])) => {
                let (x, y) = (self.int(x)?, self.int(y)?);
                self.used.borrow_mut().insert(Used {
                    row: i,
                    divisor: None,
                });
                Ok(format!("{} ≥ {}", x.operand(), y.operand()))
            }
            _ => Err(format!("{}: no rule for a requires", node(b))),
        }
    }
}

/// An `Int`-sorted application of a folded symbol as an integer expression (`Tm.int`'s argument).
fn fold_term(f: &Folder<'_>, p: &P) -> Result<Option<String>, String> {
    match row_of(p) {
        Some((_, _, Fold::Infix(_) | Fold::TDivLit, _)) => Ok(Some(f.int(p)?.text)),
        _ => Ok(None),
    }
}

/// The K name of a KORE variable (`VarN` → `N`, `Var'Unds'DotVar1` → `_DotVar1`).
fn k_name(v: &str) -> Result<String, String> {
    let body = v
        .strip_prefix("Var")
        .ok_or_else(|| format!("variable {v}: not a K variable name"))?;
    let d = names::demangle(body);
    if d == body && body.contains('\'') {
        return Err(format!("variable {v}: not a K variable name"));
    }
    Ok(d)
}

/// The variables of `p` in first-occurrence order (depth first, arguments left to right), each
/// with its sort and the innermost cell enclosing that occurrence.
fn occurrences(p: &P, cell: Option<&str>, out: &mut Vec<(String, S, Option<String>)>) {
    match p {
        P::Var(v, s) => {
            if !out.iter().any(|(w, _, _)| w == v) {
                out.push((v.clone(), s.clone(), cell.map(str::to_string)));
            }
        }
        P::App(f, _, args) => {
            let d = if f.starts_with("Lbl") {
                Some(names::demangle(f))
            } else {
                None
            };
            let inner = match &d {
                Some(n) if n.len() > 2 && n.starts_with('<') && n.ends_with('>') => {
                    Some(&n[1..n.len() - 1])
                }
                _ => cell,
            };
            for a in args {
                occurrences(a, inner, out);
            }
        }
        P::And(_, ps) | P::Or(_, ps) => ps.iter().for_each(|q| occurrences(q, cell, out)),
        P::Equals(_, _, a, b) | P::In(_, _, a, b) => {
            occurrences(a, cell, out);
            occurrences(b, cell, out);
        }
        P::Not(_, a) | P::Ceil(_, _, a) | P::Floor(_, _, a) => occurrences(a, cell, out),
        _ => {}
    }
}

/// The name of an anonymous variable first occurring in the cell `cell`.
fn cell_letter(v: &str, cell: Option<&str>) -> Result<String, String> {
    let c = cell.ok_or_else(|| format!("variable {v}: in no cell, no rule names it"))?;
    let c = c.strip_prefix("generated").unwrap_or(c);
    let l = c
        .chars()
        .next()
        .filter(|l| l.is_ascii_alphabetic())
        .ok_or_else(|| format!("variable {v}: the cell <{c}> gives no name"))?;
    Ok(l.to_ascii_uppercase().to_string())
}

fn fresh(base: String, taken: &BTreeSet<String>) -> String {
    if !taken.contains(&base) {
        return base;
    }
    (1..)
        .map(|i| format!("{base}{i}"))
        .find(|n| !taken.contains(n))
        .unwrap()
}

/// A binder's Lean type, from the variable's sort.
fn ty(t: &Table, s: &S) -> Result<String, String> {
    let st = t.sort(s)?;
    Ok(match st.as_str() {
        "KCore.Srt.int" => "Int".into(),
        "KCore.Srt.bool" => "Bool".into(),
        _ => format!("Tm {}", st.strip_prefix("KCore.").unwrap_or(&st)),
    })
}

/// The Lean text of the claim's statement, and the examples of the folds it used.
#[derive(Debug)]
pub struct Emitted {
    pub name: String,
    pub statement: String,
    pub examples: Vec<String>,
}

/// The statement of the claim labelled `label` (whole) among `claims`.
pub fn emit(claims: &[claims::RawClaim], t: &Table, label: &str) -> Result<Emitted, String> {
    let mut cs = claims.iter().filter(|c| c.label == label);
    let c = cs
        .next()
        .ok_or_else(|| format!("no claim labelled {label}"))?;
    if cs.next().is_some() {
        return Err(format!("two claims labelled {label}"));
    }
    let short = label
        .strip_prefix(&format!("{}.", c.module))
        .ok_or_else(|| format!("label {label} does not begin with its module {}", c.module))?;
    emit_one(short, &c.pattern, t)
}

/// The statement of one claim formula, declared under the name `short`.
pub fn emit_one(short: &str, pattern: &P, t: &Table) -> Result<Emitted, String> {
    let parts = claims::parts(pattern)?;
    if !parts.all_path {
        return Err("weakExistsFinally (a one-path claim): no rule".into());
    }
    if let Some(e) = parts.ensures.first() {
        return Err(format!("{}: an ensures other than \\top", node(e)));
    }
    // the requires
    let mut facts = vec![];
    for r in &parts.requires {
        match r {
            P::Equals(_, _, b, t) if matches!(&**t, P::Dv(s, v) if s.name() == Some("SortBool") && v == "true") => {
                facts.push(&**b)
            }
            _ => {
                return Err(format!(
                    "{}: a requires that is not \\equals(B, true)",
                    node(r)
                ));
            }
        }
    }
    if facts.len() > 1 {
        return Err("more than one requires: no rule".into());
    }
    // the universal variables
    let mut left = vec![];
    occurrences(parts.lhs, None, &mut left);
    let mut req = vec![];
    for f in &facts {
        occurrences(f, None, &mut req);
    }
    let named = |v: &str| k_name(v).map(|n| !n.starts_with('_'));
    let mut order: Vec<(String, S, Option<String>)> = vec![];
    for o in left.iter().chain(req.iter()) {
        if named(&o.0)? && !order.iter().any(|x| x.0 == o.0) {
            order.push(o.clone());
        }
    }
    for o in &left {
        if !named(&o.0)? {
            order.push(o.clone());
        }
    }
    for o in &req {
        if !order.iter().any(|x| x.0 == o.0) {
            return Err(format!("variable {}: anonymous, only in the requires", o.0));
        }
    }
    let mut taken: BTreeSet<String> = ["H", "x", "z"].iter().map(|s| s.to_string()).collect();
    let mut env = BTreeMap::new();
    let mut binders: Vec<(String, String)> = vec![];
    for (v, s, cell) in &order {
        let k = k_name(v)?;
        let n = if !k.starts_with('_') {
            let n = names::ident(&k);
            if taken.contains(&n) {
                return Err(format!("variable {v}: its name {n} is taken"));
            }
            n
        } else {
            fresh(cell_letter(v, cell.as_deref())?, &taken)
        };
        taken.insert(n.clone());
        env.insert(v.clone(), n.clone());
        binders.push((n, ty(t, s)?));
    }
    let universal = taken.clone();
    // the existential variables
    let mut right = vec![];
    occurrences(parts.rhs, None, &mut right);
    let mut exists = vec![];
    for (v, sort) in &parts.existentials {
        let s = S::App(sort.clone(), vec![]);
        let cell = right
            .iter()
            .find(|o| &o.0 == v)
            .map(|o| o.2.clone())
            .ok_or_else(|| format!("existential {v}: not in the right side"))?;
        let k = k_name(v)?;
        let k = k.strip_prefix('?').unwrap_or(&k).to_string();
        let mut n = if !k.starts_with('_') {
            names::ident(&k)
        } else {
            cell_letter(v, cell.as_deref())?
        };
        if universal.contains(&n) {
            n.push('\'');
        }
        let n = fresh(n, &taken);
        taken.insert(n.clone());
        env.insert(v.clone(), n.clone());
        exists.push((n, ty(t, &s)?));
    }
    for o in &right {
        if !env.contains_key(&o.0) {
            return Err(format!(
                "variable {}: only in the right side and not bound by \\exists",
                o.0
            ));
        }
    }
    // the terms
    let folder = Folder {
        env: &env,
        used: RefCell::new(BTreeSet::new()),
    };
    let fold = |_: &Lower<'_>, p: &P| fold_term(&folder, p);
    let lower = Lower {
        table: t,
        env: &env,
        int_fold: Some(&fold),
    };
    let lhs = lower.top(parts.lhs)?;
    let rhs = lower.top(parts.rhs)?;
    for (side, l) in [("left", &lhs), ("right", &rhs)] {
        if l.sort != "KCore.Srt.top" {
            return Err(format!(
                "the {side} side has sort {}, not the configuration's",
                l.sort
            ));
        }
    }
    let hyp = facts.first().map(|b| folder.fact(b)).transpose()?;
    // the statement
    let mut groups: Vec<(Vec<String>, String)> = vec![];
    for (n, ty) in binders {
        match groups.last_mut() {
            Some((ns, t)) if *t == ty => ns.push(n),
            _ => groups.push((vec![n], ty)),
        }
    }
    let mut head = String::from("∀ (H : HookParams)");
    for (ns, ty) in &groups {
        head.push_str(&format!(" ({} : {ty})", ns.join(" ")));
    }
    if let Some(h) = &hyp {
        head.push_str(&format!(" (_hreq : {h})"));
    }
    let ex: String = exists
        .iter()
        .map(|(n, ty)| format!("∃ {n} : {ty}, "))
        .collect();
    let name = format!("Generated.{}", names::ident(short));
    let statement = format!(
        "def {name} : Prop :=\n  {head},\n    AllPath (Step ({ns}.defn.sem.withHooks H))\n      \
         (fun x => x.val =\n        ({}).val)\n      (fun z => {ex}z.val =\n        ({}).val)\n",
        layout(&lhs.text),
        layout(&rhs.text),
        ns = t.ns
    );
    let examples = folder
        .used
        .borrow()
        .iter()
        .map(|u| example(&t.ns, u))
        .collect();
    Ok(Emitted {
        name,
        statement,
        examples,
    })
}

/// A configuration's text with each argument of its top cell on a line of its own (white space
/// only: the text is the same up to white space).
fn layout(text: &str) -> String {
    let mut parts = vec![];
    let (mut depth, mut start, mut in_str, mut esc) = (0i32, 0, false, false);
    for (i, ch) in text.char_indices() {
        if in_str {
            match ch {
                _ if esc => esc = false,
                '\\' => esc = true,
                '"' => in_str = false,
                _ => {}
            }
            continue;
        }
        match ch {
            '"' => in_str = true,
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ' ' if depth == 0 => {
                parts.push(&text[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(&text[start..]);
    parts.join("\n          ")
}

/// The `example` of a fold used.
fn example(ns: &str, u: &Used) -> String {
    let (kore, sym, fold) = FOLDS[u.row];
    let c = format!("({ns}.defn.sem.withHooks H)");
    let k = names::demangle(kore);
    let name = format!("{c}.symName KCore.{sym} = {}", names::string_lit(kore));
    let hook = |args: &str, v: &str| {
        format!("{c}.hookRes KCore.{sym} [{args}] =\n        some (some ({v}))")
    };
    let proof = "(Semantics.hookRes_of_notKey (by decide) _).trans rfl";
    match fold {
        Fold::Infix(op) => format!(
            "/-- `{k}` is `{op}` on the integers, under every `H`. -/\n\
             example (H : HookParams) (a b : Int) :\n    {name} ∧\n      {} :=\n  ⟨rfl, {proof}⟩\n",
            hook("KCore.int a, KCore.int b", &format!("KCore.int (a {op} b)"))
        ),
        Fold::TDivLit => {
            let d = u.divisor.as_deref().unwrap();
            format!(
                "/-- `{k}` at the divisor {d} is `Int.tdiv`, under every `H`. -/\n\
                 example (H : HookParams) (a : Int) :\n    {name} ∧\n      {} :=\n  ⟨rfl, {proof}⟩\n",
                hook(
                    &format!("KCore.int a, KCore.int {d}"),
                    &format!("KCore.int (a.tdiv {d})")
                )
            )
        }
        Fold::Ge => format!(
            "/-- `{k}` is `≥` on the integers, under every `H`, and its value is `true` exactly where\n\
             `≥` holds. -/\n\
             example (H : HookParams) (a b : Int) :\n    {name} ∧\n      {} ∧\n      \
             (KCore.bool (decide (a ≥ b)) = KCore.bool true ↔ a ≥ b) :=\n  \
             ⟨rfl, {proof}, by simp [KCore.bool]⟩\n",
            hook("KCore.int a, KCore.int b", "KCore.bool (decide (a ≥ b))")
        ),
    }
}

struct Args {
    spec: PathBuf,
    syntax: PathBuf,
    claim: String,
    out: PathBuf,
}

fn parse(args: &[String]) -> Args {
    let mut a = Args {
        spec: PathBuf::new(),
        syntax: PathBuf::new(),
        claim: String::new(),
        out: PathBuf::new(),
    };
    let mut it = args.iter();
    while let Some(x) = it.next() {
        let mut v = || {
            it.next()
                .unwrap_or_else(|| panic!("{x}: a value is required"))
                .clone()
        };
        match x.as_str() {
            "--spec" => a.spec = v().into(),
            "--syntax" => a.syntax = v().into(),
            "--claim" => a.claim = v(),
            "--out" => a.out = v().into(),
            other => panic!("kcore-claims: unknown argument {other}"),
        }
    }
    if a.spec.as_os_str().is_empty()
        || a.syntax.as_os_str().is_empty()
        || a.claim.is_empty()
        || a.out.as_os_str().is_empty()
    {
        panic!(
            "usage: k2lean kcore-claims --spec SPEC.kore --syntax PKG/NS/Syntax.lean --claim MODULE.LABEL --out FILE.lean"
        );
    }
    a
}

/// The whole file.
fn file(a: &Args) -> Result<String, String> {
    let spec = std::fs::read(&a.spec).map_err(|e| format!("{}: {e}", a.spec.display()))?;
    let syntax =
        std::fs::read_to_string(&a.syntax).map_err(|e| format!("{}: {e}", a.syntax.display()))?;
    let t = kcore_terms::read_syntax(&syntax)?;
    let cs = claims::read_claims(&a.spec);
    let e = emit(&cs, &t, &a.claim)?;
    let sha: String = Sha256::digest(&spec)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    let imports = [
        format!("{}.Core", t.ns),
        format!("{}.Syntax", t.ns),
        "KcoreSpec.Reachability".into(),
        "KcoreSpec.Params".into(),
    ];
    let mut out = format!(
        "/-\n  Generated by `k2lean kcore-claims`; not edited by hand. The claim {claim}, as its KORE\n  \
         sentence states it, over the package whose name table is {syntax}; run in kcore-spec:\n\n      \
         k2lean kcore-claims --spec {spec} \\\n        --syntax {syntax} \\\n        \
         --claim {claim} --out {out}\n\n  \
         {spec}: sha256 {sha}\n\n  \
         `{ns}.Claims.{name}`: for every interpretation `H` of the hooks, every complete path of\n  \
         the package's `Step` from the left side passes through the right side, for the values\n  \
         the requires admits. Each fold of a hooked function the statement uses is checked below:\n  \
         the symbol is the one the KORE sentence names, and the package's value of it is the fold's\n  \
         under every `H`.\n-/\n",
        claim = a.claim,
        spec = a.spec.display(),
        syntax = a.syntax.display(),
        out = a.out.display(),
        ns = t.ns,
        name = e.name,
    );
    for i in &imports {
        out.push_str(&format!("import {i}\n"));
    }
    out.push_str(&format!(
        "\nset_option autoImplicit false\nset_option maxRecDepth 1000000\n\nnamespace {ns}.Claims\n\n\
         open KCore KCore.Reachability {ns}.Syntax\n\n{}\n",
        e.statement,
        ns = t.ns
    ));
    for x in &e.examples {
        out.push_str(x);
        out.push('\n');
    }
    out.push_str(&format!("end {}.Claims\n", t.ns));
    Ok(out)
}

pub fn main(args: &[String]) {
    let a = parse(args);
    match file(&a) {
        Ok(text) => {
            std::fs::write(&a.out, text).unwrap_or_else(|e| panic!("{}: {e}", a.out.display()))
        }
        Err(e) => {
            eprintln!("kcore-claims: {e}");
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kcore_spec() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../kcore/kcore-spec")
    }

    fn read(rel: &str) -> String {
        let p = kcore_spec().join(rel);
        std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
    }

    fn table() -> Table {
        kcore_terms::read_syntax(&read("examples/ref-kimp/RefKimp/Syntax.lean")).unwrap()
    }

    fn norm(s: &str) -> String {
        s.split_whitespace().collect::<Vec<_>>().join(" ")
    }

    /// The body of `def NAME : Prop :=` in `text`, up to the next blank line, white space
    /// normalised.
    fn body(text: &str, name: &str) -> String {
        let b = text.split(&format!("def {name} : Prop :=")).nth(1).unwrap();
        norm(b.split("\n\n").next().unwrap())
    }

    fn sum_spec() -> Emitted {
        let cs = claims::read_claims(
            &kcore_spec().join("examples/ref-kimp/claims/imp-sum-spec/spec.kore"),
        );
        emit(&cs, &table(), "IMP-SUM-SPEC.sum-spec").unwrap()
    }

    /// The statement of fixture cs-sum-spec-kore's sum-spec is, up to white space,
    /// `ExpectedKore.«sum-spec»` (examples/ref-kimp/User/SumSpecStmt.lean), and its four folds
    /// each have their example.
    #[test]
    fn sum_spec_is_expected_kore() {
        let e = sum_spec();
        assert_eq!(e.name, "Generated.«sum-spec»");
        let stmt = read("examples/ref-kimp/User/SumSpecStmt.lean");
        assert_eq!(
            body(&e.statement, "Generated.«sum-spec»"),
            body(&stmt, "ExpectedKore.«sum-spec»")
        );
        let heads: Vec<&str> = e
            .examples
            .iter()
            .map(|x| x.lines().next().unwrap())
            .collect();
        assert_eq!(
            heads,
            [
                "/-- `_+Int_` is `+` on the integers, under every `H`. -/",
                "/-- `_*Int_` is `*` on the integers, under every `H`. -/",
                "/-- `_/Int_` at the divisor 2 is `Int.tdiv`, under every `H`. -/",
                "/-- `_>=Int_` is `≥` on the integers, under every `H`, and its value is `true` exactly where",
            ]
        );
    }

    /// The label is matched whole: `sum-spec` alone names no claim, `two-sum-spec` another one.
    #[test]
    fn label_whole() {
        let cs = claims::read_claims(
            &kcore_spec().join("examples/ref-kimp/claims/imp-sum-spec/spec.kore"),
        );
        let t = table();
        assert!(
            emit(&cs, &t, "sum-spec")
                .unwrap_err()
                .contains("no claim labelled")
        );
        // another claim of the text is read, and stops at its requires (`andBool`: no rule)
        let two = emit(&cs, &t, "IMP-SUM-SPEC.two-sum-spec").unwrap_err();
        assert!(two.contains("_andBool_"), "{two}");
    }

    fn srt(n: &str) -> S {
        S::App(format!("Sort{n}"), vec![])
    }

    fn var(v: &str, s: &str) -> P {
        P::Var(v.into(), srt(s))
    }

    fn app(sym: &str, args: Vec<P>) -> P {
        P::App(format!("Lbl{sym}"), vec![], args)
    }

    fn int(v: &str) -> P {
        P::Dv(srt("Int"), v.into())
    }

    /// `<generatedTop>(<k>(K), <env>(.Map), <generatedCounter>(C))`.
    fn config(k: P, c: P) -> P {
        app(
            "<generatedTop>",
            vec![
                app("<k>", vec![k]),
                app("<env>", vec![app(".Map", vec![])]),
                app("<generatedCounter>", vec![c]),
            ],
        )
    }

    fn top() -> S {
        srt("GeneratedTopCell")
    }

    /// `\implies(\and(REQ…, L), MODALITY(\exists X … \and(R, ENS…)))`.
    fn claim(req: Vec<P>, l: P, modality: &str, ex: &[(&str, &str)], r: P, ens: Vec<P>) -> P {
        let mut lhs = req;
        lhs.push(l);
        let mut rhs = vec![r];
        rhs.extend(ens);
        let mut body = P::And(top(), rhs);
        for (v, s) in ex.iter().rev() {
            body = P::Exists(top(), v.to_string(), srt(s), Box::new(body));
        }
        P::Implies(
            top(),
            Box::new(P::And(top(), lhs)),
            Box::new(P::App(modality.into(), vec![top()], vec![body])),
        )
    }

    fn eq_true(b: P) -> P {
        P::Equals(
            srt("Bool"),
            top(),
            Box::new(b),
            Box::new(P::Dv(srt("Bool"), "true".into())),
        )
    }

    fn ge(a: P, b: P) -> P {
        app("'Unds-GT-Eqls'Int'Unds'", vec![a, b])
    }

    /// Binders: named first (left side, then the requires), then anonymous by their cells; an
    /// existential takes `'` where a universal has its name.
    #[test]
    fn binders_and_names() {
        let t = table();
        let k = var("Var'Unds'DotVar0", "K");
        let p = claim(
            vec![eq_true(ge(var("VarM", "Int"), var("VarN", "Int")))],
            config(k.clone(), var("Var'Unds'Gen0", "Int")),
            "weakAlwaysFinally",
            &[("Var'QuesUnds'Gen1", "Int"), ("Var'Ques'X", "Int")],
            config(
                k,
                app(
                    "'UndsPlus'Int'Unds'",
                    vec![var("Var'QuesUnds'Gen1", "Int"), var("Var'Ques'X", "Int")],
                ),
            ),
            vec![],
        );
        let e = emit_one("c", &p, &t).unwrap();
        assert!(
            e.statement.contains(
                "∀ (H : HookParams) (M N : Int) (K : Tm Srt.k) (C : Int) (_hreq : M ≥ N),"
            ),
            "{}",
            e.statement
        );
        assert!(
            e.statement
                .contains("(fun z => ∃ C' : Int, ∃ X : Int, z.val ="),
            "{}",
            e.statement
        );
        assert!(e.statement.contains("(Tm.int (C' + X))"), "{}", e.statement);
    }

    /// Every point without a rule stops, naming it.
    #[test]
    fn closed_world() {
        let t = table();
        let k = || var("Var'Unds'DotVar0", "K");
        let c = || var("VarC", "Int");
        let ok = |m: &str, req: Vec<P>, r: P, ens: Vec<P>| {
            emit_one("c", &claim(req, config(k(), c()), m, &[], r, ens), &t)
        };
        let err = |m: &str, req: Vec<P>, r: P, ens: Vec<P>| ok(m, req, r, ens).unwrap_err();
        assert!(ok("weakAlwaysFinally", vec![], config(k(), c()), vec![]).is_ok());
        assert!(err("weakExistsFinally", vec![], config(k(), c()), vec![]).contains("one-path"));
        let ens = eq_true(ge(c(), int("0")));
        assert!(err("weakAlwaysFinally", vec![], config(k(), c()), vec![ens]).contains("ensures"));
        let div = |d: P| config(k(), app("'UndsSlsh'Int'Unds'", vec![c(), d]));
        assert!(err("weakAlwaysFinally", vec![], div(int("0")), vec![]).contains("divisor 0"));
        assert!(err("weakAlwaysFinally", vec![], div(c()), vec![]).contains("not a literal"));
        let minus = config(k(), app("'Unds'-Int'Unds'", vec![c(), int("1")]));
        assert!(err("weakAlwaysFinally", vec![], minus, vec![]).contains("`_-Int_`"));
        let lt = eq_true(app("'Unds-LT-'Int'Unds'", vec![c(), int("1")]));
        assert!(
            err("weakAlwaysFinally", vec![lt], config(k(), c()), vec![])
                .contains("no rule for a requires")
        );
        let two = vec![eq_true(ge(c(), int("0"))), eq_true(ge(c(), int("1")))];
        assert!(err("weakAlwaysFinally", two, config(k(), c()), vec![]).contains("more than one"));
        let free = config(k(), var("VarD", "Int"));
        assert!(err("weakAlwaysFinally", vec![], free, vec![]).contains("not bound by \\exists"));
        let h = claim(
            vec![],
            config(k(), var("VarH", "Int")),
            "weakAlwaysFinally",
            &[],
            config(k(), var("VarH", "Int")),
            vec![],
        );
        assert!(emit_one("c", &h, &t).unwrap_err().contains("is taken"));
        // a map key that is a function application stops, though the fold applies to values
        let entry = |key: P| {
            app(
                "'UndsPipe'-'-GT-Unds'",
                vec![
                    P::App("inj".into(), vec![srt("Int"), srt("KItem")], vec![key]),
                    P::App("inj".into(), vec![srt("Int"), srt("KItem")], vec![int("0")]),
                ],
            )
        };
        let with_env = |m: P| {
            app(
                "<generatedTop>",
                vec![
                    app("<k>", vec![k()]),
                    app("<env>", vec![m]),
                    app("<generatedCounter>", vec![c()]),
                ],
            )
        };
        let plus = app("'UndsPlus'Int'Unds'", vec![int("1"), int("1")]);
        let m = app("'Unds'Map'Unds'", vec![entry(plus), entry(int("2"))]);
        let p = claim(
            vec![],
            with_env(m.clone()),
            "weakAlwaysFinally",
            &[],
            with_env(m),
            vec![],
        );
        let e = emit_one("c", &p, &t).unwrap_err();
        assert!(e.contains("`_+Int_`"), "{e}");
    }
}
