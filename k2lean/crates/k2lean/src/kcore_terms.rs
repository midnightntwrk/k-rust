//! The terms of a claim sentence written in the Lean syntax of a package `kcore gen` wrote
//! (kcore-spec's `KcoreGen.lean`, `genSyntax`): the term lowering of `k2lean kcore-claims`.
//!
//! The name table is read from the package's `<NS>/Syntax.lean`, nothing else of the package:
//!
//! * each constructor is a doc line holding its decoded KORE symbol name (``/-- `<k>` -/``)
//!   followed by its `def`, whose name and typed binders give the Lean name, the argument sorts
//!   and the result sort (`def «<k>» (x0 : (KCore.Tm KCore.Srt.k)) : (KCore.Tm NS.Srt.«KCell») :=`);
//! * each subsort `a < b` is a line `scoped instance coe_a_b : _root_.Coe (KCore.Tm A) (KCore.Tm B)`,
//!   the coercion `Tm A → Tm B` that is the injection (`KCore.Tm.inj`).
//!
//! A KORE sort is written as the package writes it: a sort of the definition as `NS.Srt.«X»`
//! (`SortX`), a registry sort by the fixed table [`REGISTRY_SORTS`] (kcore-spec's
//! `KcoreSpec/FixedSignature.lean`, `regSortNames` and `namespace Srt`).
//!
//! The lowering, by node (every other node stops with a message naming it):
//!
//! * a constructor application: its `Syntax.lean` name, then its arguments in order, an argument
//!   that is not an atom in parentheses; each argument must have the sort the `def` gives it;
//! * `inj{a, b}(t)`: `t` alone, at a position whose sort is `b`, where `Syntax.lean` has the
//!   coercion from `a` to `b` (Lean inserts it); without the coercion, at a position whose sort is
//!   not `b`, at the top, or around another injection, it stops;
//! * `kseq{}(i, k)`: `Tm.kseq i k`; `dotk{}()`: `Tm.dotk`;
//! * `\dv{SortInt}("n")`: `Tm.int n` (`Tm.int (-n)` when negative); `\dv{SortId}("x")`:
//!   `Tm.ident "x"`; `\dv{SortBool}("true")`: `Tm.bool true` (and `false`);
//! * a `_Map_` tree whose leaves are `_|->_` entries and `.Map`: `Tm.map [(k₁, v₁), …]`, the
//!   entries in the text's order, only where the keys are pairwise distinct closed constructor
//!   terms (constructors, injections, `kseq`, `dotk`, domain values: no variable, no function).
//!   `_Map_` has no value where a key occurs twice, while `Tm.map` lets a later entry replace an
//!   earlier one; distinct closed constructor terms denote distinct elements, so the two agree;
//! * a variable, by the environment the caller gives (KORE name to Lean name; an unbound variable
//!   stops): of sort `Int` as `Tm.int X`, of sort `Bool` as `Tm.bool X`, of any other sort bare.
//!
//! An application of any other symbol (a function, a hooked symbol) stops, unless the caller's
//! [`Lower::int_fold`] writes it as a Lean integer expression; it is then `Tm.int (e)`.

use crate::ir::{P, S};
use crate::names;
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

/// The registry sorts: the KORE name without `Sort`, and the name in `KCore.Srt`.
pub const REGISTRY_SORTS: &[(&str, &str)] = &[
    ("K", "k"),
    ("KItem", "kitem"),
    ("Bool", "bool"),
    ("Int", "int"),
    ("KConfigVar", "kconfigVar"),
    ("List", "list"),
    ("Map", "map"),
    ("Set", "set"),
    ("Id", "ident"),
    ("String", "string"),
    ("Float", "float"),
    ("IOError", "ioError"),
    ("IOFile", "ioFile"),
    ("IOInt", "ioInt"),
    ("IOString", "ioString"),
    ("Stream", "stream"),
    ("GeneratedTopCell", "top"),
    ("GeneratedTopCellFragment", "topFrag"),
    ("GeneratedCounterCell", "counter"),
    ("GeneratedCounterCellOpt", "counterOpt"),
];

/// A constructor of the package: its Lean name as the `def` writes it, its argument sorts and
/// its result sort (each the Lean text of a sort, `KCore.Srt.k` or `NS.Srt.«KCell»`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ctor {
    pub lean: String,
    pub args: Vec<String>,
    pub result: String,
}

/// The name table of a package's `Syntax.lean`.
#[derive(Clone, Debug, Default)]
pub struct Table {
    /// The package's namespace (`RefKimp`).
    pub ns: String,
    /// Decoded KORE symbol name to constructor.
    pub ctors: BTreeMap<String, Ctor>,
    /// The pairs `(a, b)` of sort texts with a coercion `Tm a → Tm b`.
    pub coes: BTreeSet<(String, String)>,
    /// The sort texts of the definition's own sorts that the file mentions.
    pub own_sorts: BTreeSet<String>,
}

/// Reads the name table from the text of a package's `Syntax.lean`.
pub fn read_syntax(text: &str) -> Result<Table, String> {
    let mut t = Table::default();
    for l in text.lines() {
        if let Some(rest) = l.strip_prefix("namespace ")
            && let Some(ns) = rest.trim().strip_suffix(".Syntax")
        {
            t.ns = ns.to_string();
            break;
        }
    }
    if t.ns.is_empty() {
        return Err("Syntax.lean: no `namespace <NS>.Syntax` line".into());
    }
    let lines: Vec<&str> = text.lines().collect();
    for (i, l) in lines.iter().enumerate() {
        if let Some(rest) = l.strip_prefix("scoped instance coe_") {
            let (_, ty) = rest
                .split_once(" : _root_.Coe ")
                .ok_or_else(|| format!("Syntax.lean:{}: coercion line not understood", i + 1))?;
            let (a, ty) = tm_sort(ty)
                .ok_or_else(|| format!("Syntax.lean:{}: coercion source not understood", i + 1))?;
            let (b, ty) = tm_sort(ty.trim_start())
                .ok_or_else(|| format!("Syntax.lean:{}: coercion target not understood", i + 1))?;
            if ty.trim() != ":= ⟨KCore.Tm.inj⟩" {
                return Err(format!(
                    "Syntax.lean:{}: a coercion that is not KCore.Tm.inj",
                    i + 1
                ));
            }
            t.coes.insert((a.to_string(), b.to_string()));
            continue;
        }
        let Some(sym) = l.strip_prefix("/-- `").and_then(|r| r.strip_suffix("` -/")) else {
            continue;
        };
        let Some(def) = lines.get(i + 1).and_then(|d| d.strip_prefix("def ")) else {
            continue;
        };
        let at = |what: &str| format!("Syntax.lean:{}: {what}", i + 2);
        let (lean, mut rest) = if let Some(r) = def.strip_prefix('«') {
            let e = r.find('»').ok_or_else(|| at("unterminated «"))?;
            (format!("«{}»", &r[..e]), &r[e + '»'.len_utf8()..])
        } else {
            let e = def.find(' ').ok_or_else(|| at("def line not understood"))?;
            (def[..e].to_string(), &def[e..])
        };
        let mut args = vec![];
        loop {
            rest = rest.trim_start();
            if let Some(r) = rest.strip_prefix(&format!("(x{} : ", args.len())) {
                let (s, r) = tm_sort(r).ok_or_else(|| at("binder not understood"))?;
                rest = r.strip_prefix(')').ok_or_else(|| at("binder not closed"))?;
                args.push(s.to_string());
            } else if let Some(r) = rest.strip_prefix(": ") {
                let (s, r) = tm_sort(r).ok_or_else(|| at("result sort not understood"))?;
                if !r.trim_start().starts_with(":=") {
                    return Err(at("def line not understood after the result sort"));
                }
                let c = Ctor {
                    lean,
                    args,
                    result: s.to_string(),
                };
                if t.ctors.insert(sym.to_string(), c).is_some() {
                    return Err(at(&format!("symbol `{sym}` named twice")));
                }
                break;
            } else {
                return Err(at("def line not understood"));
            }
        }
    }
    let own = format!("{}.Srt.«", t.ns);
    let mut own_sorts = BTreeSet::new();
    for s in t
        .ctors
        .values()
        .flat_map(|c| c.args.iter().chain(std::iter::once(&c.result)))
        .chain(t.coes.iter().flat_map(|(a, b)| [a, b]))
    {
        if s.starts_with(&own) {
            own_sorts.insert(s.clone());
        }
    }
    t.own_sorts = own_sorts;
    Ok(t)
}

/// `(KCore.Tm S)` at the start of `s`: the sort text `S` and the rest after the parenthesis.
fn tm_sort(s: &str) -> Option<(&str, &str)> {
    let r = s.strip_prefix("(KCore.Tm ")?;
    let e = r.find(')')?;
    Some((&r[..e], &r[e + 1..]))
}

impl Table {
    /// The Lean text of a KORE sort (`SortInt` → `KCore.Srt.int`, `SortStmt` → `NS.Srt.«Stmt»`).
    pub fn sort(&self, s: &S) -> Result<String, String> {
        let S::App(n, a) = s else {
            return Err(format!("sort variable {s}"));
        };
        if !a.is_empty() {
            return Err(format!("parametric sort {s}"));
        }
        let short = names::short_sort(n);
        if let Some((_, l)) = REGISTRY_SORTS.iter().find(|(k, _)| *k == short) {
            return Ok(format!("KCore.Srt.{l}"));
        }
        let own = format!("{}.Srt.«{}»", self.ns, names::demangle(short));
        if self.own_sorts.contains(&own) {
            return Ok(own);
        }
        Err(format!(
            "sort {n}: neither a registry sort nor a sort Syntax.lean mentions"
        ))
    }
}

/// A lowered term: its text, the sort text of the position it may stand at, and whether it is an
/// atom (written without parentheses as an argument).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lowered {
    pub text: String,
    pub sort: String,
    pub atom: bool,
    /// The text is an injection written bare: it stands for a term of `sort` only where Lean
    /// inserts the coercion, at an argument position of that sort.
    pub coerced: bool,
}

/// The lowering of one claim's terms.
pub struct Lower<'a> {
    pub table: &'a Table,
    /// KORE variable name to Lean name.
    pub env: &'a BTreeMap<String, String>,
    /// A writer of an `Int`-sorted application of a symbol that is not a constructor as a Lean
    /// integer expression (`Ok(None)`: no rule, the lowering stops).
    #[allow(clippy::type_complexity)]
    pub int_fold: Option<&'a dyn Fn(&Lower<'a>, &P) -> Result<Option<String>, String>>,
}

const MAP_CONCAT: &str = "_Map_";
const MAP_ELEMENT: &str = "_|->_";
const MAP_UNIT: &str = ".Map";

/// A short rendering of a node, for messages.
pub fn node(p: &P) -> String {
    match p {
        P::App(f, s, a) => {
            let ss: Vec<String> = s.iter().map(|s| s.to_string()).collect();
            format!(
                "{}{{{}}}(…{} arguments)",
                if f.starts_with("Lbl") {
                    names::demangle(f)
                } else {
                    f.clone()
                },
                ss.join(","),
                a.len()
            )
        }
        P::Var(v, s) => format!("variable {v}:{s}"),
        P::Dv(s, v) => format!("\\dv{{{s}}}({v:?})"),
        P::Str(s) => format!("string {s:?}"),
        other => {
            let d = format!("{other:?}");
            d.chars().take(80).collect()
        }
    }
}

/// The integer of an `Int` token, in decimal.
pub fn int_token(v: &str) -> Result<BigInt, String> {
    let digits = v.strip_prefix(['-', '+']).unwrap_or(v);
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return Err(format!("\\dv{{SortInt{{}}}}({v:?}): not an integer token"));
    }
    v.strip_prefix('+')
        .unwrap_or(v)
        .parse::<BigInt>()
        .map_err(|e| format!("\\dv{{SortInt{{}}}}({v:?}): {e}"))
}

/// The Lean text of an integer literal: `-n` in parentheses.
pub fn int_lit(n: &BigInt) -> String {
    if n.sign() == num_bigint::Sign::Minus {
        format!("({n})")
    } else {
        n.to_string()
    }
}

fn paren(l: &Lowered) -> String {
    if l.atom {
        l.text.clone()
    } else {
        format!("({})", l.text)
    }
}

impl<'a> Lower<'a> {
    /// A term at the top: an injection written bare is refused (nothing would insert it).
    pub fn top(&self, p: &P) -> Result<Lowered, String> {
        let l = self.term(p)?;
        if l.coerced {
            return Err(format!("{}: an injection at the top", node(p)));
        }
        Ok(l)
    }

    /// A term at a position of sort `want` (a sort text).
    pub fn at(&self, p: &P, want: &str) -> Result<Lowered, String> {
        let l = self.term(p)?;
        if l.sort != want {
            return Err(format!(
                "{}: of sort {} at a position of sort {want}",
                node(p),
                l.sort
            ));
        }
        Ok(l)
    }

    /// The Lean name of a variable.
    pub fn var(&self, v: &str) -> Result<&'a str, String> {
        self.env
            .get(v)
            .map(|s| s.as_str())
            .ok_or_else(|| format!("variable {v}: not bound"))
    }

    pub fn term(&self, p: &P) -> Result<Lowered, String> {
        let t = self.table;
        match p {
            P::Var(v, s) => {
                let x = self.var(v)?;
                let sort = t.sort(s)?;
                Ok(match sort.as_str() {
                    "KCore.Srt.int" => self.plain(format!("Tm.int {x}"), sort),
                    "KCore.Srt.bool" => self.plain(format!("Tm.bool {x}"), sort),
                    _ => self.atom(x.to_string(), sort),
                })
            }
            P::Dv(s, v) => {
                let sort = t.sort(s)?;
                match sort.as_str() {
                    "KCore.Srt.int" => {
                        Ok(self.plain(format!("Tm.int {}", int_lit(&int_token(v)?)), sort))
                    }
                    "KCore.Srt.ident" => {
                        Ok(self.plain(format!("Tm.ident {}", names::string_lit(v)), sort))
                    }
                    "KCore.Srt.bool" if v == "true" || v == "false" => {
                        Ok(self.plain(format!("Tm.bool {v}"), sort))
                    }
                    _ => Err(format!("{}: no rule for this domain value", node(p))),
                }
            }
            P::App(f, ss, args) if f == "inj" => {
                let ([a, b], [x]) = (ss.as_slice(), args.as_slice()) else {
                    return Err(format!("{}: not inj{{a, b}}(t)", node(p)));
                };
                let (a, b) = (t.sort(a)?, t.sort(b)?);
                let inner = self.at(x, &a)?;
                if inner.coerced {
                    return Err(format!("{}: an injection of an injection", node(p)));
                }
                if !t.coes.contains(&(a.clone(), b.clone())) {
                    return Err(format!(
                        "{}: Syntax.lean has no coercion from {a} to {b}",
                        node(p)
                    ));
                }
                Ok(Lowered {
                    sort: b,
                    coerced: true,
                    ..inner
                })
            }
            P::App(f, ss, args) if f == "kseq" && ss.is_empty() => {
                let [i, k] = args.as_slice() else {
                    return Err(format!("{}: kseq with other than two arguments", node(p)));
                };
                let i = self.at(i, "KCore.Srt.kitem")?;
                let k = self.at(k, "KCore.Srt.k")?;
                Ok(self.plain(
                    format!("Tm.kseq {} {}", paren(&i), paren(&k)),
                    "KCore.Srt.k".into(),
                ))
            }
            P::App(f, ss, args) if f == "dotk" && ss.is_empty() && args.is_empty() => {
                Ok(self.atom("Tm.dotk".into(), "KCore.Srt.k".into()))
            }
            P::App(f, ss, args) if f.starts_with("Lbl") => {
                let sym = names::demangle(f);
                if !ss.is_empty() {
                    return Err(format!("{}: a parametric symbol", node(p)));
                }
                if sym == MAP_CONCAT || sym == MAP_ELEMENT || sym == MAP_UNIT {
                    return self.map(p);
                }
                if let Some(c) = t.ctors.get(&sym) {
                    if c.args.len() != args.len() {
                        return Err(format!(
                            "{}: {} arguments, Syntax.lean's {} takes {}",
                            node(p),
                            args.len(),
                            c.lean,
                            c.args.len()
                        ));
                    }
                    let mut text = c.lean.clone();
                    for (a, s) in args.iter().zip(&c.args) {
                        text.push(' ');
                        text.push_str(&paren(&self.at(a, s)?));
                    }
                    return Ok(if args.is_empty() {
                        self.atom(text, c.result.clone())
                    } else {
                        self.plain(text, c.result.clone())
                    });
                }
                if let Some(fold) = self.int_fold
                    && let Some(e) = fold(self, p)?
                {
                    return Ok(self.plain(format!("Tm.int ({e})"), "KCore.Srt.int".into()));
                }
                Err(format!(
                    "{}: no constructor of Syntax.lean and no rule for the symbol `{sym}`",
                    node(p)
                ))
            }
            _ => Err(format!("{}: no rule for this node", node(p))),
        }
    }

    fn plain(&self, text: String, sort: String) -> Lowered {
        Lowered {
            text,
            sort,
            atom: false,
            coerced: false,
        }
    }

    fn atom(&self, text: String, sort: String) -> Lowered {
        Lowered {
            text,
            sort,
            atom: true,
            coerced: false,
        }
    }

    /// `_Map_` / `_|->_` / `.Map` as `Tm.map [...]`.
    fn map(&self, p: &P) -> Result<Lowered, String> {
        let mut leaves = vec![];
        map_leaves(p, &mut leaves)?;
        let mut keys: Vec<String> = vec![];
        let mut entries = vec![];
        for (k, v) in leaves {
            if let Some(n) = open_node(k) {
                return Err(format!(
                    "{}: a map key that is not a closed constructor term ({})",
                    node(k),
                    node(n)
                ));
            }
            let kl = self.at(k, "KCore.Srt.kitem")?;
            let vl = self.at(v, "KCore.Srt.kitem")?;
            if keys.contains(&kl.text) {
                return Err(format!("{}: a map key that occurs twice", node(k)));
            }
            keys.push(kl.text.clone());
            entries.push(format!("({}, {})", kl.text, vl.text));
        }
        Ok(self.plain(
            format!("Tm.map [{}]", entries.join(", ")),
            "KCore.Srt.map".into(),
        ))
    }
}

/// The entries of a map term, in the text's order.
fn map_leaves<'p>(p: &'p P, out: &mut Vec<(&'p P, &'p P)>) -> Result<(), String> {
    match p {
        P::App(f, ss, args) if f.starts_with("Lbl") && ss.is_empty() => {
            match (names::demangle(f).as_str(), args.as_slice()) {
                (MAP_CONCAT, [a, b]) => {
                    map_leaves(a, out)?;
                    map_leaves(b, out)
                }
                (MAP_ELEMENT, [k, v]) => {
                    out.push((k, v));
                    Ok(())
                }
                (MAP_UNIT, []) => Ok(()),
                _ => Err(format!("{}: not an entry of a map", node(p))),
            }
        }
        _ => Err(format!(
            "{}: a map with a part that is not an entry (a variable or a function)",
            node(p)
        )),
    }
}

/// The first node of `p` that is not of a closed constructor term: a variable, or an application
/// of a symbol that is not `inj`, `kseq`, `dotk` or a constructor-named `Lbl` symbol other than the
/// map symbols (whether such a symbol is a constructor of the package is checked by the lowering).
fn open_node(p: &P) -> Option<&P> {
    match p {
        P::Dv(..) => None,
        P::App(f, _, args)
            if f == "inj"
                || f == "kseq"
                || f == "dotk"
                || (f.starts_with("Lbl")
                    && ![MAP_CONCAT, MAP_ELEMENT, MAP_UNIT]
                        .contains(&names::demangle(f).as_str())) =>
        {
            args.iter().find_map(open_node)
        }
        _ => Some(p),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    /// kcore-spec, beside k2lean in the k-rust checkout.
    fn kcore_spec() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../kcore/kcore-spec")
    }

    fn read(rel: &str) -> String {
        let p = kcore_spec().join(rel);
        std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
    }

    fn table() -> Table {
        read_syntax(&read("examples/ref-kimp/RefKimp/Syntax.lean")).unwrap()
    }

    fn srt(n: &str) -> S {
        S::App(format!("Sort{n}"), vec![])
    }

    fn var(v: &str, s: &str) -> P {
        P::Var(v.into(), srt(s))
    }

    fn app(sym: &str, args: Vec<P>) -> P {
        assert!(!sym.contains('\''));
        P::App(format!("Lbl{sym}"), vec![], args)
    }

    fn inj(a: &str, b: &str, t: P) -> P {
        P::App("inj".into(), vec![srt(a), srt(b)], vec![t])
    }

    fn dv(s: &str, v: &str) -> P {
        P::Dv(srt(s), v.into())
    }

    fn env(pairs: &[(&str, &str)]) -> BTreeMap<String, String> {
        pairs
            .iter()
            .map(|(a, b)| (a.to_string(), b.to_string()))
            .collect()
    }

    fn lower(t: &Table, e: &BTreeMap<String, String>, p: &P) -> Result<Lowered, String> {
        Lower {
            table: t,
            env: e,
            int_fold: None,
        }
        .top(p)
    }

    fn norm(s: &str) -> String {
        s.split_whitespace().collect::<Vec<_>>().join(" ")
    }

    #[test]
    fn name_table_of_ref_kimp() {
        let t = table();
        assert_eq!(t.ns, "RefKimp");
        assert_eq!(t.ctors.len(), 54);
        assert_eq!(t.coes.len(), 29);
        assert_eq!(
            t.ctors["while(_)__IMP-SYNTAX_Stmt_Expr_Stmt"],
            Ctor {
                lean: "«while(_)_»".into(),
                args: vec!["RefKimp.Srt.«Expr»".into(), "RefKimp.Srt.«Stmt»".into()],
                result: "RefKimp.Srt.«Stmt»".into(),
            }
        );
        assert_eq!(t.ctors["___CALC-SYNTAX_Stmt_Stmt_Stmt"].lean, "«__»");
        assert_eq!(t.ctors["{}_IMP-SYNTAX_Stmt"].args.len(), 0);
        assert!(
            t.coes
                .contains(&("KCore.Srt.ident".into(), "RefKimp.Srt.«Expr»".into()))
        );
        assert!(
            !t.coes
                .contains(&("RefKimp.Srt.«Stmt»".into(), "RefKimp.Srt.«Expr»".into()))
        );
    }

    /// [`REGISTRY_SORTS`] is `FixedSignature.lean`'s table: the KORE name at index `n` of
    /// `regSortNames` is the sort numbered `n` in `namespace Srt`, and every name but the
    /// parametric `MInt` is in the table.
    #[test]
    fn registry_sorts_are_the_fixed_signature() {
        let f = read("KcoreSpec/FixedSignature.lean");
        let list = f.split("def regSortNames : List String :=").nth(1).unwrap();
        let list = &list[list.find('[').unwrap() + 1..list.find(']').unwrap()];
        let kore: Vec<&str> = list
            .split(',')
            .map(|s| s.trim().trim_matches('"'))
            .collect();
        let mut num = BTreeMap::new();
        for l in f.lines() {
            if let Some(r) = l.strip_prefix("@[match_pattern, reducible] def ")
                && let Some((n, v)) = r.split_once(" : Srt := ")
                && let Ok(v) = v.trim().parse::<usize>()
            {
                num.insert(n.to_string(), v);
            }
        }
        for (k, l) in REGISTRY_SORTS {
            assert_eq!(kore.get(num[*l]), Some(k), "{k} / {l}");
        }
        for k in kore {
            assert!(
                k == "MInt" || REGISTRY_SORTS.iter().any(|(x, _)| *x == k),
                "{k} missing"
            );
        }
    }

    /// One term of every constructor of the package: each applied to variables of its argument
    /// sorts is its Lean name applied to them, at its result sort.
    #[test]
    fn every_constructor() {
        let t = table();
        let kore_sort = |s: &str| -> String {
            if let Some(l) = s.strip_prefix("KCore.Srt.") {
                REGISTRY_SORTS
                    .iter()
                    .find(|(_, x)| *x == l)
                    .unwrap()
                    .0
                    .to_string()
            } else {
                s.strip_prefix("RefKimp.Srt.«")
                    .unwrap()
                    .strip_suffix('»')
                    .unwrap()
                    .to_string()
            }
        };
        for (sym, c) in &t.ctors {
            let vs: Vec<String> = (0..c.args.len()).map(|i| format!("Vx{i}")).collect();
            let e: BTreeMap<String, String> = vs
                .iter()
                .enumerate()
                .map(|(i, v)| (v.clone(), format!("x{i}")))
                .collect();
            let p = app(
                sym,
                vs.iter()
                    .zip(&c.args)
                    .map(|(v, s)| var(v, &kore_sort(s)))
                    .collect(),
            );
            let l = lower(&t, &e, &p).unwrap();
            let mut want = c.lean.clone();
            for (i, s) in c.args.iter().enumerate() {
                want.push_str(&match s.as_str() {
                    "KCore.Srt.int" => format!(" (Tm.int x{i})"),
                    "KCore.Srt.bool" => format!(" (Tm.bool x{i})"),
                    _ => format!(" x{i}"),
                });
            }
            assert_eq!(l.text, want, "{sym}");
            assert_eq!(l.sort, c.result, "{sym}");
            assert_eq!(l.atom, c.args.is_empty(), "{sym}");
        }
    }

    #[test]
    fn domain_values_sequences_maps() {
        let t = table();
        let e = env(&[]);
        let l = |p: &P| lower(&t, &e, p).map(|l| l.text);
        assert_eq!(l(&dv("Int", "0")).unwrap(), "Tm.int 0");
        assert_eq!(l(&dv("Int", "-1")).unwrap(), "Tm.int (-1)");
        assert_eq!(l(&dv("Int", "+007")).unwrap(), "Tm.int 7");
        assert_eq!(l(&dv("Id", "a\"b")).unwrap(), "Tm.ident \"a\\\"b\"");
        assert_eq!(l(&dv("Bool", "false")).unwrap(), "Tm.bool false");
        let skip = app("{}_IMP-SYNTAX_Stmt", vec![]);
        let seq = P::App(
            "kseq".into(),
            vec![],
            vec![
                inj("Stmt", "KItem", skip.clone()),
                P::App("dotk".into(), vec![], vec![]),
            ],
        );
        assert_eq!(l(&seq).unwrap(), "Tm.kseq «{}» Tm.dotk");
        assert_eq!(l(&app(".Map", vec![])).unwrap(), "Tm.map []");
        let ent = |k: &str, v: P| {
            app(
                "_|->_",
                vec![inj("Id", "KItem", dv("Id", k)), inj("Int", "KItem", v)],
            )
        };
        let m = app(
            "_Map_",
            vec![
                app(
                    "_Map_",
                    vec![ent("$a", dv("Int", "1")), app(".Map", vec![])],
                ),
                ent("$b", dv("Int", "-2")),
            ],
        );
        assert_eq!(
            l(&m).unwrap(),
            "Tm.map [(Tm.ident \"$a\", Tm.int 1), (Tm.ident \"$b\", Tm.int (-2))]"
        );
    }

    /// Every node without a rule stops, naming the node.
    #[test]
    fn closed_world() {
        let t = table();
        let e = env(&[("VarX", "X"), ("VarM", "M")]);
        let err = |p: &P| lower(&t, &e, p).unwrap_err();
        let skip = app("{}_IMP-SYNTAX_Stmt", vec![]);
        let not = |x: P| app("!__EXPR-SYNTAX_Expr_Expr", vec![x]);
        // an injection without a coercion
        assert!(err(&not(inj("Stmt", "Expr", skip.clone()))).contains("no coercion from"));
        // an injection of an injection, and one at the top
        let ii = inj("Value", "Expr", inj("Int", "Value", dv("Int", "1")));
        assert!(err(&not(ii)).contains("an injection of an injection"));
        assert!(err(&inj("Int", "Expr", dv("Int", "1"))).contains("at the top"));
        // a symbol the package has no constructor for
        let plus = app("_+Int_", vec![var("VarX", "Int"), dv("Int", "1")]);
        assert!(err(&plus).contains("`_+Int_`"));
        // an argument of another sort
        assert!(err(&not(dv("Int", "1"))).contains("at a position of sort RefKimp.Srt.«Expr»"));
        // an unbound variable
        assert!(err(&var("VarY", "Int")).contains("VarY: not bound"));
        // domain values without a rule
        assert!(err(&dv("String", "s")).contains("no rule for this domain value"));
        assert!(err(&dv("Bool", "maybe")).contains("no rule for this domain value"));
        assert!(err(&dv("Int", "1.0")).contains("not an integer token"));
        // a sort the table does not know
        assert!(err(&var("VarX", "Nope")).contains("SortNope"));
        // a node that is not a term
        assert!(err(&P::Top(srt("K"))).contains("no rule for this node"));
        // maps: a key occurring twice, a key with a variable, a variable part
        let ent = |k: P| {
            app(
                "_|->_",
                vec![inj("Id", "KItem", k), inj("Int", "KItem", dv("Int", "0"))],
            )
        };
        let twice = app("_Map_", vec![ent(dv("Id", "$a")), ent(dv("Id", "$a"))]);
        assert!(err(&twice).contains("occurs twice"));
        let open = app("_Map_", vec![ent(dv("Id", "$a")), ent(var("VarX", "Id"))]);
        assert!(err(&open).contains("not a closed constructor term"));
        let rest = app("_Map_", vec![ent(dv("Id", "$a")), var("VarM", "Map")]);
        assert!(err(&rest).contains("not an entry"));
    }

    /// The claim `sum-spec` of fixture cs-sum-spec-kore (selected by its whole label).
    fn sum_spec() -> crate::claims::RawClaim {
        let path = kcore_spec().join("examples/ref-kimp/claims/imp-sum-spec/spec.kore");
        let mut cs: Vec<_> = crate::claims::read_claims(&path)
            .into_iter()
            .filter(|c| c.label == "IMP-SUM-SPEC.sum-spec")
            .collect();
        assert_eq!(cs.len(), 1);
        cs.pop().unwrap()
    }

    fn sum_spec_env() -> BTreeMap<String, String> {
        env(&[
            ("VarN", "N"),
            ("VarS", "S"),
            ("Var'Unds'DotVar1", "K"),
            ("Var'Unds'Gen0", "C"),
            ("Var'QuesUnds'Gen1", "C'"),
        ])
    }

    /// The left side of sum-spec is, up to white space, the left configuration of
    /// `ExpectedKore.«sum-spec»` (examples/ref-kimp/User/SumSpecStmt.lean).
    #[test]
    fn sum_spec_left_side() {
        let c = sum_spec();
        let parts = crate::claims::parts(&c.pattern).unwrap();
        let l = lower(&table(), &sum_spec_env(), parts.lhs).unwrap();
        assert_eq!(l.sort, "KCore.Srt.top");
        let stmt = read("examples/ref-kimp/User/SumSpecStmt.lean");
        let body = stmt
            .split("def ExpectedKore.«sum-spec» : Prop :=")
            .nth(1)
            .unwrap();
        let left = body.split("(fun x => x.val =").nth(1).unwrap();
        let left = &left[..left.find(".val)").unwrap()];
        assert_eq!(format!("({})", l.text), norm(left));
    }

    /// The right side of sum-spec holds `_+Int_`, a function: the term lowering alone stops
    /// there; its constructor-only cells are the right side's of `ExpectedKore.«sum-spec»`.
    #[test]
    fn sum_spec_right_side() {
        let c = sum_spec();
        let parts = crate::claims::parts(&c.pattern).unwrap();
        let t = table();
        let e = sum_spec_env();
        let err = lower(&t, &e, parts.rhs).unwrap_err();
        assert!(err.contains("`_+Int_`"), "{err}");
        let P::App(_, _, cells) = parts.rhs else {
            panic!()
        };
        let texts: Vec<String> = [&cells[0], &cells[2]]
            .iter()
            .map(|p| lower(&t, &e, p).unwrap().text)
            .collect();
        assert_eq!(texts, ["«<k>» K", "«<generatedCounter>» (Tm.int C')"]);
        let stmt = norm(&read("examples/ref-kimp/User/SumSpecStmt.lean"));
        let body = stmt
            .split("def ExpectedKore.«sum-spec» : Prop :=")
            .nth(1)
            .unwrap();
        let right = body.split("(fun z =>").nth(1).unwrap();
        for x in texts {
            assert!(right.contains(&format!("({x})")), "{x}");
        }
        assert_eq!(
            parts.existentials,
            [("Var'QuesUnds'Gen1".to_string(), "SortInt".to_string())]
        );
    }
}
