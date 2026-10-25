//! Concrete terms to Lean values: KORE patterns (krust output) and KAST JSON (krun output).

use crate::ir::{Def, P, S};
use crate::lower::{L, inj_sorts};
use crate::model::{Builtin, Kind, Model};
use crate::names;
use serde_json::Value;
use std::collections::BTreeMap;

pub struct Conv<'a> {
    pub m: &'a Model,
    pub def: &'a Def,
    /// K label → KORE symbol.
    labels: BTreeMap<String, String>,
    /// Write a `Bytes` literal as a list of bytes (`bytes_list`) rather than through a string.
    pub bytes_as_list: bool,
}

type R<T> = Result<T, String>;

/// A `Bytes` literal (one character per byte) as the list of its bytes: a run of at least 8 equal
/// bytes as `List.replicate`, the others as list literals, joined by `++`. It is the value of
/// `BytesHook.ofString val`, written so that the kernel evaluates it in time linear in its length:
/// through the string, the kernel decodes the literal's UTF-8 bytes, in time quadratic in its length.
pub fn bytes_list(val: &str) -> R<String> {
    let mut bytes = Vec::new();
    for c in val.chars() {
        bytes.push(
            u8::try_from(u32::from(c)).map_err(|_| format!("bad Bytes literal character {c:?}"))?,
        );
    }
    let mut parts: Vec<String> = Vec::new();
    let mut lit: Vec<String> = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let mut j = i;
        while j < bytes.len() && bytes[j] == bytes[i] {
            j += 1;
        }
        if j - i >= 8 {
            if !lit.is_empty() {
                parts.push(format!("[{}]", lit.join(", ")));
                lit.clear();
            }
            parts.push(format!("List.replicate {} ({} : UInt8)", j - i, bytes[i]));
        } else {
            lit.extend(bytes[i..j].iter().map(|b| b.to_string()));
        }
        i = j;
    }
    if !lit.is_empty() {
        parts.push(format!("[{}]", lit.join(", ")));
    }
    Ok(match parts.len() {
        0 => "([] : List UInt8)".to_string(),
        1 if parts[0].starts_with('[') => format!("({} : List UInt8)", parts[0]),
        _ => format!("(({}) : List UInt8)", parts.join(" ++ ")),
    })
}

impl<'a> Conv<'a> {
    pub fn new(m: &'a Model, def: &'a Def) -> Self {
        let mut labels = BTreeMap::new();
        for sym in def.symbols.keys() {
            labels.insert(names::demangle(sym), sym.clone());
        }
        Conv {
            m,
            def,
            labels,
            bytes_as_list: false,
        }
    }

    fn hook(&self, sym: &str) -> Option<String> {
        self.m.hooks.get(sym).cloned()
    }

    fn literal(&self, sort: &str, val: &str) -> R<L> {
        let info = self
            .m
            .sorts
            .get(sort)
            .ok_or(format!("literal of unknown sort {sort}"))?;
        Ok(match &info.kind {
            Kind::Builtin(Builtin::Int) => L::Raw(format!("({val} : Int)")),
            Kind::Builtin(Builtin::Bool) => L::Raw(val.to_string()),
            Kind::Builtin(Builtin::String) => L::Raw(names::string_lit(val)),
            Kind::Builtin(Builtin::Bytes) if self.bytes_as_list => L::Raw(bytes_list(val)?),
            Kind::Builtin(Builtin::Bytes) => L::Raw(format!(
                "(KPrelude.BytesHook.ofString {})",
                names::string_lit(val)
            )),
            Kind::Token => L::Raw(format!("({sort}.mk {})", names::string_lit(val))),
            _ => return Err(format!("domain value of sort {sort}")),
        })
    }

    /// The Lean value of a ground constructor term `p` at sort `sort`.
    pub fn value(&self, p: &P, sort: &str) -> R<L> {
        match p {
            P::Dv(s, v) => self.literal(s.name().unwrap_or_default(), v),
            P::App(f, params, args) if f == "inj" => {
                let (a, b) = inj_sorts(params)?;
                let _ = sort;
                match &args[0] {
                    P::App(g, gp, gargs) if g == "inj" => {
                        let (c, _) = inj_sorts(gp)?;
                        self.value(
                            &P::App(
                                "inj".into(),
                                vec![S::App(c, vec![]), S::App(b, vec![])],
                                gargs.clone(),
                            ),
                            sort,
                        )
                    }
                    P::App(g, _, gargs) if self.m.ctors.contains_key(g) => {
                        let own = self.ctor(g, gargs)?;
                        Ok(L::app(self.m.leaf_ctor(&b, &a), vec![own]))
                    }
                    t => {
                        let e = self.value(t, &a)?;
                        if self.m.sort(&a).is_simple() {
                            Ok(L::app(self.m.leaf_ctor(&b, &a), vec![e]))
                        } else {
                            Ok(L::app(
                                format!("inj_{}_{}", names::short_sort(&a), names::short_sort(&b)),
                                vec![e],
                            ))
                        }
                    }
                }
            }
            P::App(f, _, args) if self.m.ctors.contains_key(f) => {
                let s = self.m.ctors[f].sort.clone();
                let own = self.ctor(f, args)?;
                if self.m.sort(&s).is_simple() {
                    Ok(own)
                } else {
                    Ok(L::app(self.m.leaf_ctor(&s, &s), vec![own]))
                }
            }
            P::App(f, _, _)
                if matches!(
                    self.hook(f).as_deref(),
                    Some("MAP.concat" | "MAP.element" | "MAP.unit")
                ) =>
            {
                let msort = self.def.symbols[f]
                    .result
                    .name()
                    .unwrap_or("SortMap")
                    .to_string();
                let el = self.m.elems(&msort).to_vec();
                let mut entries = Vec::new();
                self.map_entries(p, &el, &mut entries)?;
                let items: Vec<String> = entries
                    .iter()
                    .map(|(k, v)| format!("({}, {})", k.render(), v.render()))
                    .collect();
                Ok(L::Raw(format!(
                    "(KPrelude.MapHook.ofEntries [{}] : {msort})",
                    items.join(", ")
                )))
            }
            P::App(f, _, _)
                if matches!(
                    self.hook(f).as_deref(),
                    Some(
                        "SET.concat"
                            | "SET.element"
                            | "SET.unit"
                            | "LIST.concat"
                            | "LIST.element"
                            | "LIST.unit"
                    )
                ) =>
            {
                let csort = self.def.symbols[f]
                    .result
                    .name()
                    .unwrap_or("SortSet")
                    .to_string();
                let el = self.m.elems(&csort)[0].clone();
                let mut items = Vec::new();
                self.coll_items(p, &el, &mut items)?;
                let items: Vec<String> = items.iter().map(|x| x.render()).collect();
                let ns = if self.hook(f).unwrap().starts_with("SET") {
                    "SetHook"
                } else {
                    "ListHook"
                };
                Ok(L::Raw(format!(
                    "(KPrelude.{ns}.ofElems [{}] : {csort})",
                    items.join(", ")
                )))
            }
            other => Err(format!(
                "not a ground constructor term: {}",
                crate::lower::short_dbg(other)
            )),
        }
    }

    fn ctor(&self, f: &str, args: &[P]) -> R<L> {
        let ci = &self.m.ctors[f];
        let mut la = Vec::new();
        for (a, s) in args.iter().zip(&ci.args) {
            la.push(self.value(a, s)?);
        }
        Ok(L::app(self.m.ctor_path(f), la))
    }

    fn map_entries(&self, p: &P, el: &[String], out: &mut Vec<(L, L)>) -> R<()> {
        let P::App(f, _, args) = p else {
            return Err("map entry".into());
        };
        match self.hook(f).as_deref() {
            Some("MAP.unit") => Ok(()),
            Some("MAP.concat") => {
                for a in args {
                    self.map_entries(a, el, out)?;
                }
                Ok(())
            }
            Some("MAP.element") => {
                out.push((self.value(&args[0], &el[0])?, self.value(&args[1], &el[1])?));
                Ok(())
            }
            _ => Err(format!("unexpected map term {f}")),
        }
    }

    fn coll_items(&self, p: &P, el: &str, out: &mut Vec<L>) -> R<()> {
        let P::App(f, _, args) = p else {
            return Err("collection item".into());
        };
        match self.hook(f).as_deref() {
            Some("SET.unit" | "LIST.unit") => Ok(()),
            Some("SET.concat" | "LIST.concat") => {
                for a in args {
                    self.coll_items(a, el, out)?;
                }
                Ok(())
            }
            Some("SET.element" | "LIST.element") => {
                out.push(self.value(&args[0], el)?);
                Ok(())
            }
            _ => Err(format!("unexpected collection term {f}")),
        }
    }

    /// KAST JSON (`krun --output json`'s `term`) to a sorted KORE-style pattern at `sort`.
    pub fn kast(&self, t: &Value, sort: &str) -> R<P> {
        let (p, nat) = self.kast_nat(t)?;
        self.coerce(p, &nat, sort)
    }

    fn coerce(&self, p: P, nat: &str, want: &str) -> R<P> {
        if nat == want {
            return Ok(p);
        }
        if want == "SortK" {
            let item = self.coerce(p, nat, "SortKItem")?;
            return Ok(P::App(
                "kseq".into(),
                vec![],
                vec![item, P::App("dotk".into(), vec![], vec![])],
            ));
        }
        if self.m.is_subsort(nat, want) {
            return Ok(P::App(
                "inj".into(),
                vec![S::App(nat.into(), vec![]), S::App(want.into(), vec![])],
                vec![p],
            ));
        }
        Err(format!("cannot use a {nat} where a {want} is expected"))
    }

    fn kast_nat(&self, t: &Value) -> R<(P, String)> {
        match t["node"].as_str() {
            Some("KToken") => {
                let sort = format!("Sort{}", t["sort"]["name"].as_str().ok_or("token sort")?);
                let tok = t["token"].as_str().ok_or("token")?.to_string();
                Ok((P::Dv(S::App(sort.clone(), vec![]), tok), sort))
            }
            Some("KSequence") => {
                let items = t["items"].as_array().ok_or("items")?;
                let mut acc = P::App("dotk".into(), vec![], vec![]);
                for it in items.iter().rev() {
                    let (p, nat) = self.kast_nat(it)?;
                    if nat == "SortK" {
                        return Err("nested K sequence".into());
                    }
                    let item = self.coerce(p, &nat, "SortKItem")?;
                    acc = P::App("kseq".into(), vec![], vec![item, acc]);
                }
                Ok((acc, "SortK".into()))
            }
            Some("KApply") => {
                let label = t["label"]["name"].as_str().ok_or("label")?;
                let sym = self
                    .labels
                    .get(label)
                    .ok_or(format!("unknown label {label}"))?;
                let d = &self.def.symbols[sym];
                let args = t["args"].as_array().ok_or("args")?;
                let mut ps = Vec::new();
                for (a, s) in args.iter().zip(&d.args) {
                    ps.push(self.kast(a, s.name().ok_or("parametric argument sort")?)?);
                }
                Ok((
                    P::App(sym.clone(), vec![], ps),
                    d.result.name().ok_or("parametric result")?.to_string(),
                ))
            }
            other => Err(format!("unsupported KAST node {other:?}")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::bytes_list;

    #[test]
    fn bytes_list_writes_runs_and_literals() {
        assert_eq!(bytes_list("").unwrap(), "([] : List UInt8)");
        assert_eq!(bytes_list("A").unwrap(), "([65] : List UInt8)");
        assert_eq!(
            bytes_list(&format!("{}AB", "\u{0}".repeat(9))).unwrap(),
            "((List.replicate 9 (0 : UInt8) ++ [65, 66]) : List UInt8)"
        );
        assert!(bytes_list("\u{100}").is_err());
    }
}
