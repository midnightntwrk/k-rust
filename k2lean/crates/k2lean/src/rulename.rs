//! Stable names for rewrite rules (the `Step` constructor names that hand proofs, residual-case
//! tags and `relate`'s correspondence refer to).
//!
//! A rule's name is its K label when it has one. Otherwise it is derived from the rule's own
//! content, never from its position, so that adding, removing or moving other rules does not
//! rename it:
//!
//! 1. the *focus* of the left-hand side, written in K-like concrete syntax (`X * Y`,
//!    `true && B`, `if(true) S1 else _`): the first item of the first `<k>` cell, or, for a rule
//!    that does not match a `<k>` cell, the first term of its left-hand side that is not a cell;
//! 2. when two rules of the definition get the same focus, each of them is written with the
//!    sorts of its variables (`X:Int + Y:Int`);
//! 3. when that still collides, a short digest of the whole rewrite axiom (left-hand side,
//!    requires, right-hand side; variables renamed by first occurrence, so their names do not
//!    count) is appended (` #1a2b3c`).
//!
//! The name is a function of the rule and of the rules that share its focus, and of nothing
//! else; in particular not of the source position (kept as the constructor's doc comment).

use crate::ir::{Def, P, S};
use crate::names;
use std::collections::BTreeMap;
use std::fmt::Write;

/// Names that Lean or the generator already uses inside the `Step`, `App`, `Rules` and `R`
/// namespaces: a content name equal to one of them is disambiguated as a collision.
const RESERVED: &[&str] = &[
    "app",
    "deterministic",
    "preserves_of",
    "Case",
    "rec",
    "recOn",
    "casesOn",
    "below",
    "brecOn",
    "ibelow",
    "binductionOn",
    "noConfusion",
    "noConfusionType",
    "mk",
    "complete",
    "applies",
    "mem",
];

/// Longest focus rendering kept whole; a longer one is rendered with deeper subterms elided.
const MAX_LEN: usize = 60;

/// The source position `file:line:col` of an axiom (the file's base name only).
pub fn location(a: &crate::ir::AxiomDecl) -> Option<String> {
    let l = a
        .attrs
        .string("org'Stop'kframework'Stop'attributes'Stop'Location")?;
    let nums: Vec<&str> = l
        .trim_start_matches("Location(")
        .trim_end_matches(')')
        .split(',')
        .collect();
    let s = a
        .attrs
        .string("org'Stop'kframework'Stop'attributes'Stop'Source")?;
    let s = s.trim_start_matches("Source(").trim_end_matches(')');
    let file = s.rsplit('/').next().unwrap_or(s);
    Some(format!("{file}:{}:{}", nums.first()?, nums.get(1)?))
}

/// The source file of an axiom (its basename), for a KORE that records no line (`krs build`).
pub fn source_file(a: &crate::ir::AxiomDecl) -> Option<String> {
    let s = a
        .attrs
        .string("org'Stop'kframework'Stop'attributes'Stop'Source")?;
    let s = s.trim_start_matches("Source(").trim_end_matches(')');
    Some(s.rsplit('/').next().unwrap_or(s).to_string())
}

/// The left-hand side (configuration pattern, without its requires) of a rewrite axiom.
fn lhs_of(p: &P) -> Option<&P> {
    let P::Rewrites(_, l, _) = p else { return None };
    Some(match &**l {
        P::And(_, ps) if ps.len() == 2 => &ps[0],
        other => other,
    })
}

fn is_cell(sym: &str) -> bool {
    let d = names::demangle(sym);
    d.starts_with('<') && d.ends_with('>') && d.len() > 2
}

/// The focus of a left-hand side (see the module documentation).
pub fn focus(lhs: &P) -> &P {
    fn k_cell(p: &P) -> Option<&P> {
        match p {
            P::App(f, _, args) if names::demangle(f) == "<k>" => args.first(),
            P::App(_, _, args) => args.iter().find_map(k_cell),
            P::And(_, ps) => ps.iter().find_map(k_cell),
            _ => None,
        }
    }
    fn first_term(p: &P) -> Option<&P> {
        match p {
            P::App(f, _, args) if is_cell(f) || f == "inj" || f == "kseq" => {
                args.iter().find_map(first_term)
            }
            P::App(..) | P::Dv(..) => Some(p),
            P::And(_, ps) => ps.iter().find_map(first_term),
            _ => None,
        }
    }
    if let Some(k) = k_cell(lhs) {
        return match k {
            P::App(f, _, args) if f == "kseq" && args.len() == 2 => &args[0],
            other => other,
        };
    }
    first_term(lhs).unwrap_or(lhs)
}

/// How a variable is written: its source name, `_` for an anonymous one, `...` for K's
/// structural frame variables.
fn var_name(v: &str) -> String {
    let d = names::demangle(v);
    let d = d.strip_prefix("Var").unwrap_or(&d);
    if d.starts_with("_DotVar") {
        return "...".into();
    }
    let anon = |s: &str| {
        s == "_"
            || s.strip_prefix("_Gen")
                .is_some_and(|n| n.chars().all(|c| c.is_ascii_digit()))
    };
    if let Some(rest) = d.strip_prefix('?') {
        return if anon(rest) {
            "?_".into()
        } else {
            d.to_string()
        };
    }
    if anon(d) { "_".into() } else { d.to_string() }
}

/// The concrete-syntax template of a symbol: K's generated label with its module and sort suffix
/// removed (`_*_`, `if(_)_else_`), else the label itself.
fn template(sym: &str, def: &Def) -> String {
    let label = names::demangle(sym);
    let Some(d) = def.symbols.get(sym) else {
        return label;
    };
    let result = d.result.name().unwrap_or_default().to_string();
    // the empty list of a `List{…}` production is written `.Sort` (K's `.Exps`)
    if label.starts_with(".List{") && d.args.is_empty() {
        return format!(".{}", names::short_sort(&result));
    }
    let args: Vec<String> = d
        .args
        .iter()
        .map(|s| s.name().unwrap_or_default().to_string())
        .collect();
    names::short_label(&label, &result, &args).unwrap_or(label)
}

struct Render<'a> {
    def: &'a Def,
    sorts: bool,
    depth: usize,
}

impl Render<'_> {
    fn is_empty_list(&self, p: &P) -> bool {
        match p {
            P::App(f, _, args) if f == "inj" && args.len() == 1 => self.is_empty_list(&args[0]),
            P::App(f, _, args) => args.is_empty() && names::demangle(f).starts_with(".List{"),
            _ => false,
        }
    }

    fn term(&self, p: &P, d: usize, out: &mut String) {
        match p {
            P::Var(v, s) => {
                out.push_str(&var_name(v));
                if self.sorts && !out.ends_with("...") {
                    out.push(':');
                    out.push_str(names::short_sort(s.name().unwrap_or("?")));
                }
            }
            P::Dv(s, val) => match s.name() {
                Some("SortString") => out.push_str(&names::string_lit(val)),
                _ => out.push_str(val),
            },
            P::App(f, _, args) if f == "inj" && args.len() == 1 => self.term(&args[0], d, out),
            P::And(_, ps) if !ps.is_empty() => {
                // `X #as P`: the conjunct that is not a variable says more
                let pick = ps
                    .iter()
                    .find(|q| !matches!(q, P::Var(..)))
                    .unwrap_or(&ps[0]);
                self.term(pick, d, out)
            }
            // `a ~> .K` is written `a`
            P::App(f, _, args)
                if f == "kseq"
                    && args.len() == 2
                    && matches!(&args[1], P::App(g, _, _) if g == "dotk") =>
            {
                self.term(&args[0], d, out)
            }
            // a list element followed by the empty list (`X, .Exps`) is written as the element
            P::App(_, _, args) if args.len() == 2 && self.is_empty_list(&args[1]) => {
                self.term(&args[0], d, out)
            }
            P::App(f, _, args) => {
                if d >= self.depth && !args.is_empty() {
                    out.push('…');
                    return;
                }
                let t = match f.as_str() {
                    "kseq" => "_~>_".to_string(),
                    "dotk" => ".K".to_string(),
                    _ => template(f, self.def),
                };
                let t = match t.as_str() {
                    // collection concatenation is juxtaposition in K
                    "_Map_" | "_Set_" | "_List_" => "_ _".to_string(),
                    _ => t,
                };
                let chunks: Vec<&str> = t.split('_').collect();
                if chunks.len() == args.len() + 1 {
                    for (i, c) in chunks.iter().enumerate() {
                        if i > 0 {
                            let a = &args[i - 1];
                            let prev = chunks[i - 1];
                            // two arguments side by side (`S1 S2`), or a terminal before an argument
                            if (i > 1 && prev.is_empty())
                                || (!prev.is_empty()
                                    && !prev.ends_with(['(', '[', '{'])
                                    && !prev.ends_with(' '))
                            {
                                out.push(' ');
                            }
                            self.term(a, d + 1, out);
                            if !c.is_empty()
                                && !c.starts_with([')', ']', '}', ',', ';', '(', '[', ' '])
                            {
                                out.push(' ');
                            }
                        }
                        out.push_str(c);
                    }
                } else if args.is_empty() {
                    out.push_str(&t);
                } else {
                    out.push_str(&t);
                    out.push('(');
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        self.term(a, d + 1, out);
                    }
                    out.push(')');
                }
            }
            _ => out.push('…'),
        }
    }
}

/// The focus written in concrete syntax, at most `MAX_LEN` characters when deeper subterms can be
/// elided; `sorts` adds each variable's sort.
pub fn render_focus(lhs: &P, def: &Def, sorts: bool) -> String {
    let f = focus(lhs);
    let one = |depth: usize| {
        let mut s = String::new();
        let r = Render { def, sorts, depth };
        r.term(f, 0, &mut s);
        // a variable at the root of the focus: its sort says what the rule is about
        let mut root = f;
        while let P::App(g, _, a) = root {
            if g != "inj" || a.len() != 1 {
                break;
            }
            root = &a[0];
        }
        if !sorts
            && let P::Var(_, srt) = root
            && s != "..."
        {
            s.push(':');
            s.push_str(names::short_sort(srt.name().unwrap_or("?")));
        }
        s
    };
    let mut s = one(usize::MAX);
    let mut depth = 4;
    while s.chars().count() > MAX_LEN && depth > 0 {
        s = one(depth);
        depth -= 1;
    }
    sanitize(&s)
}

/// A string usable inside Lean's `«…»`.
fn sanitize(s: &str) -> String {
    let mut o = String::new();
    for c in s.chars() {
        match c {
            '«' => o.push_str("<<"),
            '»' => o.push_str(">>"),
            '\n' => o.push_str("\\n"),
            c if c.is_control() => {
                let _ = write!(o, "\\x{:02x}", c as u32);
            }
            c => o.push(c),
        }
    }
    o
}

/// A digest of a rewrite axiom's pattern with variables renamed by first occurrence (FNV-1a, 64
/// bits; its first six hex digits disambiguate names).
pub fn content_digest(p: &P) -> String {
    fn ser(p: &P, vars: &mut BTreeMap<String, usize>, o: &mut String) {
        let sort = |s: &S, o: &mut String| {
            let _ = write!(o, "{s}");
        };
        match p {
            P::Var(v, s) | P::SetVar(v, s) => {
                let n = vars.len();
                let i = *vars.entry(v.clone()).or_insert(n);
                let _ = write!(o, "v{i}:");
                sort(s, o);
            }
            P::Str(s) => {
                let _ = write!(o, "{s:?}");
            }
            P::Dv(s, v) => {
                o.push_str("dv(");
                sort(s, o);
                let _ = write!(o, ",{v:?})");
            }
            P::App(f, ps, args) => {
                o.push_str(f);
                o.push('{');
                for s in ps {
                    sort(s, o);
                    o.push(',');
                }
                o.push_str("}(");
                for a in args {
                    ser(a, vars, o);
                    o.push(',');
                }
                o.push(')');
            }
            P::Top(s) => {
                o.push_str("top:");
                sort(s, o)
            }
            P::Bottom(s) => {
                o.push_str("bot:");
                sort(s, o)
            }
            P::And(_, ps) | P::Or(_, ps) => {
                o.push_str(if matches!(p, P::And(..)) {
                    "and("
                } else {
                    "or("
                });
                for a in ps {
                    ser(a, vars, o);
                    o.push(',');
                }
                o.push(')');
            }
            P::Not(_, a) | P::Ceil(_, _, a) | P::Floor(_, _, a) => {
                o.push_str(match p {
                    P::Not(..) => "not(",
                    P::Ceil(..) => "ceil(",
                    _ => "floor(",
                });
                ser(a, vars, o);
                o.push(')');
            }
            P::Implies(_, a, b)
            | P::Iff(_, a, b)
            | P::Rewrites(_, a, b)
            | P::Equals(_, _, a, b)
            | P::In(_, _, a, b) => {
                o.push_str(match p {
                    P::Implies(..) => "imp(",
                    P::Iff(..) => "iff(",
                    P::Rewrites(..) => "rw(",
                    P::Equals(..) => "eq(",
                    _ => "in(",
                });
                ser(a, vars, o);
                o.push(',');
                ser(b, vars, o);
                o.push(')');
            }
            P::Exists(_, v, s, b) | P::Forall(_, v, s, b) => {
                let n = vars.len();
                vars.entry(v.clone()).or_insert(n);
                o.push_str(if matches!(p, P::Exists(..)) {
                    "ex("
                } else {
                    "all("
                });
                sort(s, o);
                ser(b, vars, o);
                o.push(')');
            }
            P::Other(s) => o.push_str(s),
        }
    }
    let mut text = String::new();
    ser(p, &mut BTreeMap::new(), &mut text);
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in text.bytes() {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    format!("{h:016x}")
}

/// The names of the rewrite axioms of a definition, by axiom index (`AxiomDecl::index`): the
/// label, else the content name (module documentation).
pub fn assign(def: &Def) -> BTreeMap<usize, String> {
    struct Item {
        index: usize,
        plain: String,
        sorted: String,
        digest: String,
    }
    let mut out = BTreeMap::new();
    let mut items = Vec::new();
    for a in &def.axioms {
        let Some(lhs) = lhs_of(&a.pattern) else {
            continue;
        };
        if let Some(l) = a.attrs.string("label") {
            out.insert(a.index, l);
            continue;
        }
        items.push(Item {
            index: a.index,
            plain: render_focus(lhs, def, false),
            sorted: render_focus(lhs, def, true),
            digest: content_digest(&a.pattern),
        });
    }
    let labels: std::collections::BTreeSet<String> = out.values().cloned().collect();
    let taken = |n: &str| labels.contains(n) || RESERVED.contains(&n);
    let mut by_plain: BTreeMap<&str, usize> = BTreeMap::new();
    for it in &items {
        *by_plain.entry(it.plain.as_str()).or_default() += 1;
    }
    let mut by_sorted: BTreeMap<&str, usize> = BTreeMap::new();
    for it in items
        .iter()
        .filter(|it| by_plain[it.plain.as_str()] > 1 || taken(&it.plain))
    {
        *by_sorted.entry(it.sorted.as_str()).or_default() += 1;
    }
    for it in &items {
        let name = if by_plain[it.plain.as_str()] == 1 && !taken(&it.plain) {
            it.plain.clone()
        } else if by_sorted[it.sorted.as_str()] == 1 && !taken(&it.sorted) {
            it.sorted.clone()
        } else {
            format!("{} #{}", it.sorted, &it.digest[..6])
        };
        out.insert(it.index, name);
    }
    out
}

#[cfg(test)]
pub(crate) mod tests {
    //! Content names: the focus in concrete syntax, the disambiguation levels, and independence
    //! from the source position.
    use super::*;
    use crate::funcs::tests::fixture;

    fn names_of(def: &Def) -> Vec<String> {
        assign(def).into_values().collect()
    }

    #[test]
    fn variables_are_written_by_source_name() {
        assert_eq!(var_name("VarX"), "X");
        assert_eq!(var_name("Var'Unds'Gen3"), "_");
        assert_eq!(var_name("Var'Unds'DotVar1"), "...");
        assert_eq!(var_name("Var'Unds'"), "_");
    }

    #[test]
    fn digest_ignores_variable_names_but_not_structure() {
        let s = S::App("SortInt".into(), vec![]);
        let a = P::App(
            "f".into(),
            vec![],
            vec![
                P::Var("VarX".into(), s.clone()),
                P::Var("VarY".into(), s.clone()),
            ],
        );
        let b = P::App(
            "f".into(),
            vec![],
            vec![
                P::Var("VarA".into(), s.clone()),
                P::Var("VarB".into(), s.clone()),
            ],
        );
        let c = P::App(
            "f".into(),
            vec![],
            vec![P::Var("VarA".into(), s.clone()), P::Var("VarA".into(), s)],
        );
        assert_eq!(content_digest(&a), content_digest(&b));
        assert_ne!(content_digest(&a), content_digest(&c));
    }

    #[test]
    fn peano_names() {
        let def = fixture("peano");
        assert_eq!(
            names_of(&def),
            vec!["start".to_string(), "done(s(s(N)))".to_string()]
        );
    }

    /// Moving every rule (the `Location` attributes rewritten) changes no name.
    #[test]
    fn names_do_not_depend_on_positions() {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/counter/definition.kore");
        let text = std::fs::read_to_string(p).unwrap();
        let moved: String = text
            .split("Location(")
            .enumerate()
            .map(|(i, part)| {
                if i == 0 {
                    part.to_string()
                } else {
                    format!("Location(1{part}")
                }
            })
            .collect();
        assert_ne!(moved, text);
        let a = assign(&crate::ir::load(&text).unwrap());
        let b = assign(&crate::ir::load(&moved).unwrap());
        assert_eq!(
            a.into_values().collect::<Vec<_>>(),
            b.into_values().collect::<Vec<_>>()
        );
    }
}
