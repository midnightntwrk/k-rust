//! `k2lean relate`: relate two generated libraries of K definitions.
//!
//! Given the compiled KORE of two definitions `A` and `B` (each already generated into a Lean
//! library with `k2lean gen`), this proposes a correspondence and states and proves, as far as
//! the generic tactics go, that the two `Step` relations are bisimilar:
//!
//! 1. **Symbols.** Every constructor of `A` gets a constructor of `B`: the same KORE symbol;
//!    else the same result and argument sorts and the same concrete syntax (the `format`
//!    attribute of the `syntaxDefinition.kore` files); a strictness freezer follows the symbol it
//!    freezes. The result is a translation `tr : A → B` on every sort of `A`'s term universe.
//! 2. **Rules.** A rule of `A` corresponds to the rule of `B` whose KORE axiom is the same after
//!    renaming symbols by (1) and variables by first occurrence.
//! 3. **Statements.** `forward : Inv c → A.Step c c' → B.Step (tr c) (tr c')` and
//!    `backward : Inv c → B.Step (tr c) d → ∃ c', A.Step c c' ∧ d = tr c'`, packaged as a
//!    strong bisimulation. `Inv` says that the keys of every map cell are injections of the
//!    leaf sorts used as keys by `A`'s rules; it is what makes the pointwise translation of a
//!    canonical (sorted) map canonical again (the two libraries order constructors differently).
//! 4. **Proofs.** One case per rule, by generic tactics (`k2l_inv`, the `k2l_rel` simp set).
//!
//! `--roots S,...` restricts the translation to the sorts reachable from `S` and skips (2)–(4)
//! (a translation of programs only, for example into a type checker's library).

use crate::ir::{self, Def, P, S};
use crate::lower::FnSig;
use crate::model::{Coll, Kind, Model};
use crate::names;
use crate::rules::{self, Rule};
use crate::terms;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

struct Side {
    def: Def,
    syn: Option<Def>,
    m: Model,
    fns: BTreeMap<String, FnSig>,
    unfold: Vec<String>,
    rules: Vec<Rule>,
    ns: String,
}

fn load_side(kore: &str, syn: Option<&str>, ns: &str, want_rules: bool) -> Side {
    let def = ir::load(&std::fs::read_to_string(kore).unwrap()).unwrap();
    let syn = syn.map(|p| ir::load(&std::fs::read_to_string(p).unwrap()).unwrap());
    let m = Model::build(&def).unwrap_or_else(|e| panic!("{e}"));
    let mut roots = BTreeSet::new();
    for ax in &def.axioms {
        if let P::Rewrites(_, l, _) = &ax.pattern
            && rules::absent_sort(l, &m).is_none()
        {
            crate::funcs::applied(&ax.pattern, &def, &mut roots);
        }
    }
    roots.extend(m.anywhere.iter().cloned());
    let fgen =
        crate::funcs::generate(&def, &m, &roots).unwrap_or_else(|e| panic!("functions: {e}"));
    let rules = if want_rules {
        if rules::priorities(&def).len() > 1 {
            panic!("relate: definitions with several rule priorities are not supported yet");
        }
        let rs = rules::collect(&def, &m, &fgen.fns, &[]).unwrap_or_else(|e| panic!("{e}"));
        if rs.iter().any(|r| r.multi) {
            panic!("relate: free-key map patterns are not supported yet");
        }
        rs
    } else {
        vec![]
    };
    Side {
        def,
        syn,
        m,
        fns: fgen.fns,
        unfold: fgen.unfold,
        rules,
        ns: ns.to_string(),
    }
}

/// The key of a constructor for matching by concrete syntax.
fn syntax_key(side: &Side, sym: &str) -> Option<String> {
    let syn = side.syn.as_ref()?;
    let d = syn.symbols.get(sym)?;
    let fmt = d.attrs.string("format")?;
    let args: Vec<String> = d.args.iter().map(|s| s.to_string()).collect();
    Some(format!(
        "{}|{}|{}",
        d.result,
        args.join(","),
        syntax_sig(&fmt)
    ))
}

/// The terminals and argument positions of a `format` attribute, without layout and colors:
/// `%c` … `%r` brackets a terminal, `%N` is argument `N`, `%%` a literal `%`; other directives
/// (`%i`, `%d`, `%n`, spaces) are layout.
fn syntax_sig(fmt: &str) -> String {
    let cs: Vec<char> = fmt.chars().collect();
    let mut out: Vec<String> = Vec::new();
    let mut i = 0;
    let mut term: Option<String> = None;
    while i < cs.len() {
        let c = cs[i];
        if c == '%' && i + 1 < cs.len() {
            let d = cs[i + 1];
            if d == 'c' {
                term = Some(String::new());
                i += 2;
                continue;
            }
            if d == 'r' {
                if let Some(t) = term.take() {
                    out.push(format!("'{t}'"));
                }
                i += 2;
                continue;
            }
            if d == '%' {
                if let Some(t) = term.as_mut() {
                    t.push('%');
                }
                i += 2;
                continue;
            }
            if d.is_ascii_digit() {
                let mut j = i + 1;
                let mut n = String::new();
                while j < cs.len() && cs[j].is_ascii_digit() {
                    n.push(cs[j]);
                    j += 1;
                }
                out.push(n);
                i = j;
                continue;
            }
            i += 2;
            continue;
        }
        if let Some(t) = term.as_mut() {
            t.push(c);
        } else if !c.is_whitespace() {
            out.push(format!("'{c}'"));
        }
        i += 1;
    }
    out.join(" ")
}

/// `#freezer<label><n>_` → (label, n).
fn freezer_parts(label: &str) -> Option<(String, String)> {
    let body = label.strip_prefix("#freezer")?.strip_suffix('_')?;
    let digits: String = body
        .chars()
        .rev()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    if digits.is_empty() {
        return None;
    }
    let n: String = digits.chars().rev().collect();
    Some((body[..body.len() - n.len()].to_string(), n))
}

struct SymMap {
    /// A constructor symbol → (B symbol, how it was matched).
    map: BTreeMap<String, (String, &'static str)>,
    unmatched_a: Vec<String>,
    unmatched_b: Vec<String>,
}

fn match_symbols(a: &Side, b: &Side) -> SymMap {
    let mut map = BTreeMap::new();
    let mut by_syntax: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for s in b.m.ctors.keys() {
        if let Some(k) = syntax_key(b, s) {
            by_syntax.entry(k).or_default().push(s.clone());
        }
    }
    let b_by_label: BTreeMap<String, String> =
        b.m.ctors
            .keys()
            .map(|s| (names::demangle(s), s.clone()))
            .collect();
    let a_by_label: BTreeMap<String, String> =
        a.m.ctors
            .keys()
            .map(|s| (names::demangle(s), s.clone()))
            .collect();
    // symbols of A that are not constructors in A's model (functions) but whose label is a
    // freezer base: look up their declarations
    let label_of_any = |side: &Side, label: &str| -> Option<String> {
        side.def
            .symbols
            .keys()
            .find(|s| names::demangle(s) == label)
            .cloned()
    };
    let mut pending_freezers = Vec::new();
    for s in a.m.ctors.keys() {
        if b.m.ctors.contains_key(s) {
            map.insert(s.clone(), (s.clone(), "same symbol"));
            continue;
        }
        let label = names::demangle(s);
        if freezer_parts(&label).is_some() {
            pending_freezers.push(s.clone());
            continue;
        }
        if let Some(k) = syntax_key(a, s)
            && let Some(v) = by_syntax.get(&k)
            && v.len() == 1
        {
            map.insert(s.clone(), (v[0].clone(), "same syntax"));
        }
    }
    // base symbols of freezers may be constructors (`_+_`) matched above
    let mut base_map: BTreeMap<String, String> = BTreeMap::new();
    for (sa, (sb, _)) in &map {
        base_map.insert(names::demangle(sa), names::demangle(sb));
    }
    for s in pending_freezers {
        let label = names::demangle(&s);
        let (base, n) = freezer_parts(&label).unwrap();
        let base_b = base_map.get(&base).cloned().or_else(|| {
            // a base that is not a constructor of A's model: match by syntax on the declarations
            let sa = label_of_any(a, &base)?;
            let k = syntax_key(a, &sa)?;
            let sb = b
                .syn
                .as_ref()?
                .symbols
                .keys()
                .find(|x| syntax_key(b, x).as_deref() == Some(k.as_str()))?
                .clone();
            Some(names::demangle(&sb))
        });
        if let Some(bb) = base_b
            && let Some(sb) = b_by_label.get(&format!("#freezer{bb}{n}_"))
        {
            map.insert(s.clone(), (sb.clone(), "freezer of a matched symbol"));
        }
    }
    let _ = a_by_label;
    let unmatched_a: Vec<String> =
        a.m.ctors
            .keys()
            .filter(|s| !map.contains_key(*s))
            .cloned()
            .collect();
    let used_b: BTreeSet<&String> = map.values().map(|(b, _)| b).collect();
    let unmatched_b: Vec<String> =
        b.m.ctors
            .keys()
            .filter(|s| !used_b.contains(s))
            .cloned()
            .collect();
    SymMap {
        map,
        unmatched_a,
        unmatched_b,
    }
}

/// A canonical text of a pattern: symbols renamed by `ren`, variables by first occurrence.
fn canon(
    p: &P,
    ren: &BTreeMap<String, String>,
    vars: &mut BTreeMap<String, usize>,
    out: &mut String,
) {
    let sort = |s: &S| s.to_string();
    match p {
        P::Str(s) => write!(out, "{s:?}").unwrap(),
        P::Var(v, s) | P::SetVar(v, s) => {
            let n = vars.len();
            let i = *vars.entry(v.clone()).or_insert(n);
            write!(out, "${i}:{}", sort(s)).unwrap();
        }
        P::App(f, ps, args) => {
            let f2 = ren.get(f).cloned().unwrap_or_else(|| f.clone());
            write!(
                out,
                "{f2}{{{}}}(",
                ps.iter().map(sort).collect::<Vec<_>>().join(",")
            )
            .unwrap();
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                canon(a, ren, vars, out);
            }
            out.push(')');
        }
        P::Dv(s, v) => write!(out, "\\dv{{{}}}({v:?})", sort(s)).unwrap(),
        P::Top(s) => write!(out, "\\top{{{}}}", sort(s)).unwrap(),
        P::Bottom(s) => write!(out, "\\bottom{{{}}}", sort(s)).unwrap(),
        P::And(s, ps) | P::Or(s, ps) => {
            out.push_str(if matches!(p, P::And(..)) {
                "\\and"
            } else {
                "\\or"
            });
            write!(out, "{{{}}}(", sort(s)).unwrap();
            for (i, a) in ps.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                canon(a, ren, vars, out);
            }
            out.push(')');
        }
        P::Not(_, a) => {
            out.push_str("\\not(");
            canon(a, ren, vars, out);
            out.push(')');
        }
        P::Implies(_, a, b) | P::Iff(_, a, b) | P::Rewrites(_, a, b) => {
            out.push_str(match p {
                P::Implies(..) => "\\implies(",
                P::Iff(..) => "\\iff(",
                _ => "\\rewrites(",
            });
            canon(a, ren, vars, out);
            out.push(',');
            canon(b, ren, vars, out);
            out.push(')');
        }
        P::Exists(_, v, s, b) | P::Forall(_, v, s, b) => {
            let n = vars.len();
            vars.insert(v.clone(), n);
            write!(out, "\\q(${n}:{},", sort(s)).unwrap();
            canon(b, ren, vars, out);
            out.push(')');
        }
        P::Ceil(_, _, a) | P::Floor(_, _, a) => {
            out.push_str("\\ceil(");
            canon(a, ren, vars, out);
            out.push(')');
        }
        P::Equals(_, _, a, b) | P::In(_, _, a, b) => {
            out.push_str(if matches!(p, P::Equals(..)) {
                "\\equals("
            } else {
                "\\in("
            });
            canon(a, ren, vars, out);
            out.push(',');
            canon(b, ren, vars, out);
            out.push(')');
        }
        P::Other(o) => out.push_str(o),
    }
}

/// Match `A`'s pattern against `B`'s, symbols renamed by `ren`, variables consistently; a
/// variable `x:S` of `A` may match `inj{T,S}(y:T)` of `B` (B's rule is the instance of A's at a
/// subsort: a *refinement*, recorded in `refs` as (x, T)).
fn pmatch(
    pa: &P,
    pb: &P,
    ren: &BTreeMap<String, String>,
    vm: &mut BTreeMap<String, (String, Option<S>)>,
    refs: &mut BTreeSet<(String, S)>,
) -> bool {
    match (pa, pb) {
        (P::Var(x, s), P::Var(y, t)) | (P::SetVar(x, s), P::SetVar(y, t)) => {
            if s != t {
                return false;
            }
            match vm.get(x) {
                Some((y0, None)) => y0 == y,
                Some(_) => false,
                None => {
                    vm.insert(x.clone(), (y.clone(), None));
                    true
                }
            }
        }
        (P::Var(x, s), P::App(i, ps, args))
            if i == "inj" && ps.len() == 2 && &ps[1] == s && args.len() == 1 =>
        {
            let P::Var(y, t) = &args[0] else { return false };
            if t != &ps[0] {
                return false;
            }
            match vm.get(x) {
                Some((y0, Some(t0))) => y0 == y && t0 == t,
                Some(_) => false,
                None => {
                    vm.insert(x.clone(), (y.clone(), Some(t.clone())));
                    refs.insert((x.clone(), t.clone()));
                    true
                }
            }
        }
        (P::App(f, ps, xs), P::App(g, qs, ys)) => {
            let f2 = ren.get(f).unwrap_or(f);
            f2 == g
                && ps == qs
                && xs.len() == ys.len()
                && xs.iter().zip(ys).all(|(x, y)| pmatch(x, y, ren, vm, refs))
        }
        (P::And(s, xs), P::And(t, ys)) | (P::Or(s, xs), P::Or(t, ys)) => {
            s == t
                && xs.len() == ys.len()
                && xs.iter().zip(ys).all(|(x, y)| pmatch(x, y, ren, vm, refs))
        }
        (P::Rewrites(_, a1, b1), P::Rewrites(_, a2, b2))
        | (P::Implies(_, a1, b1), P::Implies(_, a2, b2))
        | (P::Iff(_, a1, b1), P::Iff(_, a2, b2))
        | (P::Equals(_, _, a1, b1), P::Equals(_, _, a2, b2))
        | (P::In(_, _, a1, b1), P::In(_, _, a2, b2)) => {
            pmatch(a1, a2, ren, vm, refs) && pmatch(b1, b2, ren, vm, refs)
        }
        (P::Not(_, a1), P::Not(_, a2))
        | (P::Ceil(_, _, a1), P::Ceil(_, _, a2))
        | (P::Floor(_, _, a1), P::Floor(_, _, a2)) => pmatch(a1, a2, ren, vm, refs),
        (P::Exists(_, x, s, a1), P::Exists(_, y, t, a2))
        | (P::Forall(_, x, s, a1), P::Forall(_, y, t, a2)) => {
            s == t && {
                vm.insert(x.clone(), (y.clone(), None));
                pmatch(a1, a2, ren, vm, refs)
            }
        }
        (P::Dv(s, v), P::Dv(t, w)) => s == t && v == w,
        (P::Top(s), P::Top(t)) | (P::Bottom(s), P::Bottom(t)) => s == t,
        (P::Str(x), P::Str(y)) => x == y,
        _ => false,
    }
}

fn rule_keys(side: &Side, ren: &BTreeMap<String, String>) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for a in &side.def.axioms {
        if !matches!(a.pattern, P::Rewrites(..)) {
            continue;
        }
        let uid = a.attrs.string("UNIQUE'Unds'ID").unwrap_or_default();
        let mut s = String::new();
        canon(&a.pattern, ren, &mut BTreeMap::new(), &mut s);
        out.insert(uid, s);
    }
    out
}

/// The Lean types of a model's term universe that `tr` covers, with their constructors:
/// (type, [(A Lean constructor, KORE symbol or leaf, argument sorts / own types)]).
#[derive(Clone)]
enum TyKind {
    /// own constructors of a sort (or `.Own` type): (symbol, Lean name, argument sorts)
    Own(Vec<(String, String, Vec<String>)>),
    /// a sum over leaves: (leaf sort, own type of the leaf)
    Sum(Vec<(String, String)>),
    /// a collection carrier: element sorts
    Coll(Coll, Vec<String>),
}

fn universe(m: &Model) -> Vec<(String, String, TyKind)> {
    // (Lean type, sort, kind)
    let mut out = Vec::new();
    for s in &m.block {
        let info = m.sort(s);
        match &info.kind {
            Kind::Coll(c) => out.push((
                s.clone(),
                s.clone(),
                TyKind::Coll(c.clone(), info.elems.clone()),
            )),
            Kind::Plain => {
                let own: Vec<(String, String, Vec<String>)> = info
                    .own
                    .iter()
                    .map(|c| (c.clone(), m.ctors[c].lean.clone(), m.ctors[c].args.clone()))
                    .collect();
                if info.is_simple() {
                    out.push((s.clone(), s.clone(), TyKind::Own(own)));
                } else {
                    let leaves = info
                        .leaves
                        .iter()
                        .map(|l| (l.clone(), m.own_ty(l)))
                        .collect();
                    out.push((s.clone(), s.clone(), TyKind::Sum(leaves)));
                    if !own.is_empty() {
                        out.push((format!("{s}.Own"), s.clone(), TyKind::Own(own)));
                    }
                }
            }
            _ => {}
        }
    }
    out
}

fn reach(m: &Model, roots: &[String]) -> BTreeSet<String> {
    // Lean types reachable from the root sorts
    let uni = universe(m);
    let by_ty: BTreeMap<String, TyKind> =
        uni.iter().map(|(t, _, k)| (t.clone(), k.clone())).collect();
    let mut seen = BTreeSet::new();
    let mut todo: Vec<String> = roots.to_vec();
    while let Some(t) = todo.pop() {
        if !seen.insert(t.clone()) {
            continue;
        }
        let Some(k) = by_ty.get(&t) else { continue };
        match k {
            TyKind::Own(cs) => {
                for (_, _, args) in cs {
                    todo.extend(args.iter().cloned());
                }
            }
            TyKind::Sum(ls) => {
                for (_, o) in ls {
                    todo.push(o.clone());
                }
            }
            TyKind::Coll(_, es) => {
                todo.extend(es.iter().cloned());
            }
        }
    }
    seen
}

pub fn main(args: &[String]) {
    let mut opt: BTreeMap<String, String> = BTreeMap::new();
    let mut it = args.iter();
    while let Some(k) = it.next() {
        let v = it.next().unwrap_or_else(|| panic!("{k} needs a value"));
        opt.insert(k.trim_start_matches("--").to_string(), v.clone());
    }
    let get = |k: &str| {
        opt.get(k)
            .cloned()
            .unwrap_or_else(|| panic!("relate: --{k} is required"))
    };
    let roots: Option<Vec<String>> = opt
        .get("roots")
        .map(|r| r.split(',').map(|s| s.to_string()).collect());
    let full = roots.is_none();
    let a = load_side(
        &get("kore-a"),
        opt.get("syntax-a").map(|s| s.as_str()),
        &get("name-a"),
        full,
    );
    let b = load_side(
        &get("kore-b"),
        opt.get("syntax-b").map(|s| s.as_str()),
        &get("name-b"),
        full,
    );
    let ns = get("ns");
    let sm = match_symbols(&a, &b);
    let ren: BTreeMap<String, String> = sm
        .map
        .iter()
        .map(|(x, (y, _))| (x.clone(), y.clone()))
        .collect();
    let covered: BTreeSet<String> = match &roots {
        Some(r) => reach(&a.m, r),
        None => universe(&a.m).into_iter().map(|(t, _, _)| t).collect(),
    };
    // report
    let mut rep = String::new();
    writeln!(
        rep,
        "# k2lean relate: correspondence between {} and {}\n",
        a.ns, b.ns
    )
    .unwrap();
    writeln!(rep, "[symbols]").unwrap();
    for (x, (y, how)) in &sm.map {
        writeln!(
            rep,
            "{:?} = {{ b = {:?}, how = {:?} }}",
            names::demangle(x),
            names::demangle(y),
            how
        )
        .unwrap();
    }
    writeln!(rep, "\n[unmatched]").unwrap();
    writeln!(
        rep,
        "a = {:?}",
        sm.unmatched_a
            .iter()
            .map(|s| names::demangle(s))
            .collect::<Vec<_>>()
    )
    .unwrap();
    writeln!(
        rep,
        "b = {:?}",
        sm.unmatched_b
            .iter()
            .map(|s| names::demangle(s))
            .collect::<Vec<_>>()
    )
    .unwrap();
    // A constructors the translation needs but B lacks
    let needed: Vec<String> = universe(&a.m)
        .into_iter()
        .filter(|(t, _, _)| covered.contains(t))
        .flat_map(|(_, _, k)| match k {
            TyKind::Own(cs) => cs.into_iter().map(|(s, _, _)| s).collect(),
            _ => vec![],
        })
        .filter(|s| !sm.map.contains_key(s))
        .collect();
    if !needed.is_empty() {
        eprintln!("{rep}");
        panic!(
            "relate: constructors of {} without a counterpart in {}: {:?}",
            a.ns,
            b.ns,
            needed
                .iter()
                .map(|s| names::demangle(s))
                .collect::<Vec<_>>()
        );
    }
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    let mut unmatched_rules_a = Vec::new();
    let mut unmatched_rules_b: Vec<usize> = Vec::new();
    // A rule index → the sorts its variables are refined to in B's rule
    let mut refined: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    if full {
        let ka = rule_keys(&a, &ren);
        let kb = rule_keys(&b, &BTreeMap::new());
        let mut b_by_key: BTreeMap<&String, Vec<&String>> = BTreeMap::new();
        for (u, k) in &kb {
            b_by_key.entry(k).or_default().push(u);
        }
        let ia: BTreeMap<&str, usize> = a
            .rules
            .iter()
            .enumerate()
            .map(|(i, r)| (r.uid.as_str(), i))
            .collect();
        let ib: BTreeMap<&str, usize> = b
            .rules
            .iter()
            .enumerate()
            .map(|(i, r)| (r.uid.as_str(), i))
            .collect();
        let mut used_b = BTreeSet::new();
        for (u, k) in &ka {
            let Some(&i) = ia.get(u.as_str()) else {
                continue;
            };
            match b_by_key.get(k).map(|v| v.as_slice()) {
                Some([ub]) => {
                    let j = ib[ub.as_str()];
                    pairs.push((i, j));
                    used_b.insert(j);
                }
                _ => unmatched_rules_a.push(i),
            }
        }
        // the rest: B's rule an instance of A's at subsorts of some variables
        let ax_a: BTreeMap<String, &P> = a
            .def
            .axioms
            .iter()
            .filter(|x| matches!(x.pattern, P::Rewrites(..)))
            .map(|x| {
                (
                    x.attrs.string("UNIQUE'Unds'ID").unwrap_or_default(),
                    &x.pattern,
                )
            })
            .collect();
        let ax_b: BTreeMap<String, &P> = b
            .def
            .axioms
            .iter()
            .filter(|x| matches!(x.pattern, P::Rewrites(..)))
            .map(|x| {
                (
                    x.attrs.string("UNIQUE'Unds'ID").unwrap_or_default(),
                    &x.pattern,
                )
            })
            .collect();
        let mut still = Vec::new();
        for i in std::mem::take(&mut unmatched_rules_a) {
            let pa = ax_a[&a.rules[i].uid];
            let cands: Vec<(usize, BTreeSet<(String, S)>)> = (0..b.rules.len())
                .filter(|j| !used_b.contains(j))
                .filter_map(|j| {
                    let mut vm = BTreeMap::new();
                    let mut refs = BTreeSet::new();
                    pmatch(pa, ax_b[&b.rules[j].uid], &ren, &mut vm, &mut refs).then_some((j, refs))
                })
                .collect();
            if let [(j, refs)] = cands.as_slice() {
                pairs.push((i, *j));
                used_b.insert(*j);
                refined.insert(
                    i,
                    refs.iter()
                        .map(|(_, t)| t.name().unwrap_or("?").to_string())
                        .collect(),
                );
            } else {
                still.push(i);
            }
        }
        unmatched_rules_a = still;
        for j in 0..b.rules.len() {
            if !used_b.contains(&j) {
                unmatched_rules_b.push(j);
            }
        }
        if std::env::var("K2L_DEBUG").is_ok() {
            for i in &unmatched_rules_a {
                eprintln!(
                    "A {}: {}",
                    rules::display_name(&a.rules[*i]),
                    ka[&a.rules[*i].uid]
                );
            }
            for j in &unmatched_rules_b {
                eprintln!(
                    "B {}: {}",
                    rules::display_name(&b.rules[*j]),
                    kb[&b.rules[*j].uid]
                );
            }
        }
        writeln!(rep, "\n[rules]").unwrap();
        for (i, j) in &pairs {
            match refined.get(i) {
                Some(ts) => writeln!(
                    rep,
                    "{:?} = {{ b = {:?}, refines-to = {:?} }}",
                    rules::display_name(&a.rules[*i]),
                    rules::display_name(&b.rules[*j]),
                    ts
                )
                .unwrap(),
                None => writeln!(
                    rep,
                    "{:?} = {:?}",
                    rules::display_name(&a.rules[*i]),
                    rules::display_name(&b.rules[*j])
                )
                .unwrap(),
            }
        }
        writeln!(rep, "\n[unmatched-rules]").unwrap();
        writeln!(
            rep,
            "a = {:?}",
            unmatched_rules_a
                .iter()
                .map(|i| rules::display_name(&a.rules[*i]))
                .collect::<Vec<_>>()
        )
        .unwrap();
        writeln!(
            rep,
            "b = {:?}",
            unmatched_rules_b
                .iter()
                .map(|j| rules::display_name(&b.rules[*j]))
                .collect::<Vec<_>>()
        )
        .unwrap();
        if !unmatched_rules_a.is_empty() {
            eprintln!(
                "note: {} rules of {} have no counterpart; the bisimulation is not stated",
                unmatched_rules_a.len(),
                a.ns
            );
        }
    }
    if let Some(r) = opt.get("report") {
        std::fs::write(r, &rep).unwrap();
    }
    let lean = emit(
        &a,
        &b,
        &ns,
        &sm,
        &covered,
        full && unmatched_rules_a.is_empty(),
        &pairs,
        &unmatched_rules_b,
        &refined,
    );
    std::fs::write(get("out"), lean).unwrap();
    eprintln!(
        "relate: {} symbols matched ({} unmatched in {}, {} in {}); {} rule pairs, {} + {} unmatched rules",
        sm.map.len(),
        sm.unmatched_a.len(),
        a.ns,
        sm.unmatched_b.len(),
        b.ns,
        pairs.len(),
        unmatched_rules_a.len(),
        unmatched_rules_b.len()
    );
}

fn tr_name(ty: &str) -> String {
    format!("tr_{}", terms::fsuffix(ty))
}

/// The translation of a value `x` of sort `s` (a sort name, or an own type).
fn val(m: &Model, s: &str, x: &str) -> String {
    match m.sorts.get(s).map(|i| &i.kind) {
        Some(Kind::Builtin(_)) => x.to_string(),
        Some(Kind::Token) => format!("({} {x})", tr_name(s)),
        _ => format!("({} {x})", tr_name(s)),
    }
}

fn is_builtin(m: &Model, s: &str) -> bool {
    matches!(m.sorts.get(s).map(|i| &i.kind), Some(Kind::Builtin(_)))
}

#[allow(clippy::too_many_arguments)]
fn emit(
    a: &Side,
    b: &Side,
    ns: &str,
    sm: &SymMap,
    covered: &BTreeSet<String>,
    bisim: bool,
    pairs: &[(usize, usize)],
    unmatched_b: &[usize],
    refined: &BTreeMap<usize, Vec<String>>,
) -> String {
    let (na, nb) = (&a.ns, &b.ns);
    let mut o = String::new();
    // only what the statements need: the relations (or, for a translation of programs, the functions)
    let m = if bisim { "Rules" } else { "Functions" };
    writeln!(
        o,
        "import {na}.{m}\nimport {nb}.{m}\nimport KPrelude.Relate\n"
    )
    .unwrap();
    writeln!(
        o,
        "/-! Generated by `k2lean relate`; do not edit.\n\n\
         The translation `tr` from `{na}` to `{nb}` (symbols matched by name, by concrete syntax, or as \
         freezers of matched symbols)"
    )
    .unwrap();
    if bisim {
        writeln!(o, "and the strong bisimulation between `{na}.Step` and `{nb}.Step` on the configurations where `Inv` holds. -/\n").unwrap();
    } else {
        writeln!(o, "on the sorts it covers. -/\n").unwrap();
    }
    writeln!(o, "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n").unwrap();
    writeln!(o, "namespace {ns}\n\nopen KPrelude\n").unwrap();
    // tokens
    let uni = universe(&a.m);
    let mut tokens = BTreeSet::new();
    for (t, _, k) in &uni {
        if !covered.contains(t) {
            continue;
        }
        let sorts: Vec<String> = match k {
            TyKind::Own(cs) => cs.iter().flat_map(|(_, _, args)| args.clone()).collect(),
            TyKind::Sum(ls) => ls.iter().map(|(_, o)| o.clone()).collect(),
            TyKind::Coll(_, es) => es.clone(),
        };
        for s in sorts {
            if matches!(a.m.sorts.get(&s).map(|i| &i.kind), Some(Kind::Token)) {
                tokens.insert(s);
            }
        }
    }
    writeln!(o, "/-! ## The translation -/\n").unwrap();
    for t in &tokens {
        writeln!(o, "def {} (x : {na}.{t}) : {nb}.{t} := ⟨x.val⟩", tr_name(t)).unwrap();
    }
    writeln!(o, "\nmutual").unwrap();
    for (t, _, k) in &uni {
        if !covered.contains(t) {
            continue;
        }
        writeln!(
            o,
            "def {} (a : {na}.{t}) : {nb}.{t} :=\n  match a with",
            tr_name(t)
        )
        .unwrap();
        match k {
            TyKind::Own(cs) => {
                for (sym, lean, args) in cs {
                    let bsym = &sm.map[sym].0;
                    let blean = &b.m.ctors[bsym].lean;
                    let xs: Vec<String> = (0..args.len()).map(|i| format!("a{i}")).collect();
                    let vs: Vec<String> =
                        args.iter().zip(&xs).map(|(s, x)| val(&a.m, s, x)).collect();
                    writeln!(
                        o,
                        "  | .{lean} {} => .{blean} {}",
                        xs.join(" "),
                        vs.join(" ")
                    )
                    .unwrap();
                }
            }
            TyKind::Sum(ls) => {
                for (l, own) in ls {
                    let short = names::short_sort(l);
                    writeln!(
                        o,
                        "  | .inj_{short} x => .inj_{short} {}",
                        val(&a.m, own, "x")
                    )
                    .unwrap();
                }
            }
            TyKind::Coll(c, es) => {
                writeln!(o, "  | .nil => .nil").unwrap();
                match c {
                    Coll::Map => writeln!(
                        o,
                        "  | .cons k v r => .cons {} {} ({} r)",
                        val(&a.m, &es[0], "k"),
                        val(&a.m, &es[1], "v"),
                        tr_name(t)
                    )
                    .unwrap(),
                    _ => writeln!(
                        o,
                        "  | .cons x r => .cons {} ({} r)",
                        val(&a.m, &es[0], "x"),
                        tr_name(t)
                    )
                    .unwrap(),
                }
            }
        }
        writeln!(o, "  termination_by structural a").unwrap();
    }
    writeln!(o, "end\n").unwrap();
    // fold lemmas
    writeln!(
        o,
        "/-! ## Folding: a constructor of `{nb}` applied to translations is a translation -/\n"
    )
    .unwrap();
    let mut fold_names: Vec<String> = Vec::new();
    for (t, _, k) in &uni {
        if !covered.contains(t) {
            continue;
        }
        let ctors: Vec<(String, String, Vec<String>)> = match k {
            TyKind::Own(cs) => cs
                .iter()
                .map(|(sym, lean, args)| {
                    (
                        lean.clone(),
                        b.m.ctors[&sm.map[sym].0].lean.clone(),
                        args.clone(),
                    )
                })
                .collect(),
            TyKind::Sum(ls) => ls
                .iter()
                .map(|(l, own)| {
                    let n = format!("inj_{}", names::short_sort(l));
                    (n.clone(), n, vec![own.clone()])
                })
                .collect(),
            TyKind::Coll(c, es) => {
                let mut v = vec![("nil".to_string(), "nil".to_string(), vec![])];
                match c {
                    Coll::Map => v.push((
                        "cons".into(),
                        "cons".into(),
                        vec![es[0].clone(), es[1].clone(), t.clone()],
                    )),
                    _ => v.push(("cons".into(), "cons".into(), vec![es[0].clone(), t.clone()])),
                }
                v
            }
        };
        for (i, (la, lb, args)) in ctors.iter().enumerate() {
            let xs: Vec<String> = (0..args.len()).map(|i| format!("x{i}")).collect();
            let binders: String = args
                .iter()
                .zip(&xs)
                .map(|(s, x)| format!(" ({x} : {na}.{s})"))
                .collect();
            let vs: Vec<String> = args.iter().zip(&xs).map(|(s, x)| val(&a.m, s, x)).collect();
            let lhs = if args.is_empty() {
                format!("{nb}.{t}.{lb}")
            } else {
                format!("{nb}.{t}.{lb} {}", vs.join(" "))
            };
            let rhs_arg = if args.is_empty() {
                format!("{na}.{t}.{la}")
            } else {
                format!("({na}.{t}.{la} {})", xs.join(" "))
            };
            writeln!(
                o,
                "@[k2l_rel] theorem fold_{}_{i}{binders} : {lhs} = {} {rhs_arg} := rfl",
                terms::fsuffix(t),
                tr_name(t)
            )
            .unwrap();
            fold_names.push(format!("fold_{}_{i}", terms::fsuffix(t)));
        }
    }
    // injections and projections
    let pairs_b: BTreeSet<(String, String)> = terms::inj_pairs(&b.m).into_iter().collect();
    writeln!(
        o,
        "\n/-! ## Injections and projections commute with the translation -/\n"
    )
    .unwrap();
    for (x, y) in terms::inj_pairs(&a.m) {
        if !pairs_b.contains(&(x.clone(), y.clone())) || !covered.contains(&y) {
            continue;
        }
        let (sx, sy) = (names::short_sort(&x), names::short_sort(&y));
        let tx = x.clone();
        if !is_builtin(&a.m, &x)
            && !covered.contains(&x)
            && !matches!(a.m.sorts[&x].kind, Kind::Token)
        {
            continue;
        }
        writeln!(
            o,
            "@[k2l_rel] theorem fold_inj_{sx}_{sy} (x : {na}.{tx}) : {nb}.inj_{sx}_{sy} {} = {} ({na}.inj_{sx}_{sy} x) := by\n  first | rfl | (cases x <;> rfl)",
            val(&a.m, &x, "x"),
            tr_name(&y)
        )
        .unwrap();
        let mapf = if is_builtin(&a.m, &x) {
            "(A := fun x => x)".to_string()
        } else {
            tr_name(&x).to_string()
        };
        let rhs = if is_builtin(&a.m, &x) {
            format!("{na}.proj_{sy}_{sx} y")
        } else {
            format!("({na}.proj_{sy}_{sx} y).map {mapf}")
        };
        writeln!(o, "@[k2l_rel] theorem comm_proj_{sy}_{sx} (y : {na}.{y}) : {nb}.proj_{sy}_{sx} ({} y) = {rhs} := by\n  cases y <;> rfl", tr_name(&y)).unwrap();
        writeln!(o, "attribute [k2l_rel] {na}.proj_inj_{sy}_{sx}").unwrap();
    }
    // functions defined by equations, used by the rules
    writeln!(
        o,
        "\n/-! ## Functions defined by equations commute with the translation -/\n"
    )
    .unwrap();
    let mut fn_count = 0;
    for (sym, sig) in &a.fns {
        let Some(sb) = b.fns.get(sym) else { continue };
        if crate::hooks::for_symbol(&a.def.symbols[sym]).is_some()
            || sb.lean != sig.lean
            || sb.args != sig.args
            || sb.result != sig.result
        {
            continue;
        }
        if sig
            .args
            .iter()
            .chain(std::iter::once(&sig.result))
            .any(|s| !is_builtin(&a.m, s) && !covered.contains(s))
        {
            continue;
        }
        let xs: Vec<String> = (0..sig.args.len()).map(|i| format!("x{i}")).collect();
        let binders: String = sig
            .args
            .iter()
            .zip(&xs)
            .map(|(s, x)| format!(" ({x} : {na}.{s})"))
            .collect();
        let vs: Vec<String> = sig
            .args
            .iter()
            .zip(&xs)
            .map(|(s, x)| val(&a.m, s, x))
            .collect();
        let call = format!("{na}.{} {}", sig.lean, xs.join(" "));
        let rhs = if sig.partial {
            if is_builtin(&a.m, &sig.result) {
                format!("({call})")
            } else {
                format!("({call}).map {}", tr_name(&sig.result))
            }
        } else {
            val(&a.m, &sig.result, &format!("({call})"))
        };
        let unf: Vec<String> = a
            .unfold
            .iter()
            .filter(|u| u.starts_with(&sig.lean))
            .flat_map(|u| [format!("{na}.{u}"), format!("{nb}.{u}")])
            .collect();
        writeln!(
            o,
            "@[k2l_rel] theorem comm_fn_{fn_count} {binders} : {nb}.{} {} = {rhs} := by\n  simp only [{}]\n  k2l_comm_fn",
            sb.lean,
            vs.join(" "),
            unf.join(", ")
        )
        .unwrap();
        fn_count += 1;
    }
    if !bisim {
        writeln!(o, "\nend {ns}").unwrap();
        return o;
    }
    // the invariant: keys of map cells
    let top = rules::top_sort(&a.def).unwrap();
    let mut key_leaves: BTreeSet<String> = BTreeSet::new();
    let map_syms: BTreeSet<String> = a
        .def
        .symbols
        .iter()
        .filter(|(_, d)| {
            matches!(
                d.hook().as_deref(),
                Some(
                    "MAP.element"
                        | "MAP.update"
                        | "MAP.lookup"
                        | "MAP.remove"
                        | "MAP.in_keys"
                        | "MAP.lookupOrDefault"
                )
            )
        })
        .map(|(n, _)| n.clone())
        .collect();
    fn keys(
        p: &P,
        map_syms: &BTreeSet<String>,
        def: &Def,
        out: &mut BTreeSet<String>,
        bad: &mut Vec<String>,
    ) {
        if let P::App(f, _, args) = p {
            if map_syms.contains(f) {
                let hook = def.symbols[f].hook().unwrap();
                let key = match hook.as_str() {
                    "MAP.in_keys" => args.first(),
                    "MAP.element" => args.first(),
                    _ => args.get(1),
                };
                match key {
                    Some(P::App(i, ps, _)) if i == "inj" => {
                        out.insert(ps[0].to_string().trim_end_matches("{}").to_string())
                    }
                    Some(other) => {
                        bad.push(format!("{other:?}"));
                        false
                    }
                    None => false,
                };
            }
            for x in args {
                keys(x, map_syms, def, out, bad);
            }
        } else if let P::And(_, ps) | P::Or(_, ps) = p {
            for x in ps {
                keys(x, map_syms, def, out, bad);
            }
        } else if let P::Rewrites(_, l, r) | P::Equals(_, _, l, r) | P::Implies(_, l, r) = p {
            keys(l, map_syms, def, out, bad);
            keys(r, map_syms, def, out, bad);
        } else if let P::Not(_, x) | P::Ceil(_, _, x) | P::Exists(_, _, _, x) = p {
            keys(x, map_syms, def, out, bad);
        }
    }
    let mut bad = Vec::new();
    for ax in &a.def.axioms {
        if matches!(ax.pattern, P::Rewrites(..)) {
            keys(&ax.pattern, &map_syms, &a.def, &mut key_leaves, &mut bad);
        }
    }
    let key_leaves: Vec<String> = key_leaves
        .into_iter()
        .map(|s| s.split('{').next().unwrap().to_string())
        .collect();
    if !bad.is_empty()
        || key_leaves.iter().any(|l| {
            !matches!(
                a.m.sorts.get(l).map(|i| &i.kind),
                Some(Kind::Builtin(_) | Kind::Token)
            )
        })
    {
        panic!(
            "relate: map keys that are not injections of builtin or token sorts: {bad:?} {key_leaves:?}"
        );
    }
    // map cells of the configuration (depth one)
    let top_ctor =
        a.m.sort(&top)
            .own
            .first()
            .cloned()
            .expect("top constructor");
    let top_args = a.m.ctors[&top_ctor].args.clone();
    let mut map_cells = Vec::new();
    for (i, cs) in top_args.iter().enumerate() {
        let info = a.m.sort(cs);
        if info.is_simple() && info.own.len() == 1 {
            let c = &a.m.ctors[&info.own[0]];
            for (j, s) in c.args.iter().enumerate() {
                if matches!(a.m.sort(s).kind, Kind::Coll(Coll::Map)) {
                    map_cells.push((i, cs.clone(), c.lean.clone(), c.args.len(), j, s.clone()));
                }
            }
        }
    }
    let map_sorts: BTreeSet<String> = map_cells.iter().map(|x| x.5.clone()).collect();
    if map_sorts
        .iter()
        .any(|s| a.m.elems(s) != ["SortKItem", "SortKItem"])
    {
        panic!("relate: typed cell maps are not supported yet");
    }
    writeln!(
        o,
        "\n/-! ## The invariant: map keys whose translation preserves the order -/\n"
    )
    .unwrap();
    writeln!(
        o,
        "/-- A key of a sort used as a map key by `{na}`'s rules ({}). -/",
        key_leaves
            .iter()
            .map(|l| names::short_sort(l))
            .collect::<Vec<_>>()
            .join(", ")
    )
    .unwrap();
    writeln!(o, "def keyOK : {na}.SortKItem → Bool").unwrap();
    for l in &key_leaves {
        writeln!(o, "  | .inj_{} _ => true", names::short_sort(l)).unwrap();
    }
    writeln!(o, "  | _ => false\n").unwrap();
    writeln!(
        o,
        "def KeysOK (m : {na}.SortMap) : Prop := MapHook.KeysOn (fun k => keyOK k = true) m\n"
    )
    .unwrap();
    writeln!(
        o,
        "theorem pres : SAL.PresOn (fun k => keyOK k = true) tr_SortKItem := by\n  intro a b ha hb\n  cases a <;> simp [keyOK] at ha <;> cases b <;> simp [keyOK] at hb <;> first | rfl | simp [compare, {na}.cmp_SortKItem, {nb}.cmp_SortKItem, {}]\n",
        tokens.iter().map(|t| format!("{na}.cmp_{t}, {nb}.cmp_{t}, {}", tr_name(t))).collect::<Vec<_>>().join(", ")
    )
    .unwrap();
    writeln!(
        o,
        "theorem toList_tr_SortMap : MapHook.Pointwise tr_SortKItem tr_SortKItem tr_SortMap := by\n  intro m\n  show {nb}.SortMap.toList (tr_SortMap m) = SAL.mapPairs tr_SortKItem tr_SortKItem ({na}.SortMap.toList m)\n  exact go m\nwhere\n  go : ∀ m, {nb}.SortMap.toList (tr_SortMap m) = SAL.mapPairs tr_SortKItem tr_SortKItem ({na}.SortMap.toList m)\n    | .nil => rfl\n    | .cons k v r => by\n      simp only [tr_SortMap, {nb}.SortMap.toList, {na}.SortMap.toList, SAL.mapPairs_cons, go r]\n"
    )
    .unwrap();
    writeln!(
        o,
        "theorem map_fwd {{k v : {na}.SortKItem}} {{D m : {na}.SortMap}} (hk : keyOK k = true) (hm : KeysOK m)\n    (h : MapHook.concat (MapHook.element k v) D = some m) :\n    MapHook.concat (MapHook.element (tr_SortKItem k) (tr_SortKItem v)) (tr_SortMap D) = some (tr_SortMap m) :=\n  MapHook.concat_element_pointwise toList_tr_SortMap pres hk hm h\n"
    )
    .unwrap();
    writeln!(
        o,
        "theorem map_bwd {{k : {na}.SortKItem}} {{v' : {nb}.SortKItem}} {{D' : {nb}.SortMap}} {{m : {na}.SortMap}} (hm : KeysOK m)\n    (h : MapHook.concat (MapHook.element (tr_SortKItem k) v') D' = some (tr_SortMap m)) (hk : keyOK k = true) :\n    ∃ v D, v' = tr_SortKItem v ∧ D' = tr_SortMap D ∧ MapHook.concat (MapHook.element k v) D = some m :=\n  MapHook.concat_element_pointwise_inv toList_tr_SortMap pres hk hm h\n"
    )
    .unwrap();
    writeln!(
        o,
        "theorem fold_update {{m : {na}.SortMap}} (hm : KeysOK m) {{k : {na}.SortKItem}} (hk : keyOK k = true) (v : {na}.SortKItem) :\n    MapHook.update (tr_SortMap m) (tr_SortKItem k) (tr_SortKItem v) = tr_SortMap (MapHook.update m k v) :=\n  MapHook.update_pointwise toList_tr_SortMap pres v hm hk\n"
    )
    .unwrap();
    writeln!(o, "theorem keysOK_update {{m : {na}.SortMap}} {{k v : {na}.SortKItem}} (hm : KeysOK m) (hk : keyOK k = true) : KeysOK (MapHook.update m k v) :=\n  MapHook.keysOn_update hm hk\n").unwrap();
    let top_lean = &a.m.ctors[&top_ctor].lean;
    // value sorts that B's rules refine map values to (`Map<Id, Value>` in KRS)
    let val_sorts: BTreeSet<String> = refined.values().flatten().cloned().collect();
    let vals = !val_sorts.is_empty();
    if vals {
        writeln!(
            o,
            "/-- A map value of a sort that `{nb}`'s rules require ({}). -/",
            val_sorts
                .iter()
                .map(|t| names::short_sort(t))
                .collect::<Vec<_>>()
                .join(", ")
        )
        .unwrap();
        let disj: Vec<String> = val_sorts
            .iter()
            .map(|t| format!("({na}.proj_KItem_{} v).isSome", names::short_sort(t)))
            .collect();
        writeln!(
            o,
            "def valOK (v : {na}.SortKItem) : Bool := {}\n",
            disj.join(" || ")
        )
        .unwrap();
        writeln!(
            o,
            "def ValsOK (m : {na}.SortMap) : Prop := ∀ p ∈ ListIso.toList m, valOK p.2 = true\n"
        )
        .unwrap();
        writeln!(o, "theorem valsOK_update {{m : {na}.SortMap}} {{k v : {na}.SortKItem}} (hm : ValsOK m) (hv : valOK v = true) : ValsOK (MapHook.update m k v) := by\n  intro p hp\n  rw [MapHook.update_def, ListIso.toList_ofList] at hp\n  rcases SAL.mem_insert hp with rfl | hp\n  · exact hv\n  · exact hm p hp\n").unwrap();
        if val_sorts.len() == 1 {
            let t = names::short_sort(val_sorts.iter().next().unwrap()).to_string();
            writeln!(o, "theorem val_of_concat {{k v : {na}.SortKItem}} {{D m : {na}.SortMap}} (hm : ValsOK m)\n    (h : MapHook.concat (MapHook.element k v) D = some m) : ∃ V, v = {na}.inj_{t}_KItem V := by\n  have hl := MapHook.lookup_of_concat_element h\n  rw [MapHook.lookup_def] at hl\n  have hv := hm _ (SAL.lookup_mem hl)\n  simp only [valOK, Option.isSome_iff_exists] at hv\n  obtain ⟨V, hV⟩ := hv\n  exact ⟨V, {na}.proj_eq_some_KItem_{t}.1 hV⟩\n").unwrap();
        } else {
            panic!("relate: refinements to several value sorts are not supported yet");
        }
    }
    let mut inv_pats = Vec::new();
    let mut vals_pats = Vec::new();
    // `Inv` through projections of the cells (matching only the top constructor), so that it
    // reduces on a configuration whose map cell is a variable
    let mut inv_unf: Vec<String> = vec!["Inv".into()];
    {
        let mut conj = Vec::new();
        for (n, (i, cs, cl, arity, j, _)) in map_cells.iter().enumerate() {
            let pats: Vec<String> = (0..top_args.len())
                .map(|k| {
                    if k == *i {
                        "x".to_string()
                    } else {
                        "_".to_string()
                    }
                })
                .collect();
            writeln!(
                o,
                "def cell{n} : {na}.{top} → {na}.{cs}\n  | .{top_lean} {} => x\n",
                pats.join(" ")
            )
            .unwrap();
            let inner: Vec<String> = (0..*arity)
                .map(|q| {
                    if q == *j {
                        "m".to_string()
                    } else {
                        "_".to_string()
                    }
                })
                .collect();
            let body = if vals {
                "KeysOK m ∧ ValsOK m"
            } else {
                "KeysOK m"
            };
            writeln!(
                o,
                "def InvCell{n} : {na}.{cs} → Prop\n  | .{cl} {} => {body}\n",
                inner.join(" ")
            )
            .unwrap();
            conj.push(format!("InvCell{n} (cell{n} c)"));
            inv_unf.push(format!("cell{n}"));
            inv_unf.push(format!("InvCell{n}"));
        }
        if conj.is_empty() {
            conj.push("True".into());
        }
        writeln!(
            o,
            "/-- Every map cell has `keyOK` keys{}. -/\ndef Inv (c : {na}.{top}) : Prop := {}\n",
            if vals { " and `valOK` values" } else { "" },
            conj.join(" ∧ ")
        )
        .unwrap();
        let total = map_cells.len();
        let nth = |k: usize| -> String {
            if total == 1 {
                "h".to_string()
            } else {
                let mut s = "h".to_string();
                for _ in 0..k {
                    s.push_str(".2");
                }
                if k + 1 < total {
                    s.push_str(".1");
                }
                s
            }
        };
        for (n, (i, cs, cl, arity, j, _)) in map_cells.iter().enumerate() {
            let xs: Vec<String> = (0..top_args.len())
                .map(|k| {
                    if k == *i {
                        format!(
                            "({na}.{cs}.{cl} {})",
                            (0..*arity)
                                .map(|q| if q == *j {
                                    "m".to_string()
                                } else {
                                    format!("y{q}")
                                })
                                .collect::<Vec<_>>()
                                .join(" ")
                        )
                    } else {
                        format!("x{k}")
                    }
                })
                .collect();
            let implicit = (0..top_args.len())
                .filter(|k| k != i)
                .map(|k| format!("x{k}"))
                .chain((0..*arity).filter(|q| q != j).map(|q| format!("y{q}")))
                .collect::<Vec<_>>()
                .join(" ");
            let keys = if vals {
                format!("{}.1", nth(n))
            } else {
                nth(n)
            };
            writeln!(o, "theorem inv_map{n} {{{implicit}}} {{m : {na}.SortMap}} (h : Inv ({na}.{top}.{top_lean} {})) : KeysOK m := {keys}\n", xs.join(" ")).unwrap();
            inv_pats.push(format!("inv_map{n} hi"));
            if vals {
                writeln!(o, "theorem inv_vals{n} {{{implicit}}} {{m : {na}.SortMap}} (h : Inv ({na}.{top}.{top_lean} {})) : ValsOK m := {}.2\n", xs.join(" "), nth(n)).unwrap();
                vals_pats.push(format!("inv_vals{n} hi"));
            }
        }
    }
    let folds_upd: String = inv_pats
        .iter()
        .map(|p| format!(", fold_update ({p})"))
        .collect();
    let unfolds_upd: String = inv_pats
        .iter()
        .map(|p| format!(", ← fold_update ({p})"))
        .collect();
    let inv_hint = inv_pats.first().cloned().unwrap_or_default();
    // the tr equations and the injections, oriented to push `tr` inwards
    let trs: Vec<String> = universe(&a.m)
        .into_iter()
        .filter(|(t, _, _)| covered.contains(t))
        .map(|(t, _, _)| tr_name(&t))
        .collect();
    let inj_names: Vec<String> = terms::inj_pairs(&a.m)
        .into_iter()
        .filter(|(x, y)| {
            pairs_b.contains(&(x.clone(), y.clone()))
                && covered.contains(y)
                && (is_builtin(&a.m, x)
                    || covered.contains(x)
                    || matches!(a.m.sorts[x].kind, Kind::Token))
        })
        .map(|(x, y)| {
            (
                names::short_sort(&x).to_string(),
                names::short_sort(&y).to_string(),
            )
        })
        .map(|(x, y)| format!("fold_inj_{x}_{y}"))
        .collect();
    // pushing `tr` inwards: the folding lemmas read backwards (they never unfold `tr` on a variable)
    let _ = &trs;
    let push = fold_names
        .iter()
        .chain(inj_names.iter())
        .map(|n| format!("← {n}"))
        .collect::<Vec<_>>()
        .join(", ");
    let proj_eqs: Vec<String> = terms::inj_pairs(&a.m)
        .into_iter()
        .map(|(x, y)| {
            format!(
                "{na}.proj_eq_some_{}_{}",
                names::short_sort(&y),
                names::short_sort(&x)
            )
        })
        .collect();
    let fin = format!(
        "first | (simp only [k2l_rel, keyOK{folds_upd}]; done) | (simp only [k2l_rel, keyOK]; done) | (simp only [{pe}] at * <;> subst_vars <;> first | (simp only [k2l_rel, keyOK{folds_upd}]; done) | (simp only [k2l_rel, keyOK]; done))",
        pe = proj_eqs.join(", ")
    );
    writeln!(o, "set_option hygiene false in\n/-- Push `tr` into a configuration (`tr`'s equations, injections, `update` under `Inv`). -/\nlocal macro \"push_tr\" : tactic => `(tactic| first | simp only [{push}{unfolds_upd}, keyOK] | simp only [{push}, keyOK])\n").unwrap();
    writeln!(o, "set_option hygiene false in\n/-- Close `d = tr c'` after a backward step. -/\nlocal macro \"fin_bwd\" : tactic => `(tactic| {fin})\n").unwrap();
    writeln!(
        o,
        "/-- Hypotheses of `{nb}`'s rules from those of `{na}`'s, and back. -/"
    )
    .unwrap();
    writeln!(o, "local macro \"hyp_fwd\" : tactic => `(tactic| first\n  | assumption\n  | (simp only [k2l_rel, keyOK] <;> assumption)\n  | (simp only [k2l_rel, keyOK] <;> rfl)\n  | (simp only [k2l_rel, keyOK, *] <;> rfl)\n  | (simp only [k2l_rel, keyOK] at * <;> simp_all))\n").unwrap();
    writeln!(o, "local macro \"hyp_bwd\" : tactic => `(tactic| first\n  | assumption\n  | (simp only [k2l_rel, keyOK] at * <;> assumption)\n  | (simp only [k2l_rel, keyOK] at * <;> simp_all))\n").unwrap();
    // inv_step
    writeln!(o, "/-! ## The invariant is preserved -/\n").unwrap();
    let upd = if vals {
        "exact ⟨keysOK_update hi.1 (by rfl), valsOK_update hi.2 (by simp [valOK])⟩".to_string()
    } else {
        "exact keysOK_update hi (by rfl)".to_string()
    };
    writeln!(
        o,
        "theorem inv_step {{c c' : {na}.{top}}} (hi : Inv c) (h : {na}.Step c c') : Inv c' := by\n  cases h <;> (try simp only [{}] at hi ⊢) <;> first | exact hi | {upd}\n",
        inv_unf.join(", ")
    )
    .unwrap();
    // forward
    writeln!(
        o,
        "/-! ## Forward simulation: every step of `{na}` is a step of `{nb}` -/\n"
    )
    .unwrap();
    writeln!(o, "theorem forward {{c c' : {na}.{top}}} (hi : Inv c) (h : {na}.Step c c') : {nb}.Step ({} c) ({} c') := by\n  cases h with", tr_name(&top), tr_name(&top)).unwrap();
    for (i, j) in pairs {
        let ra = &a.rules[*i];
        let rb = &b.rules[*j];
        let anames: Vec<String> = rules::ctor_args(&ra.step);
        let map_hyps: Vec<&String> = ra
            .step
            .hyps
            .iter()
            .filter(|(_, hp)| hp.starts_with("KPrelude.MapHook.concat (KPrelude.MapHook.element"))
            .map(|(hn, _)| hn)
            .collect();
        writeln!(o, "  | {} {} =>", ra.lean, anames.join(" ")).unwrap();
        if refined.contains_key(i) {
            for hn in &map_hyps {
                writeln!(
                    o,
                    "    obtain ⟨_, rfl⟩ := val_of_concat ({}) {hn}",
                    vals_pats.first().cloned().unwrap_or_default()
                )
                .unwrap();
            }
        }
        writeln!(o, "    push_tr").unwrap();
        let mut alts: Vec<String> = map_hyps
            .iter()
            .map(|hn| format!("exact map_fwd (by rfl) ({inv_hint}) {hn}"))
            .collect();
        alts.push("hyp_fwd".into());
        writeln!(o, "    apply {nb}.Step.{}", rb.lean).unwrap();
        writeln!(o, "    all_goals first | {}", alts.join(" | ")).unwrap();
    }
    writeln!(o).unwrap();
    // backward
    writeln!(o, "/-! ## Backward simulation: every step of `{nb}` from a translation is the translation of a step of `{na}` -/\n").unwrap();
    writeln!(
        o,
        "theorem backward {{c : {na}.{top}}} {{d : {nb}.{top}}} (hi : Inv c) (h : {nb}.Step ({} c) d) :\n    ∃ c', {na}.Step c c' ∧ d = {} c' := by\n  generalize hd : {} c = d0 at h\n  cases h with",
        tr_name(&top),
        tr_name(&top),
        tr_name(&top)
    )
    .unwrap();
    let back_of: BTreeMap<usize, usize> = pairs.iter().map(|(i, j)| (*j, *i)).collect();
    for (j, rb) in b.rules.iter().enumerate() {
        let bnames: Vec<String> = rules::ctor_args(&rb.step);
        writeln!(o, "  | {} {} =>", rb.lean, bnames.join(" ")).unwrap();
        writeln!(o, "    k2l_inv").unwrap();
        let Some(i) = back_of.get(&j) else {
            assert!(unmatched_b.contains(&j));
            continue;
        };
        let ra = &a.rules[*i];
        for (hn, hp) in &rb.step.hyps {
            if hp.starts_with("KPrelude.MapHook.concat (KPrelude.MapHook.element") {
                writeln!(o, "    all_goals obtain ⟨_, _, rfl, rfl, _⟩ := map_bwd ({inv_hint}) (by simpa only [k2l_rel] using {hn}) (by rfl)").unwrap();
            } else if hp.contains("proj_") && hp.contains("= some") {
                writeln!(
                    o,
                    "    all_goals simp only [k2l_rel, Option.map_eq_some_iff] at {hn}"
                )
                .unwrap();
                writeln!(o, "    all_goals obtain ⟨_, _, rfl⟩ := {hn}").unwrap();
            }
        }
        writeln!(
            o,
            "    all_goals exact ⟨_, by apply {na}.Step.{} <;> hyp_bwd, by fin_bwd⟩",
            ra.lean
        )
        .unwrap();
    }
    writeln!(o).unwrap();
    // the same for `App` (a rule applies: a step, or an undefined right-hand side)
    writeln!(o, "/-! ## A rule applies in `{na}` exactly when one applies in `{nb}` (so undefined and stuck configurations correspond too) -/\n").unwrap();
    writeln!(o, "theorem app_fwd {{c : {na}.{top}}} (hi : Inv c) (h : {na}.App c) : {nb}.App ({} c) := by\n  cases h with", tr_name(&top)).unwrap();
    for (i, j) in pairs {
        let ra = &a.rules[*i];
        let rb = &b.rules[*j];
        let anames: Vec<String> = rules::ctor_args(&ra.app);
        let map_hyps: Vec<&String> = ra
            .app
            .hyps
            .iter()
            .filter(|(_, hp)| hp.starts_with("KPrelude.MapHook.concat (KPrelude.MapHook.element"))
            .map(|(hn, _)| hn)
            .collect();
        writeln!(o, "  | {} {} =>", ra.lean, anames.join(" ")).unwrap();
        if refined.contains_key(i) {
            for hn in &map_hyps {
                writeln!(
                    o,
                    "    obtain ⟨_, rfl⟩ := val_of_concat ({}) {hn}",
                    vals_pats.first().cloned().unwrap_or_default()
                )
                .unwrap();
            }
        }
        writeln!(o, "    push_tr").unwrap();
        let mut alts: Vec<String> = map_hyps
            .iter()
            .map(|hn| format!("exact map_fwd (by rfl) ({inv_hint}) {hn}"))
            .collect();
        alts.push("hyp_fwd".into());
        writeln!(o, "    apply {nb}.App.{}", rb.lean).unwrap();
        writeln!(o, "    all_goals first | {}", alts.join(" | ")).unwrap();
    }
    writeln!(o).unwrap();
    writeln!(
        o,
        "theorem app_bwd {{c : {na}.{top}}} (hi : Inv c) (h : {nb}.App ({} c)) : {na}.App c := by\n  generalize hd : {} c = d0 at h\n  cases h with",
        tr_name(&top),
        tr_name(&top)
    )
    .unwrap();
    for (j, rb) in b.rules.iter().enumerate() {
        let bnames: Vec<String> = rules::ctor_args(&rb.app);
        writeln!(o, "  | {} {} =>", rb.lean, bnames.join(" ")).unwrap();
        writeln!(o, "    k2l_inv").unwrap();
        let Some(i) = back_of.get(&j) else { continue };
        let ra = &a.rules[*i];
        for (hn, hp) in &rb.app.hyps {
            if hp.starts_with("KPrelude.MapHook.concat (KPrelude.MapHook.element") {
                writeln!(o, "    all_goals obtain ⟨_, _, rfl, rfl, _⟩ := map_bwd ({inv_hint}) (by simpa only [k2l_rel] using {hn}) (by rfl)").unwrap();
            } else if hp.contains("proj_") && hp.contains("= some") {
                writeln!(
                    o,
                    "    all_goals simp only [k2l_rel, Option.map_eq_some_iff] at {hn}"
                )
                .unwrap();
                writeln!(o, "    all_goals obtain ⟨_, _, rfl⟩ := {hn}").unwrap();
            }
        }
        writeln!(o, "    all_goals (apply {na}.App.{} <;> hyp_bwd)", ra.lean).unwrap();
    }
    writeln!(o).unwrap();
    // bisimulation
    writeln!(o, "/-! ## The bisimulation -/\n").unwrap();
    writeln!(o, "/-- A configuration of `{na}` satisfying `Inv`, and its translation. -/\ndef R (c : {na}.{top}) (d : {nb}.{top}) : Prop := Inv c ∧ d = {} c\n", tr_name(&top)).unwrap();
    writeln!(
        o,
        "theorem bisim : Bisimulation {na}.Step {nb}.Step R where\n  fwd := by\n    rintro c d c' ⟨hi, rfl⟩ h\n    exact ⟨_, forward hi h, inv_step hi h, rfl⟩\n  bwd := by\n    rintro c d d' ⟨hi, rfl⟩ h\n    obtain ⟨c', hc, rfl⟩ := backward hi h\n    exact ⟨c', hc, inv_step hi hc, rfl⟩\n"
    )
    .unwrap();
    writeln!(
        o,
        "/-- Runs of `n` steps correspond, and so do terminal configurations (stuck or undefined). -/\ntheorem stepsN_iff {{n : Nat}} {{c : {na}.{top}}} (hi : Inv c) :\n    (∃ c', StepsN {na}.Step n c c') ↔ (∃ d', StepsN {nb}.Step n ({} c) d') := by\n  constructor\n  · rintro ⟨c', h⟩; obtain ⟨d', hd, -⟩ := bisim.stepsN_fwd ⟨hi, rfl⟩ h; exact ⟨d', hd⟩\n  · rintro ⟨d', h⟩; obtain ⟨c', hc, -⟩ := bisim.stepsN_bwd ⟨hi, rfl⟩ h; exact ⟨c', hc⟩\n",
        tr_name(&top)
    )
    .unwrap();
    writeln!(
        o,
        "theorem terminal_iff {{c : {na}.{top}}} (hi : Inv c) :\n    (∀ c', ¬ {na}.Step c c') ↔ (∀ d, ¬ {nb}.Step ({} c) d) :=\n  bisim.terminal_iff ⟨hi, rfl⟩\n\ntheorem app_iff {{c : {na}.{top}}} (hi : Inv c) : {na}.App c ↔ {nb}.App ({tr} c) := ⟨app_fwd hi, app_bwd hi⟩\n",
        tr_name(&top),
        tr = tr_name(&top)
    )
    .unwrap();
    writeln!(
        o,
        "/-- Every run of `{na}` from a configuration satisfying `Inv` is, translated, a run of `{nb}` of the same length, and its last configuration is terminal in one exactly when it is in the other. -/\ntheorem run_agree {{n : Nat}} {{c c' : {na}.{top}}} (hi : Inv c) (h : StepsN {na}.Step n c c') :\n    StepsN {nb}.Step n ({tr} c) ({tr} c') ∧ ((∀ x, ¬ {na}.Step c' x) ↔ (∀ y, ¬ {nb}.Step ({tr} c') y)) := by\n  obtain ⟨d', hd, hi', rfl⟩ := bisim.stepsN_fwd ⟨hi, rfl⟩ h\n  exact ⟨hd, terminal_iff hi'⟩\n",
        tr = tr_name(&top)
    )
    .unwrap();
    writeln!(o, "#k2l_assert_axioms inv_step forward backward app_fwd app_bwd bisim stepsN_iff terminal_iff app_iff run_agree\n").unwrap();
    writeln!(o, "end {ns}").unwrap();
    o
}
