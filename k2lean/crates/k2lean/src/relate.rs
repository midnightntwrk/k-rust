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
    /// Lean names of the recursive (well-founded, `Option`-valued) functions.
    recursive: BTreeSet<String>,
    /// The generated functions by call-graph component, callees first, and the termination
    /// measures of the recursive ones (`funcs::Generated`).
    groups: Vec<Vec<String>>,
    measures: BTreeMap<String, crate::funcs::Measure>,
    choose_fns: BTreeSet<String>,
    rules: Vec<Rule>,
    /// The priority ranks of the rules, and whether `App` and `Step` are stratified by them
    /// (`App i c`, and `hpri` in each `Step` constructor of a rank above 0).
    prios: Vec<i64>,
    ranked: bool,
    ns: String,
    /// The library is in the arity-indexed universe (`terms_arity.rs`, design.md §2.1).
    arity: bool,
}

impl Side {
    fn rank(&self, r: &Rule) -> usize {
        self.prios
            .iter()
            .position(|p| *p == r.priority)
            .unwrap_or(0)
    }
}

/// Stop with a message (exit status 2): a definition or a correspondence `relate` does not support.
/// Write `text` to `path`, creating its directory; a failure is reported, not a panic.
fn write_file(path: &str, text: &str) {
    let p = std::path::Path::new(path);
    if let Some(d) = p.parent().filter(|d| !d.as_os_str().is_empty()) {
        std::fs::create_dir_all(d)
            .unwrap_or_else(|e| fail(&format!("cannot create {}: {e}", d.display())));
    }
    std::fs::write(p, text).unwrap_or_else(|e| fail(&format!("cannot write {path}: {e}")));
}

fn fail(msg: &str) -> ! {
    eprintln!("relate: {msg}");
    std::process::exit(2)
}

fn load_side(kore: &str, syn: Option<&str>, ns: &str, want_rules: bool, arity: bool) -> Side {
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
    // the functions as `gen` generates them in the library's encoding (their termination measures
    // depend on it)
    let side = crate::funcs::Sidecar {
        arity_terms: arity,
        ..Default::default()
    };
    let fgen = crate::funcs::generate_with(&def, &m, &roots, &side)
        .unwrap_or_else(|e| fail(&format!("functions: {e}")));
    let (rules, prios, ranked) = if want_rules {
        rules::collect_ranked(&def, &m, &fgen.fns, &[]).unwrap_or_else(|e| fail(&e))
    } else {
        (vec![], vec![], false)
    };
    Side {
        def,
        syn,
        m,
        fns: fgen.fns,
        unfold: fgen.unfold,
        recursive: fgen.recursive,
        groups: fgen.groups,
        measures: fgen.measures,
        choose_fns: fgen.choose_fns,
        rules,
        prios,
        ranked,
        ns: ns.to_string(),
        arity,
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
    // `--per-rule true`: when not every rule pairs, one simulation lemma per paired rule instead of
    // the bisimulation (what `k2lean refine` builds a stuttering bisimulation from)
    let per_rule = opt.get("per-rule").is_some_and(|v| v == "true");
    if per_rule && !full {
        fail("--per-rule needs the whole correspondence (not --roots)");
    }
    // the encoding of the two libraries' terms, as `gen` was given it
    let arity = opt.get("arity-terms").is_some_and(|v| v == "true");
    let a = load_side(
        &get("kore-a"),
        opt.get("syntax-a").map(|s| s.as_str()),
        &get("name-a"),
        full,
        arity,
    );
    let b = load_side(
        &get("kore-b"),
        opt.get("syntax-b").map(|s| s.as_str()),
        &get("name-b"),
        full,
        arity,
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
        // a KORE axiom is one rule per overload variant (`_ov1`, …), in the same order on both
        // sides: the variants of two corresponding axioms correspond one to one
        let group = |side: &Side| {
            let mut g: BTreeMap<String, Vec<usize>> = BTreeMap::new();
            for (i, r) in side.rules.iter().enumerate() {
                g.entry(r.uid.clone()).or_default().push(i);
            }
            g
        };
        let (ga, gb) = (group(&a), group(&b));
        let mut used_b = BTreeSet::new();
        let mut unmatched_groups: Vec<&String> = Vec::new();
        for (u, k) in &ka {
            let Some(is) = ga.get(u) else {
                continue;
            };
            match b_by_key.get(k).map(|v| v.as_slice()) {
                Some([ub]) if gb.get(*ub).is_some_and(|js| js.len() == is.len()) => {
                    for (i, j) in is.iter().zip(&gb[*ub]) {
                        pairs.push((*i, *j));
                        used_b.insert(*j);
                    }
                }
                _ => unmatched_groups.push(u),
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
        for u in unmatched_groups {
            let is = &ga[u];
            let pa = ax_a[u];
            let cands: Vec<(&String, BTreeSet<(String, S)>)> = gb
                .iter()
                .filter(|(_, js)| js.len() == is.len() && js.iter().all(|j| !used_b.contains(j)))
                .filter_map(|(ub, _)| {
                    let mut vm = BTreeMap::new();
                    let mut refs = BTreeSet::new();
                    pmatch(pa, ax_b[ub], &ren, &mut vm, &mut refs).then_some((ub, refs))
                })
                .collect();
            if let [(ub, refs)] = cands.as_slice() {
                for (i, j) in is.iter().zip(&gb[*ub]) {
                    pairs.push((*i, *j));
                    used_b.insert(*j);
                    refined.insert(
                        *i,
                        refs.iter()
                            .map(|(_, t)| t.name().unwrap_or("?").to_string())
                            .collect(),
                    );
                }
            } else {
                still.extend(is.iter().copied());
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
    // priorities: a pair of rules must be of the same rank, so that "no rule of a higher rank
    // applies" corresponds on both sides
    let mut bisim = full && unmatched_rules_a.is_empty();
    if bisim {
        let bad: Vec<String> = pairs
            .iter()
            .filter(|(i, j)| a.rank(&a.rules[*i]) != b.rank(&b.rules[*j]))
            .map(|(i, _)| rules::display_name(&a.rules[*i]))
            .collect();
        if a.ranked != b.ranked || !bad.is_empty() {
            writeln!(
                rep,
                "\n# not stated: paired rules of different priority ranks: {bad:?}"
            )
            .unwrap();
            eprintln!(
                "note: paired rules of different priority ranks ({}); the bisimulation is not stated",
                bad.join(", ")
            );
            bisim = false;
        }
    }
    // whether the translation keeps every constructor's position (design.md, §3.2)
    let per_rule = per_rule && !bisim;
    if per_rule && (a.ranked || b.ranked) {
        fail("--per-rule does not support priority ranks");
    }
    let ordered = if bisim || per_rule {
        positions_kept(&a, &b, &sm, &covered)
    } else {
        Err(String::new())
    };
    if bisim {
        match &ordered {
            Ok(()) => writeln!(
                rep,
                "\n# the translation keeps every constructor's position: it preserves the order of every key"
            )
            .unwrap(),
            Err(e) => writeln!(
                rep,
                "\n# the translation moves a constructor ({e}): map keys are restricted by `Inv`"
            )
            .unwrap(),
        }
    }
    if let Some(r) = opt.get("report") {
        write_file(r, &rep);
    }
    let lean = emit(
        &a,
        &b,
        &ns,
        &sm,
        &covered,
        bisim,
        per_rule,
        ordered.is_ok(),
        &pairs,
        &unmatched_rules_b,
        &refined,
    )
    .unwrap_or_else(|e| fail(&e));
    write_file(&get("out"), &lean);
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

/// The tactic that splits a term variable into its sort's values: `cases` on a type per sort, and
/// on the arity-indexed family `k2l_cases`, which also refutes the family's constructors that no
/// value of the sort has.
fn cases_tac(a: &Side) -> &'static str {
    if a.arity { "k2l_cases" } else { "cases" }
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
    per_rule: bool,
    ordered: bool,
    pairs: &[(usize, usize)],
    unmatched_b: &[usize],
    refined: &BTreeMap<usize, Vec<String>>,
) -> Result<String, String> {
    let (na, nb) = (&a.ns, &b.ns);
    let mut o = String::new();
    // only what the statements need: the relations (or, for a translation of programs, the functions)
    let m = if bisim {
        "Rules"
    } else if per_rule {
        "Preserves"
    } else {
        "Functions"
    };
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
    if per_rule {
        writeln!(o, "and, for each pair of corresponding rules, the simulation of each by the other (`fwd.r`, `bwd.r`), from which `k2lean refine` builds a stuttering bisimulation. -/\n").unwrap();
    } else if bisim {
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
    if a.arity {
        emit_arity_tr(a, b, sm, covered, &mut o)?;
    } else {
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
    }
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
        if a.arity
            && let TyKind::Coll(c, es) = k
        {
            // a collection value is `coll_T l` of a list, translated by `trL_T`
            let f = terms::fsuffix(t);
            let elem = |e: &str| {
                if is_builtin(&a.m, e)
                    || matches!(a.m.sorts.get(e).map(|i| &i.kind), Some(Kind::Token))
                {
                    format!("{na}.{e}")
                } else {
                    format!("{na}.Term .«{e}»")
                }
            };
            let lt = match c {
                Coll::Map => format!("({} × {})", elem(&es[0]), elem(&es[1])),
                Coll::Set => format!("({} × Unit)", elem(&es[0])),
                Coll::List => format!("({})", elem(&es[0])),
            };
            writeln!(
                o,
                "@[k2l_rel] theorem fold_{f}_0 (l : List {lt}) : {nb}.Term.«coll_{f}» (trL_{f} l) = {} ({na}.Term.«coll_{f}» l) := rfl",
                tr_name(t)
            )
            .unwrap();
            fold_names.push(format!("fold_{f}_0"));
            continue;
        }
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
            "@[k2l_rel] theorem fold_inj_{sx}_{sy} (x : {na}.{tx}) : {nb}.inj_{sx}_{sy} {} = {} ({na}.inj_{sx}_{sy} x) := by\n  first | rfl | ({} x <;> rfl)",
            val(&a.m, &x, "x"),
            tr_name(&y),
            cases_tac(a)
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
        writeln!(o, "@[k2l_rel] theorem comm_proj_{sy}_{sx} (y : {na}.{y}) : {nb}.proj_{sy}_{sx} ({} y) = {rhs} := by\n  {} y <;> rfl", tr_name(&y), cases_tac(a)).unwrap();
        writeln!(o, "attribute [k2l_rel] {na}.proj_inj_{sy}_{sx}").unwrap();
    }
    // functions defined by equations, used by the rules
    writeln!(
        o,
        "\n/-! ## Functions defined by equations commute with the translation -/\n"
    )
    .unwrap();
    // an order-preserving translation: the collection lemmas come first, the functions use them
    let ordered_lemmas = ((bisim || per_rule) && ordered)
        .then(|| emit_ordered_terms(a, b, &mut o, covered, &fold_names));
    let mut fn_count = 0;
    // the commutation lemmas of total functions (`B.f (tr x) = tr (A.f x)`), which push `tr` in
    let mut pure_fns: Vec<String> = Vec::new();
    // the functions to translate, callees first: a lemma's proof rewrites with those of the
    // functions it calls, and a recursive group's lemmas are proved together
    let commutes = |sym: &String| -> bool {
        let sig = &a.fns[sym];
        let Some(sb) = b.fns.get(sym) else {
            return false;
        };
        crate::hooks::for_symbol(&a.def.symbols[sym]).is_none()
            && sb.lean == sig.lean
            && sb.args == sig.args
            && sb.result == sig.result
            && !sig
                .args
                .iter()
                .chain(std::iter::once(&sig.result))
                .any(|s| !is_builtin(&a.m, s) && !covered.contains(s))
    };
    let groups: Vec<Vec<String>> = if ordered_lemmas.is_some() {
        a.groups
            .iter()
            .map(|g| {
                g.iter()
                    .filter(|f| a.fns.contains_key(*f) && commutes(f))
                    .cloned()
                    .collect::<Vec<_>>()
            })
            .filter(|g| !g.is_empty())
            .collect()
    } else {
        a.fns
            .keys()
            .filter(|f| commutes(f))
            .map(|f| vec![f.clone()])
            .collect()
    };
    if ordered_lemmas.is_some()
        && let Some(f) = groups.iter().flatten().find(|f| a.choose_fns.contains(*f))
    {
        return Err(format!(
            "the function {} has an equation with a free-key map pattern; its commutation with the translation is not generated",
            names::demangle(f)
        ));
    }
    for group in &groups {
        let rec_group =
            ordered_lemmas.is_some() && group.iter().any(|f| a.recursive.contains(&a.fns[f].lean));
        let names: Vec<String> = (0..group.len())
            .map(|i| format!("comm_fn_{}", fn_count + i))
            .collect();
        if rec_group && group.len() > 1 {
            writeln!(o, "mutual").unwrap();
        }
        for sym in group {
            let sig = &a.fns[sym];
            let sb = &b.fns[sym];
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
            if rec_group {
                // a well-founded definition: unfolded once on both sides, both cascades split
                // in step; a recursive call of `B` is rewritten by the lemma of its function
                // (this one or one of its group), which is the induction: the lemma is defined by
                // the same well-founded recursion as `A.f`
                let gens: String = xs
                    .iter()
                    .map(|x| format!("\n  generalize h{x} : {x} = {x}'"))
                    .collect();
                let ms = a.measures.get(sym).cloned().unwrap_or_default();
                let qualify = |t: &str| t.replace("K.", &format!("{na}.K."));
                // what `A.f`'s own fallback unfolds (its injections, qualified, and the integer
                // hooks), for the calls of the lemma, whose arguments are `A.f`'s
                let unfold: Vec<String> = ms
                    .unfold
                    .iter()
                    .map(|u| {
                        if u.contains('.') {
                            u.clone()
                        } else {
                            format!("{na}.{u}")
                        }
                    })
                    .collect();
                // on the goal alone first (the lemma's context holds the induction hypothesis
                // and both cascades, which `simp_all` would rewrite too), and only by these
                // definitions: the full simp set can exceed the recursion depth on the goals of
                // the measures Lean's search tries, an error `first` does not catch
                let fallback = format!(
                    "(simp_wf; (try subst_vars); simp only [{u}]; decreasing_tactic)\n  | (simp_wf; (try subst_vars); (try simp_all [{u}]); omega)",
                    u = unfold.join(", ")
                );
                // the measure of `A.f`; without one, Lean's own search, with `A.f`'s tactics
                let term = match ms.by {
                    Some(t) => format!(
                        "termination_by {}\ndecreasing_by all_goals first\n  | k2l_decreasing [{}]\n  | {fallback}\n",
                        qualify(&t),
                        ms.ranks
                            .iter()
                            .map(|r| qualify(r))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    None => format!(
                        "decreasing_by all_goals first\n  | (simp_wf; (try subst_vars); decreasing_tactic)\n  | {fallback}\n"
                    ),
                };
                writeln!(
                o,
                "@[k2l_rel] theorem comm_fn_{fn_count} {binders} : {nb}.{} {} = {rhs} := by\n  rw [{na}.{lean}.eq_def, {nb}.{lean}.eq_def]{gens}\n  comm_rec [{}]\n{term}",
                sb.lean,
                vs.join(" "),
                names.join(", "),
                lean = sig.lean
            )
            .unwrap();
            } else {
                writeln!(
                o,
                "@[k2l_rel] theorem comm_fn_{fn_count} {binders} : {nb}.{} {} = {rhs} := by\n  simp only [{}]\n  {}",
                sb.lean,
                vs.join(" "),
                unf.join(", "),
                // a body that calls other functions: their lemmas rewrite `B`'s calls
                if ordered_lemmas.is_some() {
                    "first | k2l_comm_fn | (simp only [k2l_rel]; comm_rec [])"
                } else {
                    "k2l_comm_fn"
                }
            )
            .unwrap();
            }
            if !sig.partial && !is_builtin(&a.m, &sig.result) {
                pure_fns.push(format!("comm_fn_{fn_count}"));
            }
            fn_count += 1;
        }
        if rec_group && group.len() > 1 {
            writeln!(o, "end").unwrap();
        }
    }
    if per_rule && !ordered {
        return Err(
            "--per-rule needs a translation that keeps every constructor's position".into(),
        );
    }
    if !bisim && !per_rule {
        writeln!(o, "\nend {ns}").unwrap();
        return Ok(o);
    }
    if ordered {
        let lemmas = ordered_lemmas.expect("the lemmas of an order-preserving translation");
        return emit_ordered(
            a,
            b,
            ns,
            o,
            covered,
            pairs,
            unmatched_b,
            refined,
            &fold_names,
            &pure_fns,
            lemmas,
            per_rule,
        );
    }
    if a.ranked || b.ranked {
        return Err(format!(
            "a correspondence that moves a constructor (so map keys need `Inv`) between definitions with priority ranks or free-key map patterns ({} or {}) is not supported",
            a.ns, b.ns
        ));
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
        return Err(format!(
            "the translation moves a constructor, and map keys that are not injections of builtin or token sorts need an order-preserving translation: {bad:?} {key_leaves:?}"
        ));
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
        return Err(
            "the translation moves a constructor, and typed cell maps need an order-preserving translation"
                .into(),
        );
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
        "theorem pres : SAL.PresOn (fun k => keyOK k = true) tr_SortKItem := by\n  intro a b ha hb\n  {ct} a <;> simp [keyOK] at ha <;> {ct} b <;> simp [keyOK] at hb <;> first | rfl | simp [compare, {na}.cmp_SortKItem, {nb}.cmp_SortKItem, {}]\n",
        tokens.iter().map(|t| format!("{na}.cmp_{t}, {nb}.cmp_{t}, {}", tr_name(t))).collect::<Vec<_>>().join(", "),
        ct = cases_tac(a)
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
    // `fold_update` at each key leaf, where `keyOK` holds by evaluation: the tactics rewrite with
    // these, so no rewrite needs `simp` to discharge `keyOK k = true` (since Lean v4.33 `simp`
    // rejects a discharge proved by unfolding `keyOK`, a definition it may not unfold reducibly)
    for l in &key_leaves {
        let s = names::short_sort(l);
        writeln!(
            o,
            "theorem fold_update_{s} {{m : {na}.SortMap}} (hm : KeysOK m) {{x}} (v : {na}.SortKItem) :\n    MapHook.update (tr_SortMap m) (tr_SortKItem (.inj_{s} x)) (tr_SortKItem v) = tr_SortMap (MapHook.update m (.inj_{s} x) v) :=\n  fold_update hm rfl v\n"
        )
        .unwrap();
    }
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
            return Err("refinements to several value sorts are not supported yet".into());
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
    let upd_lemmas: Vec<String> = key_leaves
        .iter()
        .map(|l| format!("fold_update_{}", names::short_sort(l)))
        .collect();
    let folds_upd: String = inv_pats
        .iter()
        .flat_map(|p| upd_lemmas.iter().map(move |u| format!(", {u} ({p})")))
        .collect();
    let unfolds_upd: String = inv_pats
        .iter()
        .flat_map(|p| upd_lemmas.iter().map(move |u| format!(", ← {u} ({p})")))
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
    Ok(o)
}

/// Whether the translation keeps every constructor of every covered type at its position (its
/// tag in the serialization `ser`, from which each library's order on terms comes): then
/// `ser (tr a) = ser a` for every term, so the translation preserves the order of every map key
/// and commutes with every collection operation, without a hypothesis (design.md, §3.2). `Err`
/// The translation in the arity-indexed universe (design.md §2.1, `terms_arity.rs`): one function
/// `tr : {s : A.Tag} → A.Term s → TrTy s` by structural recursion on `A`'s family, where `TrTy s`
/// is `B.Term s` on the covered sorts and the builtin carriers, and `Unit` on the others (the sorts
/// a translation of programs, `--roots`, does not reach). A covered sort's values are translated by
/// the builders `mkK` (a constructor of arity `K` to its counterpart, by a match on the sort and
/// its enumeration, so the arguments' `TrTy` reduce to `B`'s argument sorts) and `mkInj` (a leaf
/// injection to the same leaf of `B`'s sort); the per-sort names `tr_S` are `tr` at sort `S`.
/// Each `B` constructor applied to translations is then `tr` of the `A` constructor by `rfl`, as
/// in the one type per sort encoding.
fn emit_arity_tr(
    a: &Side,
    b: &Side,
    sm: &SymMap,
    covered: &BTreeSet<String>,
    o: &mut String,
) -> Result<(), String> {
    let (na, nb) = (&a.ns, &b.ns);
    let sa = crate::terms_arity::shape(&a.m);
    let sb = crate::terms_arity::shape(&b.m);
    let q = |t: &str| format!("«{t}»");
    let btags: BTreeSet<&String> = sb.tags.iter().collect();
    let is_token = |t: &str| matches!(a.m.sorts.get(t).map(|i| &i.kind), Some(Kind::Token));
    // tags whose terms translate to `B`'s terms of the same tag
    let into: BTreeSet<String> = sa
        .tags
        .iter()
        .filter(|t| (covered.contains(*t) || sa.builtins.contains(*t)) && btags.contains(t))
        .cloned()
        .collect();
    for t in covered {
        if !btags.contains(t) {
            return Err(format!(
                "relate: {nb} has no sort {t} (needed by the translation)"
            ));
        }
    }
    // A's constructors by (type, Lean name)
    let mut sym_of: BTreeMap<(String, String), String> = BTreeMap::new();
    for (t, _, k) in universe(&a.m) {
        if let TyKind::Own(cs) = k {
            for (sym, lean, _) in cs {
                sym_of.insert((t.clone(), lean), sym);
            }
        }
    }
    let _ = writeln!(
        o,
        "/-- The type a term of tag `s` of `{na}` translates to: `{nb}`'s terms of the same sort, or \
`Unit` for a sort the translation does not cover. -/\n@[reducible] def TrTy : {na}.Tag → Type"
    );
    for t in &sa.tags {
        if into.contains(t) {
            let _ = writeln!(o, "  | .{} => {nb}.Term .{}", q(t), q(t));
        } else {
            let _ = writeln!(o, "  | .{} => Unit", q(t));
        }
    }
    let _ = writeln!(o);
    for t in sa
        .builtins
        .iter()
        .filter(|t| into.contains(*t) && is_token(t))
    {
        let _ = writeln!(o, "def {} (x : {na}.{t}) : {nb}.{t} := ⟨x.val⟩", tr_name(t));
    }
    let _ = writeln!(o);
    // the builders, one per arity
    for (k, sorts) in &sa.enums {
        let xs: Vec<String> = (0..*k).map(|i| format!("x{i}")).collect();
        for (t, cs) in sorts {
            if !into.contains(t) {
                continue;
            }
            let args: String = (0..*k)
                .map(|i| format!("TrTy ({na}.{t}.A{k}_{i} c) → "))
                .collect();
            let _ = writeln!(
                o,
                "@[reducible] def mk{k}_{} : (c : {na}.{t}.C{k}) → {args}{nb}.Term .{}",
                terms::fsuffix(t),
                q(t)
            );
            for (lean, _) in cs {
                let sym = &sym_of[&(t.clone(), lean.clone())];
                let blean = &b.m.ctors[&sm.map[sym].0].lean;
                let pat: String = std::iter::once(format!(".{lean}"))
                    .chain(xs.iter().cloned())
                    .collect::<Vec<_>>()
                    .join(", ");
                let _ = writeln!(
                    o,
                    "  | {pat} => {nb}.Term.c{k} (s := .{}) .{blean}{}",
                    q(t),
                    xs.iter().map(|x| format!(" {x}")).collect::<String>()
                );
            }
        }
        let args: String = (0..*k)
            .map(|i| format!("TrTy ({na}.A{k}_{i} s c) → "))
            .collect();
        let _ = writeln!(
            o,
            "@[reducible] def mk{k} : (s : {na}.Tag) → (c : {na}.C{k} s) → {args}TrTy s"
        );
        let has: BTreeSet<&String> = sorts.iter().map(|(t, _)| t).collect();
        for t in &sa.tags {
            if !has.contains(t) {
                let _ = writeln!(o, "  | .{} => fun c => nomatch c", q(t));
            } else if into.contains(t) {
                let _ = writeln!(o, "  | .{} => mk{k}_{}", q(t), terms::fsuffix(t));
            } else {
                let us: String = (0..=*k).map(|_| " _").collect();
                let _ = writeln!(o, "  | .{} => fun{us} => ()", q(t));
            }
        }
        let _ = writeln!(o);
    }
    let sums: BTreeSet<&String> = sa.sums.iter().map(|(t, _)| t).collect();
    for (t, _) in &sa.sums {
        if !into.contains(t) {
            continue;
        }
        let _ = writeln!(
            o,
            "def mkInj_{} (l : {na}.Tag) (h : {na}.{t}.leaf l = true) (x : TrTy l) : {nb}.Term .{} := by\n  \
cases l <;> first | exact {nb}.Term.inj (s := .{}) rfl _ rfl x | exact absurd h (by decide)",
            terms::fsuffix(t),
            q(t),
            q(t)
        );
    }
    let _ = writeln!(
        o,
        "@[reducible] def mkInj : (s l : {na}.Tag) → {na}.leafOK s l = true → TrTy l → TrTy s"
    );
    for t in &sa.tags {
        if !sums.contains(t) {
            let _ = writeln!(
                o,
                "  | .{} => fun _ h _ => absurd h Bool.false_ne_true",
                q(t)
            );
        } else if into.contains(t) {
            let _ = writeln!(o, "  | .{} => mkInj_{}", q(t), terms::fsuffix(t));
        } else {
            let _ = writeln!(o, "  | .{} => fun _ _ _ => ()", q(t));
        }
    }
    // the translation
    let _ = writeln!(
        o,
        "\nmutual\ndef tr : {{s : {na}.Tag}} → {na}.Term s → TrTy s"
    );
    for t in &sa.builtins {
        let c = q(&format!("b_{t}"));
        if into.contains(t) {
            let v = if is_token(t) {
                format!("({} v)", tr_name(t))
            } else {
                "v".to_string()
            };
            let _ = writeln!(o, "  | _, .{c} v => {nb}.Term.{c} {v}");
        } else {
            let _ = writeln!(o, "  | _, .{c} _ => ()");
        }
    }
    for k in sa.enums.keys() {
        let xs: String = (0..*k).map(|i| format!(" a{i}")).collect();
        let ts: String = (0..*k).map(|i| format!(" (tr a{i})")).collect();
        let _ = writeln!(o, "  | _, @{na}.Term.c{k} s c{xs} => mk{k} s c{ts}");
    }
    for (t, _, _) in &sa.colls {
        let c = q(&format!("coll_{}", terms::fsuffix(t)));
        if into.contains(t) {
            let _ = writeln!(
                o,
                "  | _, .{c} l => {nb}.Term.{c} (trL_{} l)",
                terms::fsuffix(t)
            );
        } else {
            let _ = writeln!(o, "  | _, .{c} _ => ()");
        }
    }
    let _ = writeln!(o, "  | _, @{na}.Term.inj s _ l h a => mkInj s l h (tr a)");
    let _ = writeln!(o, "termination_by structural _ a => a");
    let elem = |e: &str, x: &str| -> String {
        if sa.builtins.contains(e) {
            if is_token(e) {
                format!("{} {x}", tr_name(e))
            } else {
                x.to_string()
            }
        } else {
            format!("tr {x}")
        }
    };
    let lty = |side: &str, e: &str, sh: &crate::terms_arity::Shape| -> String {
        if sh.builtins.contains(e) {
            format!("{side}.{e}")
        } else {
            format!("{side}.Term .{}", q(e))
        }
    };
    for (t, kind, es) in &sa.colls {
        if !into.contains(t) {
            continue;
        }
        let f = format!("trL_{}", terms::fsuffix(t));
        let (ta, tb, arm) = match kind {
            Coll::Map => (
                format!("({} × {})", lty(na, &es[0], &sa), lty(na, &es[1], &sa)),
                format!("({} × {})", lty(nb, &es[0], &sb), lty(nb, &es[1], &sb)),
                format!(
                    "(k, v) :: r => ({}, {}) :: {f} r",
                    elem(&es[0], "k"),
                    elem(&es[1], "v")
                ),
            ),
            Coll::Set => (
                format!("({} × Unit)", lty(na, &es[0], &sa)),
                format!("({} × Unit)", lty(nb, &es[0], &sb)),
                format!("(k, ()) :: r => ({}, ()) :: {f} r", elem(&es[0], "k")),
            ),
            Coll::List => (
                format!("({})", lty(na, &es[0], &sa)),
                format!("({})", lty(nb, &es[0], &sb)),
                format!("x :: r => {} :: {f} r", elem(&es[0], "x")),
            ),
        };
        let _ = writeln!(
            o,
            "def {f} : List {ta} → List {tb}\n  | [] => []\n  | {arm}\ntermination_by structural l => l"
        );
    }
    let _ = writeln!(o, "end\n");
    for (t, _, _) in universe(&a.m) {
        if covered.contains(&t) {
            let _ = writeln!(o, "def {} (a : {na}.{t}) : {nb}.{t} := tr a", tr_name(&t));
        }
    }
    // the equations of each `tr_S`, one per constructor of `S` (`rfl`), in the simp set `k2l_tr`:
    // `k2l_inv` rewrites with them `tr_S` of a constructor into `B`'s constructor of translations,
    // as unfolding `tr_S` does on a type per sort
    let _ = writeln!(
        o,
        "\n/-! The equations of the translation at each sort. -/\n"
    );
    for (t, _, k) in universe(&a.m) {
        if !covered.contains(&t) {
            continue;
        }
        let f = terms::fsuffix(&t);
        let trn = tr_name(&t);
        let mut eqns = Vec::new();
        let mut eqn = |o: &mut String, binders: String, lhs: String, rhs: String| {
            let n = format!("{trn}.eq_k{}", eqns.len());
            let _ = writeln!(
                o,
                "@[k2l_tr] theorem {n}{binders} : {trn} {lhs} = {rhs} := rfl"
            );
            eqns.push(n);
        };
        let call = |c: String, xs: &[String]| {
            if xs.is_empty() {
                c
            } else {
                format!("({c} {})", xs.join(" "))
            }
        };
        match &k {
            TyKind::Own(cs) => {
                for (sym, lean, args) in cs {
                    let blean = &b.m.ctors[&sm.map[sym].0].lean;
                    let xs: Vec<String> = (0..args.len()).map(|i| format!("x{i}")).collect();
                    let binders: String = args
                        .iter()
                        .zip(&xs)
                        .map(|(s, x)| format!(" ({x} : {na}.{s})"))
                        .collect();
                    let vs: Vec<String> =
                        args.iter().zip(&xs).map(|(s, x)| val(&a.m, s, x)).collect();
                    let rhs = call(format!("{nb}.{t}.{blean}"), &vs);
                    eqn(o, binders, call(format!("{na}.{t}.{lean}"), &xs), rhs);
                }
            }
            TyKind::Sum(ls) => {
                for (l, own) in ls {
                    let c = format!("inj_{}", names::short_sort(l));
                    eqn(
                        o,
                        format!(" (x : {na}.{own})"),
                        format!("({na}.{t}.{c} x)"),
                        format!("{nb}.{t}.{c} {}", val(&a.m, own, "x")),
                    );
                }
            }
            TyKind::Coll(..) => {
                let c = format!("«coll_{f}»");
                eqn(
                    o,
                    format!(" (l : List _)"),
                    format!("({na}.Term.{c} l)"),
                    format!("{nb}.Term.{c} (trL_{f} l)"),
                );
            }
        }
    }
    let _ = writeln!(o);
    Ok(())
}

/// names the first constructor that moves.
fn positions_kept(
    a: &Side,
    b: &Side,
    sm: &SymMap,
    covered: &BTreeSet<String>,
) -> Result<(), String> {
    let bt: BTreeMap<String, Vec<String>> = terms::block_types(&b.m)
        .into_iter()
        .map(|(t, cs)| (t, cs.into_iter().map(|c| c.name).collect()))
        .collect();
    for (t, _, k) in universe(&a.m) {
        if !covered.contains(&t) {
            continue;
        }
        let Some(bcs) = bt.get(&t) else {
            return Err(format!("{} has no type {t}", b.ns));
        };
        let images: Vec<String> = match &k {
            TyKind::Own(cs) => cs
                .iter()
                .map(|(sym, _, _)| b.m.ctors[&sm.map[sym].0].lean.clone())
                .collect(),
            TyKind::Sum(ls) => ls
                .iter()
                .map(|(l, _)| format!("inj_{}", names::short_sort(l)))
                .collect(),
            TyKind::Coll(..) => vec!["nil".into(), "cons".into()],
        };
        for (i, n) in images.iter().enumerate() {
            if bcs.get(i) != Some(n) {
                let j = bcs.iter().position(|x| x == n);
                return Err(format!(
                    "{t}: the image `{n}` of constructor {i} of {} is at position {} in {}",
                    a.ns,
                    j.map(|j| j.to_string()).unwrap_or_else(|| "none".into()),
                    b.ns
                ));
            }
        }
    }
    Ok(())
}

/// The translation function of a value of type `s`, as a term (`(fun x => x)` for a builtin).
fn tr_fn(m: &Model, s: &str) -> String {
    if is_builtin(m, s) {
        "(fun x => x)".to_string()
    } else {
        tr_name(s)
    }
}

/// The lemmas of an order-preserving translation (`positions_kept`) that the commutation lemmas
/// of functions already use: `ser (tr a) = ser a` on every covered type, injectivity, the order
/// of every key, the pointwise translation of every collection and the commutation of every
/// collection operation (`k2l_rel`), `==K`. Returns the names of the lemmas that push `tr` into
/// `ser (tr a) = ser a` in the arity-indexed universe: one theorem by structural recursion on
/// `A`'s family (each arity's case split on the sort and its enumeration, each injection's on the
/// sort and the leaf tag), and the per-sort statements as its instances. It holds when the
/// translation keeps every constructor's position in its enumeration and every leaf tag's position
/// in `Tag` (`positions_kept`), since those positions are the tags `ser` writes.
fn emit_arity_ser_tr(a: &Side, b: &Side, o: &mut String, block: &[(String, Vec<terms::LCtor>)]) {
    let (na, nb) = (&a.ns, &b.ns);
    let sa = crate::terms_arity::shape(&a.m);
    let q = |t: &str| format!("«{t}»");
    let _ = writeln!(
        o,
        "/-- `{nb}`'s serialization of a translated term of tag `s`. -/\n@[reducible] def serTr : (s : {na}.Tag) → TrTy s → List Tok"
    );
    for t in &sa.tags {
        let _ = writeln!(o, "  | .{} => fun x => {nb}.ser x", q(t));
    }
    let _ = writeln!(
        o,
        "\nmutual\ntheorem ser_tr : {{s : {na}.Tag}} → (a : {na}.Term s) → serTr s (tr a) = {na}.ser a"
    );
    for t in &sa.builtins {
        let _ = writeln!(o, "  | _, .{} _ => rfl", q(&format!("b_{t}")));
    }
    for k in sa.enums.keys() {
        let xs: String = (0..*k).map(|i| format!(" a{i}")).collect();
        if *k == 0 {
            let _ = writeln!(
                o,
                "  | _, @{na}.Term.c0 s c => by cases s <;> cases c <;> rfl"
            );
            continue;
        }
        let hs: Vec<String> = (0..*k).map(|i| format!("h{i}")).collect();
        let have: String = (0..*k)
            .map(|i| format!("have h{i} := ser_tr a{i}; "))
            .collect();
        // `A.ser` of the constructor is `c k :: c idx :: (ser a0 ++ (ser a1 ++ …))`
        let mut cat = hs.last().unwrap().clone();
        for h in hs.iter().rev().skip(1) {
            cat = format!("(congr (congrArg (· ++ ·) {h}) {cat})");
        }
        let _ = writeln!(
            o,
            "  | _, @{na}.Term.c{k} s c{xs} => by\n    {have}revert {}\n    cases s <;> cases c <;> intro {} <;> exact congrArg (List.cons _) (congrArg (List.cons _) {cat})",
            hs.join(" "),
            hs.join(" ")
        );
    }
    for (t, _, _) in &sa.colls {
        let _ = writeln!(
            o,
            "  | _, .{} l => congrArg (List.cons _) (serL_tr_{} l)",
            q(&format!("coll_{}", terms::fsuffix(t))),
            terms::fsuffix(t)
        );
    }
    let _ = writeln!(
        o,
        "  | _, @{na}.Term.inj s hs l h a => by\n    have h0 := ser_tr a\n    revert hs h h0\n    cases s <;> intro hs h h0 <;> first\n      | exact absurd hs Bool.false_ne_true\n      | (revert h h0; cases l <;> intro h h0 <;> first\n          | exact absurd h Bool.false_ne_true\n          | exact congrArg (List.cons _) (congrArg (List.cons _) h0))"
    );
    let _ = writeln!(o, "termination_by structural _ a => a");
    let in_block: BTreeSet<&String> = sa
        .tags
        .iter()
        .filter(|t| !sa.builtins.contains(*t))
        .collect();
    for (t, kind, es) in &sa.colls {
        let f = terms::fsuffix(t);
        let ser = |e: &str, x: &str, side: &str| {
            if in_block.contains(&e.to_string()) {
                if side == "b" {
                    format!("{nb}.ser (tr {x})")
                } else {
                    format!("{na}.ser {x}")
                }
            } else {
                let _ = side;
                format!("ser_{} {x}", terms::fsuffix(e))
            }
        };
        let _ = ser;
        let elem = |e: &str| {
            if in_block.contains(&e.to_string()) {
                format!("{na}.Term .{}", q(e))
            } else {
                format!("{na}.{e}")
            }
        };
        let ih = |e: &str, x: &str| {
            if in_block.contains(&e.to_string()) {
                format!("(ser_tr {x})")
            } else {
                "rfl".to_string()
            }
        };
        let (lt, arm) = match kind {
            Coll::Map => (
                format!("({} × {})", elem(&es[0]), elem(&es[1])),
                format!(
                    "(k, v) :: r => congrArg (List.cons _) (congr (congrArg (· ++ ·) {}) (congr (congrArg (· ++ ·) {}) (serL_tr_{f} r)))",
                    ih(&es[0], "k"),
                    ih(&es[1], "v")
                ),
            ),
            Coll::Set => (
                format!("({} × Unit)", elem(&es[0])),
                format!(
                    "(k, ()) :: r => congrArg (List.cons _) (congr (congrArg (· ++ ·) {}) (serL_tr_{f} r))",
                    ih(&es[0], "k")
                ),
            ),
            Coll::List => (
                format!("({})", elem(&es[0])),
                format!(
                    "x :: r => congrArg (List.cons _) (congr (congrArg (· ++ ·) {}) (serL_tr_{f} r))",
                    ih(&es[0], "x")
                ),
            ),
        };
        let _ = writeln!(
            o,
            "theorem serL_tr_{f} : (l : List {lt}) → {nb}.serL_{f} (trL_{f} l) = {na}.serL_{f} l\n  | [] => rfl\n  | {arm}\ntermination_by structural l => l"
        );
    }
    let _ = writeln!(o, "end\n");
    for (t, _) in block {
        let f = terms::fsuffix(t);
        let _ = writeln!(
            o,
            "theorem ser_tr_{f} (a : {na}.{t}) : {nb}.ser_{f} ({} a) = {na}.ser_{f} a := ser_tr a",
            tr_name(t)
        );
    }
    let _ = writeln!(o);
}

/// an operation, and of the inversions of map and list patterns.
fn emit_ordered_terms(
    a: &Side,
    b: &Side,
    o: &mut String,
    covered: &BTreeSet<String>,
    fold_names: &[String],
) -> (Vec<String>, Vec<String>, Vec<String>) {
    let (na, nb) = (&a.ns, &b.ns);
    let block: Vec<(String, Vec<terms::LCtor>)> = terms::block_types(&a.m)
        .into_iter()
        .filter(|(t, _)| covered.contains(t))
        .collect();
    let in_block: BTreeSet<&String> = block.iter().map(|(t, _)| t).collect();
    // ser (tr a) = ser a
    writeln!(
        *o,
        "\n/-! ## The translation keeps every constructor's position, so it keeps every term's serialization -/\n"
    )
    .unwrap();
    if a.arity {
        emit_arity_ser_tr(a, b, o, &block);
    } else {
        writeln!(*o, "mutual").unwrap();
        for (t, ctors) in &block {
            let f = terms::fsuffix(t);
            writeln!(
            o,
            "theorem ser_tr_{f} (a : {na}.{t}) : {nb}.ser_{f} ({} a) = {na}.ser_{f} a :=\n  match a with",
            tr_name(t)
        )
        .unwrap();
            for (i, c) in ctors.iter().enumerate() {
                let xs: Vec<String> = (0..c.args.len()).map(|j| format!("a{j}")).collect();
                if c.args.is_empty() {
                    writeln!(*o, "  | .{} => rfl", c.name).unwrap();
                    continue;
                }
                let part = |side: &str, s: &str, x: &str, translate: bool| {
                    let arg = if translate {
                        val(&a.m, s, x)
                    } else {
                        x.to_string()
                    };
                    format!("{side}.ser_{} {arg}", terms::fsuffix(s))
                };
                let join = |ps: Vec<String>| {
                    let mut body = ps.last().unwrap().clone();
                    for p in ps.iter().rev().skip(1) {
                        body = format!("({p} ++ {body})");
                    }
                    body
                };
                let lhs = join(
                    c.args
                        .iter()
                        .zip(&xs)
                        .map(|(s, x)| part(nb, s, x, true))
                        .collect(),
                );
                let rhs = join(
                    c.args
                        .iter()
                        .zip(&xs)
                        .map(|(s, x)| part(na, s, x, false))
                        .collect(),
                );
                let ih: Vec<String> = c
                    .args
                    .iter()
                    .zip(&xs)
                    .filter(|(s, _)| in_block.contains(s))
                    .map(|(s, x)| format!("ser_tr_{} {x}", terms::fsuffix(s)))
                    .collect();
                let fin = if ih.is_empty() {
                    "exact rfl".to_string()
                } else {
                    format!("rw [{}] <;> exact rfl", ih.join(", "))
                };
                writeln!(
                o,
                "  | .{} {} => by\n    show (Tok.c {i} :: {lhs} : List Tok) = Tok.c {i} :: {rhs}\n    {fin}",
                c.name,
                xs.join(" ")
            )
            .unwrap();
            }
            writeln!(*o, "  termination_by structural a").unwrap();
        }
        writeln!(*o, "end\n").unwrap();
    }
    // the collection sorts and their key types
    let colls: Vec<(String, Coll, Vec<String>)> = universe(&a.m)
        .into_iter()
        .filter(|(t, _, _)| covered.contains(t))
        .filter_map(|(t, _, k)| match k {
            TyKind::Coll(c, es) => Some((t, c, es)),
            _ => None,
        })
        .collect();
    let mut keys: BTreeSet<String> = BTreeSet::new();
    for (_, c, es) in &colls {
        if !matches!(c, Coll::List) {
            keys.insert(es[0].clone());
        }
    }
    writeln!(*o, "/-! ## Order, injectivity and the collections -/\n").unwrap();
    // injectivity of every type a value of which can be compared (`==K`, `-Map`)
    for (t, _) in &block {
        let f = terms::fsuffix(t);
        writeln!(*o, "theorem tr_inj_{f} (x y : {na}.{t}) (h : {} x = {} y) : x = y :=\n  {na}.ser_{f}_inj x y (by rw [← ser_tr_{f}, ← ser_tr_{f}, h])", tr_name(t), tr_name(t)).unwrap();
        writeln!(
            *o,
            "@[k2l_rel] theorem tr_eq_iff_{f} (x y : {na}.{t}) : {} x = {} y ↔ x = y :=\n  ⟨tr_inj_{f} x y, congrArg _⟩",
            tr_name(t),
            tr_name(t)
        )
        .unwrap();
    }
    for k in &keys {
        let f = terms::fsuffix(k);
        if is_builtin(&a.m, k) {
            writeln!(
                *o,
                "theorem pres_{f} : SAL.Pres (fun x : {na}.{k} => x) := fun _ _ => rfl"
            )
            .unwrap();
        } else if in_block.contains(k) {
            writeln!(*o, "theorem pres_{f} : SAL.Pres {} := fun x y => by\n  show {nb}.cmp_{f} ({} x) ({} y) = {na}.cmp_{f} x y\n  rw [{nb}.cmp_{f}_eq, {na}.cmp_{f}_eq, ser_tr_{f}, ser_tr_{f}]", tr_name(k), tr_name(k), tr_name(k)).unwrap();
        } else {
            // a token sort: its order is the order of its strings
            writeln!(
                *o,
                "theorem pres_{f} : SAL.Pres {} := fun _ _ => rfl",
                tr_name(k)
            )
            .unwrap();
        }
    }
    writeln!(o).unwrap();
    let mut comm: Vec<String> = Vec::new();
    // `tr (A.op x) = B.op (tr x)` lemmas, pushed inward on a configuration
    let mut push_ops: Vec<String> = Vec::new();
    let mut map_bwd: Vec<String> = Vec::new();
    let mut list_bwd: Vec<String> = Vec::new();
    // the pointwise translations first: the commutation lemmas of one collection sort use those
    // of another (`keys` of a map is a set)
    for pass in [0, 1] {
        for (t, c, es) in &colls {
            let f = terms::fsuffix(t);
            let tr = tr_name(t);
            let go = |o: &mut String, pw: &str, rhs: &str, cons: &str| {
                if pass == 1 {
                    return;
                }
                if a.arity {
                    // a collection value is `coll_T l`: the translation is `trL_T` on the list
                    let elem = |e: &str| {
                        if in_block.contains(&e.to_string()) {
                            format!("{na}.Term .«{e}»")
                        } else {
                            format!("{na}.{e}")
                        }
                    };
                    let lt = match c {
                        Coll::Map => format!("({} × {})", elem(&es[0]), elem(&es[1])),
                        Coll::Set => format!("({} × Unit)", elem(&es[0])),
                        Coll::List => format!("({})", elem(&es[0])),
                    };
                    let cons = cons
                        .replacen(".cons k v r", "(k, v) :: r", 1)
                        .replacen(".cons k r", "(k, ()) :: r", 1)
                        .replacen(".cons x r", "x :: r", 1);
                    writeln!(
                        o,
                        "theorem pw_{f} : {pw} {tr} := by\n  intro m\n  match m with\n  | .«coll_{f}» l => exact go l\nwhere\n  go : ∀ l : List {lt}, trL_{f} l = {}\n    | [] => rfl\n    | {cons}\n",
                        rhs.replacen("(ListIso.toList m)", "l", 1)
                    )
                    .unwrap();
                    return;
                }
                writeln!(
                o,
                "theorem pw_{f} : {pw} {tr} := by\n  intro m\n  exact go m\nwhere\n  go : ∀ m : {na}.{t}, ListIso.toList ({tr} m) = {rhs}\n    | .nil => rfl\n    | {cons}\n"
            )
            .unwrap();
            };
            match c {
                Coll::Map => {
                    let (tk, tv) = (tr_fn(&a.m, &es[0]), tr_fn(&a.m, &es[1]));
                    go(
                        o,
                        &format!("MapHook.Pointwise {tk} {tv}"),
                        &format!("SAL.mapPairs {tk} {tv} (ListIso.toList m)"),
                        &format!(".cons k v r => congrArg (List.cons ({tk} k, {tv} v)) (go r)"),
                    );
                    if pass == 0 {
                        continue;
                    }
                    let pk = format!("pres_{}", terms::fsuffix(&es[0]));
                    let (kt, vt) = (format!("{na}.{}", es[0]), format!("{na}.{}", es[1]));
                    for (n, stmt, proof) in [
                        (
                            "unit",
                            format!(": (MapHook.unit : {nb}.{t}) = {tr} MapHook.unit"),
                            format!("(MapHook.unit_pointwise pw_{f}).symm"),
                        ),
                        (
                            "element",
                            format!(
                                "(k : {kt}) (v : {vt}) : (MapHook.element ({tk} k) ({tv} v) : {nb}.{t}) = {tr} (MapHook.element k v)"
                            ),
                            format!("MapHook.element_pointwise pw_{f} k v"),
                        ),
                        (
                            "concat",
                            format!(
                                "(x y : {na}.{t}) : MapHook.concat ({tr} x) ({tr} y) = (MapHook.concat x y).map {tr}"
                            ),
                            format!("MapHook.concat_pointwise pw_{f} {pk} x y"),
                        ),
                        (
                            "update",
                            format!(
                                "(m : {na}.{t}) (k : {kt}) (v : {vt}) : MapHook.update ({tr} m) ({tk} k) ({tv} v) = {tr} (MapHook.update m k v)"
                            ),
                            format!("MapHook.update_pointwise_of_pres pw_{f} {pk} m k v"),
                        ),
                        (
                            "remove",
                            format!(
                                "(m : {na}.{t}) (k : {kt}) : MapHook.remove ({tr} m) ({tk} k) = {tr} (MapHook.remove m k)"
                            ),
                            format!("MapHook.remove_pointwise pw_{f} {pk} m k"),
                        ),
                        (
                            "lookup",
                            format!(
                                "(m : {na}.{t}) (k : {kt}) : MapHook.lookup ({tr} m) ({tk} k) = (MapHook.lookup m k).map {tv}"
                            ),
                            format!("MapHook.lookup_pointwise pw_{f} {pk} m k"),
                        ),
                        (
                            "lookupOrDefault",
                            format!(
                                "(m : {na}.{t}) (k : {kt}) (d : {vt}) : MapHook.lookupOrDefault ({tr} m) ({tk} k) ({tv} d) = {tv} (MapHook.lookupOrDefault m k d)"
                            ),
                            format!("MapHook.lookupOrDefault_pointwise pw_{f} {pk} m k d"),
                        ),
                        (
                            "inKeys",
                            format!(
                                "(m : {na}.{t}) (k : {kt}) : MapHook.inKeys ({tk} k) ({tr} m) = MapHook.inKeys k m"
                            ),
                            format!("MapHook.inKeys_pointwise pw_{f} {pk} m k"),
                        ),
                        (
                            "size",
                            format!("(m : {na}.{t}) : MapHook.size ({tr} m) = MapHook.size m"),
                            format!("MapHook.size_pointwise pw_{f} m"),
                        ),
                        (
                            "wfb",
                            format!("(m : {na}.{t}) : MapHook.wfb ({tr} m) = MapHook.wfb m"),
                            format!("MapHook.wfb_pointwise pw_{f} {pk} m"),
                        ),
                    ] {
                        writeln!(*o, "@[k2l_rel] theorem comm_{n}_{f} {stmt} :=\n  {proof}")
                            .unwrap();
                        comm.push(format!("comm_{n}_{f}"));
                        if matches!(n, "unit" | "element" | "update" | "remove") {
                            push_ops.push(format!("comm_{n}_{f}"));
                        }
                    }
                    if in_block.contains(&es[1]) {
                        let vf = terms::fsuffix(&es[1]);
                        writeln!(*o, "@[k2l_rel] theorem comm_difference_{f} (x y : {na}.{t}) : MapHook.difference ({tr} x) ({tr} y) = {tr} (MapHook.difference x y) :=\n  MapHook.difference_pointwise pw_{f} {pk} tr_inj_{vf} x y").unwrap();
                        push_ops.push(format!("comm_difference_{f}"));
                    }
                    // keys into each set sort, values and keys_list into each list sort, of the
                    // matching element type
                    for (t2, c2, es2) in &colls {
                        let f2 = terms::fsuffix(t2);
                        let tr2 = tr_name(t2);
                        match c2 {
                            Coll::Set if es2[0] == es[0] => {
                                writeln!(*o, "@[k2l_rel] theorem comm_keys_{f}_{f2} (m : {na}.{t}) : (MapHook.keys ({tr} m) : {nb}.{t2}) = {tr2} (MapHook.keys m) :=\n  MapHook.keys_pointwise pw_{f} pw_{f2} m").unwrap();
                                push_ops.push(format!("comm_keys_{f}_{f2}"));
                            }
                            Coll::List if es2[0] == es[1] => {
                                writeln!(*o, "@[k2l_rel] theorem comm_values_{f}_{f2} (m : {na}.{t}) : (MapHook.values ({tr} m) : {nb}.{t2}) = {tr2} (MapHook.values m) :=\n  MapHook.values_pointwise pw_{f} pw_{f2} m").unwrap();
                                push_ops.push(format!("comm_values_{f}_{f2}"));
                            }
                            _ => {}
                        }
                        if matches!(c2, Coll::List) && es2[0] == es[0] {
                            writeln!(*o, "@[k2l_rel] theorem comm_keysList_{f}_{f2} (m : {na}.{t}) : (MapHook.keysList ({tr} m) : {nb}.{t2}) = {tr2} (MapHook.keysList m) :=\n  MapHook.keysList_pointwise pw_{f} pw_{f2} m").unwrap();
                            push_ops.push(format!("comm_keysList_{f}_{f2}"));
                        }
                    }
                    writeln!(*o, "theorem map_bwd_{f} {{k' : {nb}.{}}} {{v' : {nb}.{}}} {{r' : {nb}.{t}}} {{m : {na}.{t}}}\n    (h : MapHook.concat (MapHook.element k' v') r' = some ({tr} m)) :\n    ∃ k v r, k' = {tk} k ∧ v' = {tv} v ∧ r' = {tr} r ∧ MapHook.concat (MapHook.element k v) r = some m :=\n  MapHook.concat_element_pointwise_inv_free pw_{f} {pk} h\n", es[0], es[1]).unwrap();
                    map_bwd.push(format!("map_bwd_{f}"));
                }
                Coll::Set => {
                    let tk = tr_fn(&a.m, &es[0]);
                    go(
                        o,
                        &format!("MapHook.Pointwise {tk} (fun u => u)"),
                        &format!("SAL.mapPairs {tk} (fun u => u) (ListIso.toList m)"),
                        &format!(".cons k r => congrArg (List.cons ({tk} k, ())) (go r)"),
                    );
                    if pass == 0 {
                        continue;
                    }
                    let pk = format!("pres_{}", terms::fsuffix(&es[0]));
                    let kt = format!("{na}.{}", es[0]);
                    for (n, stmt, proof) in [
                        (
                            "munit",
                            format!(": (MapHook.unit : {nb}.{t}) = {tr} MapHook.unit"),
                            format!("(MapHook.unit_pointwise pw_{f}).symm"),
                        ),
                        (
                            "melement",
                            format!(
                                "(k : {kt}) (v : Unit) : (MapHook.element ({tk} k) v : {nb}.{t}) = {tr} (MapHook.element k v)"
                            ),
                            format!("MapHook.element_pointwise pw_{f} k v"),
                        ),
                        (
                            "mconcat",
                            format!(
                                "(x y : {na}.{t}) : MapHook.concat ({tr} x) ({tr} y) = (MapHook.concat x y).map {tr}"
                            ),
                            format!("MapHook.concat_pointwise pw_{f} {pk} x y"),
                        ),
                        (
                            "unit",
                            format!(": (SetHook.unit : {nb}.{t}) = {tr} SetHook.unit"),
                            format!("(SetHook.unit_pointwise pw_{f}).symm"),
                        ),
                        (
                            "element",
                            format!(
                                "(k : {kt}) : (SetHook.element ({tk} k) : {nb}.{t}) = {tr} (SetHook.element k)"
                            ),
                            format!("SetHook.element_pointwise pw_{f} k"),
                        ),
                        (
                            "concat",
                            format!(
                                "(x y : {na}.{t}) : SetHook.concat ({tr} x) ({tr} y) = (SetHook.concat x y).map {tr}"
                            ),
                            format!("SetHook.concat_pointwise pw_{f} {pk} x y"),
                        ),
                        (
                            "inSet",
                            format!(
                                "(s : {na}.{t}) (k : {kt}) : SetHook.inSet ({tk} k) ({tr} s) = SetHook.inSet k s"
                            ),
                            format!("SetHook.inSet_pointwise pw_{f} {pk} s k"),
                        ),
                        (
                            "difference",
                            format!(
                                "(x y : {na}.{t}) : SetHook.difference ({tr} x) ({tr} y) = {tr} (SetHook.difference x y)"
                            ),
                            format!("SetHook.difference_pointwise pw_{f} {pk} x y"),
                        ),
                        (
                            "size",
                            format!("(s : {na}.{t}) : SetHook.size ({tr} s) = SetHook.size s"),
                            format!("SetHook.size_pointwise pw_{f} s"),
                        ),
                        (
                            "wfb",
                            format!("(m : {na}.{t}) : MapHook.wfb ({tr} m) = MapHook.wfb m"),
                            format!("MapHook.wfb_pointwise pw_{f} {pk} m"),
                        ),
                    ] {
                        writeln!(*o, "@[k2l_rel] theorem comm_{n}_{f} {stmt} :=\n  {proof}")
                            .unwrap();
                        comm.push(format!("comm_{n}_{f}"));
                        if matches!(n, "munit" | "melement" | "unit" | "element" | "difference") {
                            push_ops.push(format!("comm_{n}_{f}"));
                        }
                    }
                    writeln!(*o, "theorem map_bwd_{f} {{k' : {nb}.{}}} {{v' : Unit}} {{r' : {nb}.{t}}} {{m : {na}.{t}}}\n    (h : MapHook.concat (MapHook.element k' v') r' = some ({tr} m)) :\n    ∃ k v r, k' = {tk} k ∧ v' = v ∧ r' = {tr} r ∧ MapHook.concat (MapHook.element k v) r = some m :=\n  MapHook.concat_element_pointwise_inv_free pw_{f} {pk} h\n", es[0]).unwrap();
                    map_bwd.push(format!("map_bwd_{f}"));
                }
                Coll::List => {
                    let te = tr_fn(&a.m, &es[0]);
                    go(
                        o,
                        &format!("ListHook.Pointwise {te}"),
                        &format!("(ListIso.toList m).map {te}"),
                        &format!(".cons x r => congrArg (List.cons ({te} x)) (go r)"),
                    );
                    if pass == 0 {
                        continue;
                    }
                    let et = format!("{na}.{}", es[0]);
                    for (n, stmt, proof) in [
                        (
                            "unit",
                            format!(": (ListHook.unit : {nb}.{t}) = {tr} ListHook.unit"),
                            format!("(ListHook.unit_pointwise pw_{f}).symm"),
                        ),
                        (
                            "element",
                            format!(
                                "(x : {et}) : (ListHook.element ({te} x) : {nb}.{t}) = {tr} (ListHook.element x)"
                            ),
                            format!("ListHook.element_pointwise pw_{f} x"),
                        ),
                        (
                            "concat",
                            format!(
                                "(x y : {na}.{t}) : ListHook.concat ({tr} x) ({tr} y) = {tr} (ListHook.concat x y)"
                            ),
                            format!("ListHook.concat_pointwise pw_{f} x y"),
                        ),
                        (
                            "size",
                            format!("(l : {na}.{t}) : ListHook.size ({tr} l) = ListHook.size l"),
                            format!("ListHook.size_pointwise pw_{f} l"),
                        ),
                    ] {
                        writeln!(*o, "@[k2l_rel] theorem comm_{n}_{f} {stmt} :=\n  {proof}")
                            .unwrap();
                        comm.push(format!("comm_{n}_{f}"));
                        if matches!(n, "unit" | "element" | "concat") {
                            push_ops.push(format!("comm_{n}_{f}"));
                        }
                    }
                    writeln!(*o, "theorem list_bwd_{f} {{x' : {nb}.{}}} {{t' l' : {nb}.{t}}} {{l : {na}.{t}}} (h : ListHook.concat (ListHook.element x') t' = {tr} l) :\n    ∃ x t, x' = {te} x ∧ t' = {tr} t ∧ ListHook.concat (ListHook.element x) t = l :=\n  ListHook.concat_element_pointwise_inv pw_{f} h\n", es[0]).unwrap();
                    writeln!(*o, "theorem list_bwd_back_{f} {{x' : {nb}.{}}} {{t' : {nb}.{t}}} {{l : {na}.{t}}} (h : ListHook.concat t' (ListHook.element x') = {tr} l) :\n    ∃ x t, x' = {te} x ∧ t' = {tr} t ∧ ListHook.concat t (ListHook.element x) = l :=\n  ListHook.concat_element_pointwise_inv_back pw_{f} h\n", es[0]).unwrap();
                    list_bwd.push(format!("list_bwd_{f}"));
                    list_bwd.push(format!("list_bwd_back_{f}"));
                }
            }
            writeln!(o).unwrap();
        }
    }
    // `==K` and `=/=K` on the types compared in rules
    for t in ["SortK", "SortKItem"] {
        if in_block.contains(&t.to_string()) {
            writeln!(*o, "@[k2l_rel] theorem comm_keq_{t} (x y : {na}.{t}) : KEqHook.eq ({} x) ({} y) = KEqHook.eq x y :=\n  KEqHook.eq_of_injective (tr_inj_{t}) x y", tr_name(t), tr_name(t)).unwrap();
            writeln!(*o, "@[k2l_rel] theorem comm_kne_{t} (x y : {na}.{t}) : KEqHook.ne ({} x) ({} y) = KEqHook.ne x y :=\n  KEqHook.ne_of_injective (tr_inj_{t}) x y\n", tr_name(t), tr_name(t)).unwrap();
        }
    }
    // pushing `tr` into constructors, injections and collection operations, and the proof of the
    // commutation of a recursive function (`comm_rec [A.f, B.f, …] [its lemma, …]`)
    let push: Vec<String> = fold_names
        .iter()
        .chain(inj_fold_names(a, b, covered).iter())
        .chain(push_ops.iter())
        .map(|n| format!("← {n}"))
        .collect();
    writeln!(o, "set_option hygiene false in\n/-- Push `tr` into constructors, injections and collection operations, in the goal and the hypotheses. -/\nlocal macro \"push_ctor\" : tactic => `(tactic| simp only [{}] at *)\n", push.join(", ")).unwrap();
    writeln!(o, "set_option hygiene false in\n/-- `B.f (tr x…) = (A.f x…).map tr` for a recursive `f`, after unfolding both once: case the parameters generalized (so that a split keeps `x = pattern`, which the termination proof reads), split `A`'s cascade and `B`'s (inverting `tr x = pattern`, pushing `tr` in, so that both reduce), rewrite `B`'s calls by the group's lemmas (`ls`, the induction; `rw`, not under binders), in rounds, since a call on the result of another (`f (f x y) z`) is a translation only once the inner call's value is identified; then identify the values, or refute a case where one cascade falls through a pattern that the other's translated scrutinee matches. -/\nlocal macro \"comm_rec\" \"[\" ls:ident,* \"]\" : tactic => do\n  let rw ← ls.getElems.foldlM (fun acc l => `(tactic| first | rw [$l:ident] at * | $acc:tactic)) (← `(tactic| fail))\n  `(tactic| (\n  symm\n  repeat' (first | (split <;> (try k2l_inv) <;> (try push_ctor)) | (k2l_split_hyps <;> (try k2l_inv) <;> (try push_ctor)))\n  all_goals (try simp only [k2l_rel] at *)\n  all_goals (repeat ($rw:tactic))\n  all_goals (iterate 4 ((try subst_vars); (try simp only [Option.some.injEq, Option.map_some, Option.map_none, reduceCtorEq] at *)))\n  all_goals (first\n    | (simp_all [k2l_rel]; done)\n    | (exfalso; solve_by_elim; done)\n    | (iterate 2 ((try simp only [@eq_comm _ none] at *); (try simp_all only [Option.some.injEq, Option.map_some, Option.map_none, reduceCtorEq]); (repeat ($rw:tactic)); (try subst_vars))\n       first | (simp_all [k2l_rel]; done) | (exfalso; solve_by_elim; done) | (simp_all; subst_vars; simp_all [k2l_rel]))\n    | (simp_all; subst_vars; simp_all [k2l_rel]))))\n").unwrap();
    (push_ops, map_bwd, list_bwd)
}

/// The constructor of `B`'s rule applied for a step of `A`'s: its variables are the translations
/// of `A`'s, position by position, when the two constructors have the same variables (the rules
/// correspond by their KORE text, so they lower to the same steps); its hypotheses, and the
/// priority hypothesis `hpri`, are left as goals. Otherwise `apply`, which finds the variables by
/// unification; a variable fixed only by a hypothesis (the key of a free-key match) then needs
/// the explicit form.
fn fwd_ctor(
    m: &Model,
    ctor: &str,
    ra: &crate::render::Rel,
    rb: &crate::render::Rel,
    hpri: bool,
) -> String {
    let same = ra.binders.len() == rb.binders.len()
        && ra.hyps.len() == rb.hyps.len()
        && ra
            .binders
            .iter()
            .zip(&rb.binders)
            .all(|((_, s), (_, t))| s == t);
    if !same {
        return format!("apply {ctor}");
    }
    // a set pattern's value is `()` (`Unit`, no translation)
    let mut args: Vec<String> = ra
        .binders
        .iter()
        .map(|(x, s)| if s == "Unit" { x.clone() } else { val(m, s, x) })
        .collect();
    args.extend(std::iter::repeat_n(
        "?_".to_string(),
        ra.hyps.len() + usize::from(hpri),
    ));
    format!("refine {ctor} {}", args.join(" "))
}

/// One simulation lemma per pair of corresponding rules (`--per-rule`), stated with the libraries'
/// per-rule principle for relations (`Step.Rel.r`, `Preserves.lean`): `fwd.r`, a step of `A` by
/// `r` is translated to a step of `B` by its counterpart, and `bwd.r`, a step of `B` by `r` from a
/// translation is the translation of a step of `A`. They are the arms of `forward` and
/// `backward`, proved alike (no priority ranks).
fn emit_per_rule(
    o: &mut String,
    a: &Side,
    b: &Side,
    trt: &str,
    pairs: &[(usize, usize)],
    back_of: &BTreeMap<usize, usize>,
    bwd_hyps: &dyn Fn(&mut String, &Rule, &crate::render::Rel),
) {
    let (na, nb) = (&a.ns, &b.ns);
    let intro = |xs: Vec<String>| {
        if xs.is_empty() {
            String::new()
        } else {
            format!("    intro {}\n", xs.join(" "))
        }
    };
    let mut names = Vec::new();
    writeln!(
        o,
        "/-! ## Forward: a step of `{na}` by a rule with a counterpart is a step of `{nb}` -/\n"
    )
    .unwrap();
    for (i, j) in pairs {
        let (ra, rb) = (&a.rules[*i], &b.rules[*j]);
        writeln!(
            o,
            "theorem fwd.{} : {na}.Step.Rel.{} (fun c c' => {nb}.Step ({trt} c) ({trt} c')) := by\n{}    show {nb}.Step _ _\n    push_tr\n    {}\n    all_goals hyp_fwd\n",
            ra.lean,
            ra.lean,
            intro(rules::ctor_args(&ra.step)),
            fwd_ctor(&a.m, &format!("{nb}.Step.{}", rb.lean), &ra.step, &rb.step, false)
        )
        .unwrap();
        names.push(format!("fwd.{}", ra.lean));
    }
    writeln!(o, "/-! ## Backward: a step of `{nb}` from a translation by a rule with a counterpart is the translation of a step of `{na}` -/\n").unwrap();
    for (j, rb) in b.rules.iter().enumerate() {
        let Some(i) = back_of.get(&j) else { continue };
        let mut xs = rules::ctor_args(&rb.step);
        xs.extend(["c".to_string(), "hd".to_string()]);
        writeln!(
            o,
            "theorem bwd.{} : {nb}.Step.Rel.{} (fun d d' => ∀ c, {trt} c = d → ∃ c', {na}.Step c c' ∧ d' = {trt} c') := by\n{}    k2l_inv",
            rb.lean,
            rb.lean,
            intro(xs)
        )
        .unwrap();
        bwd_hyps(o, rb, &rb.step);
        writeln!(
            o,
            "    all_goals exact ⟨_, by apply {na}.Step.{} <;> hyp_bwd, by fin_bwd⟩\n",
            a.rules[*i].lean
        )
        .unwrap();
        names.push(format!("bwd.{}", rb.lean));
    }
    writeln!(o, "#k2l_assert_axioms {}\n", names.join(" ")).unwrap();
}

/// The folding lemmas of the injections that both libraries have, on the covered sorts.
fn inj_fold_names(a: &Side, b: &Side, covered: &BTreeSet<String>) -> Vec<String> {
    let pairs_b: BTreeSet<(String, String)> = terms::inj_pairs(&b.m).into_iter().collect();
    terms::inj_pairs(&a.m)
        .into_iter()
        .filter(|(x, y)| {
            pairs_b.contains(&(x.clone(), y.clone()))
                && covered.contains(y)
                && (is_builtin(&a.m, x)
                    || covered.contains(x)
                    || matches!(a.m.sorts[x].kind, Kind::Token))
        })
        .map(|(x, y)| {
            format!(
                "fold_inj_{}_{}",
                names::short_sort(&x),
                names::short_sort(&y)
            )
        })
        .collect()
}

/// The bisimulation for a translation that keeps every constructor's position (`positions_kept`):
/// `Inv` is `True`; map keys need no restriction, since `tr` preserves the serialization and so
/// the order of every term; every collection operation commutes with `tr`; priorities are
/// respected rank by rank (`hpri` of a step corresponds through `app_bwd`, `app_fwd`); a free-key
/// map pattern (a match per binding) is inverted through the translated map's bindings.
#[allow(clippy::too_many_arguments)]
fn emit_ordered(
    a: &Side,
    b: &Side,
    ns: &str,
    mut o: String,
    covered: &BTreeSet<String>,
    pairs: &[(usize, usize)],
    unmatched_b: &[usize],
    refined: &BTreeMap<usize, Vec<String>>,
    fold_names: &[String],
    pure_fns: &[String],
    (push_ops, map_bwd, list_bwd): (Vec<String>, Vec<String>, Vec<String>),
    per_rule: bool,
) -> Result<String, String> {
    let (na, nb) = (&a.ns, &b.ns);
    if !refined.is_empty() {
        return Err(format!(
            "rules of {nb} that refine a rule of {na} to a subsort ({}) need a value invariant, which is generated only when the translation moves a constructor",
            refined
                .keys()
                .map(|i| rules::display_name(&a.rules[*i]))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    let top = rules::top_sort(&a.def)?;
    let trt = tr_name(&top);
    let inj_names = inj_fold_names(a, b, covered);
    let push = fold_names
        .iter()
        .chain(inj_names.iter())
        .chain(push_ops.iter())
        .chain(pure_fns.iter())
        .map(|n| format!("← {n}"))
        .collect::<Vec<_>>()
        .join(", ");
    writeln!(o, "/-! ## The invariant -/\n").unwrap();
    writeln!(o, "/-- No restriction: the translation preserves the order of every term, so it commutes with every map operation on every configuration. -/\ndef Inv (_ : {na}.{top}) : Prop := True\n").unwrap();
    writeln!(o, "theorem inv_step {{c c' : {na}.{top}}} (_ : Inv c) (_ : {na}.Step c c') : Inv c' := trivial\n").unwrap();
    writeln!(o, "set_option hygiene false in\n/-- Push `tr` into a configuration (`tr`'s equations, injections, collection operations, total functions). -/\nlocal macro \"push_tr\" : tactic => `(tactic| simp only [{push}])\n").unwrap();
    writeln!(o, "set_option hygiene false in\n/-- Close `d = tr c'` after a backward step. -/\nlocal macro \"fin_bwd\" : tactic => `(tactic| first | rfl | (simp only [k2l_rel]; done) | (simp only [k2l_rel] at * <;> simp_all <;> done))\n").unwrap();
    writeln!(
        o,
        "/-- Hypotheses of `{nb}`'s rules from those of `{na}`'s, and back. -/"
    )
    .unwrap();
    writeln!(o, "local macro \"hyp_fwd\" : tactic => `(tactic| first\n  | assumption\n  | rfl\n  | (simp only [k2l_rel, *]; done)\n  | (simp only [k2l_rel] <;> assumption)\n  | (simp only [k2l_rel, *] <;> rfl)\n  | (simp only [k2l_rel] at * <;> simp_all <;> done))\n").unwrap();
    writeln!(o, "local macro \"hyp_bwd\" : tactic => `(tactic| first\n  | assumption\n  | rfl\n  | (simp only [k2l_rel] at * <;> assumption)\n  | (simp only [k2l_rel] at * <;> simp_all <;> done))\n").unwrap();
    let alts = |names: &[String], pat: &str| -> String {
        if names.is_empty() {
            return "fail".to_string();
        }
        names
            .iter()
            .map(|n| format!("(obtain {pat} := {n} $h)"))
            .collect::<Vec<_>>()
            .join(" | ")
    };
    writeln!(o, "set_option hygiene false in\n/-- A map pattern of `{nb}` on a translated map is the translation of a match: its key, value and rest are translations. -/\nlocal macro \"map_bwd\" h:ident : tactic => `(tactic| first | {})\n", alts(&map_bwd, "⟨_, _, _, _, _, _, _⟩")).unwrap();
    writeln!(o, "set_option hygiene false in\n/-- A list pattern of `{nb}` on a translated list. -/\nlocal macro \"list_bwd\" h:ident : tactic => `(tactic| first | {})\n", alts(&list_bwd, "⟨_, _, _, _, _⟩")).unwrap();
    writeln!(o, "set_option hygiene false in\n/-- A partial operation of `{nb}` defined on translations is the translation of `{na}`'s. -/\nlocal macro \"bind_bwd\" h:ident : tactic => `(tactic| first | (simp only [k2l_rel, Option.map_eq_some_iff] at $h:ident; obtain ⟨_, _, rfl⟩ := $h:ident) | skip)\n").unwrap();
    let (jb, ja) = if a.ranked {
        ("{j : Nat} ", " j")
    } else {
        ("", "")
    };
    let is_map_hyp = |hp: &str| hp.starts_with("KPrelude.MapHook.concat (KPrelude.MapHook.element");
    let is_list_hyp =
        |hp: &str| hp.starts_with("KPrelude.ListHook.concat") && !hp.contains("= some");
    let back_of: BTreeMap<usize, usize> = pairs.iter().map(|(i, j)| (*j, *i)).collect();
    let bwd_hyps = |o: &mut String, rb: &Rule, rel: &crate::render::Rel| {
        let lhs: BTreeSet<&String> = rb.app.hyps.iter().map(|(h, _)| h).collect();
        for (hn, hp) in &rel.hyps {
            if lhs.contains(hn) && is_map_hyp(hp) {
                writeln!(o, "    all_goals map_bwd {hn}\n    all_goals k2l_inv").unwrap();
            } else if lhs.contains(hn) && is_list_hyp(hp) {
                writeln!(o, "    all_goals list_bwd {hn}\n    all_goals k2l_inv").unwrap();
            } else if hp.contains("= some") {
                writeln!(o, "    all_goals bind_bwd {hn}").unwrap();
            }
        }
    };
    if per_rule {
        emit_per_rule(&mut o, a, b, &trt, pairs, &back_of, &bwd_hyps);
        writeln!(o, "end {ns}").unwrap();
        return Ok(o);
    }
    // app_fwd, app_bwd (the priority hypotheses of the steps use them)
    writeln!(o, "/-! ## A rule applies in `{na}` exactly when its counterpart applies in `{nb}` (so undefined and stuck configurations correspond too) -/\n").unwrap();
    writeln!(o, "theorem app_fwd {jb}{{c : {na}.{top}}} (hi : Inv c) (h : {na}.App{ja} c) : {nb}.App{ja} ({trt} c) := by\n  cases h with").unwrap();
    for (i, j) in pairs {
        let (ra, rb) = (&a.rules[*i], &b.rules[*j]);
        writeln!(
            o,
            "  | {} {} =>\n    push_tr\n    {}\n    all_goals hyp_fwd",
            ra.lean,
            rules::ctor_args(&ra.app).join(" "),
            fwd_ctor(
                &a.m,
                &format!("{nb}.App.{}", rb.lean),
                &ra.app,
                &rb.app,
                false
            )
        )
        .unwrap();
    }
    writeln!(o).unwrap();
    writeln!(o, "theorem app_bwd {jb}{{c : {na}.{top}}} (hi : Inv c) (h : {nb}.App{ja} ({trt} c)) : {na}.App{ja} c := by\n  generalize hd : {trt} c = d0 at h\n  cases h with").unwrap();
    for (j, rb) in b.rules.iter().enumerate() {
        writeln!(
            o,
            "  | {} {} =>\n    k2l_inv",
            rb.lean,
            rules::ctor_args(&rb.app).join(" ")
        )
        .unwrap();
        let Some(i) = back_of.get(&j) else { continue };
        bwd_hyps(&mut o, rb, &rb.app);
        writeln!(
            o,
            "    all_goals (apply {na}.App.{} <;> hyp_bwd)",
            a.rules[*i].lean
        )
        .unwrap();
    }
    writeln!(o).unwrap();
    // forward, backward
    writeln!(
        o,
        "/-! ## Forward simulation: every step of `{na}` is a step of `{nb}` -/\n"
    )
    .unwrap();
    writeln!(o, "set_option hygiene false in\n/-- The priority hypothesis of a step of `{nb}` from that of `{na}`. -/\nlocal macro \"hpri_fwd\" : tactic => `(tactic| (intro j hj hb; exact hpri j hj (app_bwd trivial (by simpa only [k2l_rel] using hb))))\n").unwrap();
    writeln!(o, "set_option hygiene false in\n/-- The priority hypothesis of a step of `{na}` from that of `{nb}`. -/\nlocal macro \"hpri_bwd\" : tactic => `(tactic| (intro j hj ha; exact hpri j hj (by simpa only [{push}] using app_fwd trivial ha)))\n").unwrap();
    let hpri_arg = |side: &Side, r: &Rule| {
        if side.ranked && side.rank(r) > 0 {
            " hpri"
        } else {
            ""
        }
    };
    writeln!(o, "theorem forward {{c c' : {na}.{top}}} (hi : Inv c) (h : {na}.Step c c') : {nb}.Step ({trt} c) ({trt} c') := by\n  cases h with").unwrap();
    for (i, j) in pairs {
        let (ra, rb) = (&a.rules[*i], &b.rules[*j]);
        writeln!(
            o,
            "  | {} {}{} =>\n    push_tr\n    {}\n    all_goals first | hpri_fwd | hyp_fwd",
            ra.lean,
            rules::ctor_args(&ra.step).join(" "),
            hpri_arg(a, ra),
            fwd_ctor(
                &a.m,
                &format!("{nb}.Step.{}", rb.lean),
                &ra.step,
                &rb.step,
                !hpri_arg(b, rb).is_empty()
            )
        )
        .unwrap();
    }
    writeln!(o).unwrap();
    writeln!(o, "/-! ## Backward simulation: every step of `{nb}` from a translation is the translation of a step of `{na}` -/\n").unwrap();
    writeln!(o, "theorem backward {{c : {na}.{top}}} {{d : {nb}.{top}}} (hi : Inv c) (h : {nb}.Step ({trt} c) d) :\n    ∃ c', {na}.Step c c' ∧ d = {trt} c' := by\n  generalize hd : {trt} c = d0 at h\n  cases h with").unwrap();
    for (j, rb) in b.rules.iter().enumerate() {
        writeln!(
            o,
            "  | {} {}{} =>\n    k2l_inv",
            rb.lean,
            rules::ctor_args(&rb.step).join(" "),
            hpri_arg(b, rb)
        )
        .unwrap();
        let Some(i) = back_of.get(&j) else {
            assert!(unmatched_b.contains(&j));
            continue;
        };
        bwd_hyps(&mut o, rb, &rb.step);
        writeln!(o, "    all_goals exact ⟨_, by apply {na}.Step.{} <;> first | hpri_bwd | hyp_bwd, by fin_bwd⟩", a.rules[*i].lean).unwrap();
    }
    writeln!(o).unwrap();
    // the bisimulation and its corollaries: the statements of the other regime
    writeln!(o, "/-! ## The bisimulation -/\n").unwrap();
    writeln!(o, "/-- A configuration of `{na}` satisfying `Inv`, and its translation. -/\ndef R (c : {na}.{top}) (d : {nb}.{top}) : Prop := Inv c ∧ d = {trt} c\n").unwrap();
    writeln!(
        o,
        "theorem bisim : Bisimulation {na}.Step {nb}.Step R where\n  fwd := by\n    rintro c d c' ⟨hi, rfl⟩ h\n    exact ⟨_, forward hi h, inv_step hi h, rfl⟩\n  bwd := by\n    rintro c d d' ⟨hi, rfl⟩ h\n    obtain ⟨c', hc, rfl⟩ := backward hi h\n    exact ⟨c', hc, inv_step hi hc, rfl⟩\n"
    )
    .unwrap();
    writeln!(
        o,
        "/-- Runs of `n` steps correspond, and so do terminal configurations (stuck or undefined). -/\ntheorem stepsN_iff {{n : Nat}} {{c : {na}.{top}}} (hi : Inv c) :\n    (∃ c', StepsN {na}.Step n c c') ↔ (∃ d', StepsN {nb}.Step n ({trt} c) d') := by\n  constructor\n  · rintro ⟨c', h⟩; obtain ⟨d', hd, -⟩ := bisim.stepsN_fwd ⟨hi, rfl⟩ h; exact ⟨d', hd⟩\n  · rintro ⟨d', h⟩; obtain ⟨c', hc, -⟩ := bisim.stepsN_bwd ⟨hi, rfl⟩ h; exact ⟨c', hc⟩\n"
    )
    .unwrap();
    writeln!(
        o,
        "theorem terminal_iff {{c : {na}.{top}}} (hi : Inv c) :\n    (∀ c', ¬ {na}.Step c c') ↔ (∀ d, ¬ {nb}.Step ({trt} c) d) :=\n  bisim.terminal_iff ⟨hi, rfl⟩\n\ntheorem app_iff {jb}{{c : {na}.{top}}} (hi : Inv c) : {na}.App{ja} c ↔ {nb}.App{ja} ({trt} c) := ⟨app_fwd hi, app_bwd hi⟩\n"
    )
    .unwrap();
    writeln!(
        o,
        "/-- Every run of `{na}` from a configuration satisfying `Inv` is, translated, a run of `{nb}` of the same length, and its last configuration is terminal in one exactly when it is in the other. -/\ntheorem run_agree {{n : Nat}} {{c c' : {na}.{top}}} (hi : Inv c) (h : StepsN {na}.Step n c c') :\n    StepsN {nb}.Step n ({trt} c) ({trt} c') ∧ ((∀ x, ¬ {na}.Step c' x) ↔ (∀ y, ¬ {nb}.Step ({trt} c') y)) := by\n  obtain ⟨d', hd, hi', rfl⟩ := bisim.stepsN_fwd ⟨hi, rfl⟩ h\n  exact ⟨hd, terminal_iff hi'⟩\n"
    )
    .unwrap();
    writeln!(o, "#k2l_assert_axioms inv_step forward backward app_fwd app_bwd bisim stepsN_iff terminal_iff app_iff run_agree\n").unwrap();
    writeln!(o, "end {ns}").unwrap();
    Ok(o)
}
