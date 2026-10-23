//! `survey`: counts of a compiled definition (sorts, constructors, rules, functions, hooks), the
//! constructs the generator refuses and how often, and a readable dump of the rewrite rules.
//!
//! The counts come from the KORE declarations and axioms; the refusals come from running the
//! generator's own lowering on every rewrite rule and every function equation, so they are the
//! errors `gen` would report, collected instead of stopping at the first.

use crate::funcs;
use crate::hooks;
use crate::ir::{Def, P};
use crate::lower::{FnSig, Fns, Lower};
use crate::model::{Kind, Model, sort_name};
use crate::names;
use std::collections::{BTreeMap, BTreeSet};

/// A compact, K-like rendering of a pattern (labels demangled, injections elided).
pub fn show(p: &P, m: Option<&Model>) -> String {
    match p {
        P::Var(v, s) => format!(
            "{}:{}",
            names::demangle(v).trim_start_matches("Var"),
            names::short_sort(&s.to_string()).trim_end_matches("{}")
        ),
        P::SetVar(v, _) => format!("@{}", names::demangle(v)),
        P::Dv(_, v) => format!("{v:?}"),
        P::Str(s) => format!("{s:?}"),
        P::App(f, _, args) if f == "inj" => show(&args[0], m),
        P::App(f, _, args) if f == "kseq" => {
            format!("{} ~> {}", show(&args[0], m), show(&args[1], m))
        }
        P::App(f, _, _) if f == "dotk" => ".K".into(),
        P::App(f, _, args) => {
            let l = names::demangle(f);
            let l = m
                .and_then(|m| m.ctors.get(f))
                .and_then(|c| names::short_label(&l, &c.sort, &c.args))
                .unwrap_or(l);
            if args.is_empty() {
                l
            } else {
                format!(
                    "{l}({})",
                    args.iter()
                        .map(|a| show(a, m))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
        P::Top(_) => "⊤".into(),
        P::Bottom(_) => "⊥".into(),
        P::And(_, ps) => ps
            .iter()
            .map(|a| show(a, m))
            .collect::<Vec<_>>()
            .join(" ∧ "),
        P::Or(_, ps) => format!(
            "({})",
            ps.iter()
                .map(|a| show(a, m))
                .collect::<Vec<_>>()
                .join(" ∨ ")
        ),
        P::Not(_, a) => format!("¬({})", show(a, m)),
        P::Implies(_, a, b) => format!("({} → {})", show(a, m), show(b, m)),
        P::Iff(_, a, b) => format!("({} ↔ {})", show(a, m), show(b, m)),
        P::Rewrites(_, a, b) => format!("{}\n  => {}", show(a, m), show(b, m)),
        P::Exists(_, v, _, b) => format!("∃{}. {}", names::demangle(v), show(b, m)),
        P::Forall(_, v, _, b) => format!("∀{}. {}", names::demangle(v), show(b, m)),
        P::Ceil(_, _, a) => format!("⌈{}⌉", show(a, m)),
        P::Floor(_, _, a) => format!("⌊{}⌋", show(a, m)),
        P::Equals(_, _, a, b) => format!("{} = {}", show(a, m), show(b, m)),
        P::In(_, _, a, b) => format!("{} ∈ {}", show(a, m), show(b, m)),
        P::Other(s) => s.clone(),
    }
}

/// Classify an error message of the lowering into a construct name (for counting).
fn classify(e: &str) -> String {
    let keys = [
        ("map key must be bound", "map pattern with an unbound key"),
        ("existential", "?X (unbound right-hand-side variable)"),
        ("ensures", "ensures"),
        ("recursive function", "recursive function"),
        (
            "neither a hook implementation",
            "function without hook implementation or equations",
        ),
        (
            "no implementation for function",
            "function without implementation",
        ),
        ("map key must be bound", "map pattern with an unbound key"),
        ("more than one binding", "map pattern with several bindings"),
        ("two map variables", "map pattern with two rest variables"),
        ("unsupported requires", "requires clause shape"),
        ("unsupported left-hand-side", "left-hand-side pattern shape"),
        (
            "unsupported pattern under injection",
            "pattern under injection",
        ),
        ("unsupported term", "term shape"),
        ("parametric", "parametric sort"),
        (
            "domain value of sort",
            "domain value of an unsupported sort",
        ),
        ("literal of unknown sort", "literal of an unsupported sort"),
        ("unknown sort", "unsupported sort"),
    ];
    for (k, v) in keys {
        if e.contains(k) {
            return v.to_string();
        }
    }
    let short: String = e.chars().take(80).collect();
    format!("other: {short}")
}

pub fn run(def: &Def, rest: &[String]) {
    let dump_rules = rest.iter().any(|a| a == "--rules");
    let m = match Model::build(def) {
        Ok(m) => m,
        Err(e) => {
            println!("model: {e}");
            return;
        }
    };
    // ---------------------------------------------------------------- counts
    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    for s in m.sorts.values() {
        let k = match &s.kind {
            Kind::Builtin(b) => format!("builtin {b:?}"),
            Kind::Token => "token".into(),
            Kind::Coll(c) => format!("collection {c:?}"),
            Kind::Plain => "plain".into(),
        };
        *kinds.entry(k).or_default() += 1;
    }
    let parametric_sorts = def.sorts.values().filter(|d| !d.params.is_empty()).count();
    println!(
        "[sorts]\ndeclared = {}\nparametric = {}\nin_model = {}",
        def.sorts.len(),
        parametric_sorts,
        m.sorts.len()
    );
    for (k, n) in &kinds {
        println!("{k:?} = {n}");
    }
    println!("unsupported_hooked = {:?}", m.unsupported);
    let kitem_leaves = m
        .sorts
        .get("SortKItem")
        .map(|s| s.leaves.len())
        .unwrap_or(0);
    let max_leaves = m.sorts.values().map(|s| s.leaves.len()).max().unwrap_or(0);
    let types = crate::terms::block_types(&m);
    let block_ctors: usize = types.iter().map(|(_, c)| c.len()).sum();
    println!(
        "kitem_leaves = {kitem_leaves}\nmax_leaves = {max_leaves}\nblock_types = {}\nblock_constructors = {block_ctors}\ninjection_pairs = {}",
        types.len(),
        crate::terms::inj_pairs(&m).len()
    );
    println!(
        "\n[symbols]\ndeclared = {}\nconstructors = {}",
        def.symbols.len(),
        m.ctors.len()
    );
    let fn_syms: Vec<&String> = def
        .symbols
        .iter()
        .filter(|(_, d)| d.is_function())
        .map(|(n, _)| n)
        .collect();
    let hooked: Vec<&String> = fn_syms
        .iter()
        .copied()
        .filter(|n| def.symbols[*n].hook().is_some())
        .collect();
    println!(
        "functions = {}\nhooked_functions = {}",
        fn_syms.len(),
        hooked.len()
    );
    let mut hook_ns: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    let mut missing_hooks: BTreeSet<String> = BTreeSet::new();
    for n in &hooked {
        let h = def.symbols[*n].hook().unwrap();
        let ns = h.split('.').next().unwrap_or("").to_string();
        let e = hook_ns.entry(ns).or_default();
        e.0 += 1;
        if hooks::lookup(&h).is_some() {
            e.1 += 1;
        } else {
            missing_hooks.insert(h);
        }
    }
    println!(
        "\n[hooks] # namespace = [declared function symbols, implemented in the hook library]"
    );
    for (k, (a, b)) in &hook_ns {
        println!("{k:?} = [{a}, {b}]");
    }
    // ---------------------------------------------------------------- axioms
    let mut ax: BTreeMap<&str, usize> = BTreeMap::new();
    for a in &def.axioms {
        let k = match &a.pattern {
            P::Rewrites(..) => "rewrite",
            P::Implies(_, _, r) if matches!(&**r, P::Equals(..)) => {
                if a.attrs.has("simplification") {
                    "simplification"
                } else {
                    "equation"
                }
            }
            _ if a.attrs.has("subsort") => "subsort",
            _ if a.attrs.has("constructor") => "constructor (no confusion)",
            _ if a.attrs.has("functional") || a.attrs.has("total") => "functional",
            _ if a.attrs.has("assoc")
                || a.attrs.has("comm")
                || a.attrs.has("idem")
                || a.attrs.has("unit") =>
            {
                "AC / unit"
            }
            _ => "other",
        };
        *ax.entry(k).or_default() += 1;
    }
    println!("\n[axioms]\ntotal = {}", def.axioms.len());
    for (k, n) in &ax {
        println!("{k:?} = {n}");
    }
    let eqs = funcs::equations(def);
    let eq_fns = eqs.len();
    println!("functions_with_equations = {eq_fns}");
    let prios = crate::rules::priorities(def);
    println!("rule_priorities = {prios:?}");
    let mut attr_counts: BTreeMap<String, usize> = BTreeMap::new();
    for a in &def.axioms {
        if !matches!(a.pattern, P::Rewrites(..)) {
            continue;
        }
        for at in [
            "heat",
            "cool",
            "owise",
            "priority",
            "anywhere",
            "label",
            "stream",
            "fresh-generator",
        ] {
            if a.attrs.has(at) {
                *attr_counts.entry(at.to_string()).or_default() += 1;
            }
        }
    }
    println!("rewrite_attributes = {attr_counts:?}");
    // ---------------------------------------------------------------- refusals
    // every function symbol gets a signature (hooks where implemented, generated names
    // otherwise), so that a rule's refusal names its own construct, not a missing callee
    let mut fns: Fns = BTreeMap::new();
    for (sym, d) in &def.symbols {
        if !d.is_function() && !m.anywhere.contains(sym) {
            continue;
        }
        let args: Option<Vec<String>> = d.args.iter().map(sort_name).collect();
        let (args, result) = match (args, sort_name(&d.result)) {
            (Some(a), Some(r)) => (a, r),
            _ => (vec!["?".into(); d.args.len()], "?".into()),
        };
        let (lean, partial) = match hooks::for_symbol(d) {
            Some(h) => (h.lean.to_string(), h.partial),
            None => (funcs::fn_name(sym), true),
        };
        fns.insert(
            sym.clone(),
            FnSig {
                lean,
                partial,
                args,
                result,
            },
        );
    }
    let top = crate::rules::top_sort(def).unwrap_or_default();
    let mut refusals: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut ok_rules = 0;
    let mut n_rules = 0;
    let mut map_patterns_free_key = 0;
    let (
        mut multi_rules,
        mut choose_total,
        mut lookup_total,
        mut list_total,
        mut steps_total,
        mut max_steps,
    ) = (0, 0, 0, 0, 0, 0);
    for a in &def.axioms {
        let P::Rewrites(_, l, r) = &a.pattern else {
            continue;
        };
        n_rules += 1;
        let what = a
            .attrs
            .string("label")
            .unwrap_or_else(|| a.attrs.string("UNIQUE'Unds'ID").unwrap_or_default());
        if dump_rules {
            println!("\n# rule {what}\n{}", show(&a.pattern, Some(&m)));
        }
        let (lhs, req) = match &**l {
            P::And(_, ps) if ps.len() == 2 => (&ps[0], &ps[1]),
            other => (other, &P::Top(crate::ir::S::App(top.clone(), vec![]))),
        };
        let (rhs, ens) = match &**r {
            P::And(_, ps) if ps.len() == 2 => (&ps[0], &ps[1]),
            other => (other, &P::Top(crate::ir::S::App(top.clone(), vec![]))),
        };
        let mut shape = (0usize, 0usize, 0usize, 0usize);
        let res = guard(|| -> Result<(), String> {
            if !matches!(ens, P::Top(_)) {
                return Err("ensures".into());
            }
            if crate::rules::absent_sort(lhs, &m).is_some() {
                return Err("left-hand side needs a sort without values (rule left out)".into());
            }
            let lhs_n = crate::funcs::normalize_consts(lhs, def);
            let mut lw = Lower::new(&m, &fns, &[]);
            lw.param("c", &top);
            lw.pat(&lhs_n, "c", &top, true)?;
            lw.finish_lhs()?;
            lw.cond(req)?;
            lw.expr(rhs, &top)?;
            for st in &lw.steps {
                match st {
                    crate::lower::Step::MapChoose { .. } => shape.0 += 1,
                    crate::lower::Step::MapElem { .. } => shape.1 += 1,
                    crate::lower::Step::ListElem { .. } => shape.2 += 1,
                    _ => {}
                }
            }
            shape.3 = lw.steps.len();
            Ok(())
        });
        if res.is_ok() {
            if shape.0 > 0 {
                multi_rules += 1;
            }
            choose_total += shape.0;
            lookup_total += shape.1;
            list_total += shape.2;
            steps_total += shape.3;
            max_steps = max_steps.max(shape.3);
        }
        match res {
            Ok(()) => ok_rules += 1,
            Err(e) => {
                if e.contains("map key must be bound") {
                    map_patterns_free_key += 1;
                }
                if dump_rules {
                    println!("# refused: {}", e.chars().take(400).collect::<String>());
                }
                refusals.entry(classify(&e)).or_default().push(what);
            }
        }
    }
    let mut eq_ok = 0;
    let mut eq_n = 0;
    let mut eq_refusals: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (f, es) in &eqs {
        let Some(sig) = fns.get(f).cloned() else {
            continue;
        };
        for e in es {
            eq_n += 1;
            let res = guard(|| -> Result<(), String> {
                if sig.args.iter().any(|a| a == "?") {
                    return Err("parametric function".into());
                }
                let mut lw = Lower::new(&m, &fns, &[]);
                let params: Vec<String> = (0..sig.args.len()).map(|i| format!("x{i}")).collect();
                for (p, s) in params.iter().zip(&sig.args) {
                    lw.param(p, s);
                }
                for ((a, p), s) in e.args.iter().zip(&params).zip(&sig.args) {
                    lw.pat(a, p, s, true)?;
                }
                lw.finish_lhs()?;
                for r in &e.requires {
                    lw.cond(r)?;
                }
                lw.expr(&e.rhs, &sig.result)?;
                Ok(())
            });
            match res {
                Ok(()) => eq_ok += 1,
                Err(err) => eq_refusals
                    .entry(classify(&err))
                    .or_default()
                    .push(names::demangle(f)),
            }
        }
    }
    // recursion: strongly connected components of the call graph of generated functions
    let mut calls: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (f, es) in &eqs {
        let mut cs = BTreeSet::new();
        for e in es {
            funcs::applied(&e.rhs, def, &mut cs);
            for r in &e.requires {
                funcs::applied(r, def, &mut cs);
            }
        }
        cs.retain(|c| eqs.contains_key(c));
        calls.insert(f.clone(), cs);
    }
    let recursive = recursive_fns(&calls);
    println!(
        "\n[rules]\ntotal = {n_rules}\nlowered = {ok_rules}\nrefused = {}",
        n_rules - ok_rules
    );
    println!("free_key_map_patterns = {map_patterns_free_key}");
    println!(
        "rules_with_free_key_match = {multi_rules}\nfree_key_elements = {choose_total}\nbound_key_lookups = {lookup_total}\nlist_elements = {list_total}\nmatch_steps_total = {steps_total}\nmatch_steps_max = {max_steps}"
    );
    // functions reachable from the rules
    let mut roots = BTreeSet::new();
    for a in &def.axioms {
        if let P::Rewrites(_, l, _) = &a.pattern
            && crate::rules::absent_sort(l, &m).is_none()
        {
            funcs::applied(&a.pattern, def, &mut roots);
            funcs::applied_ctors(&a.pattern, &m.anywhere, &mut roots);
        }
    }
    let mut reach = BTreeSet::new();
    let mut todo: Vec<String> = roots.into_iter().collect();
    while let Some(f) = todo.pop() {
        if !reach.insert(f.clone()) {
            continue;
        }
        let Some(d) = def.symbols.get(&f) else {
            continue;
        };
        if crate::hooks::for_symbol(d).is_some() {
            continue;
        }
        let mut cs = BTreeSet::new();
        for e in eqs.get(&f).into_iter().flatten() {
            funcs::applied(&e.rhs, def, &mut cs);
            funcs::applied_ctors(&e.rhs, &m.anywhere, &mut cs);
            for r in &e.requires {
                funcs::applied(r, def, &mut cs);
            }
        }
        todo.extend(cs);
    }
    let hooked_impl = reach
        .iter()
        .filter(|f| {
            def.symbols
                .get(*f)
                .is_some_and(|d| crate::hooks::for_symbol(d).is_some())
        })
        .count();
    let hooked_missing: BTreeSet<String> = reach
        .iter()
        .filter_map(|f| {
            let d = def.symbols.get(f)?;
            let h = d.hook()?;
            (crate::hooks::for_symbol(d).is_none() && !eqs.contains_key(f)).then_some(h)
        })
        .collect();
    let with_eqs = reach
        .iter()
        .filter(|f| {
            eqs.contains_key(*f)
                && def
                    .symbols
                    .get(*f)
                    .is_some_and(|d| crate::hooks::for_symbol(d).is_none())
        })
        .count();
    println!(
        "\n[reachable_functions] # from the rules, through equations\ntotal = {}\nby_equations = {with_eqs}\nby_implemented_hooks = {hooked_impl}",
        reach.len()
    );
    println!(
        "recursive_reachable = {}",
        reach
            .iter()
            .filter(|f| recursive_fns_cache_contains(&eqs, def, f))
            .count()
    );
    println!("missing_hooks = {hooked_missing:?}");
    println!("\n[rules.refusals] # construct = [count, first examples]");
    for (k, v) in &refusals {
        let ex: Vec<&String> = v.iter().take(4).collect();
        println!("{k:?} = [{}, {ex:?}]", v.len());
    }
    println!(
        "\n[equations]\ntotal = {eq_n}\nlowered = {eq_ok}\nrecursive_functions = {}",
        recursive.len()
    );
    let rec_names: Vec<String> = recursive.iter().map(|f| names::demangle(f)).collect();
    println!("recursive = {rec_names:?}");
    println!("\n[equations.refusals]");
    for (k, v) in &eq_refusals {
        let mut fs: Vec<&String> = v.iter().collect();
        fs.dedup();
        let ex: Vec<&&String> = fs.iter().take(4).collect();
        println!("{k:?} = [{}, {ex:?}]", v.len());
    }
    println!("\n[hooks.missing] # hooks of declared function symbols with no implementation");
    println!("list = {missing_hooks:?}");
}

fn recursive_fns_cache_contains(
    eqs: &BTreeMap<String, Vec<funcs::Equation>>,
    def: &Def,
    f: &str,
) -> bool {
    // f reaches itself through equation right-hand sides
    let mut seen = BTreeSet::new();
    let mut todo = vec![f.to_string()];
    let mut first = true;
    while let Some(g) = todo.pop() {
        if !first && g == f {
            return true;
        }
        first = false;
        if !seen.insert(g.clone()) {
            continue;
        }
        for e in eqs.get(&g).into_iter().flatten() {
            let mut cs = BTreeSet::new();
            funcs::applied(&e.rhs, def, &mut cs);
            for r in &e.requires {
                funcs::applied(r, def, &mut cs);
            }
            if cs.contains(f) {
                return true;
            }
            todo.extend(cs.into_iter().filter(|c| eqs.contains_key(c)));
        }
    }
    false
}

/// Run a lowering, turning a panic (an internal assumption that does not hold) into an error.
fn guard(f: impl FnOnce() -> Result<(), String>) -> Result<(), String> {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    std::panic::set_hook(prev);
    match r {
        Ok(r) => r,
        Err(e) => Err(format!(
            "internal: {}",
            e.downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default()
        )),
    }
}

/// Functions on a cycle of the call graph.
fn recursive_fns(calls: &BTreeMap<String, BTreeSet<String>>) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for f in calls.keys() {
        // f is recursive if f is reachable from its callees
        let mut seen = BTreeSet::new();
        let mut todo: Vec<&String> = calls[f].iter().collect();
        while let Some(g) = todo.pop() {
            if g == f {
                out.insert(f.clone());
                break;
            }
            if seen.insert(g.clone())
                && let Some(cs) = calls.get(g)
            {
                todo.extend(cs.iter());
            }
        }
    }
    out
}
