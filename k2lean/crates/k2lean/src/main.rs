//! `k2lean`: a Lean 4 library from a K definition compiled to KORE by krust (`k2lean/README.md`).
//!
//! Commands: `gen` (the library), `open-from-log`, `goldens`, `cases`, `configs`, `survey`,
//! `relate`, `claims`, `new-invariant` and `diff`; `k2lean/docs/design.md` describes them.

mod casediff;
mod cases;
mod claims;
mod convert;
mod drivers;
mod eqns;
mod funcs;
mod goldens;
mod hooks;
mod index;
mod init;
mod invariants;
mod ir;
mod lower;
mod model;
mod multi;
mod names;
mod overload;
mod preserves;
mod ranked;
mod relate;
mod render;
mod rulename;
mod rules;
mod survey;
mod template;
mod termination;
mod terms;

use std::path::PathBuf;

/// The Lean toolchain of every generated project (and of `k2lean/lean/prelude` and `k2lean/lean/claims`).
pub const LEAN_TOOLCHAIN: &str = "leanprover/lean4:v4.30.0\n";

struct Args {
    cmd: String,
    kore: PathBuf,
    runtime: Option<PathBuf>,
    out: Option<PathBuf>,
    name: String,
    prelude: String,
    open: Option<PathBuf>,
    lemmas: Option<PathBuf>,
    /// per-definition termination inputs (`funcs::Sidecar`)
    termination: Option<PathBuf>,
    rest: Vec<String>,
}

fn parse_args() -> Args {
    let mut it = std::env::args().skip(1);
    let cmd = it.next().expect("command: gen | survey");
    let mut a = Args {
        cmd,
        kore: PathBuf::new(),
        runtime: None,
        out: None,
        name: "KDef".into(),
        prelude: "../prelude".into(),
        open: None,
        lemmas: None,
        termination: None,
        rest: vec![],
    };
    while let Some(x) = it.next() {
        match x.as_str() {
            "--kore" => a.kore = it.next().unwrap().into(),
            "--out" => a.out = Some(it.next().unwrap().into()),
            "--runtime" => a.runtime = Some(it.next().unwrap().into()),
            "--name" => a.name = it.next().unwrap(),
            "--prelude" => a.prelude = it.next().unwrap(),
            "--open-obligations" => a.open = Some(it.next().unwrap().into()),
            // a compiled definition with extra lemma modules: its simplification rules that the
            // main definition lacks are stated too (K keeps lemmas in separate modules)
            "--lemmas-kore" => a.lemmas = Some(it.next().unwrap().into()),
            // measures and termination proofs for the recursive functions no generic rule covers
            "--termination" => a.termination = Some(it.next().unwrap().into()),
            other => a.rest.push(other.to_string()),
        }
    }
    a
}

fn write(path: &PathBuf, text: &str) {
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir).unwrap();
    }
    std::fs::write(path, text).unwrap();
}

/// `open-from-log EQUATIONS.lean BUILD.log OPEN.txt`: add the theorems whose proofs failed in a
/// build log to the open-obligation list (they are then emitted as statements only).
fn open_from_log(args: &[String]) {
    let [eq_file, log, out] = args else {
        panic!("usage: open-from-log EQUATIONS.lean BUILD.log OPEN.txt")
    };
    let text = std::fs::read_to_string(eq_file).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    let log = std::fs::read_to_string(log).unwrap();
    let mut open: std::collections::BTreeSet<String> = std::fs::read_to_string(out)
        .unwrap_or_default()
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect();
    let file_name = std::path::Path::new(eq_file)
        .file_name()
        .unwrap()
        .to_string_lossy()
        .to_string();
    for l in log.lines() {
        let Some(pos) = l.find(&format!("{file_name}:")) else {
            continue;
        };
        if !l.trim_start().starts_with("error:") {
            continue;
        }
        let rest = &l[pos + file_name.len() + 1..];
        let Some(line) = rest.split(':').next().and_then(|n| n.parse::<usize>().ok()) else {
            continue;
        };
        // an error in a command (`#k2l_assert_axioms`) is a consequence, not a failed proof
        if lines
            .get(line.wrapping_sub(1))
            .is_some_and(|l| l.starts_with('#'))
        {
            continue;
        }
        for i in (0..line.min(lines.len())).rev() {
            if let Some(name) = lines[i].strip_prefix("theorem ") {
                // the name ends at the first space outside `«…»` (rule names hold spaces)
                open.insert(invariants::case_token(name).unwrap());
                break;
            }
        }
    }
    let joined: Vec<String> = open.into_iter().collect();
    std::fs::write(out, joined.join("\n") + "\n").unwrap();
    eprintln!("{} open obligations", joined.len());
}

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    if raw.first().map(|s| s.as_str()) == Some("claims") {
        return claims::main(&raw[1..]);
    }
    if raw.first().map(|s| s.as_str()) == Some("relate") {
        return relate::main(&raw[1..]);
    }
    if raw.first().map(|s| s.as_str()) == Some("diff") {
        return casediff::main(&raw[1..]);
    }
    if raw.first().map(|s| s.as_str()) == Some("new-invariant") {
        return template::main(&raw[1..]);
    }
    if raw.first().map(|s| s.as_str()) == Some("open-from-log") {
        return open_from_log(&raw[1..]);
    }
    let a = parse_args();
    let text = std::fs::read_to_string(&a.kore).unwrap();
    let def = ir::load(&text).unwrap();
    match a.cmd.as_str() {
        "gen" => {
            let m = model::Model::build(&def).unwrap_or_else(|e| panic!("{e}"));
            if !m.unsupported.is_empty() {
                eprintln!(
                    "note: sorts with unsupported hooks left out: {:?}",
                    m.unsupported
                );
            }
            let out = a.out.expect("--out");
            let ns = &a.name;
            write(&out.join("lean-toolchain"), LEAN_TOOLCHAIN);
            let exe = ns.to_lowercase();
            write(
                &out.join("lakefile.lean"),
                &drivers::lakefile(ns, &a.prelude, &exe),
            );
            let order: Vec<String> = match &a.runtime {
                Some(p) => {
                    let j: serde_json::Value =
                        serde_json::from_str(&std::fs::read_to_string(p).unwrap()).unwrap();
                    j["execution_rewrite_order"]
                        .as_array()
                        .map(|v| {
                            v.iter()
                                .filter_map(|x| x.as_str().map(String::from))
                                .collect()
                        })
                        .unwrap_or_default()
                }
                None => vec![],
            };
            // functions used by the rules
            let mut roots = std::collections::BTreeSet::new();
            for ax in &def.axioms {
                if let ir::P::Rewrites(_, l, _) = &ax.pattern {
                    // a rule whose left-hand side needs a sort without values is left out
                    if rules::absent_sort(l, &m).is_none() {
                        funcs::applied(&ax.pattern, &def, &mut roots);
                    }
                }
            }
            // `anywhere` and overloaded symbols: their normalizers are called by right-hand sides
            roots.extend(m.anywhere.iter().cloned());
            // functions no rule uses but a meta-theorem needs (a type
            // checker's `typeOf`), by K label prefix up to `(`: `--extra-fns typeOf,wt`
            if let Some(i) = a.rest.iter().position(|x| x == "--extra-fns") {
                for want in a.rest[i + 1].split(',') {
                    for (sym, d) in &def.symbols {
                        let l = names::demangle(sym);
                        if d.is_function() && (l == want || l.starts_with(&format!("{want}("))) {
                            roots.insert(sym.clone());
                        }
                    }
                }
            }
            // kind 1 invariants (`invariants.rs`): the functions they name are generated too
            let specs: Vec<invariants::Spec> = a
                .rest
                .iter()
                .enumerate()
                .filter(|(_, x)| x.as_str() == "--invariant")
                .map(|(i, _)| invariants::parse_spec(&a.rest[i + 1]))
                .collect();
            for s in &specs {
                roots.insert(invariants::resolve(&def, &s.name).unwrap_or_else(|e| panic!("{e}")));
            }
            let declared: Vec<invariants::Declared> =
                match a.rest.iter().position(|x| x == "--sidecar") {
                    Some(i) => invariants::read_sidecar(std::path::Path::new(&a.rest[i + 1]))
                        .unwrap_or_else(|e| panic!("{e}")),
                    None => vec![],
                };
            // the initial configuration (`init.rs`): the functions it still applies are generated too
            let init_term = init::term(&def, &funcs::equations(&def));
            if let Ok(t) = &init_term {
                roots.extend(init::functions(t, &def));
            }
            let side = match &a.termination {
                Some(p) => funcs::Sidecar::load(p).unwrap_or_else(|e| panic!("--termination: {e}")),
                None => funcs::Sidecar::default(),
            };
            let fgen = funcs::generate_with(&def, &m, &roots, &side)
                .unwrap_or_else(|e| panic!("functions: {e}"));
            for n in &fgen.notes {
                eprintln!("note: {n}");
            }
            let top = rules::top_sort(&def).unwrap();
            let mut rs =
                rules::collect(&def, &m, &fgen.fns, &order).unwrap_or_else(|e| panic!("{e}"));
            let mut prios = rules::priorities(&def);
            let multi = rs.iter().any(|r| r.multi);
            if multi {
                // several matches: the ranked, list-valued emitter (even with one priority)
                rs = rules::collect_with(&def, &m, &fgen.fns, &order, true)
                    .unwrap_or_else(|e| panic!("{e}"));
                // ranks only of the rules kept
                prios.retain(|p| rs.iter().any(|r| r.priority == *p));
                eprintln!(
                    "note: {} rules with several matches (free-key map patterns): list-valued matchers",
                    rs.iter().filter(|r| r.multi).count()
                );
            }
            let ranked = prios.len() > 1 || multi;
            if ranked {
                eprintln!(
                    "note: {} priority ranks {:?}: stratified Step",
                    prios.len(),
                    prios
                );
            }
            let mut unfold = fgen.unfold.clone();
            unfold.extend(hooks::unfold_names().iter().map(|s| s.to_string()));
            for (x, y) in terms::inj_pairs(&m) {
                unfold.push(format!(
                    "proj_{}_{}",
                    names::short_sort(&y),
                    names::short_sort(&x)
                ));
                unfold.push(format!(
                    "inj_{}_{}",
                    names::short_sort(&x),
                    names::short_sort(&y)
                ));
            }
            write(
                &out.join(format!("{ns}.lean")),
                &format!(
                    "import {ns}.Terms\nimport {ns}.Functions\nimport {ns}.Rules\nimport {ns}.Adequacy\nimport {ns}.Determinism\nimport {ns}.Equations\n"
                ),
            );
            let topts = terms::TermOpts {
                linear: a.rest.iter().any(|x| x == "--linear-terms"),
            };
            write(
                &out.join(ns).join("Terms.lean"),
                &terms::emit_with(&m, ns, topts),
            );
            write(
                &out.join(ns).join("Functions.lean"),
                &functions_module(ns, &fgen, ""),
            );
            if multi {
                write(
                    &out.join(ns).join("Rules.lean"),
                    &with_hooks(
                        multi::emit_rules(&rs, &prios, &top, ns, &rules::ctor_info(&m)),
                        ns,
                        &fgen.params,
                    ),
                );
                write(
                    &out.join(ns).join("Adequacy.lean"),
                    &with_hooks(
                        multi::emit_adequacy(&rs, &prios, &top, ns, &rules::ctor_info(&m)),
                        ns,
                        &fgen.params,
                    ),
                );
                let report = format!(
                    "{} of the {} rewrite rules have a map pattern with a free key (a match per binding, e.g. per thread),\nso `Step` is not deterministic in general.",
                    rs.iter().filter(|r| r.multi).count(),
                    rs.len()
                );
                write(
                    &out.join(ns).join("Determinism.lean"),
                    &with_hooks(multi::emit_determinism(&top, ns, &report), ns, &fgen.params),
                );
            } else if ranked {
                write(
                    &out.join(ns).join("Rules.lean"),
                    &with_hooks(
                        ranked::emit_rules(&rs, &prios, &top, ns, &rules::ctor_info(&m)),
                        ns,
                        &fgen.params,
                    ),
                );
                write(
                    &out.join(ns).join("Adequacy.lean"),
                    &with_hooks(
                        ranked::emit_adequacy(&rs, &prios, &top, ns, &rules::ctor_info(&m)),
                        ns,
                        &fgen.params,
                    ),
                );
                write(
                    &out.join(ns).join("Determinism.lean"),
                    &with_hooks(
                        ranked::emit_determinism(&top, ns, &unfold),
                        ns,
                        &fgen.params,
                    ),
                );
            } else {
                write(
                    &out.join(ns).join("Rules.lean"),
                    &with_hooks(
                        rules::emit_rules(&rs, &top, ns, &rules::ctor_info(&m)),
                        ns,
                        &fgen.params,
                    ),
                );
                write(
                    &out.join(ns).join("Adequacy.lean"),
                    &with_hooks(
                        rules::emit_adequacy(&rs, &top, ns, &unfold, &rules::ctor_info(&m)),
                        ns,
                        &fgen.params,
                    ),
                );
                write(
                    &out.join(ns).join("Determinism.lean"),
                    &with_hooks(rules::emit_determinism(&top, ns, &unfold), ns, &fgen.params),
                );
            }
            // the per-rule preservation principle, and the initial configuration
            let ranks = if ranked { Some(prios.as_slice()) } else { None };
            let pctors = preserves::ctors(&rs, ranks);
            write(
                &out.join(ns).join("Preserves.lean"),
                &with_hooks(preserves::emit(&pctors, &top, ns), ns, &fgen.params),
            );
            let mut init_ok = false;
            let mut init_params = None;
            match init_term
                .as_ref()
                .map_err(|e| e.clone())
                .and_then(|t| init::emit(t, &m, &fgen.fns, &top, ns))
            {
                Ok((text, params)) => {
                    write(
                        &out.join(ns).join("Init.lean"),
                        &with_hooks(text, ns, &fgen.params),
                    );
                    init_ok = true;
                    init_params = Some(params);
                }
                Err(e) => {
                    eprintln!("note: no initial configuration: {e}");
                    let _ = std::fs::remove_file(out.join(ns).join("Init.lean"));
                }
            }
            // K equations and simplification rules as theorems
            let open: std::collections::BTreeSet<String> = match &a.open {
                Some(p) => std::fs::read_to_string(p)
                    .unwrap_or_default()
                    .lines()
                    .map(|l| l.trim().to_string())
                    .filter(|l| !l.is_empty())
                    .collect(),
                None => Default::default(),
            };
            let eqs = funcs::equations(&def);
            // statements may mention any hook the library implements, not only the used ones
            let mut stmt_fns = fgen.fns.clone();
            for (sym, d) in &def.symbols {
                if stmt_fns.contains_key(sym) || !d.params.is_empty() {
                    continue;
                }
                let Some(h) = hooks::for_symbol(d) else {
                    continue;
                };
                let args: Option<Vec<String>> = d.args.iter().map(model::sort_name).collect();
                let (Some(args), Some(result)) = (args, model::sort_name(&d.result)) else {
                    continue;
                };
                if args
                    .iter()
                    .chain(std::iter::once(&result))
                    .any(|s| !m.sorts.contains_key(s))
                {
                    continue;
                }
                stmt_fns.insert(
                    sym.clone(),
                    lower::FnSig {
                        lean: h.lean.to_string(),
                        partial: h.partial,
                        args,
                        result,
                    },
                );
            }
            let mut stated = eqns::equation_theorems(&def, &m, &stmt_fns, &eqs);
            stated.extend(eqns::simplification_theorems(&def, &m, &stmt_fns));
            if let Some(lp) = &a.lemmas {
                let ldef = ir::load(&std::fs::read_to_string(lp).unwrap()).unwrap();
                let known: std::collections::BTreeSet<String> = def
                    .axioms
                    .iter()
                    .filter_map(|x| x.attrs.string("UNIQUE'Unds'ID"))
                    .collect();
                let extra = ir::Def {
                    axioms: ldef
                        .axioms
                        .iter()
                        .filter(|x| {
                            x.attrs
                                .string("UNIQUE'Unds'ID")
                                .is_some_and(|u| !known.contains(&u))
                        })
                        .cloned()
                        .collect(),
                    ..Default::default()
                };
                let mut more = eqns::simplification_theorems(&extra, &m, &stmt_fns);
                for s in &mut more {
                    s.name = s.name.replacen("Simp.", "Lemma.", 1);
                }
                eprintln!("{} lemmas from {}", more.len(), lp.display());
                stated.extend(more);
            }
            // definitions and hooks, but not the injections/projections (their lemmas instead)
            let mut eq_unfold = fgen.unfold.clone();
            eq_unfold.extend(hooks::eq_unfold_names().iter().map(|s| s.to_string()));
            eq_unfold.extend(terms::inj_pairs(&m).iter().map(|(x, y)| {
                format!(
                    "proj_eq_some_{}_{}",
                    names::short_sort(y),
                    names::short_sort(x)
                )
            }));
            write(
                &out.join(ns).join("Equations.lean"),
                &with_hooks(
                    eqns::emit_with(
                        ns,
                        &stated,
                        &open,
                        &eq_unfold,
                        &fgen.recursive,
                        &fgen.list_recursive,
                    ),
                    ns,
                    &fgen.params,
                ),
            );
            eprintln!(
                "{} equations and simplifications stated, {} open",
                stated.len(),
                stated.iter().filter(|s| open.contains(&s.name)).count()
            );
            // kind 1 invariants: `InvariantDefs.lean`, `Invariants.lean`, `open-invariant-cases.txt`
            if specs.is_empty() && declared.is_empty() {
                for f in ["InvariantDefs.lean", "Invariants.lean"] {
                    let _ = std::fs::remove_file(out.join(ns).join(f));
                }
            } else {
                let open_path = match a.rest.iter().position(|x| x == "--open-invariant-cases") {
                    Some(i) => PathBuf::from(&a.rest[i + 1]),
                    None => out.join("open-invariant-cases.txt"),
                };
                let open_cases = invariants::read_open(&open_path);
                let stated_names: std::collections::BTreeSet<String> =
                    stated.iter().map(|s| s.name.clone()).collect();
                let hand = out.join(ns).join("InvariantsHand.lean");
                let cx = invariants::Ctx {
                    def: &def,
                    m: &m,
                    fns: &fgen.fns,
                    eqs: &eqs,
                    stated: &stated_names,
                    open_eqns: &open,
                    recursive: &fgen.recursive,
                    ctors: &pctors,
                    top: &top,
                    ns,
                    init: match (&init_term, init_params) {
                        (Ok(t), Some(p)) => Some((t, p)),
                        _ => None,
                    },
                };
                let o = invariants::emit(&cx, &specs, &declared, &open_cases, hand.exists())
                    .unwrap_or_else(|e| panic!("invariants: {e}"));
                for n in &o.notes {
                    eprintln!("note: {n}");
                }
                write(
                    &out.join(ns).join("InvariantDefs.lean"),
                    &with_hooks(o.defs.clone(), ns, &fgen.params),
                );
                write(
                    &out.join(ns).join("Invariants.lean"),
                    &with_hooks(o.theorems.clone(), ns, &fgen.params),
                );
                write(&open_path, &o.open_list);
                if let Some(sk) = &o.hand_skeleton {
                    write(&hand, sk);
                    eprintln!(
                        "note: wrote the hand-proof skeleton {} (it is never overwritten)",
                        hand.display()
                    );
                }
                eprintln!(
                    "invariant: {} open cases",
                    o.open_list
                        .lines()
                        .filter(|l| invariants::case_token(l).is_some())
                        .count()
                );
            }
            if multi {
                write(
                    &out.join(format!("{ns}Test")).join("Main.lean"),
                    &cases::test_main(ns, &top),
                );
            } else {
                write(
                    &out.join(format!("{ns}Test")).join("Main.lean"),
                    &drivers::test_main(ns, &top),
                );
            }
            let proved: Vec<String> = stated
                .iter()
                .filter(|s| !open.contains(&s.name))
                .map(|s| s.name.clone())
                .collect();
            write(
                &out.join(format!("{ns}Test")).join("Axioms.lean"),
                &drivers::axioms_with(ns, &proved, ranked, multi, init_ok),
            );
            write(
                &out.join(format!("{ns}Bench")).join("Main.lean"),
                &drivers::bench_main(ns, &top),
            );
            if multi {
                // no benchmark programs for case-driven definitions: an empty list keeps the target building
                write(
                    &out.join(format!("{ns}Bench")).join("Programs.lean"),
                    &format!(
                        "import {ns}.Rules\n\nnamespace {ns}Bench\n\nopen {ns}\n\ndef programs : List (String × {top}) := []\n\nend {ns}Bench\n"
                    ),
                );
            }
            eprintln!("generated {} rules, {} functions", rs.len(), fgen.fns.len());
        }
        "term" => {
            // a KORE pattern on standard input → a Lean value of the top sort
            let m = model::Model::build(&def).unwrap();
            let mut input = String::new();
            std::io::Read::read_to_string(&mut std::io::stdin(), &mut input).unwrap();
            let p = ir::pat(&k_rust_kore::kore::parser::parse_pattern(&input).unwrap());
            let top = rules::top_sort(&def).unwrap();
            let c = convert::Conv::new(&m, &def);
            println!(
                "{}",
                c.value(&p, &top).unwrap_or_else(|e| panic!("{e}")).render()
            );
        }
        "goldens" => goldens::run(&def, &a.rest, &a.name),
        "survey" => survey::run(&def, &a.rest),
        "cases" => cases::run(&def, &a.rest, &a.name),
        "terms" => {
            // the term universe only (survey of large definitions): a project whose library is
            // `Terms.lean`
            let m = model::Model::build(&def).unwrap_or_else(|e| panic!("{e}"));
            let out = a.out.expect("--out");
            let ns = &a.name;
            write(&out.join("lean-toolchain"), LEAN_TOOLCHAIN);
            write(
                &out.join("lakefile.lean"),
                &format!(
                    "import Lake\nopen Lake DSL\n\npackage «{ns}» where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n\nrequire KPrelude from \"{}\"\n\n@[default_target]\nlean_lib {ns}\n",
                    a.prelude
                ),
            );
            write(
                &out.join(format!("{ns}.lean")),
                &format!("import {ns}.Terms\n"),
            );
            let topts = terms::TermOpts {
                linear: a.rest.iter().any(|x| x == "--linear-terms"),
            };
            write(
                &out.join(ns).join("Terms.lean"),
                &terms::emit_with(&m, ns, topts),
            );
            for n in &m.notes {
                eprintln!("note: {n}");
            }
            eprintln!("note: unsupported hooked sorts: {:?}", m.unsupported);
        }
        "configs" => goldens::configs(&def, &a.rest, &a.name),
        other => panic!("unknown command {other}"),
    }
}

/// `Functions.lean`: the `Hooks` class, `extra` (instances the term universe needs), and the
/// generated definitions. The termination proofs of recursive functions (`decreasing_by`) use
/// `KPrelude.Termination`; they are elaborated without a heartbeat bound, as the term universe.
fn functions_module(ns: &str, fgen: &funcs::Generated, extra: &str) -> String {
    let (import, opts) = if fgen.recursive.is_empty() && extra.is_empty() {
        ("", "")
    } else {
        (
            "import KPrelude.Termination\n",
            "set_option linter.unusedSimpArgs false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n",
        )
    };
    format!(
        "import {ns}.Terms\n{import}\n/-! Generated by k2lean; do not edit. Functions defined by KORE equations. -/\n\nset_option linter.unusedVariables false\n{opts}\nnamespace {ns}\n\nopen KPrelude\n\n{}{extra}{}\nend {ns}\n",
        hooks_class(&fgen.params),
        fgen.lean
    )
}

/// The parameters of a library (`funcs::Generated::params`) as the fields of a class that every
/// definition needing one takes as an instance argument (`variable [Hooks]`): the library is
/// stated for every implementation of them, with no axiom. Each field is `Option`-valued, since a
/// hook that is not declared `total` may be undefined.
fn hooks_class(params: &[(String, Vec<String>, String)]) -> String {
    if params.is_empty() {
        return String::new();
    }
    let mut o = String::from(
        "/-- The parameters of this library: hooks without an implementation in the hook library,\nand functions the definition gives no equations. -/\nclass Hooks where\n",
    );
    for (h, args, res) in params {
        let ty: Vec<String> = args
            .iter()
            .cloned()
            .chain(std::iter::once(format!("Option {res}")))
            .collect();
        o.push_str(&format!("  «{h}» : {}\n", ty.join(" → ")));
    }
    o.push_str("\nvariable [Hooks]\n\n");
    o
}

/// `variable [Hooks]` after the namespace of a generated module, when the library has parameters
/// and the module imports one that declares them (every module but `Terms`).
fn with_hooks(text: String, ns: &str, params: &[(String, Vec<String>, String)]) -> String {
    let terms_only = text
        .lines()
        .take_while(|l| l.starts_with("import "))
        .filter(|l| l.starts_with(&format!("import {ns}.")))
        .all(|l| l == format!("import {ns}.Terms"));
    if params.is_empty() || terms_only {
        return text;
    }
    text.replacen(
        &format!("\nnamespace {ns}\n"),
        &format!("\nnamespace {ns}\n\nvariable [Hooks]\n"),
        1,
    )
}

#[cfg(test)]
mod tests {
    //! `open-from-log`: the error lines of a Lake log name the theorems whose proofs failed.
    use super::*;

    #[test]
    fn open_from_log_finds_the_enclosing_theorem() {
        let d = std::env::temp_dir().join(format!("k2lean-open-from-log-{}", std::process::id()));
        std::fs::create_dir_all(&d).unwrap();
        let eq = d.join("Equations.lean");
        std::fs::write(&eq, "namespace N\n\ntheorem Eqn.a_1 (x : Nat) :\n    x = x := by\n  rfl\n\ntheorem Eqn.«b_c_1» :\n    1 = 1 := by\n  intros\n  first\n  | rfl\n\nend N\n").unwrap();
        let log = d.join("build.log");
        std::fs::write(
            &log,
            "error: N/Equations.lean:10:2: unsolved goals\n  error: Equations.lean:4:0: indented error lines count too\nwarning: Equations.lean:5:2: ignored\nerror: Other.lean:4:0: another file\n",
        )
        .unwrap();
        let open = d.join("open.txt");
        std::fs::write(&open, "Eqn.z_9\n\n").unwrap();
        let s = |p: &std::path::Path| p.to_string_lossy().to_string();
        open_from_log(&[s(&eq), s(&log), s(&open)]);
        assert_eq!(
            std::fs::read_to_string(&open).unwrap(),
            "Eqn.a_1\nEqn.z_9\nEqn.«b_c_1»\n"
        );
        let _ = std::fs::remove_dir_all(&d);
    }
}
