//! `k2lean`: a Lean 4 library from a K definition compiled to KORE by krust (`k2lean/README.md`).
//!
//! Commands: `gen` (the library), `open-from-log`, `goldens`, `cases`, `configs`, `survey`,
//! `relate`, `soundness`, `claims`, `new-invariant` and `diff`; `k2lean/docs/design.md` describes them.

mod agree;
mod casediff;
mod cases;
mod claims;
mod confluence;
mod convert;
mod det2;
mod diverges;
mod drivers;
mod eqns;
mod fndiff;
mod fuel;
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
mod noninterference;
mod normal;
mod overload;
mod pairs;
mod preserves;
mod ranked;
mod refine;
mod refuted;
mod relate;
mod render;
mod rulename;
mod rules;
mod soundness;
mod survey;
mod template;
mod termination;
mod terms;
mod terms_arity;

use std::path::PathBuf;

/// The Lean toolchain of every generated project (and of the `k2lean` package, `k2lean/lean`).
pub const LEAN_TOOLCHAIN: &str = "leanprover/lean4:v4.34.0\n";

/// The default bound on the weight of one module of `Equations` (`eqns::weight`,
/// `gen --equations-part-weight`).
pub const EQUATIONS_PART_WEIGHT: usize = 2000;

struct Args {
    cmd: String,
    kore: PathBuf,
    runtime: Option<PathBuf>,
    out: Option<PathBuf>,
    name: String,
    prelude: Option<String>,
    prelude_git: Option<String>,
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
        prelude: None,
        prelude_git: None,
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
            "--prelude" => a.prelude = Some(it.next().unwrap()),
            "--prelude-git" => a.prelude_git = Some(it.next().unwrap()),
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

/// The Lean files of a generated module: the file itself and, for an `Equations.lean` written in
/// parts (`eqns::emit_modules`), the parts it imports (`import NS.Equations.PartK`, at
/// `NS/Equations/PartK.lean` beside it), each with the path suffix its build errors name.
fn module_files(file: &std::path::Path) -> Vec<(PathBuf, String)> {
    let name = file.file_name().unwrap().to_string_lossy().to_string();
    let mut out = vec![(file.to_path_buf(), name.clone())];
    let (Some(dir), Some(stem)) = (file.parent(), file.file_stem()) else {
        return out;
    };
    let stem = stem.to_string_lossy().to_string();
    let ns = dir.file_name().map(|n| n.to_string_lossy().to_string());
    let text = std::fs::read_to_string(file).unwrap_or_default();
    for l in text.lines().take_while(|l| l.starts_with("import ")) {
        let Some(ns) = &ns else { break };
        let Some(part) = l
            .strip_prefix("import ")
            .and_then(|m| m.strip_prefix(&format!("{ns}.{stem}.")))
        else {
            continue;
        };
        if part.is_empty() || part.contains('.') {
            continue;
        }
        out.push((
            dir.join(&stem).join(format!("{part}.lean")),
            format!("{stem}/{part}.lean"),
        ));
    }
    out
}

/// The theorem of `lines` (a generated file) that an error at line `line` (1-based) is in: the
/// last `theorem` line at or before it, unless the error is on the lines that open a declaration
/// before its `theorem` keyword (its doc comment, a `set_option … in`), where Lean reports an
/// error of the whole declaration, such as a proof out of heartbeats; then the theorem they open.
fn failed_theorem(lines: &[&str], line: usize) -> Option<String> {
    let opens =
        |l: &str| l.starts_with("/--") || (l.starts_with("set_option ") && l.ends_with(" in"));
    let mut i = line.checked_sub(1)?;
    if lines.get(i).is_some_and(|l| opens(l)) {
        while lines.get(i).is_some_and(|l| opens(l)) {
            i += 1;
        }
    }
    let i = i.min(lines.len().checked_sub(1)?);
    (0..=i).rev().find_map(|k| {
        // the name ends at the first space outside `«…»` (rule names hold spaces)
        lines[k]
            .strip_prefix("theorem ")
            .map(|name| invariants::case_token(name).unwrap())
    })
}

/// `open-from-log EQUATIONS.lean BUILD.log OPEN.txt`: add the theorems whose proofs failed in a
/// build log to the open-obligation list (they are then emitted as statements only). The errors
/// of the parts of an `Equations.lean` written in parts count as its own.
fn open_from_log(args: &[String]) {
    let [eq_file, log, out] = args else {
        panic!("usage: open-from-log EQUATIONS.lean BUILD.log OPEN.txt")
    };
    let log = std::fs::read_to_string(log).unwrap();
    // the names of the failed proofs, added to the list; its markers and comments are kept
    let list_text = std::fs::read_to_string(out).unwrap_or_default();
    let mut open: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for (file, suffix) in module_files(std::path::Path::new(eq_file)) {
        let Ok(text) = std::fs::read_to_string(&file) else {
            continue;
        };
        let lines: Vec<&str> = text.lines().collect();
        for l in log.lines() {
            let Some(pos) = l.find(&format!("{suffix}:")) else {
                continue;
            };
            if !l.trim_start().starts_with("error:") {
                continue;
            }
            // `Equations.lean:` must not match the error of a part (`Equations/Part1.lean:`), nor
            // the reverse: the suffix starts the path or follows a `/`
            if pos > 0 && !l[..pos].ends_with('/') && !l[..pos].ends_with(' ') {
                continue;
            }
            let rest = &l[pos + suffix.len() + 1..];
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
            if let Some(name) = failed_theorem(&lines, line) {
                open.insert(name);
            }
        }
    }
    let text = refuted::add_names(&list_text, &open);
    eprintln!(
        "{} open obligations",
        text.lines()
            .filter(|l| refuted::name_of(l).is_some())
            .count()
    );
    std::fs::write(out, text).unwrap();
}

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    if raw.first().map(|s| s.as_str()) == Some("claims") {
        return claims::main(&raw[1..]);
    }
    if raw.first().map(|s| s.as_str()) == Some("relate") {
        return relate::main(&raw[1..]);
    }
    if raw.first().map(|s| s.as_str()) == Some("confluence") {
        return confluence::main(&raw[1..]);
    }
    if raw.first().map(|s| s.as_str()) == Some("noninterference") {
        return noninterference::main(&raw[1..]);
    }
    if raw.first().map(|s| s.as_str()) == Some("refine") {
        return refine::main(&raw[1..]);
    }
    if raw.first().map(|s| s.as_str()) == Some("soundness") {
        return soundness::main(&raw[1..]);
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
    // the per-sort encoding (one Lean type per sort) is retired: the arity-indexed term universe
    // (design.md §2.1) is the only one; `--arity-terms`, its former opt-in, changes nothing
    for gone in ["--per-sort-terms", "--det-pairs", "--linear-terms"] {
        if a.rest.iter().any(|x| x == gone) {
            panic!("{gone}: removed with the per-sort encoding");
        }
    }
    // fallback arms on irrefutable matches: the family's match compiler would otherwise refute
    // every other constructor of the family
    render::set_fallback_arms(!a.rest.iter().any(|x| x == "--no-fallback-arms"));
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
            // the functions the claims of a specification apply (`claims.rs`): `--spec FILE`,
            // repeatable, the spec's compiled `definition.kore` as `claims --spec` reads it
            let spec_files: Vec<PathBuf> = a
                .rest
                .iter()
                .enumerate()
                .filter(|(_, x)| x.as_str() == "--spec")
                .map(|(i, _)| PathBuf::from(&a.rest[i + 1]))
                .collect();
            roots.extend(claims::spec_functions(&spec_files, &def));
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
            write(
                &out.join("lakefile.lean"),
                &drivers::lakefile(
                    ns,
                    &drivers::require_line(a.prelude.as_deref(), a.prelude_git.as_deref()),
                    &exe,
                    !fgen.params.is_empty(),
                ),
            );
            // `functions.txt`, the functions the library defines, which `claims` checks its claims'
            // functions against; written only for a library generated for claims (`--spec`)
            if spec_files.is_empty() {
                let _ = std::fs::remove_file(out.join("functions.txt"));
            } else {
                write(
                    &out.join("functions.txt"),
                    &claims::functions_list(fgen.fns.keys()),
                );
            }
            let top = rules::top_sort(&def).unwrap();
            // several matches: the ranked, list-valued emitter (even with one priority)
            let (rs, prios, ranked) = rules::collect_ranked(&def, &m, &fgen.fns, &order)
                .unwrap_or_else(|e| panic!("{e}"));
            let multi = rs.iter().any(|r| r.multi);
            if multi {
                eprintln!(
                    "note: {} rules with several matches (free-key map patterns): list-valued matchers",
                    rs.iter().filter(|r| r.multi).count()
                );
            }
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
                    "import {ns}.Terms\nimport {ns}.Functions\nimport {ns}.Rules\nimport {ns}.Adequacy\nimport {ns}.Determinism\nimport {ns}.Equations\n{}import KPrelude.Version\n\n/-! Generated by k2lean {v}: built against the k2lean package of that release (PKG-5). -/\n\n#k2l_check_prelude \"{v}\"\n",
                    if fgen.diverges.is_empty() {
                        String::new()
                    } else {
                        format!("import {ns}.Diverges\nimport {ns}.DivergesSound\n")
                    },
                    v = env!("CARGO_PKG_VERSION")
                ),
            );
            let (terms_text, size_instances) =
                (terms_arity::emit(&m, ns), funcs::list_size_instances(&m));
            write(&out.join(ns).join("Terms.lean"), &terms_text);
            write(
                &out.join(ns).join("Functions.lean"),
                &functions_module(ns, &fgen, &size_instances),
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
                // the fuel twins, for kernel evaluation through well-founded functions (not imported
                // by the library's root: built by whoever imports it)
                // the call graph's groups by Lean name
                let lean_groups: Vec<Vec<String>> = fgen
                    .groups
                    .iter()
                    .map(|g| {
                        g.iter()
                            .filter_map(|f| fgen.fns.get(f).map(|s| s.lean.clone()))
                            .collect()
                    })
                    .collect();
                match fuel::emit(
                    &fgen.lean,
                    &fgen.recursive,
                    &lean_groups,
                    &rs,
                    &prios,
                    &top,
                    ns,
                ) {
                    Some(Ok(text)) => write(
                        &out.join(ns).join("Fuel.lean"),
                        &with_hooks(text, ns, &fgen.params),
                    ),
                    Some(Err(e)) => eprintln!("note: {ns}.Fuel not generated: {e}"),
                    None => {}
                }
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
            }
            // determinism along the rule index, modulo the overlapping pairs (`det2`), for every
            // definition whose rules match once (`--det2` is accepted and changes nothing)
            let mut det_overlaps = 0;
            let mut det_unwitnessed = 0;
            let mut det_witnessed = Vec::new();
            if multi {
                if a.rest.iter().any(|x| x == "--det2") {
                    eprintln!(
                        "note: --det2 needs every rule to match once; with free-key map rules Determinism.lean states `uniqueAt`"
                    );
                }
            } else {
                let d = det2::emit(
                    &def,
                    &m,
                    &rs,
                    &prios,
                    ranked,
                    &top,
                    ns,
                    &rules::ctor_info(&m),
                    &unfold,
                    &fgen.fns,
                    &det2::Opts::from_args(&a.rest),
                );
                // the lemma modules of an earlier generation may be more than this one's
                let _ = std::fs::remove_dir_all(out.join(ns).join("Determinism"));
                for (path, text) in d.files {
                    write(&out.join(path), &with_hooks(text, ns, &fgen.params));
                }
                eprintln!(
                    "determinism: {} overlapping pairs\n{}",
                    d.overlaps, d.report
                );
                det_overlaps = d.overlaps;
                det_unwitnessed = d.unwitnessed;
                det_witnessed = d.witnessed.clone();
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
            // the open obligations, and those of them marked refuted (`refuted.rs`)
            let open_list = match &a.open {
                Some(p) => refuted::parse(&std::fs::read_to_string(p).unwrap_or_default())
                    .unwrap_or_else(|e| panic!("{}: {e}", p.display())),
                None => Default::default(),
            };
            let open = open_list.names.clone();
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
            let mut stated = eqns::equation_theorems(
                &def,
                &m,
                &stmt_fns,
                &funcs::equations_modulo_overloads(&def, &m),
            );
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
            // hooks and the projection lemmas (not the injections/projections), in every proof's
            // simp set; the generated definitions, of which each proof gets those it names
            let mut eq_base: Vec<String> = hooks::eq_unfold_names()
                .iter()
                .map(|s| s.to_string())
                .collect();
            eq_base.extend(terms::inj_pairs(&m).iter().map(|(x, y)| {
                format!(
                    "proj_eq_some_{}_{}",
                    names::short_sort(y),
                    names::short_sort(x)
                )
            }));
            // in modules of bounded weight (`eqns::emit_modules`); the parts of an earlier
            // generation go first, so that a part no longer generated is not left behind
            let part_weight = match a.rest.iter().position(|x| x == "--equations-part-weight") {
                Some(i) => a.rest[i + 1]
                    .parse::<usize>()
                    .ok()
                    .filter(|w| *w > 0)
                    .expect("--equations-part-weight: a positive integer"),
                None => EQUATIONS_PART_WEIGHT,
            };
            // the heartbeat budget of each proof (`eqns::Budget`)
            let mut budget = eqns::Budget::default();
            if let Some(i) = a.rest.iter().position(|x| x == "--equations-heartbeats") {
                budget.default = a.rest[i + 1]
                    .parse::<usize>()
                    .ok()
                    .filter(|h| *h > 0)
                    .expect("--equations-heartbeats: a positive integer");
            }
            if let Some(i) = a
                .rest
                .iter()
                .position(|x| x == "--equations-heartbeats-file")
            {
                let f = &a.rest[i + 1];
                let text = std::fs::read_to_string(f)
                    .unwrap_or_else(|e| panic!("--equations-heartbeats-file {f}: {e}"));
                budget
                    .read_overrides(&text, &stated)
                    .unwrap_or_else(|e| panic!("--equations-heartbeats-file {f}: {e}"));
            }
            let _ = std::fs::remove_dir_all(out.join(ns).join("Equations"));
            write(
                &out.join(ns).join("EqBase.lean"),
                &eqns::emit_eq_base(ns, &eq_base),
            );
            let eq_weight: usize = stated.iter().map(|s| eqns::weight(s, &fgen.unfold)).sum();
            let mut eq_modules = 0;
            for (path, text) in eqns::emit_modules(
                ns,
                &stated,
                &open,
                &eq_base,
                &fgen.unfold,
                &fgen.recursive,
                &fgen.list_recursive,
                part_weight,
                &budget,
            ) {
                write(
                    &out.join(ns).join(format!("{path}.lean")),
                    &with_hooks(text, ns, &fgen.params),
                );
                eq_modules += 1;
            }
            eprintln!(
                "{} equations and simplifications stated, {} open; weight {eq_weight} in {} (bound {part_weight})",
                stated.len(),
                stated.iter().filter(|s| open.contains(&s.name)).count(),
                if eq_modules == 1 {
                    "one module".to_string()
                } else {
                    format!("{} parts", eq_modules - 1)
                }
            );
            // kind 1 invariants: `InvariantDefs.lean`, `Invariants.lean`, `open-invariant-cases.txt`,
            // `invariant-unfold.txt`
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
                write(&out.join("invariant-unfold.txt"), &o.unfold_list);
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
                    &parametric_test(cases::test_main(ns, &top), ns, &fgen.params),
                );
            } else {
                write(
                    &out.join(format!("{ns}Test")).join("Main.lean"),
                    &parametric_test(drivers::test_main(ns, &top), ns, &fgen.params),
                );
            }
            // and the instance theorems of the functions with a free-key equation (`agree.rs`)
            let proved: Vec<String> = stated
                .iter()
                .filter(|s| !open.contains(&s.name))
                .map(|s| s.name.clone())
                .chain(fgen.agree_thms.iter().cloned())
                .collect();
            let mut guard = drivers::axioms_with(ns, &proved, ranked, multi, init_ok);
            if !open_list.refuted.is_empty() {
                // the refutations of the obligations marked refuted, under the guard
                let prelude: Vec<&String> = open_list
                    .refuted
                    .iter()
                    .filter(|(_, s)| **s == refuted::Source::Prelude)
                    .map(|(n, _)| n)
                    .collect();
                let hand: Vec<&String> = open_list
                    .refuted
                    .iter()
                    .filter(|(_, s)| **s == refuted::Source::Hand)
                    .map(|(n, _)| n)
                    .collect();
                if !prelude.is_empty() {
                    if !fgen.params.is_empty() {
                        panic!(
                            "{}: refuting an obligation for every implementation of the parameters needs an instance: mark it `refuted hand`",
                            prelude[0]
                        );
                    }
                    write(
                        &out.join(ns).join("Refuted.lean"),
                        &refuted::emit_refuted(ns, &prelude),
                    );
                }
                let hand_file = out.join(ns).join("RefutedHand.lean");
                if !hand.is_empty() && !hand_file.exists() {
                    write(
                        &hand_file,
                        &with_hooks(
                            refuted::hand_template(ns, &hand, !fgen.params.is_empty()),
                            ns,
                            &fgen.params,
                        ),
                    );
                    eprintln!(
                        "note: wrote the hand-refutation file {} (it is never overwritten)",
                        hand_file.display()
                    );
                }
                write(
                    &out.join(format!("{ns}Test")).join("Refuted.lean"),
                    &refuted::emit_check(ns, &open_list),
                );
                guard = format!("import {ns}Test.Refuted\n{guard}");
            }
            // the open obligations retried (INFRA-6), the refuted ones aside
            let retry: Vec<&eqns::Stated> = stated
                .iter()
                .filter(|s| open.contains(&s.name) && !open_list.refuted.contains_key(&s.name))
                .collect();
            let retry_file = out.join(format!("{ns}Test")).join("Retry.lean");
            if retry.is_empty() {
                let _ = std::fs::remove_file(&retry_file);
            } else {
                write(
                    &retry_file,
                    &with_hooks(
                        eqns::emit_retry(
                            ns,
                            &retry,
                            &eq_base,
                            &fgen.unfold,
                            &fgen.recursive,
                            &fgen.list_recursive,
                            &budget,
                        ),
                        ns,
                        &fgen.params,
                    ),
                );
            }
            // the divergence obligations of the least fixed points (TERM-1)
            let div_file = out.join(ns).join("Diverges.lean");
            let div_check = out.join(format!("{ns}Test")).join("Diverges.lean");
            let div_sound = out.join(ns).join("DivergesSound.lean");
            if fgen.diverges.is_empty() {
                let _ = std::fs::remove_file(&div_file);
                let _ = std::fs::remove_file(&div_check);
                let _ = std::fs::remove_file(&div_sound);
            } else {
                write(
                    &div_file,
                    &with_hooks(diverges::emit(ns, &fgen.diverges), ns, &fgen.params),
                );
                let names: Vec<&String> = fgen.diverges.iter().map(|(n, _)| n).collect();
                // a refuted divergence: the group's rewriting terminates, so the least fixed point
                // is not what K's equations need, a measure is
                if let Some(n) = names.iter().find(|n| open_list.refuted.contains_key(**n)) {
                    panic!(
                        "{n} is marked refuted: K's rewriting of the group terminates, so it needs a termination measure, not `partial_fixpoint`"
                    );
                }
                let hand_file = out.join(ns).join("DivergesHand.lean");
                if !hand_file.exists() {
                    write(
                        &hand_file,
                        &with_hooks(diverges::hand_template(ns, &names), ns, &fgen.params),
                    );
                    eprintln!(
                        "note: wrote the divergence-proof file {} (it is never overwritten)",
                        hand_file.display()
                    );
                }
                let hand = std::fs::read_to_string(&hand_file).unwrap_or_default();
                let proved: Vec<&String> = names
                    .iter()
                    .copied()
                    .filter(|n| !open.contains(*n) && diverges::proved_in(&hand, n))
                    .collect();
                for n in &names {
                    if !proved.contains(n) {
                        eprintln!("note: {n}: open (no proof in {})", hand_file.display());
                    }
                }
                // the derived soundness of the pending-call functions (TERM-1c): open where the
                // tactic did not close it
                let sound: Vec<&(String, String)> = fgen
                    .pending_sound
                    .iter()
                    .filter(|(n, _)| !open.contains(n))
                    .collect();
                for (n, _) in &fgen.pending_sound {
                    if open.contains(n) {
                        eprintln!("note: {n}: open (the generic proof did not close it)");
                    }
                }
                write(
                    &div_sound,
                    &with_hooks(diverges::emit_sound(ns, &sound), ns, &fgen.params),
                );
                let sound_names: Vec<&String> = sound.iter().map(|(n, _)| n).collect();
                write(
                    &div_check,
                    &with_hooks(
                        diverges::emit_check(ns, &proved, &sound_names),
                        ns,
                        &fgen.params,
                    ),
                );
                guard = format!("import {ns}Test.Diverges\n{guard}");
            }
            write(&out.join(format!("{ns}Test")).join("Axioms.lean"), &guard);
            if !multi {
                write(
                    &out.join(format!("{ns}Test")).join("DetAxioms.lean"),
                    &det2::guard(ns, det_overlaps, det_unwitnessed, &det_witnessed),
                );
            }
            write(
                &out.join(format!("{ns}Bench")).join("Main.lean"),
                &if fgen.params.is_empty() {
                    drivers::bench_main(ns, &top)
                } else {
                    drivers::parametric_bench(&drivers::bench_main(ns, &top), ns)
                },
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
                    "import Lake\nopen Lake DSL\n\npackage «{ns}» where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n  fixedToolchain := true\n\n{}\n\n@[default_target]\nlean_lib {ns}\n",
                    drivers::require_line(a.prelude.as_deref(), a.prelude_git.as_deref())
                ),
            );
            write(
                &out.join(format!("{ns}.lean")),
                &format!("import {ns}.Terms\n"),
            );
            let text = terms_arity::emit(&m, ns);
            write(&out.join(ns).join("Terms.lean"), &text);
            for n in &m.notes {
                eprintln!("note: {n}");
            }
            eprintln!("note: unsupported hooked sorts: {:?}", m.unsupported);
        }
        "configs" => goldens::configs(&def, &a.rest, &a.name),
        // the classification of rule pairs behind `gen --det2`, as a report (read-only)
        "pairs" => pairs::run(&def, &a.rest, &a.kore, a.runtime.as_deref()),
        other => panic!("unknown command {other}"),
    }
}

/// `Functions.lean`: the `Hooks` class, `extra` (instances the term universe needs), and the
/// generated definitions. The termination proofs of recursive functions (`decreasing_by`) use
/// `KPrelude.Termination`; they are elaborated without a heartbeat bound, as the term universe.
fn functions_module(ns: &str, fgen: &funcs::Generated, extra: &str) -> String {
    // the instance theorems of free-key functions (`agree.rs`) use `KPrelude.Ext`'s tactic
    let (import, opts) = if fgen.recursive.is_empty()
        && extra.is_empty()
        && fgen.agree_thms.is_empty()
    {
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

/// A test driver as generated, or over the parameters when the library has some (PKG-6).
fn parametric_test(text: String, ns: &str, params: &[(String, Vec<String>, String)]) -> String {
    if params.is_empty() {
        text
    } else {
        drivers::parametric_test(&text, ns)
    }
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

    /// The `lean-toolchain` files under `root` that do not pin `LEAN_TOOLCHAIN` (Lake's build
    /// directories and Cargo's skipped).
    fn other_toolchains(root: &std::path::Path) -> Vec<std::path::PathBuf> {
        let mut out = Vec::new();
        let mut todo = vec![root.to_path_buf()];
        while let Some(d) = todo.pop() {
            let Ok(rd) = std::fs::read_dir(&d) else {
                continue;
            };
            for e in rd.flatten() {
                let p = e.path();
                let name = e.file_name();
                if p.is_dir() {
                    if ![".lake", "target", ".git"].contains(&name.to_str().unwrap_or("")) {
                        todo.push(p);
                    }
                } else if name == "lean-toolchain"
                    && std::fs::read_to_string(&p).ok().as_deref() != Some(LEAN_TOOLCHAIN)
                {
                    out.push(p);
                }
            }
        }
        out.sort();
        out
    }

    /// The `require` of the package (PKG-5): by git with the commit and the package's directory,
    /// or by path; the git form wins.
    #[test]
    fn the_package_is_required_by_git_or_by_path() {
        assert_eq!(
            drivers::require_line(
                Some("../../lean"),
                Some("https://example.org/k-rust@0123abc")
            ),
            "require k2lean from git \"https://example.org/k-rust\" @ \"0123abc\" / \"k2lean/lean\""
        );
        assert_eq!(
            drivers::require_line(Some("../../lean"), None),
            "require k2lean from \"../../lean\""
        );
    }

    /// The prelude tags exactly the hooks the generic equation proofs unfold (`k2l_eq`, CT-4c).
    #[test]
    fn the_prelude_tags_the_equation_proofs_hooks() {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../lean/prelude/KPrelude/EqBase.lean");
        let text = std::fs::read_to_string(&p).unwrap();
        let tagged: Vec<&str> = text
            .split("attribute [k2l_eq]")
            .nth(1)
            .unwrap()
            .split_whitespace()
            .collect();
        assert_eq!(tagged, hooks::eq_unfold_names());
    }

    /// One toolchain (PKG-4): the `k2lean` package, the demos and the fixtures pin the Lean the
    /// generator writes, so that a project requiring them never mixes two.
    #[test]
    fn every_checked_in_project_pins_the_generators_toolchain() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        assert!(root.join("lean/lean-toolchain").exists());
        assert_eq!(other_toolchains(&root), Vec::<std::path::PathBuf>::new());
        // and a project pinning another is reported
        let d = std::env::temp_dir().join(format!("k2lean-toolchain-{}", std::process::id()));
        std::fs::create_dir_all(d.join("p")).unwrap();
        std::fs::write(d.join("p/lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        assert_eq!(other_toolchains(&d), vec![d.join("p/lean-toolchain")]);
        std::fs::remove_dir_all(&d).unwrap();
    }

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

    /// An error at the first line of a declaration (its doc comment or `set_option … in`, where
    /// Lean reports a proof out of heartbeats) is the theorem's that the line opens, not the
    /// theorem's before it.
    #[test]
    fn failed_theorem_at_declaration_start() {
        let text = "/-- a -/\ntheorem Eqn.a_1 :\n    1 = 1 := by\n  rfl\n\nset_option maxHeartbeats 400000 in\n/-- b -/\ntheorem Eqn.b_1 :\n    1 = 1 := by\n  rfl\n";
        let lines: Vec<&str> = text.lines().collect();
        let at = |n| failed_theorem(&lines, n);
        assert_eq!(at(1).as_deref(), Some("Eqn.a_1"));
        assert_eq!(at(4).as_deref(), Some("Eqn.a_1"));
        assert_eq!(at(5).as_deref(), Some("Eqn.a_1"));
        assert_eq!(at(6).as_deref(), Some("Eqn.b_1"));
        assert_eq!(at(7).as_deref(), Some("Eqn.b_1"));
        assert_eq!(at(10).as_deref(), Some("Eqn.b_1"));
    }

    /// An `Equations.lean` written in parts: the errors of each part name its theorems, and an
    /// error of a part is not read against the aggregating file's lines, nor the reverse.
    #[test]
    fn open_from_log_reads_the_parts() {
        let d = std::env::temp_dir().join(format!("k2lean-open-parts-{}", std::process::id()));
        let n = d.join("N");
        std::fs::create_dir_all(n.join("Equations")).unwrap();
        let eq = n.join("Equations.lean");
        std::fs::write(
            &eq,
            "import N.Equations.Part1\nimport N.Equations.Part2\n\n/-! doc -/\n",
        )
        .unwrap();
        let part = |k: usize, name: &str| {
            format!("import N.Functions\n\nnamespace N\n\ntheorem Eqn.{name} :\n    1 = 1 := by\n  rfl\n\nend N\n")
                .replace("Functions", &format!("Functions -- {k}"))
        };
        std::fs::write(n.join("Equations/Part1.lean"), part(1, "a_1")).unwrap();
        std::fs::write(n.join("Equations/Part2.lean"), part(2, "b_1")).unwrap();
        let log = d.join("build.log");
        std::fs::write(
            &log,
            "error: N/Equations/Part2.lean:7:2: unsolved goals\nerror: N/Equations.lean:6:0: not a theorem line\nerror: N/XEquations/Part1.lean:6:0: another module\n",
        )
        .unwrap();
        let open = d.join("open.txt");
        let s = |p: &std::path::Path| p.to_string_lossy().to_string();
        open_from_log(&[s(&eq), s(&log), s(&open)]);
        assert_eq!(std::fs::read_to_string(&open).unwrap(), "Eqn.b_1\n");
        let _ = std::fs::remove_dir_all(&d);
    }
}
