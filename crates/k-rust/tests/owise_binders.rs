//! The owise axiom is one scope for names: each variable name in it denotes one variable at one
//! sort, and no binder captures a name that is free under it.
//!
//! The axiom of an `[owise]` equation states that no competitor applies: for each competitor, no
//! instance of its free variables matches its arguments and satisfies its condition. Each
//! competitor's disjunct therefore restates the competitor's own antecedent (its condition and the
//! matches of its arguments), with its free variables bound by the disjunct's outer `\exists`.
//! The variables of a quantifier inside a competitor are local to it, and the restatement must
//! keep every binder binding exactly what it binds in the competitor's own axiom, while the
//! names of the axiom (the owise rule's variables, the names minted for the competitors' free
//! variables, and every competitor's bound names) stay apart.
//!
//! The shapes are the cross product of five axes, each about the names a quantifier of the probed
//! competitor `q` binds:
//! - the binder: named (`#Exists Y`), anonymous (`#Exists _`), nested (`#Exists Y . #Exists Y0`)
//!   or shadowing (`#Exists Y` inside `#Exists Y`);
//! - its position: in `q`'s argument or in its condition;
//! - its bound names against the owise rule's variables: absent, at the same sort, or at another;
//! - against another competitor's bound names: absent, at the same sort, or at another;
//! - against a name minted for an earlier competitor's free variable: no clash, a clash at the
//!   same sort, or at another.
//!
//! Combinations that no K text realizes are dropped, each with its reason ([`shapes::unrealizable`]); the
//! axes a shape claims are checked against its compiled KORE, so a text that stops realizing its
//! axis fails the test instead of passing vacuously.
//!
//! Every shape goes through the library route (`load_for_compilation`,
//! `compile_loaded_definition`, which runs the kompile invariants in this profile and the
//! one-sort-per-name check on every axiom, then the KORE reader), and must compile. Its owise
//! axiom must then restate each competitor's own antecedent up to the renaming of bound
//! variables and of the free ones to the disjunct's outer binders (the capture check), keep every
//! bound name whose name no earlier part of the axiom holds, and rename every other one. A shape
//! with the quantifier in the condition is loaded by `Backend::new` and run at `go(1)`, `go(2)`
//! and `go(4)`, where the owise equation's value must follow from the meaning; the portable build
//! may leave a quantified condition undecided. A shape with the quantifier in an argument is
//! refused at `Backend::new`, which reads no quantifier at a term position, until the ML lane's
//! located compile refusal (MLP/4) refuses it at compile.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest},
    builtin::embedded,
    kompile::{CompileOptions, compile_loaded_definition},
    kore::{
        ast::{Pattern, Sentence as KoreSentence, Variable},
        codec,
        parser::{parse_definition, parse_pattern},
        printer::Printer,
    },
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};

#[path = "owise_binders/shapes.rs"]
mod shapes;

use shapes::{Binder, PROGRAMS, Position, Relation, Shape, cross_product, expected_value, source};

fn resolver(_: &str, required: &str) -> Result<ResolvedSource, String> {
    embedded(required).ok_or_else(|| format!("unexpected require {required}"))
}

/// The compiled KORE of `source`, through the library route.
fn compile(name: &str, source: String) -> Result<String, String> {
    let mut resolver = resolver;
    let options = LoadOptions {
        implicit_sources: vec![
            embedded("kast.md").unwrap(),
            embedded("prelude.md").unwrap(),
        ],
        ..k_rust::kompile::CompilationBackend::Rust.load_options()
    };
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new(format!("owise_binders/{name}.k"), source),
        "P",
        Some("P-SYNTAX"),
        &mut resolver,
        &options,
    )
    .map_err(|error| format!("load: {error}"))?;
    compile_loaded_definition(&loaded, CompileOptions::default())
        .map(|artifacts| artifacts.definition_kore)
        .map_err(|error| format!("compile: {error}"))
}

fn label(attributes: &k_rust::kore::ast::Attributes) -> Option<String> {
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == "label" => {
            match arguments.as_slice() {
                [Pattern::String(value)] => value.as_utf8().ok().map(str::to_owned),
                _ => None,
            }
        }
        _ => None,
    })
}

/// The axioms of the module `P`, by label.
fn axioms(kore: &str) -> Result<BTreeMap<String, Pattern>, String> {
    let definition = parse_definition(kore).map_err(|error| format!("KORE load: {error}"))?;
    let mut axioms = BTreeMap::new();
    for module in &definition.modules {
        for sentence in &module.sentences {
            if let KoreSentence::Axiom {
                pattern,
                attributes,
                ..
            } = sentence
                && let Some(label) = label(attributes)
            {
                axioms.insert(label, pattern.as_ref().clone());
            }
        }
    }
    Ok(axioms)
}

/// The antecedent `\and(condition, matches)` of a competitor's own axiom.
fn own_antecedent(axiom: &Pattern) -> Result<&Pattern, String> {
    match axiom {
        Pattern::Implies { left, .. } => Ok(left),
        other => Err(format!(
            "a competitor axiom is not an implication: {}",
            text(other)
        )),
    }
}

/// The competitor disjuncts of an owise axiom `\implies(\and(\not(\or(d1, .. \bottom)), own),
/// ..)`, in order, and the owise rule's own part (everything but the disjunction).
fn owise_parts(axiom: &Pattern) -> Result<(Vec<&Pattern>, Vec<&Pattern>), String> {
    let malformed = || format!("unexpected owise axiom: {}", text(axiom));
    let Pattern::Implies { left, right, .. } = axiom else {
        return Err(malformed());
    };
    let Pattern::And { arguments, .. } = left.as_ref() else {
        return Err(malformed());
    };
    let [Pattern::Not { argument, .. }, own] = arguments.as_slice() else {
        return Err(malformed());
    };
    let mut disjuncts = Vec::new();
    let mut rest = argument.as_ref();
    while let Pattern::Or { arguments, .. } = rest {
        let [first, second] = arguments.as_slice() else {
            return Err(malformed());
        };
        disjuncts.push(first);
        rest = second;
    }
    if !matches!(rest, Pattern::Bottom { .. }) {
        return Err(malformed());
    }
    Ok((disjuncts, vec![own, right.as_ref()]))
}

fn text(pattern: &Pattern) -> String {
    Printer::compact().print_pattern(pattern)
}

/// Every variable occurring in `pattern`, free or bound, and every binder's variable.
fn all_variables(pattern: &Pattern, found: &mut BTreeSet<Variable>) {
    match pattern {
        Pattern::Variable(variable) => {
            found.insert(variable.clone());
        }
        Pattern::Exists { variable, .. }
        | Pattern::Forall { variable, .. }
        | Pattern::Mu { variable, .. }
        | Pattern::Nu { variable, .. } => {
            found.insert(variable.as_ref().clone());
        }
        _ => {}
    }
    for child in k_rust::kore::walk::children(pattern) {
        all_variables(child, found);
    }
}

/// The variables of every `\exists` and `\forall` of `pattern`, in preorder.
fn binders(pattern: &Pattern, found: &mut Vec<Variable>) {
    if let Pattern::Exists { variable, .. } | Pattern::Forall { variable, .. } = pattern {
        found.push(variable.as_ref().clone());
    }
    for child in k_rust::kore::walk::children(pattern) {
        binders(child, found);
    }
}

/// How the names `bound` meet the variables `names`: every bound name must meet them alike.
fn relation(bound: &BTreeSet<Variable>, names: &BTreeSet<Variable>) -> Result<Relation, String> {
    let relations = bound
        .iter()
        .map(|variable| {
            let sorts = names
                .iter()
                .filter(|name| name.name == variable.name)
                .map(|name| &name.sort)
                .collect::<Vec<_>>();
            if sorts.is_empty() {
                Relation::Absent
            } else if sorts.iter().all(|sort| **sort == variable.sort) {
                Relation::SameSort
            } else {
                Relation::OtherSort
            }
        })
        .collect::<Vec<_>>();
    match relations.first() {
        None => Ok(Relation::Absent),
        Some(first) if relations.iter().all(|relation| relation == first) => Ok(*first),
        Some(_) => Err(format!(
            "the bound names meet the names unevenly: {relations:?}"
        )),
    }
}

fn is_equation_variable(variable: &Variable) -> bool {
    variable
        .name
        .strip_prefix('X')
        .is_some_and(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
}

fn is_generated(name: &str) -> bool {
    name.strip_prefix("Var'Unds'Gen")
        .is_some_and(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
}

/// `pattern` with each binder's variable renamed `B<i>` (the i-th binder in preorder), each
/// occurrence it binds renamed alike, and each free variable other than an equation variable
/// renamed `F<j>` (the j-th distinct one in preorder). A free variable outside `allowed` (when
/// given) is an error: it is a competitor variable left free.
fn canonical(pattern: &Pattern, allowed: Option<&BTreeSet<Variable>>) -> Result<Pattern, String> {
    struct Walk<'a> {
        scope: Vec<(Variable, String)>,
        free: BTreeMap<Variable, String>,
        binders: usize,
        allowed: Option<&'a BTreeSet<Variable>>,
    }
    impl Walk<'_> {
        fn rename(&mut self, variable: &Variable) -> Result<Variable, String> {
            if let Some((_, name)) = self.scope.iter().rev().find(|(bound, _)| bound == variable) {
                return Ok(Variable {
                    name: name.clone(),
                    ..variable.clone()
                });
            }
            if is_equation_variable(variable) {
                return Ok(variable.clone());
            }
            if let Some(allowed) = self.allowed
                && !allowed.contains(variable)
            {
                return Err(format!("{} is free", variable.name));
            }
            let next = self.free.len();
            let name = self
                .free
                .entry(variable.clone())
                .or_insert_with(|| format!("F{next}"))
                .clone();
            Ok(Variable {
                name,
                ..variable.clone()
            })
        }

        fn walk(&mut self, pattern: &mut Pattern) -> Result<(), String> {
            match pattern {
                Pattern::Variable(variable) => {
                    *variable = self.rename(variable)?;
                    return Ok(());
                }
                Pattern::Exists { variable, body, .. } | Pattern::Forall { variable, body, .. } => {
                    let name = format!("B{}", self.binders);
                    self.binders += 1;
                    self.scope.push((variable.as_ref().clone(), name.clone()));
                    variable.name = name;
                    let result = self.walk(body);
                    self.scope.pop();
                    return result;
                }
                _ => {}
            }
            for child in children_mut(pattern) {
                self.walk(child)?;
            }
            Ok(())
        }
    }
    let mut walk = Walk {
        scope: Vec::new(),
        free: BTreeMap::new(),
        binders: 0,
        allowed,
    };
    let mut pattern = pattern.clone();
    walk.walk(&mut pattern)?;
    if let Some(allowed) = allowed {
        let unused = allowed
            .iter()
            .filter(|variable| !walk.free.contains_key(variable))
            .map(|variable| variable.name.clone())
            .collect::<Vec<_>>();
        if !unused.is_empty() {
            return Err(format!("outer binders bind nothing: {}", unused.join(", ")));
        }
    }
    Ok(pattern)
}

fn children_mut(pattern: &mut Pattern) -> Vec<&mut Pattern> {
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => arguments.iter_mut().collect(),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => vec![argument],
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => vec![left, right],
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => vec![body],
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => Vec::new(),
    }
}

/// The capture check of one competitor: its disjunct is its own antecedent up to renaming, every
/// outer binder binding one free variable of it and every inner binder the occurrences the
/// competitor's own binder binds. Returns the pairs (own binder, emitted binder), in preorder.
fn restates(own: &Pattern, disjunct: &Pattern) -> Result<Vec<(Variable, Variable)>, String> {
    let (body, outer) = disjunct.leading_existentials();
    let outer = outer.into_iter().cloned().collect::<BTreeSet<_>>();
    let source = canonical(own, None)?;
    let emitted = canonical(body, Some(&outer))?;
    if source != emitted {
        return Err(format!(
            "the disjunct binds otherwise than the competitor: own {} vs emitted {}",
            text(own),
            text(disjunct)
        ));
    }
    let (mut own_binders, mut emitted_binders) = (Vec::new(), Vec::new());
    binders(own, &mut own_binders);
    binders(body, &mut emitted_binders);
    Ok(own_binders.into_iter().zip(emitted_binders).collect())
}

/// A compact rendering of a leaf's `<k>` cell, `Lbl` prefixes, injections and the `kseq` unit
/// dropped.
fn render(pattern: &Pattern) -> String {
    match pattern {
        Pattern::Application { symbol, arguments } => {
            let name = symbol.name.as_str();
            if name == "inj" && arguments.len() == 1 {
                return render(&arguments[0]);
            }
            if name == "kseq" && arguments.len() == 2 {
                let rest = render(&arguments[1]);
                let head = render(&arguments[0]);
                return if rest == "." {
                    head
                } else {
                    format!("{head} ~> {rest}")
                };
            }
            if name == "dotk" {
                return ".".to_owned();
            }
            let name = name.strip_prefix("Lbl").unwrap_or(name);
            if arguments.is_empty() {
                name.to_owned()
            } else {
                let list = arguments.iter().map(render).collect::<Vec<_>>();
                format!("{name}({})", list.join(", "))
            }
        }
        Pattern::DomainValue { value, .. } => value.as_utf8().unwrap_or("?").to_owned(),
        Pattern::Variable(_) => "_".to_owned(),
        other => text(other),
    }
}

fn k_cell(pattern: &Pattern) -> Option<&Pattern> {
    if let Pattern::Application { symbol, arguments } = pattern
        && symbol.name == "Lbl'-LT-'k'-GT-'"
    {
        return arguments.first();
    }
    k_rust::kore::walk::children(pattern)
        .into_iter()
        .find_map(k_cell)
}

fn initial_state(n: i64) -> Pattern {
    parse_pattern(&format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortPgm{{}}, SortKItem{{}}}}(Lblgo{{}}(\\dv{{SortInt{{}}}}(\"{n}\"))), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
    ))
    .unwrap()
}

/// The leaves of `go(n)`: the rendering of each leaf's `<k>` cell, its halt reason, and whether
/// it carries a constraint.
fn run(backend: &mut Backend, n: i64) -> Result<Vec<(String, String, bool)>, String> {
    let request = ExecuteRequest {
        max_depth: Some(5),
        ..ExecuteRequest::new(initial_state(n))
    };
    let result = backend
        .execute(request)
        .map_err(|error| error.to_string())?;
    Ok(result
        .leaves
        .iter()
        .map(|leaf| {
            let state = codec::from_value(&leaf.state).expect("a result state is KORE JSON");
            let term = k_cell(&state).map_or_else(|| text(&state), render);
            let constrained = !matches!(
                &state,
                Pattern::Application { symbol, .. } if symbol.name == "Lbl'-LT-'generatedTop'-GT-'"
            );
            (term, format!("{:?}", leaf.reason), constrained)
        })
        .collect())
}

/// Every problem of one shape; empty when it conforms.
fn check(shape: &Shape) -> Vec<String> {
    let mut problems = Vec::new();
    let anonymous = shape.binder == Binder::Anonymous;
    let kore = match compile(&shape.name().replace('/', "_"), source(shape)) {
        Ok(kore) => kore,
        Err(error) => return vec![error],
    };
    let axioms = match axioms(&kore) {
        Ok(axioms) => axioms,
        Err(error) => return vec![error],
    };
    let Some(owise) = axioms.get("P.o") else {
        return vec!["no owise axiom P.o".to_owned()];
    };
    let (disjuncts, owise_own) = match owise_parts(owise) {
        Ok(parts) => parts,
        Err(error) => return vec![error],
    };
    let competitors = ["P.m", "P.p", "P.q"]
        .into_iter()
        .filter(|label| axioms.contains_key(*label))
        .collect::<Vec<_>>();
    if competitors.len() != disjuncts.len() {
        return vec![format!(
            "{} competitors but {} disjuncts in {}",
            competitors.len(),
            disjuncts.len(),
            text(owise)
        )];
    }
    // The axes the shape claims, read from its KORE: q's bound names against the owise rule's
    // names, p's bound names, and the names minted for the earlier competitors.
    let bound_of = |label: &str| {
        let mut found = Vec::new();
        binders(own_antecedent(&axioms[label]).unwrap(), &mut found);
        found.into_iter().collect::<BTreeSet<_>>()
    };
    let q_bound = bound_of("P.q");
    let mut owise_names = BTreeSet::new();
    for part in owise_own {
        all_variables(part, &mut owise_names);
    }
    let p_bound = if axioms.contains_key("P.p") {
        bound_of("P.p")
    } else {
        BTreeSet::new()
    };
    let mut minted = BTreeSet::new();
    for disjunct in &disjuncts[..disjuncts.len() - 1] {
        minted.extend(disjunct.leading_existentials().1.into_iter().cloned());
    }
    for (axis, names, claimed) in [
        ("owise", &owise_names, shape.owise),
        ("other", &p_bound, shape.other),
        ("minted", &minted, shape.minted),
    ] {
        match relation(&q_bound, names) {
            Ok(realized) if realized == claimed => {}
            Ok(realized) => problems.push(format!(
                "the text realizes {axis} {realized:?}, not {claimed:?}"
            )),
            Err(error) => problems.push(format!("{axis}: {error}")),
        }
    }
    // The capture check, and the renaming rule: a bound name is kept where no earlier part of
    // the axiom holds it, and renamed otherwise, a named binder to a name not spelled like a
    // generated one, an anonymous one to a generated name.
    for (label, disjunct) in competitors.iter().zip(&disjuncts) {
        let own = own_antecedent(&axioms[*label]).unwrap();
        let pairs = match restates(own, disjunct) {
            Ok(pairs) => pairs,
            Err(error) => {
                problems.push(format!("{label}: {error}"));
                continue;
            }
        };
        let taken = match *label {
            "P.q" => shape.q_taken(),
            "P.p" => {
                shape.owise != Relation::Absent || (anonymous && shape.minted != Relation::Absent)
            }
            _ => false,
        };
        for (authored, emitted) in pairs {
            let renamed = authored.name != emitted.name;
            if renamed != taken {
                problems.push(format!(
                    "{label}: binder {} emitted as {} where its name is {}taken",
                    authored.name,
                    emitted.name,
                    if taken { "" } else { "not " }
                ));
            }
            if renamed && is_generated(&authored.name) != is_generated(&emitted.name) {
                problems.push(format!(
                    "{label}: binder {} renamed to {}, which changes whether it reads as generated",
                    authored.name, emitted.name
                ));
            }
        }
    }
    let backend = Backend::new(&kore, "P", BackendOptions::default());
    match (shape.position, backend) {
        (Position::Argument, Ok(_)) => problems.push(
            "Backend::new loaded a quantifier at a term position; MLP/4 must now refuse it".into(),
        ),
        (Position::Argument, Err(error)) => {
            let message = error.to_string();
            if !message.contains("not supported where a term is required") {
                problems.push(format!("Backend::new refused otherwise: {message}"));
            }
        }
        (Position::Condition, Err(error)) => {
            problems.push(format!("Backend::new: {error}"));
        }
        (Position::Condition, Ok(mut backend)) => {
            let z3 = cfg!(feature = "z3-inference");
            for n in PROGRAMS {
                let value = format!("done({})", expected_value(shape, n));
                let unevaluated = format!("done(f(g({n}, 0), true))");
                let trivial = format!("go({n})");
                let leaves = match run(&mut backend, n) {
                    Ok(leaves) => leaves,
                    Err(error) => {
                        problems.push(format!("go({n}): {error}"));
                        continue;
                    }
                };
                // Without a solver the quantified conditions may stay undecided: `f` is then
                // left unevaluated, with the definedness branch of its application.
                let conforms = if z3 {
                    leaves.len() == 1 && leaves[0].0 == value && leaves[0].1 == "Stuck"
                } else {
                    !leaves.is_empty()
                        && leaves.iter().all(|(term, halt, constrained)| {
                            (*term == value && halt == "Stuck")
                                || (*term == unevaluated && halt == "Stuck")
                                || (*term == trivial && halt == "Trivial" && *constrained)
                        })
                };
                if !conforms {
                    problems.push(format!("go({n}): {leaves:?}, expected {value}"));
                }
            }
        }
    }
    problems
}

fn check_all(binder: Binder, position: Position) {
    let mut failures = Vec::new();
    let mut checked = 0;
    for (shape, dropped) in cross_product() {
        if shape.binder != binder || shape.position != position || dropped.is_some() {
            continue;
        }
        checked += 1;
        let problems = check(&shape);
        if problems.is_empty() {
            println!("{}: conforms", shape.name());
        } else {
            println!("{}: FAILS: {}", shape.name(), problems.join("; "));
            failures.push(format!("{}:\n  {}", shape.name(), problems.join("\n  ")));
        }
    }
    assert!(checked > 0);
    assert!(
        failures.is_empty(),
        "{} of {checked} shapes fail:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The cross product has 4 x 2 x 3 x 3 x 3 = 216 combinations; a clash with a minted name is
/// realizable only for an anonymous binder whose names the owise rule does not hold, so 2 x 9
/// named, nested and shadowing shapes each, and 2 x (9 + 2 x 3) anonymous shapes remain.
#[test]
fn the_shapes_are_the_realizable_cross_product() {
    let shapes = cross_product();
    assert_eq!(shapes.len(), 216);
    let kept = shapes
        .iter()
        .filter(|(_, dropped)| dropped.is_none())
        .count();
    assert_eq!(kept, 3 * 2 * 9 + 2 * 15);
}

macro_rules! shape_tests {
    ($($name:ident: $binder:ident, $position:ident;)*) => {
        $(
            #[test]
            fn $name() {
                check_all(Binder::$binder, Position::$position);
            }
        )*
    };
}

shape_tests! {
    named_binder_in_an_argument: Named, Argument;
    named_binder_in_a_condition: Named, Condition;
    anonymous_binder_in_an_argument: Anonymous, Argument;
    anonymous_binder_in_a_condition: Anonymous, Condition;
    nested_binders_in_an_argument: Nested, Argument;
    nested_binders_in_a_condition: Nested, Condition;
    shadowing_binders_in_an_argument: Shadowing, Argument;
    shadowing_binders_in_a_condition: Shadowing, Condition;
}
