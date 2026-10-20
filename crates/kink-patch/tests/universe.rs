//! The declared written-rule universe and its exhaustive selector predicates.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::builtin;
use k_rust::definition::sentence_mut;
use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::{Sort, Term};
use k_rust::outer::ResolvedSource;
use kink_patch::{
    Baseline, Discovery, Edit, ExclusionReason, Patch, SelectionPolicy, SentenceRef, SiteSelector,
    Universe, canonical_json, derive_sites, derive_sites_in, payload_digest, resolve_universe,
    select,
};
use serde_json::json;

fn load_text(text: &str) -> Baseline {
    load_module("CELLS", text)
}

fn load_module(module: &str, text: &str) -> Baseline {
    let mut resolver = |_: &str, name: &str| {
        builtin::embedded(name).ok_or_else(|| format!("{name} is not embedded"))
    };
    Baseline::load(
        ResolvedSource::new("cells.k", text),
        module,
        None,
        &mut resolver,
        &support::options(),
    )
    .expect("inline fixture loads")
}

fn cells() -> Baseline {
    load_text(
        r#"
module CELLS
 imports INT
 imports BASIC-K
 syntax KItem ::= go() [symbol(go)] | done() [symbol(done)]
 configuration <top> <k> .K </k> <n> 0 </n> </top>
 rule [go]: <k> go() => done() ... </k> <n> N => N +Int 1 </n>
endmodule
"#,
    )
}

fn all_rules() -> Universe {
    Universe {
        authored: true,
        typed: false,
        exclude_attributes: vec![],
        exclude_macro_rules: false,
    }
}

fn paths(discovery: &Discovery<'_>) -> Vec<Vec<u32>> {
    discovery
        .tuples()
        .iter()
        .map(|tuple| tuple.sites[0].at.path.0.clone())
        .collect()
}

#[test]
fn each_new_clause_has_positive_and_negative_exhaustive_rows() {
    let baseline = support::load("counter.k");
    let universe = resolve_universe(&baseline, &Universe::v1());
    let rule = SiteSelector::RuleLabel("COUNTER.increment".to_owned());
    let rows = [
        (
            vec![
                SiteSelector::Path(vec![0, 1, 0]),
                SiteSelector::NotHead {
                    label: "z".to_owned(),
                },
            ],
            true,
        ),
        (
            vec![
                SiteSelector::Path(vec![0, 1, 0]),
                SiteSelector::NotHead {
                    label: "s".to_owned(),
                },
            ],
            false,
        ),
        (
            vec![
                SiteSelector::Path(vec![1]),
                SiteSelector::NotToken {
                    token: "false".to_owned(),
                    sort: Sort::new("Bool"),
                },
            ],
            true,
        ),
        (
            vec![
                SiteSelector::Path(vec![1]),
                SiteSelector::NotToken {
                    token: "true".to_owned(),
                    sort: Sort::new("Bool"),
                },
            ],
            false,
        ),
        (
            vec![
                SiteSelector::Path(vec![1]),
                SiteSelector::TokenOfSort {
                    sort: Sort::new("Bool"),
                },
            ],
            true,
        ),
        (
            vec![
                SiteSelector::Path(vec![1]),
                SiteSelector::TokenOfSort {
                    sort: Sort::new("Int"),
                },
            ],
            false,
        ),
        (
            vec![
                SiteSelector::Path(vec![0]),
                SiteSelector::RuleAttribute {
                    key: "label".to_owned(),
                    present: true,
                },
            ],
            true,
        ),
        (
            vec![
                SiteSelector::Path(vec![0]),
                SiteSelector::RuleAttribute {
                    key: "label".to_owned(),
                    present: false,
                },
            ],
            false,
        ),
        (
            vec![
                SiteSelector::Path(vec![0, 1, 0]),
                SiteSelector::ArgumentCount { count: 1 },
            ],
            true,
        ),
        (
            vec![
                SiteSelector::Path(vec![0, 1, 0]),
                SiteSelector::ArgumentCount { count: 2 },
            ],
            false,
        ),
    ];
    for (mut clauses, present) in rows {
        clauses.push(rule.clone());
        let derived = derive_sites_in(&baseline, &universe, &clauses).expect("valid clauses");
        assert!(derived.exhaustive(), "{clauses:?}");
        assert_eq!(derived.tuples().len(), usize::from(present), "{clauses:?}");
        assert_eq!(
            derived.tuples(),
            derive_sites(&baseline, "site", &clauses)
                .expect("legacy clauses")
                .tuples()
        );
    }
    for present in [false, true] {
        let derived = derive_sites_in(
            &baseline,
            &universe,
            &[
                rule.clone(),
                SiteSelector::Path(vec![0]),
                SiteSelector::RuleAttribute {
                    key: "owise".to_owned(),
                    present,
                },
            ],
        )
        .expect("attribute absence");
        assert!(derived.exhaustive());
        assert_eq!(derived.tuples().len(), usize::from(!present));
    }
}

#[test]
fn cell_syntax_is_a_sort_non_site_only_in_the_declared_universe() {
    let baseline = cells();
    let universe = resolve_universe(&baseline, &Universe::v1());
    assert!(universe.excluded().is_empty());
    for label in ["#cells", "#dots", "#noDots"] {
        let head = SiteSelector::Head {
            label: label.to_owned(),
        };
        let syntax = derive_sites(&baseline, "site", std::slice::from_ref(&head)).expect("head");
        assert!(!syntax.tuples().is_empty(), "fixture has {label}");
        let clauses = [head, SiteSelector::Sort(Sort::new("Int"))];
        let old = derive_sites(&baseline, "site", &clauses).expect("legacy sort");
        let new = derive_sites_in(&baseline, &universe, &clauses).expect("universe sort");
        assert!(!old.exhaustive(), "legacy {label}");
        assert!(new.exhaustive(), "universe {label}");
        assert!(new.tuples().is_empty());
        assert_eq!(paths(&new), paths(&old));
    }
}

fn user_cell_label_is_undecided(module: &str, text: &str, sort: &str, sites: usize) {
    let baseline = load_module(module, text);
    let universe = resolve_universe(&baseline, &Universe::v1());
    assert!(universe.excluded().is_empty());
    assert_eq!(universe.included().len(), 1);
    let clauses = [SiteSelector::Sort(Sort::new(sort))];
    let old = derive_sites(&baseline, "site", &clauses).expect("legacy sort");
    let new = derive_sites_in(&baseline, &universe, &clauses).expect("universe sort");
    assert!(!old.exhaustive(), "legacy {module}");
    assert_eq!(old.tuples().len(), sites, "legacy {module}");
    assert_eq!(new.tuples(), old.tuples(), "{module}");
    assert!(!new.exhaustive(), "universe {module}");
}

#[test]
fn user_dots_constructor_is_not_a_sort_non_site() {
    user_cell_label_is_undecided(
        "RVDOTSCTOR",
        r##"module RVDOTSCTOR imports INT imports BASIC-K syntax Foo ::= "#dots" "(" Int ")" [symbol(#dots)] | "foo0" [symbol(foo0)] syntax KItem ::= go(Foo) [symbol(go)] rule [g]: go(#dots(I)) => go(#dots(I -Int 1)) requires I >Int 0 endmodule"##,
        "Foo",
        0,
    );
}

#[test]
fn user_dots_hook_is_not_a_sort_non_site() {
    user_cell_label_is_undecided(
        "RVDOTSHOOK",
        r##"module RVDOTSHOOK imports INT imports BASIC-K syntax Int ::= "#dots" "(" Int ")" [symbol(#dots), function, total, hook(INT.abs)] syntax KItem ::= go(Int) [symbol(go)] | done(Int) [symbol(done)] rule [g]: go(I) => done(#dots(I -Int 10)) requires I >Int 0 endmodule"##,
        "Int",
        9,
    );
}

#[test]
fn user_cells_constructor_is_not_a_sort_non_site() {
    user_cell_label_is_undecided(
        "RVCELLSCTOR",
        r##"module RVCELLSCTOR imports INT imports BASIC-K syntax Foo ::= "#cells" "(" Int ")" [symbol(#cells)] | "foo0" [symbol(foo0)] syntax KItem ::= go(Foo) [symbol(go)] rule [g]: go(#cells(I)) => go(#cells(I -Int 1)) requires I >Int 0 endmodule"##,
        "Foo",
        0,
    );
}

#[test]
fn universe_value_has_exact_keys_and_the_excluded_payload_digest() {
    let baseline = support::load("claims.k");
    let resolved = resolve_universe(&baseline, &Universe::v1());
    let value = resolved.value();
    let keys = value
        .as_object()
        .expect("object")
        .keys()
        .map(String::as_str)
        .collect::<Vec<_>>();
    assert_eq!(
        keys,
        [
            "authored",
            "exclude_attributes",
            "exclude_macro_rules",
            "excluded",
            "excluded_sha256",
            "kinds",
            "typed"
        ]
    );
    assert_eq!(value["kinds"], json!(["rule"]));
    assert_eq!(value["authored"], true);
    assert_eq!(value["typed"], true);
    assert_eq!(
        value["exclude_attributes"],
        json!(["simplification", "smt-lemma"])
    );
    assert_eq!(value["exclude_macro_rules"], true);
    assert_eq!(
        value["excluded_sha256"],
        payload_digest(
            "kink/universe-excluded/v1",
            canonical_json(&value["excluded"]).as_bytes()
        )
        .to_string()
    );
    for entry in value["excluded"].as_array().expect("exclusions") {
        assert_eq!(
            entry
                .as_object()
                .expect("entry")
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            ["index", "module", "reason"]
        );
    }
    assert!(resolved.included().windows(2).all(|pair| pair[0] < pair[1]));
    assert!(
        resolved
            .excluded()
            .windows(2)
            .all(|pair| pair[0].0 < pair[1].0)
    );
}

/// A rule k-rust 501f18b9 compiles but its sentence typer still refuses: a local function whose
/// equation has a variable in the body of a cell with children (`SentenceTypingError::
/// CellCompletion`, the stated exception of k-rust docs/compatibility.md to compiles-implies-
/// types; k-rust tests/sentence_typing.rs
/// a_cell_with_a_variable_in_a_local_functions_equation_is_refused). Re-pin R0a kept it to
/// exercise the `Untyped` exclusion once `#let` typed (findings C-01, E-12); since L2-2-fix-1 no
/// typing error excludes a rule, and it exercises an included rule with no site sorts
/// (`ResolvedUniverse::unsorted`).
const UNTYPED_CELL: &str = r#"module UNTYPEDCELL
  imports INT
  imports BOOL
  configuration <t>
    <k> $PGM:K </k>
    <accounts> <account multiplicity="*" type="Map"> <id> 0 </id> <bal> 0 </bal> </account> </accounts>
  </t>
  syntax KItem ::= "go" | "stop" | box(AccountsCell) | fooK(K)
  rule [completed]: <k> go => #fun(box(<accounts> B </accounts>) => fooK(B))(box(<accounts> A </accounts>)) ... </k> <accounts> A </accounts>
  rule [plain]: <k> stop => .K ... </k>
endmodule
"#;

fn untyped_cell() -> Baseline {
    load_module("UNTYPEDCELL", UNTYPED_CELL)
}

#[test]
fn expected_rule_exclusions() {
    let partial = support::load("sympartial.k");
    let resolved = resolve_universe(&partial, &Universe::v1());
    // Re-pin R0a (findings C-01, E-12; k-rust KINK-03, SentenceTyper types `#let`): at 927b9ce6
    // SYMPARTIAL.halflet (a `#let` in its requires) was excluded as Untyped; at 501f18b9 it types
    // and is a mutation site, and sympartial.k excludes nothing.
    assert_eq!(resolved.excluded(), &[]);
    assert!(
        resolved
            .included()
            .contains(&support::rule(&partial, "SYMPARTIAL.halflet"))
    );
    // Re-pin L2-2-fix-1: UNTYPEDCELL.completed, which no typing view types, was excluded as
    // Untyped; the baseline compiles, so it is included, without site sorts.
    let untyped = untyped_cell();
    let resolved = resolve_universe(&untyped, &Universe::v1());
    let completed = support::rule(&untyped, "UNTYPEDCELL.completed");
    assert_eq!(resolved.excluded(), &[]);
    assert!(resolved.included().contains(&completed));
    assert_eq!(resolved.unsorted(), &[completed]);
    let macros = support::load("t12macro.k");
    let resolved = resolve_universe(&macros, &Universe::v1());
    assert_eq!(
        resolved.excluded(),
        &[(SentenceRef::new("T12MACRO", 1), ExclusionReason::MacroRule)]
    );
    let claims = support::load("claims.k");
    let resolved = resolve_universe(&claims, &Universe::v1());
    assert!(resolved.excluded().contains(&(
        support::rule(&claims, "CLAIMS.lemma"),
        ExclusionReason::Attribute("simplification".to_owned())
    )));
}

#[test]
fn every_other_missing_sort_keeps_the_discovery_incomplete() {
    let baseline = support::load("counter.k");
    let at = support::rule(&baseline, "COUNTER.increment");
    let mut definition = baseline.definition().clone();
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == at.module)
        .expect("module");
    let Sentence::Rule { requires, .. } =
        sentence_mut(&mut module.local_sentences[at.index as usize])
    else {
        panic!("rule");
    };
    *requires = Term::Variable {
        name: "B".to_owned(),
        sort: None,
    };
    let baseline = Baseline::new(
        baseline
            .loaded()
            .with_definition(definition)
            .expect("relinks"),
    );
    let universe = resolve_universe(&baseline, &all_rules());
    let clauses = [
        SiteSelector::Path(vec![1]),
        SiteSelector::Sort(Sort::new("Bool")),
    ];
    let old = derive_sites(&baseline, "site", &clauses).expect("legacy");
    let new = derive_sites_in(&baseline, &universe, &clauses).expect("universe");
    assert!(!old.exhaustive() && !new.exhaustive());
    assert_eq!(old.tuples(), new.tuples());
}

#[test]
fn a_foreign_universe_cannot_silently_skip_rules() {
    let counter = support::load("counter.k");
    let memory = support::load("memory.k");
    let universe = resolve_universe(&memory, &all_rules());
    assert!(derive_sites_in(&counter, &universe, &[]).is_err());
}

/// Re-pin L2-2-fix-1: `Untyped`, formerly first, is gone (no typing error excludes a rule).
#[test]
fn exclusion_priority_is_attribute_then_macro_rule() {
    let partial = support::load("sympartial.k");
    let universe = Universe {
        exclude_attributes: vec!["label".to_owned()],
        ..Universe::v1()
    };
    let resolved = resolve_universe(&partial, &universe);
    // Re-pin R0a (findings C-01, E-12): halflet types at 501f18b9, so its label excludes it.
    // UNTYPEDCELL.completed, which no typing view types and which carries a label too, is excluded
    // by its label since L2-2-fix-1 (Untyped before), and an excluded rule is never unsorted.
    assert!(resolved.excluded().contains(&(
        support::rule(&partial, "SYMPARTIAL.halflet"),
        ExclusionReason::Attribute("label".to_owned())
    )));
    assert!(resolved.excluded().contains(&(
        support::rule(&partial, "SYMPARTIAL.half"),
        ExclusionReason::Attribute("label".to_owned())
    )));
    let untyped = untyped_cell();
    let resolved = resolve_universe(&untyped, &universe);
    assert!(resolved.excluded().contains(&(
        support::rule(&untyped, "UNTYPEDCELL.completed"),
        ExclusionReason::Attribute("label".to_owned())
    )));
    assert_eq!(resolved.unsorted(), &[]);
    assert!(resolved.excluded().contains(&(
        support::rule(&untyped, "UNTYPEDCELL.plain"),
        ExclusionReason::Attribute("label".to_owned())
    )));
    let macros = support::load("t12macro.k");
    let default = resolve_universe(&macros, &Universe::v1());
    let macro_at = &default.excluded()[0].0;
    let universe = Universe {
        exclude_attributes: vec![AttributeKey::Source.as_str().to_owned()],
        ..Universe::v1()
    };
    let resolved = resolve_universe(&macros, &universe);
    assert!(resolved.excluded().contains(&(
        macro_at.clone(),
        ExclusionReason::Attribute(AttributeKey::Source.as_str().to_owned())
    )));
}

/// Re-pin R0a (findings C-01, E-12; k-rust KINK-03): sympartial.k excluded SYMPARTIAL.halflet
/// as Untyped at 927b9ce6 (1 exclusion, 3 requires sites); at 501f18b9 it types, so sympartial.k
/// excludes nothing and halflet's requires is a fourth site. Re-pin L2-2-fix-1: the
/// recorded-exclusion case, kept on UNTYPEDCELL's Untyped rule until then, is on claims.k's
/// `simplification` lemma; an included rule with no site sorts is
/// an_unsorted_rule_is_included_and_keeps_a_sort_selected_discovery_incomplete.
#[test]
fn recorded_exclusions_alone_do_not_make_a_generation_incomplete() {
    for (baseline, excluded, sites) in [
        (support::load("sympartial.k"), 0, 4),
        (support::load("claims.k"), 2, 7),
    ] {
        recorded_exclusions_row(&baseline, excluded, sites);
    }
}

/// Re-pin L2-2-fix-1 (deliverable 2): a rule of a compiling baseline that no typing view types is
/// in the universe, recorded as unsorted. A sort-selected discovery skips its sites and is not
/// exhaustive, so no generation over it is scored; a discovery that selects no sort reaches it.
#[test]
fn an_unsorted_rule_is_included_and_keeps_a_sort_selected_discovery_incomplete() {
    let baseline = untyped_cell();
    support::compile(baseline.loaded()).expect("the baseline compiles");
    let universe = resolve_universe(&baseline, &Universe::v1());
    let completed = support::rule(&baseline, "UNTYPEDCELL.completed");
    let plain = support::rule(&baseline, "UNTYPEDCELL.plain");
    assert_eq!(universe.unsorted(), std::slice::from_ref(&completed));
    let sorted = derive_sites_in(
        &baseline,
        &universe,
        &[
            SiteSelector::Path(vec![1]),
            SiteSelector::Sort(Sort::new("Bool")),
        ],
    )
    .expect("requires sites");
    assert!(!sorted.exhaustive());
    let rules = |discovery: &Discovery<'_>| {
        discovery
            .tuples()
            .iter()
            .map(|tuple| tuple.sites[0].at.sentence.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(rules(&sorted), std::slice::from_ref(&plain));
    let unsorted = derive_sites_in(&baseline, &universe, &[SiteSelector::Path(vec![1])])
        .expect("requires sites");
    assert!(unsorted.exhaustive());
    assert_eq!(rules(&unsorted), [completed, plain]);
}

fn recorded_exclusions_row(baseline: &Baseline, excluded: usize, sites: usize) {
    let universe = resolve_universe(baseline, &Universe::v1());
    assert_eq!(universe.excluded().len(), excluded);
    let discovery = derive_sites_in(
        baseline,
        &universe,
        &[
            SiteSelector::Path(vec![1]),
            SiteSelector::Sort(Sort::new("Bool")),
        ],
    )
    .expect("declared requires sites");
    assert!(discovery.exhaustive());
    assert_eq!(discovery.tuples().len(), sites);
    let generation = select(&discovery, SelectionPolicy::Each, 16)
        .expect("finite selection")
        .fold("requires-false", |origin| {
            let at = origin.site_tuple[0].clone();
            Patch::new(vec![Edit::ReplaceTerm {
                expected: baseline.term(&at).expect("term").clone(),
                at,
                replacement: Term::Token {
                    token: "false".to_owned(),
                    sort: Sort::new("Bool"),
                },
            }])
            .expect("one edit")
        })
        .expect("each edit stays in its origin");
    assert!(generation.scored());
    assert_eq!(generation.candidates().len(), sites);
}

#[test]
fn v1_discovery_refuses_an_un_authored_declaration() {
    let baseline = support::load("counter.k");
    let universe = resolve_universe(
        &baseline,
        &Universe {
            authored: false,
            ..all_rules()
        },
    );
    assert!(derive_sites_in(&baseline, &universe, &[]).is_err());
}

/// Re-pin L1-3-tail (review L1-3-fix-2-1 P1): resolving the universe and a sort-selected discovery
/// type every baseline rule (`CompilationTyping::site_typing`), by k-rust's unguarded recursion,
/// on a stack sized from the rule's depth. A baseline whose rules nest deep, through a unary
/// symbol and through `#if` conditions (a parametric production, the costliest shape measured),
/// resolves on a 1 MiB thread exactly as on a 64 MiB one, every rule sorted and the discovery
/// exhaustive. Before, typing ran on the calling thread: this thread overflowed and the process
/// aborted, as kink-corpus's 256 MiB thread did near 230,000 levels. Packet test-gate TG-P: the
/// depth is 1,500, down from 5,000: without kink's stack guard, resolving either rule alone
/// overflows a 2 MiB thread (twice the small thread) from 1,342 levels, at the dev and test
/// profile's `opt-level = 1` (TG-P handoff; typing.rs `DEPTH`).
#[test]
fn a_deep_baseline_rule_resolves_alike_on_a_thread_too_small_for_its_typing() {
    const DEPTH: usize = 1_500;
    let text = format!(
        "module DEEP\n  imports INT\n  imports BOOL\n  imports K-EQUAL\n  syntax Peano ::= \"z\" | s(Peano)\n  \
         syntax Exp ::= go(Int) | deep(Peano) | pick(Int)\n  rule [big]: go(I:Int) => \
         deep({}z{}) requires I >Int 100\n  rule [pick]: go(I:Int) => pick(#if {}true{} #then 0 \
         #else 1 #fi) requires I <Int 100\nendmodule\n",
        "s(".repeat(DEPTH),
        ")".repeat(DEPTH),
        "#if ".repeat(DEPTH),
        " #then true #else false #fi".repeat(DEPTH),
    );
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let baseline = load_module("DEEP", &text);
            let resolved = |stack: usize| {
                std::thread::scope(|scope| {
                    std::thread::Builder::new()
                        .stack_size(stack)
                        .spawn_scoped(scope, || {
                            let universe = resolve_universe(&baseline, &Universe::v1());
                            let discovery = derive_sites_in(
                                &baseline,
                                &universe,
                                &[
                                    SiteSelector::Path(vec![1]),
                                    SiteSelector::Sort(Sort::new("Bool")),
                                ],
                            )
                            .expect("requires sites");
                            let sites = discovery
                                .tuples()
                                .iter()
                                .map(|tuple| tuple.sites[0].at.clone())
                                .collect::<Vec<_>>();
                            (
                                universe.value(),
                                universe.unsorted().to_vec(),
                                discovery.exhaustive(),
                                sites,
                            )
                        })
                        .unwrap()
                        .join()
                        .unwrap()
                })
            };
            let large = resolved(64 << 20);
            assert!(large.1.is_empty(), "every rule is sorted: {:?}", large.1);
            assert!(large.2, "the discovery is exhaustive");
            assert_eq!(
                large.3.len(),
                2,
                "both guards are Bool sites: {:?}",
                large.3
            );
            assert_eq!(resolved(1 << 20), large);
        })
        .unwrap()
        .join()
        .unwrap();
}
