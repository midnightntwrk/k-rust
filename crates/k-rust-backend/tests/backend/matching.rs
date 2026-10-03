//! Public contracts of `k_rust_backend::matching`.

use std::sync::Arc;

use k_rust_backend::{
    definition::BackendDefinition,
    matching::*,
    simplify::SimplificationOptions,
    substitution::Substitution,
    term::{
        CollectionSymbols, FunctionType, HeadRole, ListDefinition, MapDefinition, Name, Sort,
        Symbol, SymbolAttributes, SymbolType, Term, Variable,
    },
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::{ground_overload_definition, internal_term, unstopped::simplify};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Outcome {
    Success,
    Failed,
    Indeterminate,
}

fn outcome(result: MatchResult) -> Outcome {
    match result {
        MatchResult::Success(_) => Outcome::Success,
        MatchResult::Failed(_) => Outcome::Failed,
        MatchResult::Indeterminate { .. } => Outcome::Indeterminate,
    }
}

fn sort() -> Sort {
    Sort::simple("SomeSort")
}

fn subsort() -> Sort {
    Sort::simple("ASubsort")
}

fn variable(name: &str, sort: Sort) -> Variable {
    Variable::new(name, sort)
}

fn var(name: &str, sort: Sort) -> Term {
    Term::variable(variable(name, sort))
}

fn domain_value(sort: Sort, value: &str) -> Term {
    Term::domain_value(sort, value)
}

fn constructor() -> Arc<Symbol> {
    Arc::new(Symbol::constructor("con1", vec![sort()], sort()))
}

fn function() -> Arc<Symbol> {
    Arc::new(Symbol {
        name: "f1".into(),
        sort_variables: Vec::new(),
        argument_sorts: vec![sort()],
        result_sort: sort(),
        attributes: {
            let mut attributes = SymbolAttributes::constructor().with_declared_function(true);
            attributes.symbol_type = SymbolType::Function(FunctionType::Total);
            attributes
        },
    })
}

fn injective_function() -> Arc<Symbol> {
    let mut symbol = (*function()).clone();
    symbol.name = "injective".into();
    symbol.attributes = symbol.attributes.with_injective(true);
    Arc::new(symbol)
}

fn application(symbol: Arc<Symbol>, argument: Term) -> Term {
    Term::application(symbol, Vec::new(), vec![argument])
}

fn collection_symbols(prefix: &str) -> CollectionSymbols {
    CollectionSymbols {
        unit: format!("{prefix}Unit").into(),
        element: format!("{prefix}Element").into(),
        concat: format!("{prefix}Concat").into(),
    }
}

fn map_definition() -> Arc<MapDefinition> {
    Arc::new(MapDefinition {
        symbols: collection_symbols("map"),
        key_sort: "MapKey".into(),
        value_sort: "MapValue".into(),
        map_sort: "MapSort".into(),
    })
}

fn list_definition() -> Arc<ListDefinition> {
    Arc::new(ListDefinition {
        symbols: collection_symbols("list"),
        element_sort: "SomeSort".into(),
        list_sort: "ListSort".into(),
    })
}

fn list_update_pattern(index: Term, value: Term, hooked: bool) -> Term {
    let mut symbol = (*function()).clone();
    symbol.argument_sorts = vec![Sort::simple("ListSort"), index.sort(), sort()];
    symbol.result_sort = Sort::simple("ListSort");
    symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Partial);
    symbol.attributes.hook = hooked.then(|| "LIST.update".into());
    Term::application(
        Arc::new(symbol),
        Vec::new(),
        vec![
            Term::variable(variable("LIST", Sort::simple("ListSort"))),
            index,
            value,
        ],
    )
}

#[test]
fn list_update_matching_rejects_impossible_results() {
    let subject = Term::list(
        list_definition(),
        vec![domain_value(sort(), "a"), domain_value(sort(), "b")],
        None,
    );
    // Updating preserves length and fixes the selected element, regardless of the base list.
    for index in ["0", "-1", "2", "184467440737095516160"] {
        let pattern = list_update_pattern(
            domain_value(Sort::simple("SortInt"), index),
            domain_value(sort(), "b"),
            true,
        );
        for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
            assert!(
                matches!(
                    match_terms(mode, &SortGraph::default(), &pattern, &subject),
                    MatchResult::Failed(_)
                ),
                "{mode:?}, index {index}"
            );
        }
    }
}

#[test]
fn list_update_matching_defers_results_it_cannot_refute() {
    let a = domain_value(sort(), "a");
    let b = domain_value(sort(), "b");
    let index = domain_value(Sort::simple("SortInt"), "0");
    let concrete = Term::list(list_definition(), vec![a.clone()], None);
    let symbolic = Term::list(
        list_definition(),
        vec![Term::variable(variable("ITEM", sort()))],
        None,
    );
    let open = Term::list(
        list_definition(),
        Vec::new(),
        Some((
            Term::variable(variable("REST", Sort::simple("ListSort"))),
            vec![a.clone()],
        )),
    );
    for (pattern, subject) in [
        (
            list_update_pattern(index.clone(), a, true),
            concrete.clone(),
        ),
        (
            list_update_pattern(
                index.clone(),
                Term::variable(variable("VALUE", sort())),
                true,
            ),
            concrete.clone(),
        ),
        (
            list_update_pattern(
                Term::variable(variable("INDEX", Sort::simple("SortInt"))),
                b.clone(),
                true,
            ),
            concrete.clone(),
        ),
        (
            list_update_pattern(index.clone(), b.clone(), true),
            symbolic,
        ),
        (list_update_pattern(index.clone(), b.clone(), true), open),
        (list_update_pattern(index, b, false), concrete),
    ] {
        for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
            assert!(matches!(
                match_terms(mode, &SortGraph::default(), &pattern, &subject),
                MatchResult::Indeterminate { .. }
            ));
        }
    }
}

fn set_definition() -> Arc<k_rust_backend::term::SetDefinition> {
    Arc::new(k_rust_backend::term::SetDefinition {
        symbols: collection_symbols("set"),
        element_sort: "SetElement".into(),
        list_sort: "SetSort".into(),
    })
}

fn kinds() -> Vec<(&'static str, Term, Term)> {
    let subject_constructor = application(constructor(), domain_value(sort(), "constructor"));
    let map_definition = map_definition();
    let list_definition = list_definition();
    let set_definition = set_definition();
    vec![
        (
            "And",
            Term::and(var("P1", sort()), var("P2", sort())),
            Term::and(subject_constructor.clone(), subject_constructor.clone()),
        ),
        (
            "DomainValue",
            domain_value(sort(), "domain"),
            domain_value(sort(), "domain"),
        ),
        (
            "Injection",
            Term::injection(subsort(), sort(), var("PI", subsort())),
            Term::injection(subsort(), sort(), domain_value(subsort(), "injected")),
        ),
        (
            "Map",
            Term::map(map_definition.clone(), Vec::new(), None),
            Term::map(map_definition, Vec::new(), None),
        ),
        (
            "List",
            Term::list(list_definition.clone(), Vec::new(), None),
            Term::list(list_definition, Vec::new(), None),
        ),
        (
            "Set",
            Term::set(set_definition.clone(), Vec::new(), None),
            Term::set(set_definition, Vec::new(), None),
        ),
        (
            "Constructor",
            application(constructor(), var("PC", sort())),
            subject_constructor,
        ),
        (
            "Function",
            application(function(), var("PF", sort())),
            application(function(), domain_value(sort(), "function")),
        ),
        ("Variable", var("PX", sort()), var("SY", sort())),
    ]
}

fn sort_graph() -> SortGraph {
    let mut graph = SortGraph::default();
    graph.insert("SomeSort", [Name::from("ASubsort")]);
    graph.insert("ASubsort", []);
    for name in ["MapKey", "MapValue", "MapSort", "ListSort", "SetSort"] {
        graph.insert(name, []);
    }
    graph
}

#[test]
fn differing_symbolic_injections_preserve_a_common_subsort_match() {
    let item = Sort::simple("SortItem");
    let left = Sort::simple("SortLeft");
    let right = Sort::simple("SortRight");
    let common = Name::from("SortCommon");
    let disjoint = Sort::simple("SortDisjoint");
    let mut graph = SortGraph::default();
    graph.insert(
        "SortItem",
        [
            Name::from("SortLeft"),
            Name::from("SortRight"),
            common.clone(),
            Name::from("SortDisjoint"),
        ],
    );
    graph.insert("SortLeft", [common.clone()]);
    graph.insert("SortRight", [common]);
    graph.insert("SortCommon", []);
    graph.insert("SortDisjoint", []);

    let pattern = Term::injection(left.clone(), item.clone(), var("PATTERN", left.clone()));
    let overlapping = Term::injection(right.clone(), item.clone(), var("SUBJECT", right.clone()));
    let separate = Term::injection(disjoint.clone(), item.clone(), var("SEPARATE", disjoint));

    for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
        assert_eq!(
            outcome(match_terms(mode, &graph, &pattern, &overlapping)),
            Outcome::Indeterminate,
            "{mode:?}",
        );
        assert_eq!(
            outcome(match_terms(mode, &graph, &pattern, &separate)),
            Outcome::Failed,
            "{mode:?}",
        );

        let concrete_left = Term::injection(
            left.clone(),
            item.clone(),
            domain_value(left.clone(), "left"),
        );
        let concrete_right = Term::injection(
            right.clone(),
            item.clone(),
            domain_value(right.clone(), "right"),
        );
        assert_eq!(
            outcome(match_terms(mode, &graph, &concrete_left, &overlapping)),
            Outcome::Failed,
            "{mode:?}, constructor-like pattern",
        );
        assert_eq!(
            outcome(match_terms(mode, &graph, &pattern, &concrete_right)),
            Outcome::Failed,
            "{mode:?}, constructor-like subject",
        );
    }

    let parameter = Sort::simple("SortParameter");
    let parametric = |name| Sort::Application {
        name: Name::from(name),
        arguments: vec![parameter.clone()],
    };
    let parametric_left = parametric("SortLeft");
    let parametric_right = parametric("SortRight");
    assert_eq!(
        outcome(match_terms(
            MatchMode::Evaluate,
            &graph,
            &Term::injection(
                parametric_left.clone(),
                Sort::simple("SortItem"),
                var("PARAMETRIC_PATTERN", parametric_left),
            ),
            &Term::injection(
                parametric_right.clone(),
                Sort::simple("SortItem"),
                var("PARAMETRIC_SUBJECT", parametric_right),
            ),
        )),
        Outcome::Failed,
    );
}

#[test]
fn collection_heads_fix_the_source_sort_of_differing_injections() {
    let item = Sort::simple("SortItem");
    let left = Sort::simple("SortLeft");
    let right = Sort::simple("SortRight");
    let mut graph = SortGraph::default();
    graph.insert(
        "SortItem",
        [
            Name::from("SortLeft"),
            Name::from("SortRight"),
            Name::from("SortCommon"),
        ],
    );
    graph.insert("SortLeft", [Name::from("SortCommon")]);
    graph.insert("SortRight", [Name::from("SortCommon")]);
    graph.insert("SortCommon", []);

    let open_map = |prefix: &str, source: &Sort| {
        let definition = Arc::new(MapDefinition {
            symbols: collection_symbols(prefix),
            key_sort: "SomeSort".into(),
            value_sort: "SomeSort".into(),
            map_sort: match source {
                Sort::Application { name, .. } => name.clone(),
                Sort::Variable(_) => unreachable!(),
            },
        });
        Term::map(
            definition,
            vec![(domain_value(sort(), "key"), domain_value(sort(), "value"))],
            Some(var(&format!("{prefix}_REST"), source.clone())),
        )
    };
    let pattern = Term::injection(left.clone(), item.clone(), open_map("left", &left));
    let subject = Term::injection(right.clone(), item, open_map("right", &right));

    for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
        assert_eq!(
            outcome(match_terms(mode, &graph, &pattern, &subject)),
            Outcome::Failed,
            "{mode:?}",
        );
    }
}

fn overload_definition() -> BackendDefinition {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortSub{} [hasDomainValues{}()]
                sort SortLeft{} []
                sort SortRight{} []
                sort SortTop{} []
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                symbol lower{}(SortSub{}) : SortSub{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol upper{}(SortTop{}) : SortTop{} [constructor{}()]
                symbol left{}(SortLeft{}) : SortLeft{} [constructor{}()]
                symbol right{}(SortRight{}) : SortRight{} [constructor{}()]
                symbol common{}(SortTop{}) : SortTop{} [constructor{}()]
                axiom{R} \equals{SortTop{}, R}(
                    upper{}(X:SortTop{}),
                    inj{SortSub{}, SortTop{}}(lower{}(Y:SortSub{}))
                ) [symbol-overload{}(upper{}(), lower{}())]
                axiom{R} \equals{SortTop{}, R}(
                    common{}(X:SortTop{}),
                    inj{SortLeft{}, SortTop{}}(left{}(Y:SortLeft{}))
                ) [symbol-overload{}(common{}(), left{}())]
                axiom{R} \equals{SortTop{}, R}(
                    common{}(X:SortTop{}),
                    inj{SortRight{}, SortTop{}}(right{}(Y:SortRight{}))
                ) [symbol-overload{}(common{}(), right{}())]
            endmodule []"#,
    )
    .expect("overload definition should parse");
    let mut definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("overload definition should internalize");
    definition.sort_graph.insert(
        "SortTop",
        [
            Name::from("SortSub"),
            Name::from("SortLeft"),
            Name::from("SortRight"),
        ],
    );
    definition
        .sort_graph
        .insert("SortLeft", [Name::from("SortSub")]);
    definition
        .sort_graph
        .insert("SortRight", [Name::from("SortSub")]);
    definition
}

fn expected(mode: MatchMode) -> [[Outcome; 9]; 9] {
    use Outcome::{Failed as F, Indeterminate as I, Success as S};
    match mode {
        MatchMode::Rewrite => [
            [S, S, S, F, F, F, S, S, S],
            [F, S, F, F, F, F, F, I, I],
            [F, F, S, F, F, F, F, I, I],
            [F, F, F, S, F, F, F, I, I],
            [F, F, F, F, S, F, F, I, I],
            [F, F, F, F, F, S, F, I, I],
            [S, F, F, F, F, F, S, I, I],
            [I, I, I, I, I, I, I, I, I],
            [S, S, S, F, F, F, S, S, S],
        ],
        MatchMode::Evaluate => [
            [I, S, S, F, F, F, S, S, I],
            [I, S, F, F, F, F, F, I, I],
            [I, F, S, I, I, I, F, I, I],
            [I, F, I, S, F, F, F, I, I],
            [I, F, I, F, S, F, F, I, I],
            [I, F, I, F, F, S, F, I, I],
            [I, F, F, F, F, F, S, I, I],
            [I, I, I, I, I, I, I, S, I],
            [I, S, S, F, F, F, S, S, S],
        ],
        MatchMode::Implies => [
            [S, S, S, F, F, F, S, S, S],
            [F, S, F, F, F, F, F, I, I],
            [F, F, S, F, F, F, F, I, I],
            [F, F, F, S, F, F, F, I, I],
            [F, F, F, F, S, F, F, I, I],
            [F, F, F, F, F, S, F, I, I],
            [S, F, F, F, F, F, S, I, I],
            [I, I, I, I, I, I, I, I, I],
            [S, S, S, F, F, F, S, S, S],
        ],
    }
}

#[test]
fn matches_the_reference_dispatch_grid() {
    let kinds = kinds();
    let sorts = sort_graph();
    for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
        for ((pattern_name, pattern, _), expected_row) in kinds.iter().zip(expected(mode)) {
            for ((subject_name, _, subject), expected) in kinds.iter().zip(expected_row) {
                assert_eq!(
                    outcome(match_terms(mode, &sorts, pattern, subject)),
                    expected,
                    "{mode:?}: {pattern_name} vs {subject_name}"
                );
            }
        }
    }
}

#[test]
fn returns_the_reference_oriented_substitution() {
    let pattern = application(constructor(), var("X", sort()));
    let subject = application(constructor(), domain_value(sort(), "value"));
    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::from([(
            variable("X", sort()),
            domain_value(sort(), "value"),
        )]))
    );
}

#[test]
fn signed_and_unsigned_int_literals_match_as_the_same_domain_value() {
    let int_sort = Sort::simple("SortInt");
    let pattern = domain_value(int_sort.clone(), "3");
    let subject = domain_value(int_sort, "+3");

    assert_eq!(
        match_terms(
            MatchMode::Rewrite,
            &SortGraph::default(),
            &pattern,
            &subject
        ),
        MatchResult::Success(Substitution::new())
    );
}

#[test]
fn identical_shared_variables_match_without_a_binding() {
    let term = Term::variable(variable("X", sort()));

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &term, &term),
        MatchResult::Success(Substitution::new())
    );
}

#[test]
fn decomposes_matching_injective_functions_during_rewriting() {
    let symbol = injective_function();
    let variable = variable("X", sort());
    let value = domain_value(sort(), "value");
    let pattern = application(symbol.clone(), Term::variable(variable.clone()));
    let subject = application(symbol, value.clone());

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::from([(variable, value)]))
    );
}

#[test]
fn anywhere_heads_are_rigid_only_for_rewrite_matching() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortS{} []
                symbol value{}() : SortS{} [constructor{}(), total{}()]
                symbol anywhereHead{}(SortS{}) : SortS{}
                    [anywhere{}(), total{}()]
                symbol constructorHead{}(SortS{}) : SortS{}
                    [constructor{}(), total{}()]
                symbol functionHead{}(SortS{}) : SortS{}
                    [function{}(), total{}()]
                symbol anywhereFunction{}(SortS{}) : SortS{}
                    [anywhere{}(), function{}(), total{}()]
            endmodule []"#,
    )
    .expect("anywhere definition should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("anywhere definition should internalize");
    let value = Term::application(definition.symbols["value"].clone(), Vec::new(), Vec::new());
    let variable = Variable::new("X", Sort::simple("SortS"));
    let application = |name: &str, argument: Term| {
        Term::application(definition.symbols[name].clone(), Vec::new(), vec![argument])
    };
    let pattern = application("anywhereHead", Term::variable(variable.clone()));

    assert_eq!(
        definition.symbols["anywhereHead"].attributes.head_role(),
        HeadRole::EquationHead
    );
    assert_eq!(
        match_terms_in_definition(
            MatchMode::Rewrite,
            &definition,
            &pattern,
            &application("anywhereHead", value.clone()),
        ),
        MatchResult::Success(Substitution::from([(variable, value.clone())]))
    );
    assert!(matches!(
        match_terms_in_definition(
            MatchMode::Rewrite,
            &definition,
            &pattern,
            &application("constructorHead", value.clone()),
        ),
        MatchResult::Failed(FailReason::DifferentSymbols(..))
    ));

    for subject in [
        application("functionHead", value.clone()),
        Term::variable(Variable::new("SUBJECT", Sort::simple("SortS"))),
    ] {
        assert!(matches!(
            match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject,),
            MatchResult::Indeterminate { .. }
        ));
    }
    for mode in [MatchMode::Evaluate, MatchMode::Implies] {
        assert!(matches!(
            match_terms_in_definition(
                mode,
                &definition,
                &pattern,
                &application("constructorHead", value.clone()),
            ),
            MatchResult::Indeterminate { .. }
        ));
    }
    assert!(matches!(
        match_terms_in_definition(
            MatchMode::Rewrite,
            &definition,
            &application(
                "anywhereFunction",
                Term::variable(Variable::new("Y", Sort::simple("SortS"))),
            ),
            &application("constructorHead", value),
        ),
        MatchResult::Indeterminate { .. }
    ));
}

/// B3: `injective` on a declared function that also carries `anywhere` does not make the
/// matcher compare its applications by arguments. The `anywhere` equation makes `f(s(z))` equal
/// `f(z)`, so the pattern `f(z)` is not refuted against the subject `f(s(z))` by the clash of
/// `z` with `s(z)`; without `anywhere` the declared `injective` still decides.
#[test]
fn injective_anywhere_function_is_not_decomposed_by_the_matcher() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortNat{} []
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol f{}(SortNat{}) : SortNat{}
                    [anywhere{}(), function{}(), total{}(), injective{}()]
                symbol g{}(SortNat{}) : SortNat{} [function{}(), total{}(), injective{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(z{}())), \top{R}())
                    ),
                    \equals{SortNat{}, R}(
                        f{}(X0:SortNat{}),
                        \and{SortNat{}}(f{}(z{}()), \top{SortNat{}}())
                    )
                ) [label{}("collapse"), anywhere{}()]
            endmodule []"#,
    )
    .expect("injective anywhere function definition should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("injective anywhere function definition should internalize");
    let constant =
        |name: &str| Term::application(definition.symbols[name].clone(), Vec::new(), Vec::new());
    let application = |name: &str, argument: Term| {
        Term::application(definition.symbols[name].clone(), Vec::new(), vec![argument])
    };
    let z = constant("z");
    let s_z = application("s", z.clone());

    for mode in [MatchMode::Rewrite, MatchMode::Implies] {
        let result = match_terms_in_definition(
            mode,
            &definition,
            &application("f", z.clone()),
            &application("f", s_z.clone()),
        );
        assert!(
            matches!(result, MatchResult::Indeterminate { .. }),
            "{mode:?}: f(s(z)) equals f(z) by the anywhere equation: {result:?}"
        );
        assert!(matches!(
            match_terms_in_definition(
                mode,
                &definition,
                &application("g", z.clone()),
                &application("g", s_z.clone()),
            ),
            MatchResult::Failed(FailReason::DifferentSymbols(..))
        ));
    }
}

#[test]
fn rewrite_matching_decides_an_anywhere_head_under_a_widening_injection() {
    let syntax = parse_definition(
        r#"[]
            module MAIN
                sort SortInt{} [hasDomainValues{}()]
                sort SortExp{} []
                sort SortKItem{} []
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                symbol first{}() : SortExp{} [constructor{}(), total{}()]
                symbol second{}() : SortExp{} [constructor{}(), total{}()]
                symbol anywhereHead{}(SortExp{}, SortExp{}) : SortExp{}
                    [anywhere{}(), total{}(), injective{}()]
                symbol declaredHead{}(SortExp{}, SortExp{}) : SortExp{}
                    [function{}(), total{}(), injective{}()]
                axiom{R} \exists{R}(E:SortExp{}, \equals{SortExp{}, R}(
                    E:SortExp{}, inj{SortInt{}, SortExp{}}(I:SortInt{})
                )) [subsort{SortInt{}, SortExp{}}()]
                axiom{R} \exists{R}(K:SortKItem{}, \equals{SortKItem{}, R}(
                    K:SortKItem{}, inj{SortExp{}, SortKItem{}}(E:SortExp{})
                )) [subsort{SortExp{}, SortKItem{}}()]
            endmodule []"#,
    )
    .expect("widening-injection definition should parse");
    let definition = BackendDefinition::internalize(&syntax, "MAIN")
        .expect("widening-injection definition should internalize");
    let pattern = internal_term(
        &definition,
        "inj{SortExp{}, SortKItem{}}(anywhereHead{}(HOLE:SortExp{}, K1:SortExp{}))",
    );
    let unlike = internal_term(
        &definition,
        r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0"))"#,
    );

    assert!(matches!(
        match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &unlike),
        MatchResult::Failed(FailReason::DifferentSymbols(..))
    ));
    for mode in [MatchMode::Evaluate, MatchMode::Implies] {
        assert!(matches!(
            match_terms_in_definition(mode, &definition, &pattern, &unlike),
            MatchResult::Indeterminate { .. }
        ));
    }

    let positive = internal_term(
        &definition,
        "inj{SortExp{}, SortKItem{}}(anywhereHead{}(first{}(), second{}()))",
    );
    assert_eq!(
        match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &positive),
        MatchResult::Success(Substitution::from([
            (
                Variable::new("HOLE", Sort::simple("SortExp")),
                internal_term(&definition, "first{}()"),
            ),
            (
                Variable::new("K1", Sort::simple("SortExp")),
                internal_term(&definition, "second{}()"),
            ),
        ]))
    );

    let declared = internal_term(
        &definition,
        "inj{SortExp{}, SortKItem{}}(declaredHead{}(HOLE:SortExp{}, K1:SortExp{}))",
    );
    assert!(matches!(
        match_terms_in_definition(MatchMode::Rewrite, &definition, &declared, &unlike),
        MatchResult::Indeterminate { .. }
    ));

    let narrow_pattern = internal_term(
        &definition,
        r#"inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0"))"#,
    );
    assert!(matches!(
        match_terms_in_definition(MatchMode::Rewrite, &definition, &narrow_pattern, &positive,),
        MatchResult::Failed(FailReason::DifferentSymbols(..))
    ));
    assert!(matches!(
        match_terms_in_definition(MatchMode::Evaluate, &definition, &narrow_pattern, &positive,),
        MatchResult::Indeterminate { .. }
    ));
}

/// An overload lift cannot replace an uninterpreted root by a free common head
/// and then bind arguments that the uninterpreted application's role leaves opaque.
#[test]
fn overload_lifting_preserves_uninterpreted_applications() {
    let syntax = parse_definition(
        r#"[]
        module MAIN
            sort SortS{} []
            symbol a{}() : SortS{} [constructor{}(), functional{}()]
            symbol lower{}(SortS{}) : SortS{} [functional{}()]
            symbol upper{}(SortS{}) : SortS{} [constructor{}(), functional{}()]
            axiom{R} \equals{SortS{}, R}(upper{}(X:SortS{}), lower{}(Y:SortS{}))
                [symbol-overload{}(upper{}(), lower{}())]
        endmodule []"#,
    )
    .expect("overload definition parses");
    let definition = BackendDefinition::internalize(&syntax, "MAIN").expect("definition loads");
    let opaque_variable = internal_term(&definition, "lower{}(X:SortS{})");
    let opaque_value = internal_term(&definition, "lower{}(a{}())");
    let free_variable = internal_term(&definition, "upper{}(X:SortS{})");
    let free_value = internal_term(&definition, "upper{}(a{}())");
    for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
        // Q2 may refute an overloaded pattern against a rigid root; it never binds
        // the uninterpreted pattern's arguments by lifting to a common production.
        assert!(matches!(
            match_terms_in_definition(mode, &definition, &opaque_variable, &free_value),
            MatchResult::Indeterminate { .. }
                | MatchResult::Failed(FailReason::DifferentSymbols(..))
        ));
        // An uninterpreted subject always reaches the identity/defer gate.
        assert!(matches!(
            match_terms_in_definition(mode, &definition, &free_variable, &opaque_value),
            MatchResult::Indeterminate { .. }
        ));
    }
}

#[test]
fn lifts_a_direct_overload_across_a_sort_injection() {
    let definition = overload_definition();
    let variable = Variable::new("X", Sort::simple("SortTop"));
    let pattern = Term::application(
        definition.symbols["upper"].clone(),
        Vec::new(),
        vec![Term::variable(variable.clone())],
    );
    let value = Term::domain_value(Sort::simple("SortSub"), "value");
    let subject = Term::injection(
        Sort::simple("SortSub"),
        Sort::simple("SortTop"),
        Term::application(
            definition.symbols["lower"].clone(),
            Vec::new(),
            vec![value.clone()],
        ),
    );

    assert_eq!(
        match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject),
        MatchResult::Success(Substitution::from([(
            variable,
            Term::injection(Sort::simple("SortSub"), Sort::simple("SortTop"), value,),
        )]))
    );
}

#[test]
fn rejects_a_rigid_domain_value_outside_an_overload_family() {
    let definition = overload_definition();
    let pattern = Term::application(
        definition.symbols["upper"].clone(),
        Vec::new(),
        vec![Term::variable(Variable::new("X", Sort::simple("SortTop")))],
    );
    let subject = Term::injection(
        Sort::simple("SortSub"),
        Sort::simple("SortTop"),
        Term::domain_value(Sort::simple("SortSub"), "value"),
    );

    assert!(matches!(
        match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject),
        MatchResult::Failed(FailReason::DifferentSymbols(..))
    ));
}

#[test]
fn lowers_a_normalized_ground_overload_for_sort_membership() {
    let definition = ground_overload_definition();
    let variable = Variable::new("X", Sort::simple("SortKResult"));
    let pattern = Term::injection(
        Sort::simple("SortKResult"),
        Sort::simple("SortKItem"),
        Term::variable(variable.clone()),
    );
    let subject = internal_term(
        &definition,
        "inj{SortExps{}, SortKItem{}}(exps{}(inj{SortVal{}, SortExp{}}(val{}()), inj{SortVals{}, SortExps{}}(dotVals{}())))",
    );

    assert_eq!(
        match_terms_in_definition(MatchMode::Evaluate, &definition, &pattern, &subject),
        MatchResult::Success(Substitution::from([(
            variable,
            internal_term(
                &definition,
                "inj{SortVals{}, SortKResult{}}(vals{}(val{}(), dotVals{}()))",
            ),
        )]))
    );
}

#[test]
fn refutes_sort_membership_when_a_ground_overload_cannot_lower() {
    let definition = ground_overload_definition();
    let pattern = internal_term(
        &definition,
        "inj{SortKResult{}, SortKItem{}}(X:SortKResult{})",
    );
    let subject = internal_term(
        &definition,
        "inj{SortExps{}, SortKItem{}}(exps{}(fun{}(), inj{SortVals{}, SortExps{}}(dotVals{}())))",
    );

    assert!(matches!(
        match_terms_in_definition(MatchMode::Evaluate, &definition, &pattern, &subject),
        MatchResult::Failed(FailReason::DifferentSorts(..))
    ));
}

/// Lowering an overload is also argument decomposition. A ground uninterpreted
/// member must retain the sort-membership condition instead of becoming a lower constructor.
#[test]
fn overload_lowering_preserves_an_uninterpreted_subject() {
    let mut syntax = parse_definition(include_str!("../fixtures/ground-overload.kore"))
        .expect("overload fixture parses");
    for module in &mut syntax.modules {
        for sentence in &mut module.sentences {
            if let k_rust_kore::kore::ast::Sentence::SymbolDeclaration {
                symbol, attributes, ..
            } = sentence
                && symbol.name == "exps"
            {
                *attributes = k_rust_kore::kore::ast::Attributes(vec![
                    k_rust_kore::kore::parser::parse_pattern("functional{}()")
                        .expect("functional attribute parses"),
                ]);
            }
        }
    }
    let definition = BackendDefinition::internalize(&syntax, "GROUND-OVERLOAD")
        .expect("uninterpreted overload definition loads");
    let pattern = internal_term(
        &definition,
        "inj{SortKResult{}, SortKItem{}}(X:SortKResult{})",
    );
    let subject = internal_term(
        &definition,
        "inj{SortExps{}, SortKItem{}}(exps{}(inj{SortVal{}, SortExp{}}(val{}()), inj{SortVals{}, SortExps{}}(dotVals{}())))",
    );
    assert!(matches!(
        match_terms_in_definition(MatchMode::Evaluate, &definition, &pattern, &subject),
        MatchResult::Indeterminate { .. }
    ));
}

#[test]
fn keeps_symbolic_and_ordinary_function_overload_membership_indeterminate() {
    let definition = ground_overload_definition();
    let pattern = internal_term(
        &definition,
        "inj{SortKResult{}, SortKItem{}}(X:SortKResult{})",
    );
    for subject in [
        "inj{SortExps{}, SortKItem{}}(exps{}(E:SortExp{}, inj{SortVals{}, SortExps{}}(dotVals{}())))",
        "inj{SortExps{}, SortKItem{}}(exps{}(ordinary{}(fun{}()), inj{SortVals{}, SortExps{}}(dotVals{}())))",
    ] {
        let subject = internal_term(&definition, subject);
        assert!(matches!(
            match_terms_in_definition(MatchMode::Evaluate, &definition, &pattern, &subject),
            MatchResult::Indeterminate { .. }
        ));
    }
}

#[test]
fn lifts_a_direct_overload_in_the_pattern_orientation() {
    let definition = overload_definition();
    let variable = Variable::new("X", Sort::simple("SortSub"));
    let pattern = Term::injection(
        Sort::simple("SortSub"),
        Sort::simple("SortTop"),
        Term::application(
            definition.symbols["lower"].clone(),
            Vec::new(),
            vec![Term::variable(variable.clone())],
        ),
    );
    let value = Term::domain_value(Sort::simple("SortSub"), "value");
    let subject = Term::application(
        definition.symbols["upper"].clone(),
        Vec::new(),
        vec![Term::injection(
            Sort::simple("SortSub"),
            Sort::simple("SortTop"),
            value.clone(),
        )],
    );

    assert_eq!(
        match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject),
        MatchResult::Success(Substitution::from([(variable, value)]))
    );
}

#[test]
fn defers_sort_aligned_injection_pairs_for_a_supersort_subject_variable() {
    let sub = Sort::simple("SortSub");
    let sup = Sort::simple("SortSup");
    let top = Sort::simple("SortTop");
    let pattern_child = var("X", sub.clone());
    let subject_child = var("Y", sup.clone());
    let pattern = Term::injection(sub.clone(), top.clone(), pattern_child.clone());
    let subject = Term::injection(sup.clone(), top, subject_child.clone());
    let mut sorts = SortGraph::default();
    sorts.insert("SortSub", []);
    sorts.insert("SortSup", [Name::from("SortSub")]);
    sorts.insert("SortTop", [Name::from("SortSub"), Name::from("SortSup")]);

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sorts, &pattern, &subject),
        MatchResult::Indeterminate {
            substitution: Substitution::new(),
            remainder: vec![(Term::injection(sub, sup, pattern_child), subject_child,)],
        }
    );
}

#[test]
fn defers_sort_aligned_injection_pairs_for_a_supersort_pattern_function() {
    let sub = Sort::simple("SortSub");
    let sup = Sort::simple("SortSup");
    let top = Sort::simple("SortTop");
    let mut function = Symbol::constructor("f", vec![sub.clone()], sup.clone());
    function.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
    function.attributes.has_evaluators = true;
    let pattern_child =
        Term::application(Arc::new(function), Vec::new(), vec![var("X", sub.clone())]);
    let subject_child = domain_value(sub.clone(), "a");
    let pattern = Term::injection(sup.clone(), top.clone(), pattern_child.clone());
    let subject = Term::injection(sub.clone(), top, subject_child.clone());
    let mut sorts = SortGraph::default();
    sorts.insert("SortSub", []);
    sorts.insert("SortSup", [Name::from("SortSub")]);
    sorts.insert("SortTop", [Name::from("SortSub"), Name::from("SortSup")]);

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sorts, &pattern, &subject),
        MatchResult::Indeterminate {
            substitution: Substitution::new(),
            remainder: vec![(pattern_child, Term::injection(sub, sup, subject_child),)],
        }
    );
}

#[test]
fn lifts_incomparable_symbols_to_their_unique_common_overload() {
    let definition = overload_definition();
    let variable = Variable::new("X", Sort::simple("SortSub"));
    let pattern = Term::injection(
        Sort::simple("SortLeft"),
        Sort::simple("SortTop"),
        Term::application(
            definition.symbols["left"].clone(),
            Vec::new(),
            vec![Term::injection(
                Sort::simple("SortSub"),
                Sort::simple("SortLeft"),
                Term::variable(variable.clone()),
            )],
        ),
    );
    let value = Term::domain_value(Sort::simple("SortSub"), "value");
    let subject = Term::injection(
        Sort::simple("SortRight"),
        Sort::simple("SortTop"),
        Term::application(
            definition.symbols["right"].clone(),
            Vec::new(),
            vec![Term::injection(
                Sort::simple("SortSub"),
                Sort::simple("SortRight"),
                value.clone(),
            )],
        ),
    );

    assert_eq!(
        match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &subject),
        MatchResult::Success(Substitution::from([(variable, value)]))
    );
}

#[test]
fn matches_concrete_list_heads() {
    let definition = list_definition();
    let first = domain_value(sort(), "first");
    let second = domain_value(sort(), "second");
    let pattern = Term::list(
        definition.clone(),
        vec![first.clone(), var("X", sort())],
        None,
    );
    let subject = Term::list(definition, vec![first, second.clone()], None);

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::from([(variable("X", sort()), second,)]))
    );
}

#[test]
fn extracts_a_list_remainder() {
    let definition = list_definition();
    let first = domain_value(sort(), "first");
    let second = domain_value(sort(), "second");
    let remainder = variable("REST", Sort::simple("ListSort"));
    let pattern = Term::list(
        definition.clone(),
        Vec::new(),
        Some((Term::variable(remainder.clone()), Vec::new())),
    );
    let expected = Term::list(
        definition.clone(),
        vec![first.clone(), second.clone()],
        None,
    );
    let subject = Term::list(definition, vec![first, second], None);

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::from([(remainder, expected)]))
    );
}

#[test]
fn defers_a_closed_list_pattern_against_a_variable_frame_in_rewrite_mode() {
    let definition = list_definition();
    let first = domain_value(sort(), "first");
    let frame = variable("FRAME", Sort::simple("ListSort"));
    let pattern = Term::list(definition.clone(), vec![first.clone()], None);
    let subject = Term::list(
        definition.clone(),
        vec![first.clone()],
        Some((Term::variable(frame.clone()), Vec::new())),
    );

    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Indeterminate { substitution, remainder }
            if substitution.is_empty()
                && remainder == vec![(
                    Term::list(definition.clone(), Vec::new(), None),
                    Term::list(
                        definition.clone(),
                        Vec::new(),
                        Some((Term::variable(frame.clone()), Vec::new())),
                    ),
                )]
    ));
    assert!(matches!(
        match_terms(MatchMode::Evaluate, &sort_graph(), &pattern, &subject),
        MatchResult::Failed(FailReason::DifferentValues(_, _))
    ));

    let empty = Term::list(definition.clone(), Vec::new(), None);
    let longer_subject = Term::list(
        definition,
        vec![first],
        Some((Term::variable(frame), Vec::new())),
    );
    for mode in [MatchMode::Rewrite, MatchMode::Evaluate] {
        assert!(matches!(
            match_terms(mode, &sort_graph(), &empty, &longer_subject),
            MatchResult::Failed(FailReason::DifferentValues(_, _))
        ));
    }
}

#[test]
fn matches_map_values_at_concrete_keys() {
    let definition = map_definition();
    let key = domain_value(Sort::simple("MapKey"), "key");
    let value = domain_value(Sort::simple("MapValue"), "value");
    let value_variable = variable("VALUE", Sort::simple("MapValue"));
    let pattern = Term::map(
        definition.clone(),
        vec![(key.clone(), Term::variable(value_variable.clone()))],
        None,
    );
    let subject = Term::map(definition, vec![(key, value.clone())], None);

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::from([(value_variable, value)]))
    );
}

#[test]
fn defers_a_closed_map_pattern_against_a_variable_frame_in_rewrite_mode() {
    let definition = map_definition();
    let key = domain_value(Sort::simple("MapKey"), "key");
    let value = domain_value(Sort::simple("MapValue"), "value");
    let frame = variable("FRAME", Sort::simple("MapSort"));
    let pattern = Term::map(definition.clone(), vec![(key.clone(), value.clone())], None);
    let subject = Term::map(
        definition.clone(),
        vec![(key, value)],
        Some(Term::variable(frame.clone())),
    );

    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Indeterminate { substitution, remainder }
            if substitution.is_empty()
                && remainder == vec![(
                    Term::map(definition.clone(), Vec::new(), None),
                    Term::map(
                        definition.clone(),
                        Vec::new(),
                        Some(Term::variable(frame.clone())),
                    ),
                )]
    ));
    for mode in [MatchMode::Evaluate, MatchMode::Implies] {
        assert!(matches!(
            match_terms(mode, &sort_graph(), &pattern, &subject),
            MatchResult::Failed(FailReason::DifferentContents(_, _))
        ));
    }
}

#[test]
fn matches_the_only_symbolic_map_entry() {
    let definition = map_definition();
    let key_variable = variable("KEY", Sort::simple("MapKey"));
    let value_variable = variable("VALUE", Sort::simple("MapValue"));
    let key = domain_value(Sort::simple("MapKey"), "key");
    let value = domain_value(Sort::simple("MapValue"), "value");
    let pattern = Term::map(
        definition.clone(),
        vec![(
            Term::variable(key_variable.clone()),
            Term::variable(value_variable.clone()),
        )],
        None,
    );
    let subject = Term::map(definition, vec![(key.clone(), value.clone())], None);

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::from([
            (key_variable, key),
            (value_variable, value),
        ]))
    );
}

#[test]
fn empties_a_map_frame_after_an_unambiguous_selection() {
    let definition = map_definition();
    let key_variable = variable("KEY", Sort::simple("MapKey"));
    let value_variable = variable("VALUE", Sort::simple("MapValue"));
    let rest_variable = variable("REST", Sort::simple("MapSort"));
    let key = domain_value(Sort::simple("MapKey"), "key");
    let value = domain_value(Sort::simple("MapValue"), "value");
    let empty = Term::map(definition.clone(), Vec::new(), None);
    let pattern = Term::map(
        definition.clone(),
        vec![(
            Term::variable(key_variable.clone()),
            Term::variable(value_variable.clone()),
        )],
        Some(Term::variable(rest_variable.clone())),
    );
    let subject = Term::map(definition, vec![(key.clone(), value.clone())], None);

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::from([
            (key_variable, key),
            (rest_variable, empty),
            (value_variable, value),
        ]))
    );
}

#[test]
fn defers_a_symbolic_map_entry_against_a_subject_frame() {
    let definition = map_definition();
    let key_variable = variable("KEY", Sort::simple("MapKey"));
    let value_variable = variable("VALUE", Sort::simple("MapValue"));
    let rest_variable = variable("REST", Sort::simple("MapSort"));
    let subject_key = variable("SUBJECT_KEY", Sort::simple("MapKey"));
    let subject_value = variable("SUBJECT_VALUE", Sort::simple("MapValue"));
    let subject_rest = variable("SUBJECT_REST", Sort::simple("MapSort"));
    let pattern = Term::map(
        definition.clone(),
        vec![(
            Term::variable(key_variable.clone()),
            Term::variable(value_variable.clone()),
        )],
        Some(Term::variable(rest_variable.clone())),
    );
    let subject = Term::map(
        definition.clone(),
        vec![(
            Term::variable(subject_key.clone()),
            Term::variable(subject_value.clone()),
        )],
        Some(Term::variable(subject_rest.clone())),
    );

    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Indeterminate { substitution, remainder }
            if substitution.is_empty()
                && remainder == vec![(pattern.clone(), subject.clone())]
    ));
    let closed_subject = Term::map(
        definition,
        vec![(Term::variable(subject_key), Term::variable(subject_value))],
        None,
    );
    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &closed_subject,),
        MatchResult::Success(_)
    ));
}

#[test]
fn extracts_a_map_remainder_after_common_keys() {
    let definition = map_definition();
    let common_key = domain_value(Sort::simple("MapKey"), "common");
    let extra_key = domain_value(Sort::simple("MapKey"), "extra");
    let common_value = domain_value(Sort::simple("MapValue"), "common-value");
    let extra_value = domain_value(Sort::simple("MapValue"), "extra-value");
    let remainder = variable("REST", Sort::simple("MapSort"));
    let pattern = Term::map(
        definition.clone(),
        vec![(common_key.clone(), common_value.clone())],
        Some(Term::variable(remainder.clone())),
    );
    let expected = Term::map(
        definition.clone(),
        vec![(extra_key.clone(), extra_value.clone())],
        None,
    );
    let subject = Term::map(
        definition,
        vec![(common_key, common_value), (extra_key, extra_value)],
        None,
    );

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::from([(remainder, expected)]))
    );
}

#[test]
fn matches_identical_concrete_sets_independent_of_input_order() {
    let definition = set_definition();
    let first = domain_value(Sort::simple("SetElement"), "first");
    let second = domain_value(Sort::simple("SetElement"), "second");
    let pattern = Term::set(
        definition.clone(),
        vec![first.clone(), second.clone()],
        None,
    );
    let subject = Term::set(definition, vec![second, first], None);

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::new())
    );
}

#[test]
fn extracts_a_set_remainder_after_common_elements() {
    let definition = set_definition();
    let common = domain_value(Sort::simple("SetElement"), "common");
    let extra = domain_value(Sort::simple("SetElement"), "extra");
    let remainder = variable("REST", Sort::simple("SetSort"));
    let pattern = Term::set(
        definition.clone(),
        vec![common.clone()],
        Some(Term::variable(remainder.clone())),
    );
    let expected = Term::set(definition.clone(), vec![extra.clone()], None);
    let subject = Term::set(definition, vec![common, extra], None);

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::from([(remainder, expected)]))
    );
}

#[test]
fn matches_an_unambiguous_symbolic_set_element() {
    let definition = set_definition();
    let element_variable = variable("ELEMENT", Sort::simple("SetElement"));
    let element = domain_value(Sort::simple("SetElement"), "element");
    let pattern = Term::set(
        definition.clone(),
        vec![Term::variable(element_variable.clone())],
        None,
    );
    let subject = Term::set(definition, vec![element.clone()], None);

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::from([(element_variable, element)]))
    );
}

#[test]
fn empties_a_set_frame_after_an_unambiguous_selection() {
    let definition = set_definition();
    let element_variable = variable("ELEMENT", Sort::simple("SetElement"));
    let rest_variable = variable("REST", Sort::simple("SetSort"));
    let element = domain_value(Sort::simple("SetElement"), "element");
    let empty = Term::set(definition.clone(), Vec::new(), None);
    let pattern = Term::set(
        definition.clone(),
        vec![Term::variable(element_variable.clone())],
        Some(Term::variable(rest_variable.clone())),
    );
    let subject = Term::set(definition, vec![element.clone()], None);

    assert_eq!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Success(Substitution::from([
            (element_variable, element),
            (rest_variable, empty),
        ]))
    );
}

#[test]
fn defers_a_symbolic_set_element_against_a_subject_frame() {
    let definition = set_definition();
    let element_variable = variable("ELEMENT", Sort::simple("SetElement"));
    let rest_variable = variable("REST", Sort::simple("SetSort"));
    let subject_element = variable("SUBJECT_ELEMENT", Sort::simple("SetElement"));
    let subject_rest = variable("SUBJECT_REST", Sort::simple("SetSort"));
    let pattern = Term::set(
        definition.clone(),
        vec![Term::variable(element_variable.clone())],
        Some(Term::variable(rest_variable.clone())),
    );
    let subject = Term::set(
        definition.clone(),
        vec![Term::variable(subject_element.clone())],
        Some(Term::variable(subject_rest.clone())),
    );

    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Indeterminate { substitution, remainder }
            if substitution.is_empty()
                && remainder == vec![(pattern.clone(), subject.clone())]
    ));
    let closed_subject = Term::set(definition, vec![Term::variable(subject_element)], None);
    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &closed_subject,),
        MatchResult::Success(_)
    ));
}

#[test]
fn defers_a_closed_set_pattern_against_a_variable_frame_in_rewrite_mode() {
    let definition = set_definition();
    let first = domain_value(Sort::simple("SetElement"), "first");
    let frame = variable("FRAME", Sort::simple("SetSort"));
    let pattern = Term::set(definition.clone(), vec![first.clone()], None);
    let subject = Term::set(definition, vec![first], Some(Term::variable(frame)));

    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Indeterminate { substitution, remainder }
            if substitution.is_empty() && remainder.len() == 1
    ));
    assert!(matches!(
        match_terms(MatchMode::Evaluate, &sort_graph(), &pattern, &subject),
        MatchResult::Failed(FailReason::DifferentContents(_, _))
    ));
}

#[test]
fn defers_ambiguous_symbolic_set_selection() {
    let definition = set_definition();
    let pattern = Term::set(
        definition.clone(),
        vec![var("ELEMENT", Sort::simple("SetElement"))],
        Some(var("REST", Sort::simple("SetSort"))),
    );
    let subject = Term::set(
        definition,
        vec![
            domain_value(Sort::simple("SetElement"), "first"),
            domain_value(Sort::simple("SetElement"), "second"),
        ],
        None,
    );

    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Indeterminate { remainder, .. } if remainder == vec![(pattern, subject)]
    ));
}

#[test]
fn rejects_a_nonempty_pattern_against_the_empty_set() {
    let definition = set_definition();
    let pattern = Term::set(
        definition.clone(),
        vec![var("ELEMENT", Sort::simple("SetElement"))],
        Some(var("REST", Sort::simple("SetSort"))),
    );
    let subject = Term::set(definition, Vec::new(), None);

    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Failed(FailReason::DifferentContents(_, _))
    ));
}

/// Set concatenation is nilpotent: a set that holds an element twice is `\bottom`, so it matches
/// nothing, and a pattern whose elements the substitution makes equal matches nothing either.
#[test]
fn a_set_holding_an_element_twice_matches_nothing() {
    let definition = set_definition();
    let element = domain_value(Sort::simple("SetElement"), "a");
    let repeated = Term::set(
        definition.clone(),
        vec![element.clone(), element.clone()],
        None,
    );
    let rest = var("REST", Sort::simple("SetSort"));
    let pattern = Term::set(
        definition.clone(),
        vec![var("X", Sort::simple("SetElement"))],
        Some(rest),
    );
    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &repeated),
        MatchResult::Failed(FailReason::DuplicateKeys(found, _)) if found == element
    ));

    let pair = Arc::new(Symbol::constructor(
        "pair",
        vec![Sort::simple("SetElement"), Sort::simple("SetSort")],
        sort(),
    ));
    let x = var("X", Sort::simple("SetElement"));
    let pattern = Term::application(
        pair.clone(),
        Vec::new(),
        vec![
            x.clone(),
            Term::set(definition.clone(), vec![x, element.clone()], None),
        ],
    );
    let subject = Term::application(
        pair,
        Vec::new(),
        vec![
            element.clone(),
            Term::set(
                definition,
                vec![element, domain_value(Sort::simple("SetElement"), "b")],
                None,
            ),
        ],
    );
    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Failed(FailReason::DuplicateKeys(..))
    ));
}

#[test]
fn reports_duplicate_map_keys() {
    let definition = map_definition();
    let key = domain_value(Sort::simple("MapKey"), "duplicate");
    let pattern = Term::map(
        definition.clone(),
        vec![
            (key.clone(), domain_value(Sort::simple("MapValue"), "one")),
            (key.clone(), domain_value(Sort::simple("MapValue"), "two")),
        ],
        None,
    );
    let subject = Term::map(definition, Vec::new(), None);

    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Failed(FailReason::DuplicateKeys(found, _)) if found == key
    ));
}

#[test]
fn reports_the_least_duplicate_map_key() {
    let definition = map_definition();
    let key = |name| domain_value(Sort::simple("MapKey"), name);
    let value = |name| domain_value(Sort::simple("MapValue"), name);
    let subject = Term::map(
        definition.clone(),
        vec![
            (key("b"), value("one")),
            (key("b"), value("two")),
            (key("a"), value("one")),
            (key("a"), value("two")),
        ],
        None,
    );
    let pattern = Term::map(definition, Vec::new(), None);

    assert!(matches!(
        match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
        MatchResult::Failed(FailReason::DuplicateKeys(found, _)) if found == key("a")
    ));
}

/// A pattern variable bound to a subject variable reaches a map key, so that matching binds the
/// subject variable `X` to the subject key: `pair(K, {K |-> V})` against `pair(X, {key(X) |->
/// 1})` asks `X = key(X)`. Through the free constructor `succ` the equation has no finite
/// solution, and the refutation carries the cycle; through the function `g` it holds when
/// `g(X)` evaluates to `X`, so the pair is left to the caller in every mode.
#[test]
fn a_variable_cycle_refutes_a_match_only_through_free_constructors() {
    let key_sort = Sort::simple("MapKey");
    let pair = Arc::new(Symbol::constructor(
        "pair",
        vec![key_sort.clone(), Sort::simple("MapSort")],
        sort(),
    ));
    let successor = Arc::new(Symbol::constructor(
        "succ",
        vec![key_sort.clone()],
        key_sort.clone(),
    ));
    let mut g = Symbol::constructor("g", vec![key_sort.clone()], key_sort.clone());
    g.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
    let g = Arc::new(g);
    let x = variable("X", key_sort.clone());
    let one = domain_value(Sort::simple("MapValue"), "1");
    let pattern = Term::application(
        pair.clone(),
        Vec::new(),
        vec![
            var("K", key_sort.clone()),
            Term::map(
                map_definition(),
                vec![(
                    var("K", key_sort.clone()),
                    var("V", Sort::simple("MapValue")),
                )],
                None,
            ),
        ],
    );
    let subject = |key: Term| {
        Term::application(
            pair.clone(),
            Vec::new(),
            vec![
                Term::variable(x.clone()),
                Term::map(map_definition(), vec![(key, one.clone())], None),
            ],
        )
    };
    let through_constructor =
        Term::application(successor, Vec::new(), vec![Term::variable(x.clone())]);
    let through_function = Term::application(g, Vec::new(), vec![Term::variable(x.clone())]);
    for mode in [MatchMode::Rewrite, MatchMode::Evaluate] {
        let result = match_terms(
            mode,
            &sort_graph(),
            &pattern,
            &subject(through_constructor.clone()),
        );
        assert!(
            matches!(
                &result,
                MatchResult::Failed(FailReason::VariableRecursion(cycle))
                    if cycle.variable() == &x && cycle.term() == &through_constructor
            ),
            "{mode:?}: {result:?}"
        );
        let result = match_terms(
            mode,
            &sort_graph(),
            &pattern,
            &subject(through_function.clone()),
        );
        assert!(
            matches!(
                &result,
                MatchResult::Indeterminate { remainder, .. }
                    if remainder.contains(&(Term::variable(x.clone()), through_function.clone()))
            ),
            "{mode:?}: {result:?}"
        );
    }
}

/// In `Implies` mode the two sides share variables: `q(X, Y)` against `q(Y, X)` binds `X` to
/// `Y` and then asks `Y = Y`, which holds. A variable is no cycle of itself, so the match is not
/// refuted.
#[test]
fn a_variable_is_no_cycle_of_itself() {
    let q = Arc::new(Symbol::constructor("q", vec![sort(), sort()], sort()));
    let pattern = Term::application(
        q.clone(),
        Vec::new(),
        vec![var("X", sort()), var("Y", sort())],
    );
    let subject = Term::application(q, Vec::new(), vec![var("Y", sort()), var("X", sort())]);
    let result = match_terms(MatchMode::Implies, &sort_graph(), &pattern, &subject);
    assert!(
        matches!(result, MatchResult::Indeterminate { .. }),
        "{result:?}"
    );
}

/// A refutation by the roots holds the pattern and the subject the matcher compared.
#[test]
fn a_head_clash_holds_the_compared_pattern_and_subject() {
    let other = Arc::new(Symbol::constructor("con2", vec![sort()], sort()));
    let value = domain_value(sort(), "value");
    let pattern = application(constructor(), value.clone());
    let subject = application(other, value);
    for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
        let MatchResult::Failed(FailReason::DifferentSymbols(clash)) =
            match_terms(mode, &sort_graph(), &pattern, &subject)
        else {
            panic!("two free constructors with different names clash in {mode:?}");
        };
        assert_eq!(clash.into_terms(), (pattern.clone(), subject.clone()));
    }
}

/// Commutativity identifies the two argument orders, so failure to match as written cannot
/// justify the owise equation. Syntactically identical arguments still select the first equation.
#[test]
fn an_uninterpreted_commutative_argument_blocks_owise() {
    let definition = algebraic_argument_definition("functional{}()", COMMUTATIVITY);
    let input = internal_term(&definition, "f{}(g{}(b{}(), a{}()))");
    let result = simplify(&definition, &input, SimplificationOptions::default())
        .expect("unknown matching leaves the function unevaluated");
    assert_eq!(result.term, input);
    assert!(result.applied_rules.is_empty());

    let input = internal_term(&definition, "f{}(g{}(a{}(), b{}()))");
    let result = simplify(&definition, &input, SimplificationOptions::default())
        .expect("syntactic identity selects the first equation");
    assert_eq!(
        result.term,
        internal_term(&definition, r#"\dv{SortResult{}}("1")"#)
    );
}

const COMMUTATIVITY: &str = r"axiom{R} \equals{SortE{}, R}(
                g{}(X:SortE{}, Y:SortE{}),
                g{}(Y:SortE{}, X:SortE{})
            ) [comm{}()]";

fn algebraic_argument_definition(attributes: &str, axiom: &str) -> BackendDefinition {
    let source = r#"[]
        module MAIN
            sort SortE{} []
            sort SortResult{} [hasDomainValues{}()]
            symbol a{}() : SortE{} [constructor{}(), functional{}()]
            symbol b{}() : SortE{} [constructor{}(), functional{}()]
            symbol g{}(SortE{}, SortE{}) : SortE{} [functional{}()]
            symbol f{}(SortE{}) : SortResult{} [function{}()]
            axiom{R} \equals{SortE{}, R}(
                g{}(X:SortE{}, Y:SortE{}),
                g{}(Y:SortE{}, X:SortE{})
            ) [comm{}()]
            axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(\in{SortE{}, R}(X0:SortE{}, g{}(a{}(), b{}())), \top{R}())
                ),
                \equals{SortResult{}, R}(
                    f{}(X0:SortE{}),
                    \and{SortResult{}}(\dv{SortResult{}}("1"), \top{SortResult{}}())
                )
            ) [label{}("hit")]
            axiom{R} \implies{R}(
                \and{R}(
                    \top{R}(),
                    \and{R}(\in{SortE{}, R}(X0:SortE{}, X:SortE{}), \top{R}())
                ),
                \equals{SortResult{}, R}(
                    f{}(X0:SortE{}),
                    \and{SortResult{}}(\dv{SortResult{}}("0"), \top{SortResult{}}())
                )
            ) [label{}("fallback"), owise{}()]
        endmodule []"#;
    let source = source
        .replace("[functional{}()]", &format!("[{attributes}]"))
        .replace(
            r"axiom{R} \equals{SortE{}, R}(
                g{}(X:SortE{}, Y:SortE{}),
                g{}(Y:SortE{}, X:SortE{})
            ) [comm{}()]",
            axiom,
        );
    let syntax = parse_definition(&source).expect("algebraic definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("algebraic definition should internalize")
}

/// Decomposition of a declared algebraic function can find an equation instance, but a
/// mismatching argument must not justify owise. Cover declaration facts and axiom-only facts.
#[test]
fn declared_algebraic_function_arguments_never_refute_owise() {
    for (attributes, axiom) in [
        ("function{}(), total{}(), assoc{}()", ""),
        ("function{}(), total{}(), idem{}()", ""),
        ("function{}(), total{}()", COMMUTATIVITY),
        (
            "function{}(), total{}()",
            r"axiom{R} \equals{SortE{}, R}(
            g{}(X:SortE{}, a{}()), X:SortE{}
        ) [unit{}()]",
        ),
    ] {
        let definition = algebraic_argument_definition(attributes, axiom);
        let pattern = internal_term(&definition, "g{}(a{}(), b{}())");
        let subject = internal_term(&definition, "g{}(b{}(), a{}())");
        let matched =
            match_terms_in_definition(MatchMode::Evaluate, &definition, &pattern, &subject);
        assert!(matched.refutation().is_none(), "{attributes}: {matched:?}");
        assert!(matches!(matched, MatchResult::Indeterminate { .. }));
        let input = internal_term(&definition, "f{}(g{}(b{}(), a{}()))");
        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();
        assert_eq!(result.term, input, "{attributes}");
        assert!(result.applied_rules.is_empty());

        let input = internal_term(&definition, "f{}(g{}(a{}(), b{}()))");
        let result = simplify(&definition, &input, SimplificationOptions::default()).unwrap();
        assert_eq!(
            result.term,
            internal_term(&definition, r#"\dv{SortResult{}}("1")"#)
        );
    }
}

/// Bindings from one algebraic argument order are only a candidate. A later conflict must
/// discard those bindings and defer the original problem; a complete candidate still succeeds.
#[test]
fn algebraic_function_candidate_bindings_cannot_feed_a_later_refutation() {
    let definition = algebraic_argument_definition("function{}(), total{}()", COMMUTATIVITY);
    let pair = Arc::new(Symbol::constructor(
        "pair",
        vec![Sort::simple("SortE"); 2],
        Sort::simple("SortE"),
    ));
    let pattern = Term::application(
        pair.clone(),
        Vec::new(),
        vec![
            internal_term(&definition, "g{}(X:SortE{}, Y:SortE{})"),
            var("X", Sort::simple("SortE")),
        ],
    );
    for (last, succeeds) in [("b{}()", false), ("a{}()", true), ("Z:SortE{}", false)] {
        let subject = Term::application(
            pair.clone(),
            Vec::new(),
            vec![
                internal_term(&definition, "g{}(a{}(), b{}())"),
                internal_term(&definition, last),
            ],
        );
        let matched =
            match_terms_in_definition(MatchMode::Evaluate, &definition, &pattern, &subject);
        if succeeds {
            assert!(matches!(matched, MatchResult::Success(_)), "{matched:?}");
        } else {
            assert_eq!(
                matched,
                MatchResult::Indeterminate {
                    substitution: Substitution::new(),
                    remainder: vec![(pattern.clone(), subject)],
                }
            );
        }
    }
}
