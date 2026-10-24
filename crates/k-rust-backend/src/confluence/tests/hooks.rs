//! Hook pairs: an executable equation at a symbol whose hook the evaluator applies before any
//! equation, against the hook's written meaning (`confluence/hooks.rs`).

use k_rust_kore::kore::parser::parse_definition;

use super::super::{CheckScope, UnjoinedReason, ValueClaims};
use crate::definition::BackendDefinition;

/// `sel : Bool AB AB -> AB` hooked to `KEQUAL.ite`, `addAB : AB AB -> AB` hooked to `INT.add`
/// (evaluated, no written meaning), `opq : AB -> AB` hooked to a hook no evaluator implements,
/// the constructors `a` and `bb`, and `equations`.
fn definition(equations: &str) -> BackendDefinition {
    let source = format!(
        r#"[] module MAIN
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            sort SortAB{{}} []
            symbol a{{}}() : SortAB{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol bb{{}}() : SortAB{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            hooked-symbol sel{{}}(SortBool{{}}, SortAB{{}}, SortAB{{}}) : SortAB{{}}
                [function{{}}(), total{{}}(), hook{{}}("KEQUAL.ite")]
            hooked-symbol addAB{{}}(SortAB{{}}, SortAB{{}}) : SortAB{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.add")]
            hooked-symbol opq{{}}(SortAB{{}}) : SortAB{{}} [function{{}}(), hook{{}}("ORACLE.function")]
            {equations}
        endmodule []"#
    );
    BackendDefinition::internalize(&parse_definition(&source).expect("parses"), "MAIN")
        .expect("internalizes")
}

/// The equation `head(X0, ..., Xn) = right` over the variables `variables` (`name:sort`),
/// labelled `label`.
fn equation(head: &str, variables: &[&str], right: &str, label: &str) -> String {
    let binders =
        variables
            .iter()
            .enumerate()
            .fold(r"\top{R}()".to_owned(), |rest, (index, variable)| {
                let sort = variable.split_once(':').expect("name:sort").1;
                format!(r"\and{{R}}(\in{{{sort}, R}}(X{index}:{sort}, {variable}), {rest})")
            });
    let arguments = variables
        .iter()
        .enumerate()
        .map(|(index, variable)| format!("X{index}:{}", variable.split_once(':').unwrap().1))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), {binders}),
            \equals{{SortAB{{}}, R}}({head}{{}}({arguments}), \and{{SortAB{{}}}}({right}, \top{{SortAB{{}}}}()))
        ) [label{{}}("{label}")]"#
    )
}

fn all(definition: &BackendDefinition) -> ValueClaims {
    definition.value_claims_in_scope(CheckScope::All)
}

/// r4-hookite: `sel(_, _, Y) = Y` disagrees with `KEQUAL.ite`, whose builtin gives
/// `sel(true, a, bb) = a`; the full check names it against the hook's first meaning.
#[test]
fn an_equation_that_disagrees_with_its_hook_is_named_against_the_hooks_meaning() {
    let definition = definition(&equation(
        "sel",
        &["B:SortBool{}", "X:SortAB{}", "Y:SortAB{}"],
        "Y:SortAB{}",
        "sel-last",
    ));
    let claims = all(&definition);
    let unjoined = claims.unjoined();
    assert_eq!(unjoined.len(), 1, "{unjoined:#?}");
    let pair = &unjoined[0];
    assert_eq!(pair.reason, UnjoinedReason::DifferentResults);
    assert_eq!(pair.hook.as_deref(), Some("KEQUAL.ite"));
    assert_eq!(pair.first.attributes.label.as_deref(), Some("sel-last"));
    assert_eq!(
        pair.second.attributes.label.as_deref(),
        Some("KEQUAL.ite meaning 1")
    );
    // `sel` is hooked, so not taintable: the pair withdraws no claim and is not named at load.
    assert!(!pair.reported());
    let counts = claims.counts();
    assert_eq!((counts.hook.equations, counts.hook.pairs), (1, 2));
    assert_eq!((counts.hook.not_joined, counts.hook.refuted), (1, 0));
    // Hook pairs are counted apart: the definition has no pair of its own equations.
    assert_eq!((counts.pairs, counts.overlaps, counts.unjoined), (0, 0, 1));
}

/// `sel(B, X, X) = X` is an identity of selection: both hook pairs join.
#[test]
fn an_equation_that_agrees_with_its_hook_joins_its_meaning() {
    // `X` binds both branches.
    let definition = definition(
        r#"axiom{R} \implies{R}(
            \and{R}(\top{R}(), \and{R}(\in{SortBool{}, R}(X0:SortBool{}, B:SortBool{}),
                \and{R}(\in{SortAB{}, R}(X1:SortAB{}, X:SortAB{}), \and{R}(\in{SortAB{}, R}(X2:SortAB{}, X:SortAB{}), \top{R}())))),
            \equals{SortAB{}, R}(sel{}(X0:SortBool{}, X1:SortAB{}, X2:SortAB{}), \and{SortAB{}}(X:SortAB{}, \top{SortAB{}}()))
        ) [label{}("sel-same")]"#,
    );
    let claims = all(&definition);
    assert!(claims.unjoined().is_empty(), "{:#?}", claims.unjoined());
    let counts = claims.counts();
    assert_eq!((counts.hook.pairs, counts.hook.joined), (2, 2));
}

/// An equation at a hook the evaluator applies but the table writes no meaning for is reported
/// on its own, whatever the scope; an equation at a hook no evaluator implements is an ordinary
/// equation.
#[test]
fn an_unmodelled_hook_is_reported_and_an_unevaluated_one_is_not() {
    let definition = definition(&format!(
        "{} {}",
        equation(
            "addAB",
            &["X:SortAB{}", "Y:SortAB{}"],
            "X:SortAB{}",
            "add-left"
        ),
        equation("opq", &["X:SortAB{}"], "X:SortAB{}", "opq-id"),
    ));
    for claims in [definition.value_claims().clone(), all(&definition)] {
        let unjoined = claims.unjoined();
        assert_eq!(unjoined.len(), 1, "{unjoined:#?}");
        assert_eq!(
            unjoined[0].reason,
            UnjoinedReason::UnmodelledHook("INT.add".into())
        );
        assert!(unjoined[0].reason.describes_one_equation());
        assert_eq!(
            unjoined[0].first.attributes.label.as_deref(),
            Some("add-left")
        );
        let counts = claims.counts();
        assert_eq!(
            (
                counts.hook.equations,
                counts.hook.unevaluated,
                counts.hook.unmodelled
            ),
            (2, 1, 1)
        );
    }
}

/// The load's scope pairs an equation with its hook's meaning only where the equation is
/// relevant: `sel`'s equation reaches no symbol the gate is asked about, so the load names no
/// hook pair, and the full check does.
#[test]
fn the_load_pairs_only_relevant_equations_with_their_hooks() {
    let definition = definition(&equation(
        "sel",
        &["B:SortBool{}", "X:SortAB{}", "Y:SortAB{}"],
        "Y:SortAB{}",
        "sel-last",
    ));
    assert!(definition.value_claims().unjoined().is_empty());
    assert_eq!(all(&definition).unjoined().len(), 1);
}

/// FUN's prelude holds every equation of `domains.md` at a hooked symbol, with the source
/// locations stripped: each one at an evaluated hook joins every equation of its hook's meaning,
/// but `replaceAll(S, T, R) => replace(S, T, R, countAllOccurrences(S, T))`. Its `replace`
/// equations cannot be identified as domains.md's by origin here, so the guarded lemma that would
/// join it is absent (`hooks::domains_replace`), and it is named against both equations of the
/// meaning written by evaluated builtins.
#[test]
fn the_preludes_hooked_equations_join_their_hooks_meanings() {
    let definition = prelude();
    let claims = all(&definition);
    let named = claims
        .unjoined()
        .iter()
        .filter(|pair| {
            pair.hook.is_some() || matches!(pair.reason, UnjoinedReason::UnmodelledHook(_))
        })
        .map(|pair| {
            (
                pair.hook.as_deref().map(str::to_owned),
                pair.second.attributes.label.clone(),
            )
        })
        .collect::<Vec<_>>();
    let replace_all = Some("STRING.replaceAll".to_owned());
    assert_eq!(
        named,
        [
            (
                replace_all.clone(),
                Some("STRING.replaceAll meaning 1".to_owned())
            ),
            (replace_all, Some("STRING.replaceAll meaning 2".to_owned())),
        ]
    );
    let counts = claims.counts();
    assert!(counts.hook.pairs > 0, "{counts:?}");
    assert_eq!(counts.hook.not_joined, 2);
    assert_eq!(counts.hook.unmodelled, 0);
}

fn prelude() -> BackendDefinition {
    let source = include_str!("../../../tests/fixtures/fun-prelude-hooked-equations.kore");
    BackendDefinition::internalize(&parse_definition(source).expect("parses"), "FUN-UNTYPED")
        .expect("internalizes")
}

/// Review A, B1: a written meaning is a fixed identity of a builtin, so besides the hooked symbol
/// itself it names only constructors, literals and symbols whose hook the evaluator applies,
/// never a symbol whose meaning the definition's equations supply (`STRING.replace`), except
/// domains.md's own `replace` while it is read by exactly domains.md's equations
/// (`hooks::domains_replace`; in this fixture, whose locations are stripped, it is not).
#[test]
fn every_written_meaning_names_only_evaluated_builtins() {
    use crate::{
        confluence::hooks::{HookSymbols, Meaning, WRITTEN, meaning},
        term::{HeadRole, Term, TermKind, Variable},
    };
    let definition = prelude();
    let symbols = HookSymbols::of(&definition);
    for hook in WRITTEN {
        let symbol = definition
            .symbols()
            .values()
            .find(|symbol| symbol.attributes.hook.as_deref() == Some(hook))
            .expect("the prelude declares the hook");
        let sort_arguments = if symbol.sort_variables.is_empty() {
            Vec::new()
        } else {
            vec![crate::term::Sort::simple("SortK")]
        };
        let arguments = symbol
            .argument_sorts
            .iter()
            .enumerate()
            .map(|(index, sort)| {
                let sort = if matches!(sort.node(), crate::term::SortNode::Variable(_)) {
                    crate::term::Sort::simple("SortK")
                } else {
                    *sort
                };
                Term::variable(Variable::new(format!("Z{index}"), sort))
            })
            .collect();
        let lhs = Term::application(std::sync::Arc::clone(symbol), sort_arguments, arguments);
        let guarded = crate::confluence::hooks::domains_replace(&definition);
        let Meaning::Built(rules) = meaning(&symbols, hook, &lhs) else {
            panic!("{hook} has no written meaning in the prelude");
        };
        for rule in rules {
            let mut terms = vec![rule.lhs.clone()];
            if let crate::rule::RuleRhs::Term(rhs) = &rule.rhs {
                terms.push(rhs.clone());
            }
            for predicate in rule.requires.iter() {
                if let crate::rule::Predicate::Equals(left, right) = predicate {
                    terms.extend([left.clone(), right.clone()]);
                }
            }
            for term in terms {
                term.visit_symbols(&mut |used| {
                    let fixed = used.name == symbol.name
                        || guarded
                            .as_ref()
                            .is_some_and(|replace| replace.name == used.name)
                        || used.attributes.head_role() == HeadRole::FreeConstructor
                        || matches!(term.kind(), TermKind::DomainValue { .. })
                        || used
                            .attributes
                            .hook
                            .as_deref()
                            .is_some_and(crate::builtin::evaluates);
                    assert!(fixed, "{hook}'s meaning names `{}`", used.name);
                });
            }
        }
    }
}
