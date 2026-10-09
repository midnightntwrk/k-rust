//! `#[k::context(hole = x, result = S, label = "..")]` fns and the
//! `result = S` key of `#[k::context_alias]` (KF-021).

use krs_syntax::{KrsSyntax, ProvenanceRole, SyntaxErrorKind};

fn roles(anchors: &[krs_syntax::ProvenanceAnchor]) -> Vec<ProvenanceRole> {
    anchors
        .iter()
        .map(krs_syntax::ProvenanceAnchor::role)
        .collect()
}

#[test]
fn a_context_names_its_hole_and_optional_result_and_label() {
    let context = krs_syntax::ContextAttribute::parse_source(
        r#"hole = h, result = crate::ExecResult, label = "assign-target""#,
    )
    .unwrap();
    assert_eq!(context.hole(), "h");
    assert_eq!(
        quote::ToTokens::to_token_stream(context.result_sort().unwrap()).to_string(),
        "crate :: ExecResult"
    );
    assert_eq!(context.label().unwrap().value(), "assign-target");
    let name = syn::Ident::new("assign_target", proc_macro2::Span::call_site());
    let attribute = context.rule_attribute(&name);
    let (kind, marker) = attribute.evaluation().unwrap();
    assert_eq!(kind, krs_ir::EvaluationKind::Context);
    assert_eq!(marker, "assign_target");
    assert_eq!(
        roles(&attribute.provenance().unwrap()),
        [
            ProvenanceRole::ContextLabel,
            ProvenanceRole::ContextDeclaration,
            ProvenanceRole::ContextHole,
            ProvenanceRole::ContextResult,
        ]
    );
}

#[test]
fn a_context_requires_one_hole_and_rejects_other_keys() {
    let error = |source: &str| {
        krs_syntax::ContextAttribute::parse_source(source)
            .unwrap_err()
            .kind()
            .clone()
    };
    assert_eq!(
        error(r#"label = "l""#),
        SyntaxErrorKind::MissingArgument { name: "hole" }
    );
    assert_eq!(
        error("hole = h, hole = g"),
        SyntaxErrorKind::DuplicateArgument { name: "hole" }
    );
    assert_eq!(
        error("hole = h, heat"),
        SyntaxErrorKind::UnknownArgument {
            name: "heat".into()
        }
    );
}

#[test]
fn a_term_context_returns_unit_and_rewrites_at_most_its_hole_once() {
    let plain = krs_syntax::RuleItem::parse_context_tokens(quote::quote! {
        fn add_lhs(k::term![Op::Add(h, _)]: Term<Exp>) {}
    })
    .unwrap();
    assert!(plain.result().is_none());
    let lvalue = krs_syntax::RuleItem::parse_context_tokens(quote::quote! {
        fn increment_target(k::term![Op::Inc(k::rewrite!(h => Op::LValue(h)))]: Term<Exp>) {}
    })
    .unwrap();
    assert!(lvalue.result().is_none());

    let reason = |tokens| {
        krs_syntax::RuleItem::parse_context_tokens(tokens)
            .unwrap_err()
            .to_string()
    };
    assert!(
        reason(quote::quote! {
            fn wrapped(k::term![Op::Wrap(h)]: Term<Exp>) -> Term<Exp> { h }
        })
        .contains("a context returns `()`")
    );
    assert!(
        reason(quote::quote! {
            fn twice(k::term![Op::Pair(k::rewrite!(h => Op::Wrap(h)), k::rewrite!(g => Op::Wrap(g)))]: Term<Exp>) {}
        })
        .contains("a context rewrites at most its hole, once")
    );
    assert!(
        reason(quote::quote! {
            #[k::exists(n: Int)]
            fn existential(k::term![Op::Wrap(h)]: Term<Exp>) {}
        })
        .contains("a context takes no `#[k::exists]`")
    );
}

#[test]
fn a_cells_context_lists_its_hole_with_its_other_binders() {
    let context = krs_syntax::StateRuleItem::parse_context_tokens(quote::quote! {
        fn assign_target(
            h: Exp,
            k::cells! {
                k: k::configuration::KCell(Op::Assign(h, _), ..),
                evaluate: k::configuration::Cell(true),
                state @ ..
            }: Machine,
        ) {}
    })
    .unwrap();
    assert!(context.result().is_none());
    assert!(
        krs_syntax::StateRuleItem::parse_context_tokens(quote::quote! {
            fn unlisted(
                k::cells! { k: k::configuration::KCell(Op::Assign(h, _), ..), state @ .. }: Machine,
            ) {}
        })
        .is_err()
    );
}

#[test]
fn a_context_alias_takes_an_optional_result_sort() {
    let alias = krs_syntax::ContextAliasAttribute::parse_source(
        "name = translate, here = site, result = ExecResult",
    )
    .unwrap();
    assert_eq!(
        quote::ToTokens::to_token_stream(alias.result_sort().unwrap()).to_string(),
        "ExecResult"
    );
    assert_eq!(
        roles(&alias.provenance().unwrap()),
        [
            ProvenanceRole::ContextAliasName,
            ProvenanceRole::ContextAliasHere,
            ProvenanceRole::ContextAliasResult,
        ]
    );
    assert_eq!(
        krs_syntax::ContextAliasAttribute::parse_source(
            "name = translate, here = site, result = A, result = B"
        )
        .unwrap_err()
        .kind(),
        &SyntaxErrorKind::DuplicateArgument { name: "result" }
    );
}
