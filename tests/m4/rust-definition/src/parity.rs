//! Readable-versus-prior-explicit semantic parity.
//!
//! Both routes share the production declarations and fixed configuration. The
//! explicit route restates only the 27 migrated IMP rules in the previous
//! `#[k::rule]`/`cells!` form. Comparisons erase source provenance, alpha-rename
//! compiler-generated opaque IDs, and map this test module to `imp`; those are
//! the only intentional source-level differences.

mod prior {
    use k::Term;
    use k::builtin::{Bool, Id, Int, Map, bool, int};
    use k::configuration::{Cell, KCell};
    #[allow(unused_imports)]
    use k::{cells, map};

    use crate::{Expr, Machine, Op, Stmt, StmtSyntax, Value};

    #[k::rule]
    fn eval_neg(k::term![Op::Neg { value }]: Term<Expr>) -> Term<Expr> {
        int::sub(0, value)
    }

    #[k::rule]
    fn eval_not(k::term![Op::Not { value }]: Term<Expr>) -> Term<Expr> {
        bool::not(value)
    }

    macro_rules! binary_rule {
        ($name:ident, $constructor:ident, $operation:path) => {
            #[k::rule]
            fn $name(
                k::term![Op::$constructor { lhs, rhs }]: Term<Expr>,
            ) -> Term<Expr> {
                $operation(lhs, rhs)
            }
        };
    }

    binary_rule!(eval_add, Add, int::add);
    binary_rule!(eval_sub, Sub, int::sub);
    binary_rule!(eval_mul, Mul, int::mul);
    binary_rule!(eval_div, Div, int::div);
    binary_rule!(eval_ge, Ge, int::ge);
    binary_rule!(eval_gt, Gt, int::gt);
    binary_rule!(eval_le, Le, int::le);
    binary_rule!(eval_lt, Lt, int::lt);

    #[k::rule]
    fn eval_bool_eq(
        lhs: Term<Bool>,
        rhs: Term<Bool>,
        k::term![Op::Eq { lhs, rhs }]: Term<Expr>,
    ) -> Term<Expr> {
        bool::eq(lhs, rhs)
    }

    #[k::rule]
    fn eval_int_eq(
        lhs: Term<Int>,
        rhs: Term<Int>,
        k::term![Op::Eq { lhs, rhs }]: Term<Expr>,
    ) -> Term<Expr> {
        int::eq(lhs, rhs)
    }

    #[k::rule]
    fn eval_bool_ne(
        lhs: Term<Bool>,
        rhs: Term<Bool>,
        k::term![Op::Ne { lhs, rhs }]: Term<Expr>,
    ) -> Term<Expr> {
        bool::ne(lhs, rhs)
    }

    #[k::rule]
    fn eval_int_ne(
        lhs: Term<Int>,
        rhs: Term<Int>,
        k::term![Op::Ne { lhs, rhs }]: Term<Expr>,
    ) -> Term<Expr> {
        int::ne(lhs, rhs)
    }

    #[k::rule]
    fn and_true(k::term![Op::And { lhs: true, rhs }]: Term<Expr>) -> Term<Expr> {
        rhs
    }

    #[k::rule]
    fn and_false(k::term![Op::And { lhs: false, rhs: _ }]: Term<Expr>) -> Term<Expr> {
        false
    }

    #[k::rule]
    fn or_true(k::term![Op::Or { lhs: true, rhs: _ }]: Term<Expr>) -> Term<Expr> {
        true
    }

    #[k::rule]
    fn or_false(k::term![Op::Or { lhs: false, rhs }]: Term<Expr>) -> Term<Expr> {
        rhs
    }

    #[k::rule]
    fn step(
        s1: Stmt,
        s2: Stmt,
        cells! {
            k: KCell(StmtSyntax::Sequence(s1, s2), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! { k: KCell(s1, s2, ..tail), ..state }
    }

    #[k::rule]
    fn var(
        name: Term<Id>,
        value: Value,
        cells! {
            k: KCell(name, tail @ ..),
            env: Cell(map![name => value, rest @ ..]),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! { k: KCell(value, ..tail), ..state }
    }

    #[k::rule]
    fn assign(
        name: Term<Id>,
        value: Value,
        environment: Term<Map>,
        cells! {
            k: KCell(StmtSyntax::Assign(name, value), tail @ ..),
            env: Cell(environment),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! {
            k: KCell(..tail),
            env: Cell(map![environment; name <- value]),
            ..state
        }
    }

    #[k::rule(label = "if-true")]
    fn if_true(
        then_branch: Stmt,
        cells! {
            k: KCell(StmtSyntax::IfThenElse(true, then_branch, _), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! { k: KCell(then_branch, ..tail), ..state }
    }

    #[k::rule(label = "if-false")]
    fn if_false(
        else_branch: Stmt,
        cells! {
            k: KCell(StmtSyntax::IfThenElse(false, _, else_branch), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! { k: KCell(else_branch, ..tail), ..state }
    }

    #[k::rule(label = "if-else")]
    fn if_else(
        condition: Expr,
        body: Stmt,
        cells! {
            k: KCell(StmtSyntax::IfThen(condition, body), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! {
            k: KCell(
                StmtSyntax::IfThenElse(condition, body, StmtSyntax::EmptyBlock()),
                ..tail
            ),
            ..state
        }
    }

    #[k::rule(label = "while")]
    fn r#while(
        condition: Expr,
        body: Stmt,
        cells! {
            k: KCell(StmtSyntax::While(condition, body), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! {
            k: KCell(
                StmtSyntax::IfThen(
                    condition,
                    StmtSyntax::Block(StmtSyntax::Sequence(
                        body,
                        StmtSyntax::While(condition, body)
                    ))
                ),
                ..tail
            ),
            ..state
        }
    }

    #[k::rule(label = "block")]
    fn block(
        body: Stmt,
        cells! {
            k: KCell(StmtSyntax::Block(body), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! { k: KCell(body, StmtSyntax::EmptyBlock(), ..tail), ..state }
    }

    #[k::rule(label = "done")]
    fn done(
        cells! {
            k: KCell(StmtSyntax::EmptyBlock(), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! { k: KCell(..tail), ..state }
    }
}

use std::collections::BTreeMap;
use std::path::Path;

use k::{HostDescriptor, HostDescriptorPayload, ItemKind};
use krs_compiler::{
    PackageContext, collect_host_descriptors_with_builtins, emit_k, lower_descriptor_bundle,
    lower_semantic_theory,
};
use serde_json::Value as Json;

const MIGRATED_RULES: usize = 27;

fn is_prior(descriptor: &HostDescriptor) -> bool {
    descriptor.id.rust_module_path() == ["parity", "prior"]
}

fn is_readable_imp_rule(descriptor: &HostDescriptor) -> bool {
    descriptor.id.item_kind() == ItemKind::Rule
        && descriptor.id.rust_module_path() == ["imp"]
        && matches!(descriptor.payload, HostDescriptorPayload::HeadRule(_))
}

fn context() -> PackageContext {
    PackageContext::new(
        "KRS-M4-COMPLETE-IMP",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        "krs_m4_complete_imp",
        Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"),
    )
    .unwrap()
}

fn collect_route(explicit: bool) -> krs_ir::DescriptorBundle {
    let descriptors = k::host_descriptors()
        .filter(|descriptor| {
            if explicit {
                !is_readable_imp_rule(descriptor)
            } else {
                !is_prior(descriptor)
            }
        })
        .collect::<Vec<_>>();
    collect_host_descriptors_with_builtins(
        [context()],
        descriptors,
        &k::builtin_registry(),
    )
    .unwrap()
}

/// Remove only source identity and alpha-rename compiler-owned opaque IDs.
fn normalized(mut value: Json, explicit: bool) -> Json {
    fn visit(
        value: &mut Json,
        explicit: bool,
        generated: &mut BTreeMap<String, String>,
    ) {
        match value {
            Json::Object(object) => {
                object.remove("origin");
                for value in object.values_mut() {
                    visit(value, explicit, generated);
                }
            }
            Json::Array(values) => {
                if explicit
                    && values.len() == 2
                    && values[0] == "parity"
                    && values[1] == "prior"
                {
                    *values = vec![Json::String("imp".into())];
                } else {
                    for value in values {
                        visit(value, explicit, generated);
                    }
                }
            }
            Json::String(text)
                if text.starts_with("sem.")
                    || text.starts_with("def.")
                    || text.starts_with("origin.") =>
            {
                let next = generated.len();
                let replacement = generated
                    .entry(text.clone())
                    .or_insert_with(|| format!("opaque.{next}"));
                *text = replacement.clone();
            }
            _ => {}
        }
    }

    visit(&mut value, explicit, &mut BTreeMap::new());
    value
}

#[test]
fn readable_and_prior_explicit_routes_are_semantically_identical() {
    let readable_bundle = collect_route(false);
    let explicit_bundle = collect_route(true);

    let readable_count = readable_bundle
        .descriptors
        .iter()
        .filter(|descriptor| is_readable_imp_rule_host_id(descriptor))
        .count();
    let explicit_count = explicit_bundle
        .descriptors
        .iter()
        .filter(|descriptor| descriptor.id.module_path() == ["parity", "prior"])
        .count();
    assert_eq!((readable_count, explicit_count), (MIGRATED_RULES, MIGRATED_RULES));

    // Descriptor boundary: everything outside the migrated payload family is
    // byte-identical, and the migrated descriptors have a one-to-one label.
    let shared = |bundle: &krs_ir::DescriptorBundle| {
        krs_ir::DescriptorBundle::new(
            bundle
                .descriptors
                .iter()
                .filter(|descriptor| {
                    descriptor.id.item_kind() != ItemKind::Rule
                        || (!is_readable_imp_rule_host_id(descriptor)
                            && descriptor.id.module_path() != ["parity", "prior"])
                })
                .cloned()
                .collect(),
        )
        .to_canonical_json()
        .unwrap()
    };
    assert_eq!(shared(&readable_bundle), shared(&explicit_bundle));

    let readable_semantic = lower_descriptor_bundle(&readable_bundle).unwrap();
    let explicit_semantic = lower_descriptor_bundle(&explicit_bundle).unwrap();
    assert_eq!(
        normalized(
            serde_json::from_str(&readable_semantic.to_canonical_json().unwrap()).unwrap(),
            false,
        ),
        normalized(
            serde_json::from_str(&explicit_semantic.to_canonical_json().unwrap()).unwrap(),
            true,
        ),
        "Semantic IR differs after the documented source normalization"
    );

    let readable_definition = lower_semantic_theory(&readable_semantic).unwrap();
    let explicit_definition = lower_semantic_theory(&explicit_semantic).unwrap();
    assert_eq!(
        normalized(
            serde_json::from_str(
                &readable_definition.definition().to_canonical_json().unwrap(),
            )
            .unwrap(),
            false,
        ),
        normalized(
            serde_json::from_str(
                &explicit_definition.definition().to_canonical_json().unwrap(),
            )
            .unwrap(),
            true,
        ),
        "Definition IR differs after the documented source normalization"
    );

    assert_eq!(
        emit_k(&readable_definition).unwrap().source(),
        emit_k(&explicit_definition).unwrap().source(),
        "canonical K emission differs"
    );
}

fn is_readable_imp_rule_host_id(descriptor: &krs_ir::Descriptor) -> bool {
    descriptor.id.item_kind() == ItemKind::Rule
        && descriptor.id.module_path() == ["imp"]
}
