//! Readable-versus-prior-explicit semantic parity.
//!
//! Both routes share the production declarations and fixed configuration. The
//! explicit route preserves the pre-migration rule boundary: the 18 expression
//! rules are bare `Expr -> Expr` rewrites, copied from the repository's
//! pre-readability `imp.rs`, while the nine stateful rules retain their
//! `#[k::rule]`/`cells!` configuration form. The descriptor transports therefore
//! differ by design (`StructuredRule`/`ConfigurationRule` versus `HeadRule`);
//! [`MIGRATED_RULE_MAP`] is the complete, auditable mapping at that boundary.
//! Equality starts at the first common semantic boundary and continues through
//! Semantic IR, Definition IR, and emitted K. The only normalizations are
//! documented at their implementations below.

mod prior {
    use k::Term;
    use k::builtin::{Id, Map, bool, int};
    use k::configuration::{Cell, KCell};
    #[allow(unused_imports)]
    use k::{cells, map};

    use crate::{Expr, Machine, Op, Stmt, StmtSyntax, Value};

    // These 18 bare term rewrites preserve the actual pre-migration boundary
    // from `git show HEAD:tests/imp/rust-definition/src/imp.rs`. Constructor
    // paths changed from standalone structs to enum variants, but the rule
    // shape and symbolic bodies are unchanged.
    #[k::rule]
    fn eval_neg(Op::Neg { value }: Term<Expr>) -> Term<Expr> {
        int::sub(0, value)
    }

    #[k::rule]
    fn eval_not(Op::Not { value }: Term<Expr>) -> Term<Expr> {
        bool::not(value)
    }

    #[k::rule]
    fn eval_add(Op::Add { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        int::add(lhs, rhs)
    }

    #[k::rule]
    fn eval_sub(Op::Sub { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        int::sub(lhs, rhs)
    }

    #[k::rule]
    fn eval_mul(Op::Mul { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        int::mul(lhs, rhs)
    }

    #[k::rule]
    fn eval_div(Op::Div { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        int::div(lhs, rhs)
    }

    #[k::rule]
    fn eval_ge(Op::Ge { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        int::ge(lhs, rhs)
    }

    #[k::rule]
    fn eval_gt(Op::Gt { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        int::gt(lhs, rhs)
    }

    #[k::rule]
    fn eval_le(Op::Le { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        int::le(lhs, rhs)
    }

    #[k::rule]
    fn eval_lt(Op::Lt { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        int::lt(lhs, rhs)
    }

    #[k::rule]
    fn eval_bool_eq(Op::Eq { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        bool::eq(lhs, rhs)
    }

    #[k::rule]
    fn eval_int_eq(Op::Eq { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        int::eq(lhs, rhs)
    }

    #[k::rule]
    fn eval_bool_ne(Op::Ne { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        bool::ne(lhs, rhs)
    }

    #[k::rule]
    fn eval_int_ne(Op::Ne { lhs, rhs }: Term<Expr>) -> Term<Expr> {
        int::ne(lhs, rhs)
    }

    #[k::rule]
    fn and_true(Op::And { lhs: true, rhs }: Term<Expr>) -> Term<Expr> {
        rhs
    }

    #[k::rule]
    fn and_false(Op::And { lhs: false, rhs: _ }: Term<Expr>) -> Term<Expr> {
        false
    }

    #[k::rule]
    fn or_true(Op::Or { lhs: true, rhs: _ }: Term<Expr>) -> Term<Expr> {
        true
    }

    #[k::rule]
    fn or_false(Op::Or { lhs: false, rhs }: Term<Expr>) -> Term<Expr> {
        rhs
    }

    #[k::rule(label = "step")]
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

    #[k::rule(label = "var")]
    fn var(
        name: Term<Id>,
        value: Value,
        cells! {
            k: KCell(name, tail @ ..),
            env: Cell(map![name -> value, rest @ ..]),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! { k: KCell(value, ..tail), ..state }
    }

    #[k::rule(label = "assign")]
    fn assign(
        name: Term<Id>,
        value: Value,
        e: Term<Map>,
        cells! {
            k: KCell(StmtSyntax::Assign(name, value), tail @ ..),
            env: Cell(e),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! {
            k: KCell(..tail),
            env: Cell(map![e; name <- value]),
            ..state
        }
    }

    #[k::rule(label = "if-true")]
    fn if_true(
        s1: Stmt,
        cells! {
            k: KCell(StmtSyntax::IfThenElse(true, s1, _), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! { k: KCell(s1, ..tail), ..state }
    }

    #[k::rule(label = "if-false")]
    fn if_false(
        s2: Stmt,
        cells! {
            k: KCell(StmtSyntax::IfThenElse(false, _, s2), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! { k: KCell(s2, ..tail), ..state }
    }

    #[k::rule(label = "if-else")]
    fn if_else(
        c: Expr,
        s: Stmt,
        cells! {
            k: KCell(StmtSyntax::IfThen(c, s), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! {
            k: KCell(
                StmtSyntax::IfThenElse(c, s, StmtSyntax::EmptyBlock()),
                ..tail
            ),
            ..state
        }
    }

    #[k::rule(label = "while")]
    fn r#while(
        c: Expr,
        s: Stmt,
        cells! {
            k: KCell(StmtSyntax::While(c, s), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! {
            k: KCell(
                StmtSyntax::IfThen(
                    c,
                    StmtSyntax::Block(StmtSyntax::Sequence(
                        s,
                        StmtSyntax::While(c, s)
                    ))
                ),
                ..tail
            ),
            ..state
        }
    }

    #[k::rule(label = "block")]
    fn block(
        s: Stmt,
        cells! {
            k: KCell(StmtSyntax::Block(s), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        cells! { k: KCell(s, StmtSyntax::EmptyBlock(), ..tail), ..state }
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

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use k::{HostDescriptor, HostDescriptorPayload, ItemKind};
use krs_collector::{FacadeAliases, PackageContext, collect_host_descriptors_with_builtins};
use krs_compiler::{
    DescriptorLoweringError, emit_k, expand_reference_source, lower_descriptor_bundle,
    lower_semantic_theory,
};
use krs_ir::{
    DescriptorBundle, DescriptorDeclaration, DescriptorPayload, RustVisibility, StableItemId,
};
use quote::ToTokens;
use serde_json::Value as Json;
use syn::ext::IdentExt;

const MIGRATED_RULES: usize = 27;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PriorTransport {
    StructuredRule,
    ConfigurationRule,
}

#[derive(Clone, Copy)]
struct MigratedRuleRoute {
    item: &'static str,
    label: &'static str,
    prior_transport: PriorTransport,
}

/// Complete mapping from the preserved pre-migration descriptor transports to
/// the readable head-rule transport. Adding, removing, renaming, or changing
/// the transport family of any migrated rule is therefore a parity failure at
/// the Descriptor Bundle boundary, before semantic lowering can hide it.
const MIGRATED_RULE_MAP: [MigratedRuleRoute; MIGRATED_RULES] = [
    MigratedRuleRoute {
        item: "eval_neg",
        label: "eval-neg",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_not",
        label: "eval-not",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_add",
        label: "eval-add",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_sub",
        label: "eval-sub",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_mul",
        label: "eval-mul",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_div",
        label: "eval-div",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_ge",
        label: "eval-ge",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_gt",
        label: "eval-gt",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_le",
        label: "eval-le",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_lt",
        label: "eval-lt",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_bool_eq",
        label: "eval-bool-eq",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_int_eq",
        label: "eval-int-eq",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_bool_ne",
        label: "eval-bool-ne",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "eval_int_ne",
        label: "eval-int-ne",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "and_true",
        label: "and-true",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "and_false",
        label: "and-false",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "or_true",
        label: "or-true",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "or_false",
        label: "or-false",
        prior_transport: PriorTransport::StructuredRule,
    },
    MigratedRuleRoute {
        item: "step",
        label: "step",
        prior_transport: PriorTransport::ConfigurationRule,
    },
    MigratedRuleRoute {
        item: "var",
        label: "var",
        prior_transport: PriorTransport::ConfigurationRule,
    },
    MigratedRuleRoute {
        item: "assign",
        label: "assign",
        prior_transport: PriorTransport::ConfigurationRule,
    },
    MigratedRuleRoute {
        item: "if_true",
        label: "if-true",
        prior_transport: PriorTransport::ConfigurationRule,
    },
    MigratedRuleRoute {
        item: "if_false",
        label: "if-false",
        prior_transport: PriorTransport::ConfigurationRule,
    },
    MigratedRuleRoute {
        item: "if_else",
        label: "if-else",
        prior_transport: PriorTransport::ConfigurationRule,
    },
    MigratedRuleRoute {
        item: "while",
        label: "while",
        prior_transport: PriorTransport::ConfigurationRule,
    },
    MigratedRuleRoute {
        item: "block",
        label: "block",
        prior_transport: PriorTransport::ConfigurationRule,
    },
    MigratedRuleRoute {
        item: "done",
        label: "done",
        prior_transport: PriorTransport::ConfigurationRule,
    },
];

fn is_prior(descriptor: &HostDescriptor) -> bool {
    descriptor
        .id
        .rust_module_path()
        .iter()
        .rev()
        .take(2)
        .map(String::as_str)
        .eq(["prior", "parity"])
}

fn is_readable_imp_rule(descriptor: &HostDescriptor) -> bool {
    descriptor.id.item_kind() == ItemKind::Rule
        && descriptor
            .id
            .rust_module_path()
            .last()
            .is_some_and(|module| module == "imp")
        && matches!(descriptor.payload, HostDescriptorPayload::HeadRule(_))
}

fn context() -> PackageContext {
    PackageContext::new(
        "KRS-IMP",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        "krs_imp_definition",
        Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"),
    )
    .unwrap()
}

fn collect_route(explicit: bool) -> krs_ir::DescriptorBundle {
    let descriptors = k::host_descriptors()
        .map(Result::unwrap)
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
        descriptors.into_iter().map(Ok),
        &k::builtin_registry(),
    )
    .unwrap()
}

fn readable_structured_route(object: &serde_json::Map<String, Json>) -> Option<MigratedRuleRoute> {
    if let Some(id) = object.get("id").and_then(Json::as_object)
        && id
            .get("module_path")
            .and_then(Json::as_array)
            .is_some_and(|module| module == &[Json::String("imp".into())])
        && let Some(item) = id.get("item_name").and_then(Json::as_str)
        && let Some(route) = MIGRATED_RULE_MAP.iter().copied().find(|route| {
            route.prior_transport == PriorTransport::StructuredRule
                && route.item == item.strip_prefix("r#").unwrap_or(item)
        })
    {
        return Some(route);
    }
    let emitted = object.get("label")?.get("emitted_name")?.as_str()?;
    MIGRATED_RULE_MAP.iter().copied().find(|route| {
        route.prior_transport == PriorTransport::StructuredRule && route.label == emitted
    })
}

/// Project a readable completed-head configuration rewrite back to the bare
/// term-rewrite boundary used by the preserved expression rule.
///
/// This is intentionally structural and fail-closed: it accepts exactly one
/// computation-cell clause, one omitted sibling, a K-sequence tail frame, and
/// one item on each side. Any future expansion that changes more than the
/// completion wrapper fails here instead of being normalized away.
fn project_completed_head_body(body: &Json, item: &str) -> Json {
    let body = body
        .as_object()
        .unwrap_or_else(|| panic!("{item} readable body is not an object"));
    assert_eq!(
        body.keys().map(String::as_str).collect::<BTreeSet<_>>(),
        BTreeSet::from(["clauses", "configuration", "omitted_siblings"]),
        "{item} readable completion body changed shape",
    );
    let omitted = body["omitted_siblings"].as_array().unwrap();
    assert_eq!(
        omitted.len(),
        1,
        "{item} must frame exactly the env sibling"
    );
    let clauses = body["clauses"].as_array().unwrap();
    assert_eq!(
        clauses.len(),
        1,
        "{item} must complete exactly one k-cell clause"
    );
    let clause = clauses[0].as_object().unwrap();
    assert_eq!(
        clause.keys().map(String::as_str).collect::<BTreeSet<_>>(),
        BTreeSet::from(["after", "before", "cell", "clause_kind", "frame"]),
        "{item} completed k-cell clause changed shape",
    );
    assert_eq!(
        clause["clause_kind"], "fixed",
        "{item} must complete the exactly-once k cell",
    );
    assert_eq!(
        clause["frame"],
        serde_json::json!({"frame_kind": "k_sequence_tail"}),
        "{item} must preserve exactly the implicit k tail",
    );
    let before = clause["before"].as_object().unwrap();
    assert_eq!(before["term_kind"], "k_sequence");
    let before_items = before["items"].as_array().unwrap();
    assert_eq!(
        before_items.len(),
        1,
        "{item} subject must contain one head item"
    );
    let after = clause["after"].as_object().unwrap();
    assert_eq!(after["post_kind"], "replace");
    let after_term = after["term"].as_object().unwrap();
    assert_eq!(after_term["term_kind"], "k_sequence");
    let after_items = after_term["items"].as_array().unwrap();
    assert_eq!(
        after_items.len(),
        1,
        "{item} result must contain one head item"
    );
    serde_json::json!({
        "term_kind": "rewrite",
        "sort": before["item_sort"].clone(),
        "from": before_items[0].clone(),
        "to": after_items[0].clone(),
    })
}

/// Remove only source identity and alpha-rename compiler-owned opaque IDs.
#[allow(clippy::too_many_lines)]
fn normalized(mut value: Json, explicit: bool) -> Json {
    fn frame_bindings(value: &Json, output: &mut BTreeSet<String>) {
        match value {
            Json::Object(object) => {
                if object.contains_key("frame_kind")
                    && let Some(binding) = object.get("binding").and_then(Json::as_str)
                {
                    output.insert(binding.to_owned());
                }
                for value in object.values() {
                    frame_bindings(value, output);
                }
            }
            Json::Array(values) => {
                for value in values {
                    frame_bindings(value, output);
                }
            }
            _ => {}
        }
    }

    fn sentence_order_key(value: &Json) -> String {
        fn scrub(value: &mut Json) {
            match value {
                Json::Object(object) => {
                    for child in object.values_mut() {
                        scrub(child);
                    }
                }
                Json::Array(values) => {
                    for child in values {
                        scrub(child);
                    }
                }
                Json::String(text)
                    if text.starts_with("sem.")
                        || text.starts_with("def.")
                        || text.starts_with("origin.") =>
                {
                    *text = "<opaque>".into();
                }
                _ => {}
            }
        }
        let mut key = value.clone();
        scrub(&mut key);
        key.to_string()
    }

    fn visit(value: &mut Json, explicit: bool) {
        match value {
            Json::Object(object) => {
                object.remove("origin");
                if let Some(Json::String(item_name)) = object.get_mut("item_name")
                    && let Some(identifier) = item_name.strip_prefix("r#")
                {
                    *item_name = identifier.to_owned();
                }
                if let Some(emitted_name) = object
                    .get("emitted_name")
                    .and_then(Json::as_str)
                    .map(str::to_owned)
                    && let Some(Json::String(id)) = object.get_mut("id")
                    && id.starts_with("rule:")
                {
                    *id = format!("rule.emitted.{emitted_name}");
                }
                let mut bindings = BTreeSet::new();
                if let Some(body) = object.get("body") {
                    frame_bindings(body, &mut bindings);
                }
                if let Some(Json::Array(variables)) = object.get_mut("variables") {
                    variables.retain(|variable| {
                        variable
                            .get("id")
                            .and_then(Json::as_str)
                            .is_none_or(|id| !bindings.contains(id))
                    });
                }
                if object.contains_key("frame_kind") {
                    // Readable completion owns anonymous frames; the explicit
                    // spelling names them only so `cells!` can reuse them.
                    object.remove("binding");
                }
                for value in object.values_mut() {
                    visit(value, explicit);
                }
                if !explicit
                    && let Some(route) = readable_structured_route(object)
                    && let Some(body) = object.get("body")
                {
                    let projected = project_completed_head_body(body, route.item);
                    object.insert("body".into(), projected);
                    // E2 deliberately adds labels to readable clauses. The
                    // Descriptor mapping above proves every such label; the
                    // genuinely prior bare rules are unlabeled at the common
                    // semantic payload boundary.
                    object.remove("label");
                }
                if object
                    .get("label")
                    .and_then(|label| label.get("emitted_name"))
                    .and_then(Json::as_str)
                    .is_some_and(|label| label.starts_with("krsRule_"))
                {
                    // Definition lowering assigns an internal source-derived
                    // symbol to some unlabeled sentences. It is not an
                    // authored K label; the Descriptor mapping above retains
                    // and compares every authored label separately.
                    object.remove("label");
                }
            }
            Json::Array(values) => {
                if explicit && values.len() == 2 && values[0] == "parity" && values[1] == "prior" {
                    *values = vec![Json::String("imp".into())];
                } else {
                    for value in &mut *values {
                        visit(value, explicit);
                    }
                    if values.iter().all(|value| {
                        value
                            .get("id")
                            .and_then(Json::as_object)
                            .is_some_and(|id| id.contains_key("item_kind"))
                    }) {
                        values.sort_by_cached_key(|value| value["id"].to_string());
                    } else if values
                        .iter()
                        .all(|value| value.get("sentence_kind").is_some())
                    {
                        // Module sentences are a semantic set. Order them by
                        // emitted/stable semantic identities before opaque-ID
                        // alpha-renaming, so route-specific source IDs cannot
                        // choose different alpha names by encounter order.
                        values.sort_by_cached_key(sentence_order_key);
                    }
                }
            }
            _ => {}
        }
    }

    fn rename_generated(value: &mut Json, generated: &mut BTreeMap<String, String>) {
        match value {
            Json::Object(object) => {
                for child in object.values_mut() {
                    rename_generated(child, generated);
                }
            }
            Json::Array(values) => {
                for child in values {
                    rename_generated(child, generated);
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

    fn sort_semantic_sets(value: &mut Json) {
        match value {
            Json::Object(object) => {
                for child in object.values_mut() {
                    sort_semantic_sets(child);
                }
            }
            Json::Array(values) => {
                for child in &mut *values {
                    sort_semantic_sets(child);
                }
                if values
                    .iter()
                    .all(|value| value.get("sentence_kind").is_some())
                {
                    values.sort_by_cached_key(Json::to_string);
                }
            }
            _ => {}
        }
    }

    visit(&mut value, explicit);
    rename_generated(&mut value, &mut BTreeMap::new());
    sort_semantic_sets(&mut value);
    value
}

fn first_difference<'a>(left: &'a Json, right: &'a Json, path: &str) -> Option<String> {
    match (left, right) {
        (Json::Object(left), Json::Object(right)) => {
            if left.keys().collect::<Vec<_>>() != right.keys().collect::<Vec<_>>() {
                return Some(format!(
                    "{path}: object keys differ ({:?} != {:?}); ids {:?} != {:?}; labels {:?} != {:?}",
                    left.keys().collect::<Vec<_>>(),
                    right.keys().collect::<Vec<_>>(),
                    left.get("id"),
                    right.get("id"),
                    left.get("label"),
                    right.get("label")
                ));
            }
            left.iter().find_map(|(key, value)| {
                first_difference(value, &right[key], &format!("{path}.{key}"))
            })
        }
        (Json::Array(left), Json::Array(right)) => {
            if left.len() != right.len() {
                return Some(format!(
                    "{path}: array lengths differ ({} != {}): {left:?} != {right:?}",
                    left.len(),
                    right.len()
                ));
            }
            left.iter()
                .zip(right)
                .enumerate()
                .find_map(|(index, (left, right))| {
                    first_difference(left, right, &format!("{path}[{index}]"))
                })
        }
        _ if left == right => None,
        _ => Some(format!("{path}: {left} != {right}")),
    }
}

/// Canonicalize the two equivalent K renderings of an anonymous cell frame.
///
/// Head rules use `...`; the explicit fixture has to name `tail @ ..` and
/// `rest @ ..` so that `cells!` can repeat them. This is deliberately scoped
/// to labeled rules, leaving declarations, claims, equations, side conditions,
/// and every non-frame fragment byte-exact.
fn normalized_emitted_k(source: &str) -> String {
    let mut in_labeled_rule = false;
    source
        .lines()
        .map(|line| {
            let trimmed = line.trim_start();
            if trimmed.starts_with("rule [") {
                in_labeled_rule = true;
            } else if (!trimmed.is_empty() && !line.starts_with(' '))
                || trimmed.starts_with("claim [")
                || trimmed.starts_with("rule ")
            {
                in_labeled_rule = false;
            }

            if !in_labeled_rule {
                return line.to_owned();
            }

            if let Some(body) = line
                .strip_prefix("    <k> ")
                .and_then(|line| line.strip_suffix(" </k>"))
                && let Some((before, after)) = body.split_once(" => ")
                && let Some((before, frame)) = before.rsplit_once(" ~> ")
                && let Some(after) = after.strip_suffix(&format!(" ~> {frame}"))
            {
                return format!("    <k> {before} => {after} ... </k>");
            }

            // The explicit configuration route can render its named
            // `tail @ ..` frame only on the result side when the subject's
            // frame is implicit in the cell pattern. Keep this exact: the
            // generated K variable is the readable spelling of `tail`, at sort K.
            if let Some(body) = line
                .strip_prefix("    <k> ")
                .and_then(|line| line.strip_suffix(" </k>"))
                && let Some((before, after)) = body.split_once(" => ")
                && let Some(after) = after.strip_suffix(" ~> Tail:K")
            {
                return format!("    <k> {before} => {after} ... </k>");
            }

            if let Some(body) = line
                .strip_prefix("    <env> ")
                .and_then(|line| line.strip_suffix(" </env>"))
                && !body.contains(" => ")
                && let Some((prefix, frame)) = body.rsplit_once(' ')
                && frame.starts_with(|character: char| {
                    character.is_ascii_uppercase() || character == '_'
                })
                && frame.ends_with(":Map")
            {
                return format!("    <env> {prefix} ... </env>");
            }

            line.to_owned()
        })
        .collect::<Vec<_>>()
        .join("\n")
        + "\n"
}

fn emitted_rule_blocks(source: &str) -> (Vec<String>, String) {
    fn sentence_start(line: &str) -> bool {
        let Some(value) = line.strip_prefix("  ") else {
            return false;
        };
        !value.starts_with(' ')
            && [
                "rule ",
                "claim ",
                "syntax ",
                "configuration",
                "context alias ",
            ]
            .iter()
            .any(|prefix| value.starts_with(prefix))
    }

    let lines = source.lines().collect::<Vec<_>>();
    let mut rules = Vec::new();
    let mut retained = Vec::new();
    let mut index = 0;
    while index < lines.len() {
        if lines[index].starts_with("  rule ") {
            let start = index;
            index += 1;
            while index < lines.len() && !sentence_start(lines[index]) {
                index += 1;
            }
            rules.push(
                lines[start..index]
                    .iter()
                    .copied()
                    .filter(|line| !line.is_empty())
                    .collect::<Vec<_>>()
                    .join("\n"),
            );
        } else {
            if !lines[index].is_empty() {
                retained.push(lines[index]);
            }
            index += 1;
        }
    }
    (rules, retained.join("\n"))
}

fn labeled_rule<'a>(blocks: &'a [String], label: &str) -> &'a str {
    let prefix = format!("  rule [{label}]:");
    let matches = blocks
        .iter()
        .filter(|block| block.lines().next() == Some(prefix.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "expected one emitted [{label}] rule");
    matches[0]
}

fn completed_expression_body(block: &str, label: &str) -> String {
    let lines = block.lines().collect::<Vec<_>>();
    assert_eq!(
        lines.len(),
        2,
        "[{label}] must contain exactly one k-cell line"
    );
    let body = lines[1]
        .strip_prefix("    <k> ")
        .and_then(|line| line.strip_suffix(" ... </k>"))
        .unwrap_or_else(|| panic!("[{label}] changed completed-head K shape"));
    assert!(body.contains(" => "), "[{label}] is not a rewrite");
    body.to_owned()
}

fn prior_expression_block<'a>(blocks: &'a [String], body: &str, label: &str) -> &'a str {
    let prefix = format!("  rule {body} [label(krsRule_");
    let matches = blocks
        .iter()
        .filter(|block| {
            !block.contains('\n') && block.starts_with(&prefix) && block.ends_with(")]")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        matches.len(),
        1,
        "prior bare expression rule for [{label}] is absent or ambiguous",
    );
    matches[0]
}

fn assert_emitted_k_mapping(readable: &str, prior: &str) {
    let readable = normalized_emitted_k(readable);
    let prior = normalized_emitted_k(prior);
    let (readable_rules, readable_non_rules) = emitted_rule_blocks(&readable);
    let (prior_rules, prior_non_rules) = emitted_rule_blocks(&prior);
    assert_eq!(
        readable_non_rules, prior_non_rules,
        "non-rule emitted K differs",
    );

    let mut readable_migrated = BTreeSet::new();
    let mut prior_migrated = BTreeSet::new();
    for route in MIGRATED_RULE_MAP {
        let readable_block = labeled_rule(&readable_rules, route.label);
        readable_migrated.insert(readable_block.to_owned());
        match route.prior_transport {
            PriorTransport::StructuredRule => {
                let body = completed_expression_body(readable_block, route.label);
                let prior_block = prior_expression_block(&prior_rules, &body, route.label);
                prior_migrated.insert(prior_block.to_owned());
            }
            PriorTransport::ConfigurationRule => {
                let prior_block = labeled_rule(&prior_rules, route.label);
                assert_eq!(
                    readable_block, prior_block,
                    "stateful emitted K differs for [{}]",
                    route.label,
                );
                prior_migrated.insert(prior_block.to_owned());
            }
        }
    }

    let remaining = |blocks: &[String], migrated: &BTreeSet<String>| {
        blocks
            .iter()
            .filter(|block| !migrated.contains(*block))
            .cloned()
            .collect::<BTreeSet<_>>()
    };
    assert_eq!(
        remaining(&readable_rules, &readable_migrated),
        remaining(&prior_rules, &prior_migrated),
        "unrelated emitted K rules differ",
    );
}

fn prior_transport(descriptor: &krs_ir::Descriptor) -> Option<PriorTransport> {
    match descriptor.payload() {
        krs_ir::DescriptorPayload::StructuredRule(_) => Some(PriorTransport::StructuredRule),
        krs_ir::DescriptorPayload::ConfigurationRule(_) => Some(PriorTransport::ConfigurationRule),
        _ => None,
    }
}

fn rule_label(descriptor: &krs_ir::Descriptor) -> Option<&str> {
    match descriptor.payload() {
        krs_ir::DescriptorPayload::StructuredRule(rule) => rule.label.as_ref(),
        krs_ir::DescriptorPayload::ConfigurationRule(rule) => rule.label.as_ref(),
        krs_ir::DescriptorPayload::HeadRule(rule) => rule.label.as_ref(),
        _ => None,
    }
    .map(|label| label.name.as_str())
}

fn mapped_descriptors<'a>(
    bundle: &'a krs_ir::DescriptorBundle,
    module: &[&str],
) -> BTreeMap<&'a str, &'a krs_ir::Descriptor> {
    bundle
        .descriptors()
        .iter()
        .filter(|descriptor| {
            descriptor.id().item_kind() == ItemKind::Rule
                && descriptor
                    .id()
                    .module_path()
                    .iter()
                    .map(String::as_str)
                    .eq(module.iter().copied())
        })
        // Raw identifiers are a Rust spelling escape, not object-language
        // identity. The readable macro canonicalizes it earlier than the
        // explicit attribute route, so compare the unraw item name here.
        .map(|descriptor| {
            (
                descriptor
                    .id()
                    .item_name()
                    .strip_prefix("r#")
                    .unwrap_or_else(|| descriptor.id().item_name()),
                descriptor,
            )
        })
        .collect()
}

fn assert_descriptor_transport_mapping(
    readable_bundle: &krs_ir::DescriptorBundle,
    prior_bundle: &krs_ir::DescriptorBundle,
) {
    let readable = mapped_descriptors(readable_bundle, &["imp"]);
    let prior = mapped_descriptors(prior_bundle, &["parity", "prior"]);
    assert_eq!(
        (readable.len(), prior.len()),
        (MIGRATED_RULES, MIGRATED_RULES)
    );

    let expected_items = MIGRATED_RULE_MAP
        .iter()
        .map(|route| route.item)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        readable.keys().copied().collect::<BTreeSet<_>>(),
        expected_items
    );
    assert_eq!(
        prior.keys().copied().collect::<BTreeSet<_>>(),
        expected_items
    );

    for route in MIGRATED_RULE_MAP {
        let readable = readable[route.item];
        let prior = prior[route.item];
        assert!(
            matches!(readable.payload(), krs_ir::DescriptorPayload::HeadRule(_)),
            "readable {} must use the HeadRule transport",
            route.item,
        );
        assert_eq!(
            prior_transport(prior),
            Some(route.prior_transport),
            "prior {} changed transport family",
            route.item,
        );
        assert_eq!(
            rule_label(readable),
            Some(route.label),
            "{} readable label differs",
            route.item,
        );
        let expected_prior_label = match route.prior_transport {
            // The preserved bare-rule form derives its emitted label from the
            // stable item identity during lowering; it has no authored label
            // payload at the Descriptor transport boundary.
            PriorTransport::StructuredRule => None,
            PriorTransport::ConfigurationRule => Some(route.label),
        };
        assert_eq!(
            rule_label(prior),
            expected_prior_label,
            "{} prior label transport differs",
            route.item,
        );
        assert_eq!(
            readable.id().disambiguator(),
            prior.id().disambiguator(),
            "{} stable disambiguator differs",
            route.item,
        );
        assert_eq!(
            readable_bundle
                .declaration(readable.id())
                .map(|value| &value.visibility),
            prior_bundle
                .declaration(prior.id())
                .map(|value| &value.visibility),
            "{} declaration visibility differs",
            route.item,
        );
    }
}

fn unrelated_descriptor_json(bundle: &krs_ir::DescriptorBundle) -> Json {
    let mut value: Json = serde_json::from_str(&bundle.to_canonical_json().unwrap()).unwrap();
    let object = value.as_object_mut().unwrap();
    for field in ["descriptors", "declarations"] {
        object[field].as_array_mut().unwrap().retain(|entry| {
            let id = &entry["id"];
            let module = id["module_path"].as_array().unwrap();
            let item_kind = id["item_kind"].as_str();
            item_kind != Some("rule")
                || (module != &[Json::String("imp".into())]
                    && module != &[Json::String("parity".into()), Json::String("prior".into())])
        });
    }
    value
}

#[test]
fn readable_and_prior_explicit_routes_are_semantically_identical() {
    let readable_bundle = collect_route(false);
    let explicit_bundle = collect_route(true);

    // Descriptor boundary: assert the complete, payload-family-aware mapping
    // for every migrated rule, then require every unrelated descriptor and its
    // exact declaration metadata to remain byte-identical.
    assert_descriptor_transport_mapping(&readable_bundle, &explicit_bundle);
    assert_eq!(
        unrelated_descriptor_json(&readable_bundle),
        unrelated_descriptor_json(&explicit_bundle),
    );

    let readable_semantic = lower_descriptor_bundle(&readable_bundle).unwrap();
    let explicit_semantic = lower_descriptor_bundle(&explicit_bundle).unwrap();
    let readable_semantic_json = normalized(
        serde_json::from_str(&readable_semantic.to_canonical_json().unwrap()).unwrap(),
        false,
    );
    let explicit_semantic_json = normalized(
        serde_json::from_str(&explicit_semantic.to_canonical_json().unwrap()).unwrap(),
        true,
    );
    if let Some(difference) =
        first_difference(&readable_semantic_json, &explicit_semantic_json, "semantic")
    {
        panic!("Semantic IR differs after the documented source normalization: {difference}");
    }

    let readable_definition = lower_semantic_theory(&readable_semantic).unwrap();
    let explicit_definition = lower_semantic_theory(&explicit_semantic).unwrap();
    let readable_definition_json = normalized(
        serde_json::from_str(
            &readable_definition
                .definition()
                .to_canonical_json()
                .unwrap(),
        )
        .unwrap(),
        false,
    );
    let explicit_definition_json = normalized(
        serde_json::from_str(
            &explicit_definition
                .definition()
                .to_canonical_json()
                .unwrap(),
        )
        .unwrap(),
        true,
    );
    if let Some(difference) = first_difference(
        &readable_definition_json,
        &explicit_definition_json,
        "definition",
    ) {
        panic!("Definition IR differs after the documented source normalization: {difference}");
    }

    let readable_k = emit_k(&readable_definition).unwrap();
    let explicit_k = emit_k(&explicit_definition).unwrap();
    assert_emitted_k_mapping(readable_k.source(), explicit_k.source());
    for production_doc in [
        "// Dangling else: `avoid` makes the parser prefer the `IfThen` reading.",
        "// Deliberately not strict: the `[while]` rule unfolds the loop instead.",
    ] {
        assert_eq!(
            readable_k.source().matches(production_doc).count(),
            1,
            "production rustdoc did not survive into emitted K",
        );
    }
    assert!(
        !readable_k
            .source()
            .contains("Select the true branch of an evaluated conditional"),
        "rule rustdoc policy is still open and must not leak into emitted K",
    );
}

#[test]
fn readable_overlap_is_rejected_after_sort_inference() {
    let bundle = collect_route(false);
    let original = bundle
        .descriptors()
        .iter()
        .find(|descriptor| {
            descriptor.id().item_name() == "eval_neg"
                && matches!(descriptor.payload(), DescriptorPayload::HeadRule(_))
        })
        .expect("readable eval_neg descriptor");
    let duplicate_id = StableItemId::new(
        original.id().package().clone(),
        original.id().module_path().iter().cloned(),
        "eval_neg_overlap",
        original.id().item_kind(),
        original.id().disambiguator(),
    )
    .unwrap();
    let duplicate = krs_ir::Descriptor::new(
        duplicate_id,
        original.cfg().clone(),
        original.provenance().clone(),
        original.payload().clone(),
    )
    .unwrap();
    let mut descriptors = bundle.descriptors().to_vec();
    descriptors.push(duplicate.clone());
    let mut declarations = bundle.declarations().to_vec();
    declarations.push(DescriptorDeclaration::new(
        duplicate.id().clone(),
        RustVisibility::Inherited,
        None,
    ));
    let adversarial = DescriptorBundle::with_declarations(descriptors, declarations).unwrap();
    let error = lower_descriptor_bundle(&adversarial).unwrap_err();
    assert!(
        matches!(error, DescriptorLoweringError::OverlappingRules { .. }),
        "unexpected diagnostic: {error}"
    );
}

#[test]
#[allow(clippy::too_many_lines)] // One end-to-end deterministic expansion contract.
fn readable_expansion_is_complete_deterministic_reference_rust() {
    fn attribute_is(attribute: &syn::Attribute, name: &str) -> bool {
        attribute
            .path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == name)
    }

    fn attribute_text(attribute: &syn::Attribute) -> String {
        attribute.meta.to_token_stream().to_string()
    }

    fn rustdocs(attributes: &[syn::Attribute]) -> Vec<String> {
        attributes
            .iter()
            .filter_map(|attribute| {
                if !attribute.path().is_ident("doc") {
                    return None;
                }
                let syn::Meta::NameValue(meta) = &attribute.meta else {
                    return None;
                };
                let syn::Expr::Lit(expression) = &meta.value else {
                    return None;
                };
                let syn::Lit::Str(literal) = &expression.lit else {
                    return None;
                };
                let value = literal.value();
                Some(value.strip_prefix(' ').unwrap_or(&value).to_owned())
            })
            .collect()
    }

    let bundle = collect_route(false);
    let semantic = lower_descriptor_bundle(&bundle).unwrap();
    let package = bundle
        .descriptors()
        .iter()
        .find(|descriptor| matches!(descriptor.payload(), krs_ir::DescriptorPayload::HeadRule(_)))
        .map(|descriptor| descriptor.id().package().clone())
        .expect("the readable route has head rules");
    let source = include_str!("imp.rs");
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let facade = FacadeAliases::from_manifest(&manifest)
        .expect("the IMP manifest names the facade")
        .scope();
    let expanded = expand_reference_source(
        source,
        &facade,
        &package,
        &["imp".into()],
        &bundle,
        &semantic,
    )
    .expect("readable IMP projects to reference Rust");
    let repeated = expand_reference_source(
        source,
        &facade,
        &package,
        &["imp".into()],
        &bundle,
        &semantic,
    )
    .expect("repeated readable IMP projection succeeds");
    assert_eq!(
        expanded, repeated,
        "reference projection is not deterministic"
    );
    assert_eq!(
        expanded,
        include_str!("../../goldens/imp.expanded.rs"),
        "live IMP expansion differs from its reviewed golden",
    );

    let file = syn::parse_file(&expanded).expect("expanded output is Rust syntax");
    let item_macros = file
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Macro(item) => Some(item),
            _ => None,
        })
        .collect::<Vec<_>>();
    for removed in ["sorts", "rules"] {
        assert_eq!(
            item_macros
                .iter()
                .filter(|item| {
                    item.mac
                        .path
                        .segments
                        .last()
                        .is_some_and(|segment| segment.ident == removed)
                })
                .count(),
            0,
            "layer-1 `{removed}!` survived reference projection",
        );
    }

    let sort_traits = file
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Trait(item) => Some((item.ident.to_string(), item)),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        sort_traits.keys().map(String::as_str).collect::<Vec<_>>(),
        ["ExprSort", "StmtSort", "ValueSort"],
    );
    for (name, sort_attribute, bracket_attribute, supertraits) in [
        (
            "ExprSort",
            "k :: sort (alias = Expr)",
            Some("k :: bracket (\"({value})\")"),
            "",
        ),
        (
            "ValueSort",
            "k :: sort (alias = Value , parents = [Expr , k :: KResult])",
            None,
            "ExprSort + k :: KResultSort",
        ),
        ("StmtSort", "k :: sort (alias = Stmt)", None, ""),
    ] {
        let item = sort_traits[name];
        let sort_attributes = item
            .attrs
            .iter()
            .filter(|attribute| attribute_is(attribute, "sort"))
            .collect::<Vec<_>>();
        assert_eq!(sort_attributes.len(), 1, "sort carrier for {name}");
        assert_eq!(attribute_text(sort_attributes[0]), sort_attribute);
        let brackets = item
            .attrs
            .iter()
            .filter(|attribute| attribute_is(attribute, "bracket"))
            .map(attribute_text)
            .collect::<Vec<_>>();
        assert_eq!(brackets.as_slice(), bracket_attribute.as_slice());
        assert_eq!(item.supertraits.to_token_stream().to_string(), supertraits);
        assert!(matches!(item.vis, syn::Visibility::Public(_)));
    }

    let aliases = file
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Type(item) => Some((item.ident.to_string(), item)),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(aliases.len(), 3);
    for (name, ty) in [
        ("Expr", "k :: Term < dyn ExprSort >"),
        ("Value", "k :: Term < dyn ValueSort >"),
        ("Stmt", "k :: Term < dyn StmtSort >"),
    ] {
        let alias = aliases[name];
        assert_eq!(alias.ty.to_token_stream().to_string(), ty);
        assert!(matches!(alias.vis, syn::Visibility::Public(_)));
    }

    let trait_impls = file
        .items
        .iter()
        .filter_map(|item| {
            let syn::Item::Impl(item) = item else {
                return None;
            };
            let (_, trait_path, _) = item.trait_.as_ref()?;
            Some((
                format!(
                    "{} for {}",
                    trait_path.to_token_stream(),
                    item.self_ty.to_token_stream()
                ),
                item,
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(trait_impls.len(), 5);
    for (signature, subsort_attribute) in [
        ("ExprSort for Id", Some("k :: subsort (sort = Expr)")),
        ("ValueSort for Int", Some("k :: subsort (sort = Value)")),
        ("ExprSort for Int", None),
        ("ValueSort for Bool", Some("k :: subsort (sort = Value)")),
        ("ExprSort for Bool", None),
    ] {
        let item = trait_impls
            .iter()
            .find_map(|(actual, item)| (actual == signature).then_some(*item))
            .unwrap_or_else(|| panic!("missing projected impl `{signature}`"));
        let attributes = item
            .attrs
            .iter()
            .filter(|attribute| attribute_is(attribute, "subsort"))
            .map(attribute_text)
            .collect::<Vec<_>>();
        assert_eq!(attributes.as_slice(), subsort_attribute.as_slice());
    }
    assert_eq!(
        trait_impls
            .iter()
            .filter(|(_, item)| {
                !item
                    .attrs
                    .iter()
                    .any(|attribute| attribute_is(attribute, "subsort"))
            })
            .count(),
        2,
    );

    let families = file
        .items
        .iter()
        .filter_map(|item| {
            let syn::Item::Enum(item) = item else {
                return None;
            };
            item.attrs
                .iter()
                .any(|attribute| attribute_is(attribute, "constructors"))
                .then(|| (item.ident.to_string(), item))
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(families.len(), 2);
    for (name, constructor_attribute) in [
        ("Op", "k :: constructors (sort = Expr , reference)"),
        ("StmtSyntax", "k :: constructors (sort = Stmt , reference)"),
    ] {
        let family = families[name];
        let constructors = family
            .attrs
            .iter()
            .filter(|attribute| attribute_is(attribute, "constructors"))
            .map(attribute_text)
            .collect::<Vec<_>>();
        assert_eq!(constructors, [constructor_attribute]);
        assert!(
            !family
                .attrs
                .iter()
                .any(|attribute| attribute_is(attribute, "precedence")),
            "enum-level readable precedence survived on {name}",
        );
    }

    let mut production_count = 0;
    let mut term_field_count = 0;
    let mut strictness_count = 0;
    let mut avoid = Vec::new();
    let mut production_docs = BTreeMap::new();
    for family in families.values() {
        for variant in &family.variants {
            production_count += 1;
            let name = variant.ident.to_string();
            let field_types = variant
                .fields
                .iter()
                .map(|field| field.ty.to_token_stream().to_string())
                .collect::<Vec<_>>();
            term_field_count += field_types.len();
            let expected_fields: &[&str] = if family.ident == "Op" {
                match name.as_str() {
                    "Neg" | "Not" => &["k :: Term < dyn ExprSort >"],
                    _ => &["k :: Term < dyn ExprSort >", "k :: Term < dyn ExprSort >"],
                }
            } else {
                match name.as_str() {
                    "Assign" => &[
                        "k :: Term < k :: builtin :: Id >",
                        "k :: Term < dyn ExprSort >",
                    ],
                    "IfThenElse" => &[
                        "k :: Term < dyn ExprSort >",
                        "k :: Term < dyn StmtSort >",
                        "k :: Term < dyn StmtSort >",
                    ],
                    "IfThen" | "While" => {
                        &["k :: Term < dyn ExprSort >", "k :: Term < dyn StmtSort >"]
                    }
                    "Block" => &["k :: Term < dyn StmtSort >"],
                    "EmptyBlock" => &[],
                    "Sequence" => &["k :: Term < dyn StmtSort >", "k :: Term < dyn StmtSort >"],
                    _ => panic!("unexpected StmtSyntax variant `{name}`"),
                }
            };
            assert_eq!(
                field_types.iter().map(String::as_str).collect::<Vec<_>>(),
                expected_fields,
                "projected fields for {name}",
            );

            let syntax = variant
                .attrs
                .iter()
                .filter(|attribute| attribute_is(attribute, "syntax"))
                .collect::<Vec<_>>();
            assert_eq!(syntax.len(), 1, "syntax carrier for {name}");
            let syntax = attribute_text(syntax[0]);
            let group = match name.as_str() {
                "Neg" | "Not" => "op_tier0",
                "Mul" | "Div" => "op_tier1",
                "Add" | "Sub" => "op_tier2",
                "Ge" | "Gt" | "Le" | "Lt" => "op_tier3",
                "Eq" | "Ne" => "op_tier4",
                "And" => "op_tier5",
                "Or" => "op_tier6",
                "Sequence" => "seq_stmt",
                _ => "stmt",
            };
            assert!(syntax.contains(&format!("group = \"{group}\"")));
            assert!(syntax.contains("format ="), "missing format for {name}");
            if syntax.contains("avoid =") {
                assert!(syntax.contains("avoid = true"));
                avoid.push(name.clone());
            }
            let docs = rustdocs(&variant.attrs);
            if !docs.is_empty() {
                production_docs.insert(name.clone(), docs);
            }

            let strictness = variant
                .attrs
                .iter()
                .filter(|attribute| {
                    attribute_is(attribute, "strict") || attribute_is(attribute, "seqstrict")
                })
                .collect::<Vec<_>>();
            let expected_strictness = match name.as_str() {
                "Neg" | "Not" | "Assign" => Some(("strict", "value")),
                "Mul" | "Div" | "Add" | "Sub" | "Ge" | "Gt" | "Le" | "Lt" | "Eq" | "Ne" => {
                    Some(("seqstrict", "lhs , rhs"))
                }
                "And" | "Or" => Some(("strict", "lhs")),
                "IfThenElse" => Some(("strict", "condition")),
                _ => None,
            };
            if let Some((kind, sequence)) = expected_strictness {
                strictness_count += 1;
                assert_eq!(strictness.len(), 1, "strictness carrier for {name}");
                assert_eq!(
                    attribute_text(strictness[0]),
                    format!("k :: {kind} (sequence = [{sequence}] , result = k :: KResult)"),
                );
            } else {
                assert!(strictness.is_empty(), "unexpected strictness on {name}");
            }
        }
    }
    assert_eq!(production_count, 21);
    assert_eq!(term_field_count, 38);
    assert_eq!(strictness_count, 16);
    assert_eq!(avoid, ["IfThenElse"]);
    assert_eq!(
        production_docs,
        BTreeMap::from([
            (
                "IfThenElse".to_owned(),
                vec![
                    "Dangling else: `avoid` makes the parser prefer the `IfThen` reading."
                        .to_owned()
                ],
            ),
            (
                "While".to_owned(),
                vec![
                    "Deliberately not strict: the `[while]` rule unfolds the loop instead."
                        .to_owned()
                ],
            ),
        ]),
    );

    let precedence = item_macros
        .iter()
        .filter(|item| {
            item.mac
                .path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "precedence")
        })
        .map(|item| item.mac.tokens.to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        precedence,
        BTreeSet::from([
            "for Op ; op_tier0 > op_tier1 > op_tier2 > op_tier3 > op_tier4 > op_tier5 > op_tier6"
                .to_owned(),
            "for StmtSyntax ; stmt > seq_stmt".to_owned(),
        ]),
    );
    let associativity = item_macros
        .iter()
        .filter(|item| {
            item.mac
                .path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "associativity")
        })
        .map(|item| item.mac.tokens.to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        associativity,
        BTreeSet::from([
            "for Op ; left : op_tier1 ; left : op_tier2 ; left : op_tier3 ; left : op_tier4 ; left : op_tier5 ; left : op_tier6 ;"
                .to_owned(),
            "for StmtSyntax ; right : seq_stmt ;".to_owned(),
        ]),
    );
    let associativity = associativity.into_iter().collect::<Vec<_>>().join("\n");
    assert!(!associativity.contains("non_associative"));

    let machine = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Struct(item) if item.ident == "Machine" => Some(item),
            _ => None,
        })
        .expect("expanded output retains Machine");
    assert_eq!(
        rustdocs(&machine.attrs),
        ["The oracle's fixed two-cell calculation state."]
    );
    assert_eq!(
        rustdocs(&machine.fields.iter().next().unwrap().attrs),
        ["K's computation cell: the continuation, head-first."]
    );
    assert_eq!(
        rustdocs(&machine.fields.iter().nth(1).unwrap().attrs),
        Vec::<String>::new()
    );
    let machine = machine.to_token_stream().to_string();
    assert!(machine.contains("k :: configuration :: KCell < KSequence >"));
    assert!(machine.contains("k :: configuration :: Cell < Map < Id , Value > >"));
    assert!(expanded.contains("#[k::config_var(name = \"PGM\", main)]"));
    assert!(expanded.contains("#[k::config_var(name = \"ENV\")]"));
    assert!(expanded.contains("k: k::configuration::KCell::new(k::k![pgm])"));
    assert!(expanded.contains("env: k::configuration::Cell::new(env)"));
    assert_eq!(
        expanded,
        include_str!("../../expanded-definition/src/imp.rs"),
        "strict replacement crate must compile the reviewed golden itself",
    );

    let rules = file
        .items
        .iter()
        .filter_map(|item| {
            let syn::Item::Fn(function) = item else {
                return None;
            };
            function
                .attrs
                .iter()
                .any(|attribute| {
                    attribute
                        .path()
                        .segments
                        .last()
                        .is_some_and(|part| part.ident == "rule")
                })
                .then(|| {
                    (
                        function.sig.ident.unraw().to_string(),
                        function.to_token_stream().to_string(),
                    )
                })
        })
        .collect::<BTreeMap<_, _>>();
    let expected = MIGRATED_RULE_MAP
        .iter()
        .map(|route| route.item.to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(rules.len(), MIGRATED_RULES);
    assert_eq!(rules.keys().cloned().collect::<BTreeSet<_>>(), expected);

    let rule_docs = file
        .items
        .iter()
        .filter_map(|item| {
            let syn::Item::Fn(function) = item else {
                return None;
            };
            let docs = rustdocs(&function.attrs);
            (!docs.is_empty()).then(|| (function.sig.ident.unraw().to_string(), docs))
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        rule_docs,
        BTreeMap::from([
            (
                "assign".to_owned(),
                vec!["Consume a value assignment and update the environment map.".to_owned()],
            ),
            (
                "block".to_owned(),
                vec!["Expose a nonempty block body followed by an empty block.".to_owned()],
            ),
            (
                "done".to_owned(),
                vec!["Remove an empty block from the computation cell.".to_owned()],
            ),
            (
                "if_else".to_owned(),
                vec!["Normalize the no-else form with an explicit empty branch.".to_owned()],
            ),
            (
                "if_false".to_owned(),
                vec!["Select the false branch of an evaluated conditional.".to_owned()],
            ),
            (
                "if_true".to_owned(),
                vec!["Select the true branch of an evaluated conditional.".to_owned()],
            ),
            (
                "step".to_owned(),
                vec!["Expose the right-associated statement pair as K sequencing.".to_owned()],
            ),
            (
                "var".to_owned(),
                vec!["Replace an identifier at the head of `k` with its mapped value.".to_owned()],
            ),
            (
                "while".to_owned(),
                vec!["Unfold one loop test without making the constructor strict.".to_owned()],
            ),
        ]),
    );

    let eval_neg = &rules["eval_neg"];
    assert!(eval_neg.contains("KCell (crate :: imp :: Op :: Neg (value) , tail @ ..)"));
    assert!(eval_neg.contains("KCell (k :: builtin :: int :: sub (0 , value) , .. tail)"));
    assert!(
        !eval_neg.contains("env :"),
        "ordinary completion must frame env"
    );

    let step = &rules["step"];
    assert!(
        step.contains("KCell (s1 , s2 , .. tail)"),
        "splice result was not expanded"
    );
    let done = &rules["done"];
    assert!(
        done.contains("KCell (.. tail)"),
        "erase result was not expanded"
    );

    let var = &rules["var"];
    assert!(var.contains("Cell (map ! [name -> value , rest0 @ ..])"));
    assert_eq!(
        var.matches("env :").count(),
        1,
        "map reads must be preserved by the configuration frame",
    );
    assert!(var.contains(".. state"));

    let assign = &rules["assign"];
    assert_eq!(assign.matches("env :").count(), 2);
    assert!(assign.contains("Cell (k :: builtin :: map :: update (e , name , value))"));
}
