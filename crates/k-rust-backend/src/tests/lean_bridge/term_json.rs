//! The JSON form of a `Term` as the Lean term model `KRust.TermAttributes.Term` holds it
//! (`lean/KRustBridge/Json.lean` decodes it). The encoding covers every field of `TermKind`
//! (term.rs:227-259) that the model keeps, so that the model's equality is Rust's `Eq for Term`:
//! the sort arguments of an application, the sort of a variable, and the definition of a
//! collection are all sent.
//!
//! The model keeps sorts, names, domain values, collection definitions and the symbol fields it
//! does not name as strings, and assumes only that the Rust values map to them injectively. The
//! renderings here are injective:
//! - a sort is `"name"{arg,…}` for an application and `"name"` for a variable, each name as a
//!   JSON string literal, so that no name can imitate the punctuation;
//! - a domain value's `KoreString` bytes are lower-case hex, because they need not be UTF-8;
//! - a collection definition and the symbol fields in the model's `other` are their derived
//!   `Debug` text, which quotes and escapes every string.
//!
//! Symbols and their attributes are destructured without `..`, so that a new Rust field
//! does not compile until it is placed in the encoding.

use serde_json::{Value, json};

use crate::term::{
    FunctionType, Sort, Symbol, SymbolAttributes, SymbolType, Term, TermKind, Variable,
    VariableKind,
};

fn quoted(name: &str) -> String {
    Value::from(name).to_string()
}

pub(super) fn sort_text(sort: &Sort) -> String {
    match sort {
        Sort::Variable(name) => quoted(name),
        Sort::Application { name, arguments } => format!(
            "{}{{{}}}",
            quoted(name),
            arguments
                .iter()
                .map(sort_text)
                .collect::<Vec<_>>()
                .join(",")
        ),
    }
}

fn sorts_json(sorts: &[Sort]) -> Value {
    Value::Array(sorts.iter().map(|sort| sort_text(sort).into()).collect())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// The model's `Sym` (lean/KRust/TermAttributes.lean): the fields the walks read, and every other
/// field of `Symbol` and `SymbolAttributes` (term.rs:128-172) in `other`.
fn symbol_json(symbol: &Symbol) -> Value {
    let Symbol {
        name,
        sort_variables,
        argument_sorts,
        result_sort,
        attributes,
    } = symbol;
    let SymbolAttributes {
        symbol_type,
        anywhere,
        declared_function,
        binder,
        injective,
        associative,
        idempotent,
        macro_or_alias,
        has_evaluators,
        smt,
        hook,
        collection,
    } = attributes;
    let other = format!(
        "{:?}",
        (
            sort_variables,
            argument_sorts,
            result_sort,
            binder,
            associative,
            idempotent,
            has_evaluators,
            smt,
            hook,
            collection,
        )
    );
    json!({
        "name": name.as_ref(),
        "type": match symbol_type {
            SymbolType::Constructor => "constructor",
            SymbolType::Function(FunctionType::Partial) => "partial",
            SymbolType::Function(FunctionType::Total) => "total",
        },
        "anywhere": anywhere,
        "declaredFunction": declared_function,
        "injective": injective,
        "macroOrAlias": macro_or_alias,
        "other": other,
    })
}

pub(super) fn terms_json<'a>(terms: impl IntoIterator<Item = &'a Term>) -> Value {
    Value::Array(terms.into_iter().map(term_json).collect())
}

pub(super) fn term_json(term: &Term) -> Value {
    match term.kind() {
        TermKind::And(left, right) => json!({ "and": [term_json(left), term_json(right)] }),
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => json!({ "app": {
            "symbol": symbol_json(symbol),
            "sorts": sorts_json(sort_arguments),
            "args": terms_json(arguments),
        }}),
        TermKind::DomainValue { sort, value } => {
            json!({ "dv": { "sort": sort_text(sort), "value": hex(value.as_bytes()) } })
        }
        TermKind::Variable(Variable { kind, sort, name }) => json!({ "var": {
            "kind": match kind {
                VariableKind::Element => "element",
                VariableKind::Set => "set",
            },
            "sort": sort_text(sort),
            "name": name.as_ref(),
        }}),
        TermKind::Injection {
            source,
            target,
            term,
        } => json!({ "inj": {
            "source": sort_text(source),
            "target": sort_text(target),
            "term": term_json(term),
        }}),
        TermKind::Map {
            definition,
            entries,
            rest,
        } => json!({ "map": {
            "definition": format!("{definition:?}"),
            "entries": entries
                .iter()
                .map(|(key, value)| json!([term_json(key), term_json(value)]))
                .collect::<Vec<_>>(),
            "rest": rest.as_ref().map_or(Value::Null, term_json),
        }}),
        TermKind::List {
            definition,
            heads,
            rest,
        } => json!({ "list": {
            "definition": format!("{definition:?}"),
            "heads": terms_json(heads),
            "rest": rest.as_ref().map_or(Value::Null, |(middle, tails)| json!({
                "middle": term_json(middle),
                "tails": terms_json(tails),
            })),
        }}),
        TermKind::Set {
            definition,
            elements,
            rest,
        } => json!({ "set": {
            "definition": format!("{definition:?}"),
            "elements": terms_json(elements),
            "rest": rest.as_ref().map_or(Value::Null, term_json),
        }}),
    }
}
