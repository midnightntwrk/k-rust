use super::{SENTENCE_END_OFFSET_ATTRIBUTE, SENTENCE_START_OFFSET_ATTRIBUTE};

pub(crate) const MODULE: u16 = 1 << 0;
pub(crate) const SYNTAX_SORT: u16 = 1 << 1;
pub(crate) const SORT_SYNONYM: u16 = 1 << 2;
pub(crate) const SYNTAX_LEXICAL: u16 = 1 << 3;
pub(crate) const PRODUCTION: u16 = 1 << 4;
pub(crate) const SYNTAX_ASSOCIATIVITY: u16 = 1 << 5;
pub(crate) const SYNTAX_PRIORITY: u16 = 1 << 6;
pub(crate) const CONTEXT_ALIAS: u16 = 1 << 7;
pub(crate) const CONTEXT: u16 = 1 << 8;
pub(crate) const RULE: u16 = 1 << 9;
pub(crate) const CLAIM: u16 = 1 << 10;
pub(crate) const CONFIGURATION: u16 = 1 << 11;
pub(crate) const BUBBLE: u16 = 1 << 12;
const ALL_SENTENCES: u16 = !MODULE;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum KeyParameter {
    Required,
    Optional,
    Forbidden,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct BuiltinKey {
    pub(crate) parameter: KeyParameter,
    pub(crate) targets: u16,
}

pub(crate) fn builtin_key(key: &str) -> Option<BuiltinKey> {
    use KeyParameter::{Forbidden, Optional, Required};

    let (parameter, targets) = match key {
        "group" | "label" => (Required, ALL_SENTENCES),
        "all-path" | "one-path" => (Forbidden, CLAIM | MODULE),
        "concrete" | "symbolic" => (Optional, MODULE | PRODUCTION | RULE),
        "cellCollection" | "token" => (Forbidden, PRODUCTION | SYNTAX_SORT),
        "hook" => (Required, PRODUCTION | SYNTAX_SORT),
        "comm" | "initializer" => (Forbidden, PRODUCTION | RULE),
        "priority" | "result" => (Required, CONTEXT | CONTEXT_ALIAS | PRODUCTION | RULE),
        "private" | "public" => (Forbidden, MODULE | PRODUCTION),
        "stream" => (Optional, PRODUCTION | RULE),
        "unboundVariables" => (
            Required,
            CONTEXT | CONTEXT_ALIAS | PRODUCTION | RULE | CLAIM,
        ),
        "circularity" | "trusted" => (Forbidden, CLAIM),
        "depends" => (Required, CLAIM),
        "context" => (Required, CONTEXT_ALIAS),
        "cool"
        | "heat"
        | "non-executable"
        | "owise"
        | "preserves-definedness"
        | "smt-lemma"
        | "anywhere" => (Forbidden, RULE),
        "simplification" => (Optional, RULE),
        "syntactic" => (Required, RULE),
        "haskell" | "not-lr1" => (Forbidden, MODULE),
        "locations" => (Forbidden, SYNTAX_SORT),
        "applyPriority" | "cellName" | "color" | "colors" | "element" | "format" | "index"
        | "klabel" | "latex" | "multiplicity" | "overload" | "parser" | "prec" | "smtlib"
        | "smt-hook" | "terminator-symbol" | "type" | "unit" | "update" | "wrapElement" => {
            (Required, PRODUCTION)
        }
        "hybrid" | "seqstrict" | "strict" | "symbol" => (Optional, PRODUCTION),
        "alias" | "alias-rec" | "assoc" | "avoid" | "bag" | "binder" | "bracket" | "cell"
        | "constructor" | "deprecated" | "exit" | "freshGenerator" | "function" | "functional"
        | "idem" | "impure" | "initial" | "injective" | "internal" | "left" | "macro"
        | "macro-rec" | "maincell" | "memo" | "mlBinder" | "mlOp" | "non-assoc"
        | "no-evaluators" | "prefer" | "returnsUnit" | "right" | "total" | "unparseAvoid"
        | "unused" => (Forbidden, PRODUCTION),
        _ => return None,
    };
    Some(BuiltinKey { parameter, targets })
}

pub(crate) fn is_internal_key(key: &str) -> bool {
    matches!(
        key,
        "anonymous"
            | "bracketLabel"
            | "cellFragment"
            | "cellOptAbsent"
            | "cellSort"
            | "concat"
            | "contentStartColumn"
            | "contentStartLine"
            | "contentStartOffset"
            | "cool-like"
            | "denormal"
            | "digest"
            | "dummy_cell"
            | "filterElement"
            | "fresh"
            | "hasDomainValues"
            | "left"
            | "nat"
            | "notInjection"
            | "not-lr1-modules"
            | "originalPrd"
            | "predicate"
            | "prettyPrintWithSortAnnotation"
            | "priorities"
            | "org.kframework.definition.Production"
            | "projection"
            | "recordPrd"
            | "recordPrd-zero"
            | "recordPrd-one"
            | "recordPrd-main"
            | "recordPrd-empty"
            | "recordPrd-subsort"
            | "recordPrd-repeat"
            | "recordPrd-item"
            | "refreshed"
            | "right"
            | "smt-prelude"
            | "org.kframework.kore.Sort"
            | "sortParams"
            | "org.kframework.attributes.Source"
            | "org.kframework.attributes.SourceId"
            | "org.krust.provenance.Origin"
            | SENTENCE_START_OFFSET_ATTRIBUTE
            | SENTENCE_END_OFFSET_ATTRIBUTE
            | "org.kframework.attributes.Location"
            | "symbol-overload"
            | "syntaxModule"
            | "temporary-cell-sort-decl"
            | "terminals"
            | "UNIQUE_ID"
            | "userList"
            | "userListTerminator"
            | "withConfig"
    )
}
