//! The K names K itself gives a meaning in every definition, or in every definition that imports
//! a given builtin module, which no authored declaration may take.
//!
//! A K name names one thing in its namespace: a sort, a symbol, a cell. An authored declaration
//! that takes a name K already declares does not declare a new thing; it adds to K's (a sort
//! `KCell` beside a cell `<k>` is that cell's sort, a function `Ite` a second production of
//! K's conditional's symbol `ite`), so the K means something the Rust does not say. The tables
//! below are those of the pinned K 7.1.337 (`kast.md`, `domains.md`), restricted to the names an
//! authored declaration can spell: a sort is a Rust type name, and a production's symbol starts
//! with a lowercase letter or `_` (`lowerCamel` of a Rust name).

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::CellCollectionType;

/// The sorts of K's own modules, which every rule and configuration of a definition is parsed
/// with (`kast.md`): the sorts of terms, labels, lists and strings of K's syntax, of
/// configuration variables, and of cells and cell bags. `K`, `KItem` and `KResult` are claimed
/// elsewhere (the builtin sort `KSequence`, the framework module).
const KAST_SORTS: [&str; 7] = [
    "Bag",
    "Cell",
    "KBott",
    "KConfigVar",
    "KLabel",
    "KList",
    "KString",
];

/// The cells K adds to every configuration: its top cell and the counter of fresh values.
pub(crate) const K_CELLS: [(&str, &str); 2] = [
    (
        "generatedTop",
        "K adds as the top cell of every configuration",
    ),
    (
        "generatedCounter",
        "K adds to every configuration as the counter of fresh values",
    ),
];

/// The words that begin or end a sentence of K's outer syntax. K reads a sentence's text up to
/// the next of them, so a rule that applies a production with such a terminal ends at it.
const SENTENCE_KEYWORDS: [&str; 6] = [
    "claim",
    "configuration",
    "context",
    "endmodule",
    "rule",
    "syntax",
];

/// The modules that bring a builtin module's symbols into a definition: each imports it,
/// directly or through the modules it imports.
const LIST_IMPORTERS: &[&str] = &["COLLECTIONS", "K-IO", "LIST", "MAP", "MAP-SYMBOLIC"];
const MAP_IMPORTERS: &[&str] = &["COLLECTIONS", "MAP", "MAP-SYMBOLIC"];
const SET_IMPORTERS: &[&str] = &["COLLECTIONS", "MAP", "MAP-SYMBOLIC", "SET"];
const BOOL_IMPORTERS: &[&str] = &[
    "BOOL",
    "BYTES",
    "FLOAT",
    "INT",
    "K-EQUAL",
    "K-IO",
    "MAP-SYMBOLIC",
    "STRING",
];
const K_EQUAL_IMPORTERS: &[&str] = &["BYTES", "INT", "K-EQUAL", "K-IO", "MAP-SYMBOLIC", "STRING"];
const INT_IMPORTERS: &[&str] = &["BYTES", "INT", "K-IO", "STRING"];
const BYTES_IMPORTERS: &[&str] = &["BYTES"];
/// Every definition's: `ML-SYNTAX` is part of K's own modules.
const EVERY_DEFINITION: &[&str] = &[];

/// The symbols of K's builtin modules that an authored symbol could spell, each with its module
/// and the modules that bring it in.
const BUILTIN_SYMBOLS: [(&str, &str, &[&str]); 25] = [
    ("_List_", "LIST", LIST_IMPORTERS),
    ("_inList_", "LIST", LIST_IMPORTERS),
    ("pushList", "LIST", LIST_IMPORTERS),
    ("sizeList", "LIST", LIST_IMPORTERS),
    ("sizeMInt", "LIST", LIST_IMPORTERS),
    ("_Map_", "MAP", MAP_IMPORTERS),
    ("sizeMap", "MAP", MAP_IMPORTERS),
    ("_Set_", "SET", SET_IMPORTERS),
    ("weakAlwaysFinally", "ML-SYNTAX", EVERY_DEFINITION),
    ("weakExistsFinally", "ML-SYNTAX", EVERY_DEFINITION),
    ("_andBool_", "BOOL", BOOL_IMPORTERS),
    ("_andThenBool_", "BOOL", BOOL_IMPORTERS),
    ("_impliesBool_", "BOOL", BOOL_IMPORTERS),
    ("_orBool_", "BOOL", BOOL_IMPORTERS),
    ("_orElseBool_", "BOOL", BOOL_IMPORTERS),
    ("_xorBool_", "BOOL", BOOL_IMPORTERS),
    ("notBool_", "BOOL", BOOL_IMPORTERS),
    ("ite", "K-EQUAL", K_EQUAL_IMPORTERS),
    ("_divInt_", "INT", INT_IMPORTERS),
    ("_modInt_", "INT", INT_IMPORTERS),
    ("_xorInt_", "INT", INT_IMPORTERS),
    ("bigEndianBytes", "BYTES", BYTES_IMPORTERS),
    ("littleEndianBytes", "BYTES", BYTES_IMPORTERS),
    ("signedBytes", "BYTES", BYTES_IMPORTERS),
    ("unsignedBytes", "BYTES", BYTES_IMPORTERS),
];

/// The sorts of K's builtin modules that are no builtin sort of KRS, with the modules that bring
/// them in: `MInt` (`MINT-SYNTAX`, imported by `LIST` and `BYTES`) and the sorts of `K-IO`.
const BUILTIN_MODULE_SORTS: [(&str, &str, &[&str]); 6] = [
    (
        "MInt",
        "MINT-SYNTAX",
        &[
            "BYTES",
            "COLLECTIONS",
            "K-IO",
            "LIST",
            "MAP",
            "MAP-SYMBOLIC",
        ],
    ),
    ("IOError", "K-IO", &["K-IO"]),
    ("IOFile", "K-IO", &["K-IO"]),
    ("IOInt", "K-IO", &["K-IO"]),
    ("IOString", "K-IO", &["K-IO"]),
    ("Stream", "K-IO", &["K-IO"]),
];

/// The sorts K declares in every definition with the cells `cells` (each cell's K name, and its
/// collection type for a collection cell): K's own sorts, and for each cell, the cell's sort, its
/// optional and fragment sorts and a collection's sort of instances; also the sorts of the
/// cells K adds. Each sort maps to what it is.
pub(crate) fn reserved_sorts(
    cells: &[(String, Option<CellCollectionType>)],
) -> BTreeMap<String, String> {
    let mut sorts = BTreeMap::new();
    for sort in KAST_SORTS {
        sorts.insert(
            sort.to_owned(),
            "K declares as a sort of its own".to_owned(),
        );
    }
    let generated = K_CELLS.iter().map(|(cell, _)| ((*cell).to_owned(), None));
    for (cell, collection) in cells.iter().cloned().chain(generated) {
        let sort = krs_ir_levels::k_surface::cell_sort_name(&cell);
        for (suffix, role) in [
            ("", "sort"),
            ("Opt", "optional sort"),
            ("Fragment", "fragment sort"),
        ] {
            sorts.insert(
                format!("{sort}{suffix}"),
                format!("K generates as the {role} of the cell `<{cell}>`"),
            );
        }
        if let Some(collection) = collection {
            sorts.insert(
                krs_ir_levels::k_surface::collection_sort_name(&cell, collection),
                format!("K generates as the sort of the instances of the cell `<{cell}>`"),
            );
        }
    }
    sorts
}

/// The sorts of the builtin modules `imports` brings into the definition, each with what it is.
pub(crate) fn imported_sorts(imports: &BTreeSet<&str>) -> BTreeMap<&'static str, String> {
    BUILTIN_MODULE_SORTS
        .iter()
        .filter(|(_, _, importers)| importers.iter().any(|module| imports.contains(module)))
        .map(|(sort, module, _)| {
            (
                *sort,
                format!("K's builtin module `{module}` declares as a sort"),
            )
        })
        .collect()
}

/// The symbols of the builtin modules `imports` brings into the definition, each with what it
/// is.
pub(crate) fn imported_symbols(imports: &BTreeSet<&str>) -> BTreeMap<&'static str, String> {
    BUILTIN_SYMBOLS
        .iter()
        .filter(|(_, _, importers)| {
            importers.is_empty() || importers.iter().any(|module| imports.contains(module))
        })
        .map(|(symbol, module, _)| {
            (
                *symbol,
                format!("K's builtin module `{module}` declares as a symbol"),
            )
        })
        .collect()
}

/// The first word of the terminal `text` that is a sentence keyword of K's outer syntax.
pub(crate) fn sentence_keyword(text: &str) -> Option<&'static str> {
    text.split_whitespace().find_map(|word| {
        SENTENCE_KEYWORDS
            .into_iter()
            .find(|keyword| *keyword == word)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_cell_reserves_its_sorts_and_k_its_own() {
        let sorts = reserved_sorts(&[
            ("k".to_owned(), None),
            ("acct".to_owned(), Some(CellCollectionType::Map)),
        ]);
        for sort in [
            "KCell",
            "KCellOpt",
            "KCellFragment",
            "AcctCellMap",
            "GeneratedTopCell",
            "GeneratedCounterCellFragment",
            "KBott",
            "Bag",
        ] {
            assert!(sorts.contains_key(sort), "{sort}");
        }
        assert!(!sorts.contains_key("KCellMap"));
        assert!(!sorts.contains_key("Stmt"));
    }

    #[test]
    fn a_builtin_symbol_is_reserved_where_its_module_is_imported() {
        let none = imported_symbols(&BTreeSet::new());
        assert!(none.contains_key("weakAlwaysFinally"));
        assert!(!none.contains_key("ite"));
        assert!(!none.contains_key("sizeMap"));
        let int = imported_symbols(&BTreeSet::from(["INT"]));
        assert!(int.contains_key("ite") && int.contains_key("_andBool_"));
        assert!(!int.contains_key("bigEndianBytes"));
        let bytes = imported_symbols(&BTreeSet::from(["BYTES"]));
        assert!(bytes.contains_key("signedBytes") && bytes.contains_key("ite"));
        let map = imported_symbols(&BTreeSet::from(["MAP"]));
        assert!(map.contains_key("sizeMap") && map.contains_key("pushList"));
        assert!(imported_sorts(&BTreeSet::from(["MAP"])).contains_key("MInt"));
        assert!(imported_sorts(&BTreeSet::from(["INT"])).is_empty());
    }

    #[test]
    fn a_sentence_keyword_is_a_whole_word_of_a_terminal() {
        assert_eq!(sentence_keyword("rule"), Some("rule"));
        assert_eq!(sentence_keyword("if syntax"), Some("syntax"));
        assert_eq!(sentence_keyword("rules"), None);
        assert_eq!(sentence_keyword("requires"), None);
    }
}
