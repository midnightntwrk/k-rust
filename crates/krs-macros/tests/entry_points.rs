//! `krs_expand::{AttributeMacro, FunctionMacro}` stay equal to the entry points
//! of this crate, and each entry point only dispatches to its own variant.

use krs_expand::{AttributeMacro, FunctionMacro};
use quote::ToTokens;

/// `(name, body tokens)` of one entry-point function.
type Entry = (String, String);

/// Every `#[proc_macro_attribute]` and every `#[proc_macro]` function of
/// `krs-macros`, in source order.
fn krs_macros_entries() -> (Vec<Entry>, Vec<Entry>) {
    let file =
        syn::parse_file(include_str!("../src/lib.rs")).expect("krs-macros/src/lib.rs parses");
    let mut attributes = Vec::new();
    let mut functions = Vec::new();
    for item in file.items {
        let syn::Item::Fn(function) = item else {
            continue;
        };
        let entry = (
            function.sig.ident.to_string(),
            function.block.to_token_stream().to_string(),
        );
        for attribute in &function.attrs {
            if attribute.path().is_ident("proc_macro_attribute") {
                attributes.push(entry.clone());
            } else if attribute.path().is_ident("proc_macro") {
                functions.push(entry.clone());
            }
        }
    }
    (attributes, functions)
}

#[test]
fn entry_enums_equal_the_krs_macros_entry_points() {
    let (attributes, functions) = krs_macros_entries();
    let names = |entries: &[Entry]| {
        entries
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(
        names(&attributes),
        AttributeMacro::ALL
            .iter()
            .map(|entry| entry.name())
            .collect::<Vec<_>>()
    );
    assert_eq!(
        names(&functions),
        FunctionMacro::ALL
            .iter()
            .map(|entry| entry.name())
            .collect::<Vec<_>>()
    );
}

#[test]
fn every_krs_macros_entry_point_dispatches_to_its_own_variant() {
    let (attributes, functions) = krs_macros_entries();
    for (name, body) in attributes {
        let entry = AttributeMacro::from_name(&name).expect("an attribute entry point");
        assert_eq!(
            body,
            format!("{{ attribute_macro (AttributeMacro :: {entry:?} , attributes , item) }}"),
            "`{name}` must only dispatch to krs-expand"
        );
    }
    for (name, body) in functions {
        let entry = FunctionMacro::from_name(&name).expect("a function-like entry point");
        assert_eq!(
            body,
            format!("{{ function_macro (FunctionMacro :: {entry:?} , input) }}"),
            "`{name}` must only dispatch to krs-expand"
        );
    }
}
