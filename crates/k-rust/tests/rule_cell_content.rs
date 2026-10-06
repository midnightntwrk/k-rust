//! Rule cell content keeps its declared sort while the parser recognizes rewrites of that sort.
//! The KORE digests use one set of snapshots in both inference builds.

use k_rust::{
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use sha2::{Digest, Sha256};

/// `rule`, in a module with a `<k>` and a `Map`-sorted `<cell>` cell, compiles to the KORE whose
/// size and digest the snapshot `cell_<name>` pins in both builds.
fn assert_cell_content_digest(name: &str, rule: &str) {
    let source = format!(
        "module CELL-CONTENT\n  imports INT\n  imports MAP\n  configuration\n    <k> $PGM:KItem </k>\n    <cell> .Map </cell>\n  syntax Int ::= f() [function]\n  {rule}\nendmodule\n"
    );
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new(format!("{name}.k"), source),
        "CELL-CONTENT",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{name} does not load: {error:?}"));
    let kore = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("{name} does not compile: {error:?}"))
        .definition_kore;
    let hash = Sha256::digest(kore.as_bytes())
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    let digest = format!("{} bytes, {hash}", kore.len());
    insta::assert_snapshot!(format!("cell_{name}"), digest);
}

/// One test per rule, named by its case.
macro_rules! rule_cell_contents_emit_the_same_kore_in_both_builds {
    ($($name:ident: $rule:literal,)*) => {
        mod rule_cell_contents_emit_the_same_kore_in_both_builds {
            $(
                #[test]
                fn $name() {
                    super::assert_cell_content_digest(stringify!($name), $rule);
                }
            )*
        }
    };
}

rule_cell_contents_emit_the_same_kore_in_both_builds! {
    anonymous_map: "rule [[ f() => 0 ]] <cell> _M </cell>",
    anonymous_k: "rule [[ f() => 0 ]] <k> _ </k>",
    named_map: "rule [[ f() => 0 ]] <cell> M </cell>",
    named_k: "rule [[ f() => 0 ]] <k> X </k>",
    rewrite_map: "rule <cell> M => .Map </cell>",
    rewrite_k: "rule <k> X => .K </k>",
    frame_map: "rule [[ f() => 0 ]] <cell> M ... </cell>",
    frame_k: "rule [[ f() => 0 ]] <k> X ... </k>",
}
