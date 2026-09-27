//! Rule cell content keeps its declared sort while the parser recognizes rewrites of that sort.
//! The KORE digests use one set of snapshots in both inference builds.

use k_rust::{
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use sha2::{Digest, Sha256};

struct Case {
    name: &'static str,
    rule: &'static str,
}

const CASES: &[Case] = &[
    Case {
        name: "anonymous_map",
        rule: "rule [[ f() => 0 ]] <cell> _M </cell>",
    },
    Case {
        name: "anonymous_k",
        rule: "rule [[ f() => 0 ]] <k> _ </k>",
    },
    Case {
        name: "named_map",
        rule: "rule [[ f() => 0 ]] <cell> M </cell>",
    },
    Case {
        name: "named_k",
        rule: "rule [[ f() => 0 ]] <k> X </k>",
    },
    Case {
        name: "rewrite_map",
        rule: "rule <cell> M => .Map </cell>",
    },
    Case {
        name: "rewrite_k",
        rule: "rule <k> X => .K </k>",
    },
    Case {
        name: "frame_map",
        rule: "rule [[ f() => 0 ]] <cell> M ... </cell>",
    },
    Case {
        name: "frame_k",
        rule: "rule [[ f() => 0 ]] <k> X ... </k>",
    },
];

#[test]
fn rule_cell_contents_emit_the_same_kore_in_both_builds() {
    for case in CASES {
        let source = format!(
            "module CELL-CONTENT\n  imports INT\n  imports MAP\n  configuration\n    <k> $PGM:KItem </k>\n    <cell> .Map </cell>\n  syntax Int ::= f() [function]\n  {}\nendmodule\n",
            case.rule
        );
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new(format!("{}.k", case.name), source),
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
        .unwrap_or_else(|error| panic!("{} does not load: {error:?}", case.name));
        let kore = compile_loaded_definition(&loaded, CompileOptions::default())
            .unwrap_or_else(|error| panic!("{} does not compile: {error:?}", case.name))
            .definition_kore;
        let hash = Sha256::digest(kore.as_bytes())
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        let digest = format!("{} bytes, {hash}", kore.len());
        insta::assert_snapshot!(format!("cell_{}", case.name), digest);
    }
}
