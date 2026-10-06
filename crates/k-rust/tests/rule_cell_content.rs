//! Rule cell content keeps its declared sort while the parser recognizes rewrites of that sort.
//! Each probe pins a digest of the axioms its own rule compiles to. One set of snapshots serves
//! both inference builds, so the two builds must emit the same axioms for every probe.

use std::collections::BTreeSet;

use k_rust::{
    builtin::embedded,
    definition::Sentence,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_with_options},
    provenance::{InputAddress, InputSpace},
};
use k_rust_kore::{
    kore::{ast, parser::parse_definition, printer::Printer},
    names::KoreAttribute,
};
use sha2::{Digest, Sha256};

const MODULE: &str = "CELL-CONTENT";

/// `rule`, in a module with a `<k>` and a `Map`-sorted `<cell>` cell, compiles to axioms whose
/// count, size and digest the snapshot `rule_axioms_<name>` pins in both builds.
///
/// The probe's axioms are those of `definition.kore` whose UNIQUE_ID's provenance names the
/// probe rule as an input sentence: they are what that rule compiles to, whatever pass shaped
/// them, and they carry the sorts inference gave the rule's cell contents and variables. The
/// rest of the definition (the prelude, the configuration's initializers, symbol declarations)
/// is not part of the probe, so changes there do not move these digests.
fn assert_rule_axioms_digest(name: &str, rule: &str) {
    let source = format!(
        "module {MODULE}\n  imports INT\n  imports MAP\n  configuration\n    <k> $PGM:KItem </k>\n    <cell> .Map </cell>\n  syntax Int ::= f() [function]\n  {rule}\nendmodule\n"
    );
    let file = format!("{name}.k");
    let rule_line = source
        .lines()
        .position(|line| line.trim() == rule)
        .map(|index| u32::try_from(index + 1).unwrap())
        .unwrap();
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new(file.clone(), source),
        MODULE,
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
    let probe = probe_rule_address(&loaded, &file, rule_line);
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("{name} does not compile: {error:?}"));

    let probe_ids = artifacts
        .sentence_provenance
        .iter()
        .filter(|(_, provenance)| provenance.input_addresses.contains(&probe))
        .map(|(id, _)| id.as_str())
        .collect::<BTreeSet<_>>();
    assert!(
        !probe_ids.is_empty(),
        "{name}: no emitted sentence derives from the probe rule {probe:?}"
    );
    let kore = parse_definition(&artifacts.definition_kore)
        .unwrap_or_else(|error| panic!("{name}: definition.kore does not parse: {error:?}"));
    let axioms = kore
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter(|sentence| match sentence {
            ast::Sentence::Axiom { attributes, .. } => attributes
                .string(KoreAttribute::UniqueId)
                .unwrap()
                .is_some_and(|id| probe_ids.contains(id)),
            _ => false,
        })
        .collect::<Vec<_>>();
    let selected_ids = axioms
        .iter()
        .filter_map(|axiom| match axiom {
            ast::Sentence::Axiom { attributes, .. } => {
                attributes.string(KoreAttribute::UniqueId).unwrap()
            }
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        selected_ids, probe_ids,
        "{name}: every sentence derived from the probe rule is an axiom of definition.kore"
    );

    // Compact printing makes the digest a function of the probe's axioms alone, independent of
    // the definition's layout and of where they sit in it.
    let text = axioms
        .iter()
        .map(|axiom| Printer::compact().print_sentence(axiom))
        .collect::<Vec<_>>()
        .join("\n");
    let hash = Sha256::digest(text.as_bytes())
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    let digest = format!(
        "axioms: {}, bytes: {}, sha256: {hash}",
        axioms.len(),
        text.len()
    );
    insta::assert_snapshot!(format!("rule_axioms_{name}"), digest);
}

/// The input address of the one loaded rule of `file` that starts on `line`.
fn probe_rule_address(loaded: &LoadedDefinition, file: &str, line: u32) -> InputAddress {
    let main = loaded.definition().main_module().unwrap();
    assert_eq!(main.name, MODULE);
    let indices = main
        .local_sentences
        .iter()
        .enumerate()
        .filter(|(_, sentence)| {
            matches!(&***sentence, Sentence::Rule { .. })
                && sentence.attributes().source() == Some(file)
                && sentence
                    .attributes()
                    .location()
                    .is_some_and(|location| location.start_line == line)
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let [index] = indices.as_slice() else {
        panic!("expected one loaded rule at {file}:{line}, found {indices:?}");
    };
    InputAddress::new(InputSpace::Compile, MODULE, u32::try_from(*index).unwrap())
}

/// One test per rule, named by its case.
macro_rules! rule_cell_contents_emit_the_same_kore_in_both_builds {
    ($($name:ident: $rule:literal,)*) => {
        mod rule_cell_contents_emit_the_same_kore_in_both_builds {
            $(
                #[test]
                fn $name() {
                    super::assert_rule_axioms_digest(stringify!($name), $rule);
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
