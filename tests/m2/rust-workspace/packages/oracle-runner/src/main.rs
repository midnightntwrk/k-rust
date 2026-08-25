//! External M2 artifact runner and adversarial host-collection cases.

use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};

use krs_compiler::{
    PackageContext, collect_host_descriptors, emit_k, lower_descriptor_bundle,
    lower_semantic_theory,
};
use krs_ir::{
    BuiltinSort, DescriptorBundle, DescriptorPayload, HostAuthoredAnchor,
    HostDescriptorPayload, HostProvenance, HostSourceAnchor, HostTypeReference, ItemKind,
    SemanticSortRef, SemanticTerm, SemanticTermKind,
};
use krs_k_rust::{
    Backend, CapabilityError, CompileOptions, DefinitionCompileError,
    compile_definition, compile_definition_provisional_oracle,
};

// Deliberate linker retention: the authored semantics is not incidentally
// retained through a normal Rust value import.
#[allow(unused_extern_crates)]
extern crate m2_semantics as _;

const NAMESPACE: &str = "ORG-KRS-M2-RUST";

fn main() -> Result<(), Box<dyn Error>> {
    let mut arguments = std::env::args_os().skip(1);
    let command = arguments
        .next()
        .ok_or("expected source, native, or one negative case")?
        .into_string()
        .map_err(|_| "command is not UTF-8")?;
    let output = arguments.next().map(PathBuf::from);
    if arguments.next().is_some() {
        return Err("unexpected extra argument".into());
    }
    match command.as_str() {
        "source" => build_source(output.ok_or("source requires OUTPUT")?.as_path()),
        "native" => build_native(output.ok_or("native requires OUTPUT")?.as_path()),
        "negative-cross-wired-init" => negative(Negative::CrossWiredInit),
        "negative-wrong-reference-kind" => negative(Negative::WrongReferenceKind),
        "negative-stale-split-provenance" => negative(Negative::StaleSplitProvenance),
        _ => Err(format!("unknown command {command:?}").into()),
    }
}

fn package_context() -> Result<PackageContext, Box<dyn Error>> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../m2-semantics/Cargo.toml")
        .canonicalize()?;
    Ok(PackageContext::new(
        NAMESPACE,
        "m2-semantics",
        "0.0.0",
        "workspace",
        "m2_semantics",
        manifest,
    )?)
}

fn collect() -> Result<DescriptorBundle, Box<dyn Error>> {
    let host = language_host::host_descriptors().collect::<Vec<_>>();
    assert_eq!(
        m2_semantics::init_runtime_drops(),
        0,
        "descriptor factories must not evaluate Machine::init"
    );
    let configuration_count = host
        .iter()
        .filter(|descriptor| descriptor.id.item_kind() == ItemKind::Configuration)
        .count();
    assert_eq!(configuration_count, 1, "one combined configuration registration");
    assert_eq!(host.len(), 7, "three sorts, two constructors, one config, one rule");
    let bundle = collect_host_descriptors([package_context()?], host)?;
    assert_eq!(m2_semantics::init_runtime_drops(), 0);
    Ok(bundle)
}

fn build_source(output: &Path) -> Result<(), Box<dyn Error>> {
    let bundle = collect()?;
    assert_bundle(&bundle);
    let semantic = lower_descriptor_bundle(&bundle)?;
    assert_semantic(&semantic);
    let lowered = lower_semantic_theory(&semantic)?;
    let definition_json = lowered.definition().to_canonical_json()?;
    let emitted = emit_k(&lowered)?;
    assert_canonical_k(emitted.source());

    fs::create_dir_all(output)?;
    fs::write(output.join("bundle.json"), bundle.to_canonical_json()?)?;
    fs::write(output.join("semantic-theory.json"), semantic.to_canonical_json()?)?;
    fs::write(output.join("definition-ir.json"), definition_json)?;
    fs::write(output.join("definition.k"), emitted.source())?;
    fs::write(
        output.join("symbols.json"),
        emitted.symbol_map().to_canonical_json()?,
    )?;
    fs::write(
        output.join("sources.json"),
        emitted.source_map().to_canonical_json()?,
    )?;
    reject_leaks(output)?;
    println!("source artifacts passed; runtime_init_calls=0");
    Ok(())
}

fn build_native(output: &Path) -> Result<(), Box<dyn Error>> {
    let bundle = collect()?;
    let semantic = lower_descriptor_bundle(&bundle)?;
    let lowered = lower_semantic_theory(&semantic)?;
    match compile_definition(lowered.definition(), CompileOptions::default()) {
        Err(DefinitionCompileError::Capability(
            CapabilityError::StructuredDefinitionPreparationUnavailable,
        )) => {}
        other => return Err(format!("permanent structured seam changed unexpectedly: {other:?}").into()),
    }
    let artifacts = compile_definition_provisional_oracle(
        lowered.definition(),
        CompileOptions {
            backend: Backend::Llvm,
            ..CompileOptions::default()
        },
    )?;
    fs::create_dir_all(output)?;
    fs::write(output.join("definition.kore"), artifacts.definition_kore)?;
    fs::write(
        output.join("syntaxDefinition.kore"),
        artifacts.syntax_definition_kore,
    )?;
    fs::write(output.join("macros.kore"), artifacts.macros_kore)?;
    reject_leaks(output)?;
    println!("structured Definition IR provisional native oracle passed");
    Ok(())
}

fn assert_bundle(bundle: &DescriptorBundle) {
    assert_eq!(bundle.protocol_version().0, 5);
    assert_eq!(bundle.descriptors.len(), 7);
    let configurations = bundle
        .descriptors
        .iter()
        .filter(|descriptor| matches!(descriptor.payload, DescriptorPayload::Configuration(_)))
        .collect::<Vec<_>>();
    assert_eq!(configurations.len(), 1);
    let descriptor = configurations[0];
    assert_eq!(descriptor.id.item_name(), "Machine");
    assert_eq!(descriptor.id.item_kind(), ItemKind::Configuration);
    assert!(
        bundle
            .descriptors
            .iter()
            .all(|item| item.id.item_name() != "init"),
        "the associated initializer has no stable Rust item identity"
    );
    let DescriptorPayload::Configuration(configuration) = &descriptor.payload else {
        unreachable!()
    };
    assert_eq!(configuration.root, "machine");
    assert_eq!(configuration.cell.name, "k");
    assert_eq!(configuration.cell.content_sort, BuiltinSort::KSequence);
    assert!(configuration.main_variable.is_none());
    assert_eq!(configuration.initializer.name, "init");
    assert_eq!(configuration.initializer.references.len(), 1);
    let reference = &configuration.initializer.references[0];
    assert_eq!(reference.key.role(), "initializer_term_path");
    assert_eq!(reference.key.ordinal(), 0);
    assert_eq!(reference.target.item_name(), "Foo");
    assert_eq!(reference.target.item_kind(), ItemKind::Constructor);
    let origin = descriptor
        .provenance
        .origin_for(&reference.key)
        .expect("initializer Foo reference has exact v5 provenance");
    let authored = origin.frames().first().expect("nonempty origin");
    assert!(authored.is_authored());
}

fn assert_semantic(theory: &krs_ir::SemanticTheory) {
    assert_eq!(theory.schema_version().0, 1);
    assert_eq!(theory.modules().len(), 1);
    let module = &theory.modules()[0];
    assert!(module.imports().is_empty());
    assert_eq!(module.sorts().len(), 3);
    assert_eq!(module.productions().len(), 2);
    assert_eq!(module.rules().len(), 1);

    let sort = |name: &str| {
        module
            .sorts()
            .iter()
            .find(|sort| sort.id().item_name() == name)
            .unwrap_or_else(|| panic!("missing sort {name}"))
    };
    assert!(sort("KItem").direct_parents().is_empty());
    assert_eq!(
        sort("KResult").direct_parents()[0].item_name(),
        "KItem"
    );
    assert_eq!(sort("M2Obj").direct_parents()[0].item_name(), "KResult");

    let configuration = module.configuration().expect("one configuration");
    assert_eq!(configuration.cell().name(), "k");
    assert_eq!(
        configuration.cell().sort(),
        &SemanticSortRef::Builtin(BuiltinSort::KSequence)
    );
    assert!(configuration.initializer().variables().is_empty());
    let SemanticTermKind::KSequence { item_sort, items } =
        configuration.initializer().body().kind()
    else {
        panic!("initializer must preserve the builtin KSequence layer")
    };
    assert_eq!(item_sort.item_name(), "KItem");
    assert_eq!(items.len(), 1);
    assert_application(&items[0], "M2Obj", "Foo");

    let rule = &module.rules()[0];
    let SemanticTermKind::Rewrite { from, to } = rule.body().kind() else {
        panic!("rule must be a structured rewrite")
    };
    assert_application(from, "M2Obj", "Foo");
    assert_application(to, "M2Obj", "Bar");
}

fn assert_application(term: &SemanticTerm, sort: &str, constructor: &str) {
    let SemanticSortRef::Declared(actual_sort) = term.sort() else {
        panic!("constructor application must retain a declared sort")
    };
    assert_eq!(actual_sort.item_name(), sort);
    let SemanticTermKind::Application {
        production,
        arguments,
    } = term.kind()
    else {
        panic!("expected constructor application")
    };
    assert_eq!(production.item_name(), constructor);
    assert!(arguments.is_empty());
}

fn assert_canonical_k(source: &str) {
    for required in [
        "syntax KItem",
        "syntax KResult",
        "syntax M2Obj",
        "syntax KItem ::= KResult",
        "syntax KResult ::= M2Obj",
        "syntax M2Obj ::= \"foo\" [symbol(foo)]",
        "syntax M2Obj ::= \"bar\" [symbol(bar)]",
        "configuration <k> foo </k>",
        "rule foo => bar [label(",
    ] {
        assert!(source.contains(required), "canonical K lacks {required:?}\n{source}");
    }
    assert!(!source.contains("syntax Bool"));
    assert!(!source.contains("inj{"));
    assert!(!source.contains("dotk"));
}

fn reject_leaks(directory: &Path) -> Result<(), Box<dyn Error>> {
    for entry in fs::read_dir(directory)? {
        let path = entry?.path();
        if !path.is_file() {
            continue;
        }
        let bytes = fs::read(&path)?;
        let text = String::from_utf8_lossy(&bytes);
        for forbidden in [env!("CARGO_MANIFEST_DIR"), "/home/", "TypeId", "0x"] {
            assert!(!text.contains(forbidden), "{} leaks {forbidden:?}", path.display());
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum Negative {
    CrossWiredInit,
    WrongReferenceKind,
    StaleSplitProvenance,
}

fn negative(case: Negative) -> Result<(), Box<dyn Error>> {
    let mut host = language_host::host_descriptors().collect::<Vec<_>>();
    let foo_type = host
        .iter()
        .find(|descriptor| descriptor.id.item_name() == "Foo")
        .and_then(|descriptor| descriptor.declared_type)
        .ok_or("Foo host type missing")?;
    let m2obj_type = host
        .iter()
        .find(|descriptor| descriptor.id.item_name() == "M2Obj")
        .and_then(|descriptor| descriptor.declared_type)
        .ok_or("M2Obj host type missing")?;
    let configuration = host
        .iter_mut()
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Configuration)
        .ok_or("configuration host descriptor missing")?;
    let HostDescriptorPayload::Configuration(payload) = &mut configuration.payload else {
        unreachable!()
    };
    match case {
        Negative::CrossWiredInit => payload.initializer.owner_type = foo_type,
        Negative::WrongReferenceKind => {
            payload.initializer.references[0].target = HostTypeReference {
                key: m2obj_type,
                // Preserve the parser-owned spelling so this reaches the
                // semantic kind check instead of failing provenance first.
                authored_path: "Foo".to_owned(),
            };
        }
        Negative::StaleSplitProvenance => {
            payload.initializer.provenance =
                remap_provenance(&payload.initializer.provenance, "src/provenance-decoy.rs")?;
        }
    }
    match collect_host_descriptors([package_context()?], host) {
        Ok(_) => Err("adversarial host descriptors unexpectedly collected".into()),
        Err(error) => {
            println!("{:?}: {}", error.kind(), error.detail());
            Ok(())
        }
    }
}

fn remap_provenance(
    provenance: &HostProvenance,
    display_file: &str,
) -> Result<HostProvenance, Box<dyn Error>> {
    let remap = |anchor: &HostSourceAnchor| {
        HostSourceAnchor::new(
            display_file,
            anchor.start(),
            anchor.end(),
            anchor.precision(),
        )
    };
    let invocation = remap(provenance.invocation())?;
    let authored = provenance
        .authored()
        .iter()
        .map(|node| {
            Ok(HostAuthoredAnchor::new(
                node.key().clone(),
                remap(node.anchor())?,
            ))
        })
        .collect::<Result<Vec<_>, krs_ir::HostProvenanceError>>()?;
    Ok(HostProvenance::new(invocation, authored)?)
}
