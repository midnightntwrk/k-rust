//! Production-API artifact projection for the complete IMP definition.

use std::fs;
use std::path::{Path, PathBuf};

use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
use krs_compiler::{emit_k, lower_descriptor_bundle, lower_semantic_theory};
use krs_k_rust::adapt_definition;

fn write(path: &Path, value: impl AsRef<[u8]>) -> Result<(), Box<dyn std::error::Error>> {
    fs::write(path, value)?;
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Force the authored package into the final link so its inventory
    // registrations are visible. This is a type reference, not semantics.
    let _ = std::any::TypeId::of::<imp::StmtSyntax>();

    let output = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .ok_or("usage: krs-imp-artifact-probe OUTPUT-DIRECTORY")?;
    if output.exists() {
        return Err(format!("output already exists: {}", output.display()).into());
    }
    fs::create_dir_all(&output)?;

    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../rust-definition/Cargo.toml")
        .canonicalize()?;
    let context = PackageContext::new(
        "KRS-IMP",
        "krs-imp-definition",
        "0.0.0",
        "workspace",
        "krs_imp_definition",
        manifest,
    )?
    // The package sets `int-literals = "unsigned"`, as the CLI plan reads it.
    .with_int_literals(krs_collector::IntLiterals::Unsigned);
    let mut descriptors = k::host_descriptors().collect::<Vec<_>>();
    let bundle = collect_host_descriptors_with_builtins(
        [context.clone()],
        descriptors.clone(),
        &k::builtin_registry(),
    )?;
    descriptors.reverse();
    let reordered =
        collect_host_descriptors_with_builtins([context], descriptors, &k::builtin_registry())?;
    if bundle.to_canonical_json()? != reordered.to_canonical_json()? {
        return Err("descriptor bundle depends on registration order".into());
    }

    let semantic = lower_descriptor_bundle(&bundle)?;
    let reordered_semantic = lower_descriptor_bundle(&reordered)?;
    if semantic.to_canonical_json()? != reordered_semantic.to_canonical_json()? {
        return Err("Semantic IR depends on registration order".into());
    }
    let lowered = lower_semantic_theory(&semantic)?;
    let reordered_lowered = lower_semantic_theory(&reordered_semantic)?;
    if lowered.definition().to_canonical_json()?
        != reordered_lowered.definition().to_canonical_json()?
    {
        return Err("Definition IR depends on registration order".into());
    }
    let emitted = emit_k(&lowered)?;
    let reordered_emitted = emit_k(&reordered_lowered)?;
    if emitted != reordered_emitted {
        return Err("canonical K artifacts depend on registration order".into());
    }
    let native = adapt_definition(lowered.definition())?;
    // KAST JSON v4 has no KContextAlias node. Preserve the complete public
    // native source model through its deterministic derived Debug projection;
    // native semantic comparison itself is performed over compiled KORE.
    let native_projection = format!("{:#?}\n", native.definition());

    write(
        &output.join("descriptor-bundle.json"),
        bundle.to_canonical_json()?,
    )?;
    write(
        &output.join("semantic-ir.json"),
        semantic.to_canonical_json()?,
    )?;
    write(
        &output.join("definition-ir.json"),
        lowered.definition().to_canonical_json()?,
    )?;
    write(&output.join("definition.k"), emitted.source())?;
    let spec = emitted
        .spec()
        .ok_or("the complete IMP definition emits its claims to spec.k")?;
    write(&output.join("spec.k"), spec.source())?;
    write(
        &output.join("symbols.json"),
        emitted.symbol_map().to_canonical_json()?,
    )?;
    write(
        &output.join("sources.json"),
        emitted.source_map().to_canonical_json()?,
    )?;
    write(&output.join("native-source.txt"), native_projection)?;

    println!(
        "IMP artifacts: descriptors={}, modules={}, native_origins={}",
        bundle.descriptors().len(),
        semantic.modules().len(),
        native.origins().len(),
    );
    Ok(())
}
