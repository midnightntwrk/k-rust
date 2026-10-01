//! Identity, walkthrough, diagnostic, and replacement projections.

use super::{QueryResult, accepts, encoded, enum_name, read};
use krs_compiler::{SourceMap, SymbolMap, definition_module_imports, definition_sentence_source};
use krs_ir::{
    CellContentFrame, CellPost, DefinitionIr, DefinitionRuleBody, DefinitionSentence,
    DescriptorBundle, DescriptorHeadRuleResult, DescriptorPayload, DescriptorTerm,
    DescriptorTermArgument, GrammarDescriptor, RustVisibility, SentenceKind,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

/// Remove public-projection provenance and normalize selected package and item identities.
fn normalize(
    value: &mut Value,
    names: &BTreeMap<String, String>,
    public: bool,
    namespace: Option<&str>,
) {
    match value {
        Value::String(name) => {
            if let Some(replacement) = names.get(name) {
                *name = replacement.clone();
            }
        }
        Value::Array(values) => {
            for child in values {
                normalize(child, names, public, namespace);
            }
        }
        Value::Object(object) => {
            if object.contains_key("k_namespace")
                && object.contains_key("cargo_name")
                && object.contains_key("cargo_version")
                && object.contains_key("cargo_source")
            {
                if public {
                    object.retain(|key, _| key == "k_namespace");
                } else if namespace.is_some_and(|n| object["k_namespace"] == n) {
                    object.insert("cargo_name".into(), json!("normalized-imp-package"));
                    object.insert("cargo_version".into(), json!("0.0.0"));
                    object.insert("cargo_source".into(), json!("workspace"));
                }
            } else {
                if public {
                    object.remove("provenance");
                }
                for child in object.values_mut() {
                    normalize(child, names, public, namespace);
                }
            }
        }
        _ => {}
    }
}

pub(super) fn descriptor_details(
    directory: &Path,
    module_path: Option<&[String]>,
    item_name: Option<&str>,
    public_only: bool,
) -> QueryResult {
    let bundle: DescriptorBundle = read(directory, krs_compiler::DESCRIPTOR_ARTIFACT)?;
    let mut rows = Vec::new();
    for descriptor in &bundle.descriptors {
        let declaration = bundle
            .declarations
            .iter()
            .find(|d| d.id() == &descriptor.id)
            .ok_or("descriptor lacks declaration metadata")?;
        if module_path.is_some_and(|path| path != descriptor.id.module_path())
            || !accepts(item_name, descriptor.id.item_name())
            || (public_only && declaration.visibility != RustVisibility::Public)
        {
            continue;
        }
        let mut normalized = encoded(descriptor);
        normalize(&mut normalized, &BTreeMap::new(), true, None);
        rows.push(json!({
            "module_path":descriptor.id.module_path(), "item_name":descriptor.id.item_name(),
            "item_kind":descriptor.id.item_kind(), "visibility":declaration.visibility,
            "explicit_symbol":declaration.explicit_symbol, "normalized":normalized,
        }));
    }
    Ok(json!({"rows":rows}))
}

pub(super) fn head_rule_walkthrough(directory: &Path, item_name: &str) -> QueryResult {
    let bundle: DescriptorBundle = read(directory, krs_compiler::DESCRIPTOR_ARTIFACT)?;
    let mut matches = bundle
        .descriptors
        .iter()
        .filter(|d| d.id.item_name() == item_name);
    let descriptor = matches.next().ok_or("walkthrough descriptor is absent")?;
    if matches.next().is_some() {
        return Err("walkthrough descriptor is ambiguous".into());
    }
    let DescriptorPayload::HeadRule(rule) = &descriptor.payload else {
        return Err("walkthrough requires a head rule".into());
    };
    let DescriptorTerm::Application {
        reference,
        arguments,
        ..
    } = &rule.subject
    else {
        return Err("walkthrough subject requires an application".into());
    };
    let krs_ir::DescriptorApplicationRef::Declared(id) = &reference.application else {
        return Err("walkthrough subject requires a declared application".into());
    };
    let fields = arguments
        .iter()
        .map(|arg| match arg {
            DescriptorTermArgument::Named { field, .. } => Ok(field.as_str()),
            DescriptorTermArgument::Positional { .. } => {
                Err("walkthrough subject requires named arguments")
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let DescriptorHeadRuleResult::Replace(DescriptorTerm::Application {
        reference: result,
        arguments: result_args,
        ..
    }) = &rule.result
    else {
        return Err("walkthrough requires an application replacement".into());
    };
    let krs_ir::DescriptorApplicationRef::Builtin(operation) = &result.application else {
        return Err("walkthrough replacement requires a builtin".into());
    };
    let args = result_args
        .iter()
        .map(|arg| match arg {
            DescriptorTermArgument::Positional { value }
                if matches!(**value, DescriptorTerm::Variable { .. }) =>
            {
                let DescriptorTerm::Variable { name, .. } = &**value else {
                    unreachable!()
                };
                Ok(name.as_str())
            }
            _ => Err("walkthrough replacement requires positional variables"),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(json!({
        "id":descriptor.id.item_name(), "kind":"head_rule", "sentence_kind":rule.sentence_kind,
        "label":rule.label.as_ref().ok_or("walkthrough requires a label")?.name,
        "configuration":rule.configuration.item_name(), "cell":rule.computation_cell.cell.field.as_str(),
        "bindings":rule.bindings.iter().map(|b|b.name.as_str()).collect::<Vec<_>>(),
        "subject":{"application":id.item_name(),"arguments":fields},
        "result":{"application":format!("builtin:{}",enum_name(operation)),"arguments":args},
    }))
}

pub(super) fn symbol_projection(directory: &Path, names: &[String]) -> QueryResult {
    let map: SymbolMap = read(directory, krs_compiler::SYMBOLS_ARTIFACT)?;
    let mut rows = map.entries().iter().filter(|e| names.iter().any(|n|n == e.emitted_name()))
        .map(|e|json!({"identity":e.identity(),"emitted_name":e.emitted_name(),"symbol_kind":e.symbol_kind()}))
        .collect::<Vec<_>>();
    rows.sort_by_key(Value::to_string);
    let mut source_keys = map
        .entries()
        .iter()
        .filter(|e| names.iter().any(|n| n == e.emitted_name()))
        .map(|e| e.source_map_key().as_str())
        .collect::<Vec<_>>();
    source_keys.sort_unstable();
    Ok(json!({"rows":rows,"source_keys":source_keys}))
}

pub(super) fn source_token(
    directory: &Path,
    authored: &Path,
    relative: &str,
    token: &str,
    artifact: &str,
) -> QueryResult {
    if !matches!(
        artifact,
        krs_compiler::DEFINITION_ARTIFACT | krs_compiler::SPEC_ARTIFACT
    ) {
        return Err("source_token artifact must be definition.k or spec.k".into());
    }
    let map: SourceMap = read(directory, krs_compiler::SOURCES_ARTIFACT)?;
    let source = fs::read(authored)?;
    let generated_source = fs::read(directory.join(artifact))?;
    let hash = krs_ir::lower_hex(&Sha256::digest(&source));
    let selected = map.filtered(|entry| {
        let Some(generated) = entry.generated() else {
            return false;
        };
        let Some(origin) = krs_cli::exact_authored_range_from_origin(entry.origin()) else {
            return false;
        };
        let authored_bytes = usize::try_from(origin.start_byte)
            .ok()
            .zip(usize::try_from(origin.end_byte).ok())
            .and_then(|(start, end)| source.get(start..end));
        let generated_bytes = usize::try_from(generated.start_byte())
            .ok()
            .zip(usize::try_from(generated.end_byte()).ok())
            .and_then(|(start, end)| generated_source.get(start..end));
        generated.artifact() == artifact
            && origin.file.package_relative_path() == relative
            && origin.file.content_sha256().as_str() == hash
            && authored_bytes == Some(token.as_bytes())
            && !token.is_empty()
            && generated_bytes.is_some_and(|bytes| !bytes.is_empty())
    });
    if selected.entries().len() != 1 {
        return Err(format!(
            "expected one exact sidecar mapping for {token:?}, got {}",
            selected.entries().len()
        )
        .into());
    }
    let generated = selected.entries()[0]
        .generated()
        .expect("selected a generated range");
    let diagnostic = krs_cli::translate_k_frontend_diagnostic(
        &selected,
        "gate-source-token",
        "exact authored token",
        generated.start_byte(),
        generated.end_byte(),
        krs_cli::DiagnosticGeneratedRange {
            artifact: artifact.to_owned(),
            start_line: generated.start_line(),
            start_column: generated.start_column(),
            end_line: generated.end_line(),
            end_column: generated.end_column(),
        },
    )
    .ok_or("selected source token lacks exact diagnostic translation")?;
    Ok(json!({"authored_range":diagnostic.authored_range,"generated":generated}))
}

fn non_rules(
    bundle: &DescriptorBundle,
    path: &[String],
    head: bool,
    namespace: &str,
) -> QueryResult {
    let mut relations = Vec::new();
    for d in &bundle.descriptors {
        if d.id.module_path() == path
            && let DescriptorPayload::Grammar(grammar) = &d.payload
            && matches!(**grammar, GrammarDescriptor::Subsort { .. })
        {
            let mut relation = encoded(grammar)["grammar"].clone();
            normalize(&mut relation, &BTreeMap::new(), false, Some(namespace));
            relations.push((relation.to_string(), d.id.item_name().to_owned()));
        }
    }
    relations.sort();
    if relations.windows(2).any(|p| p[0].0 == p[1].0) {
        return Err("duplicate subsort relation".into());
    }
    let names = relations
        .iter()
        .enumerate()
        .map(|(i, (_, name))| (name.clone(), format!("__krs_grammar_subsort_alpha_{i}")))
        .collect();
    let mut descriptors = Vec::new();
    let mut declarations = Vec::new();
    let mut counts = BTreeMap::<String, usize>::new();
    for d in &bundle.descriptors {
        if d.id.module_path() != path
            || matches!(
                (&d.payload, head),
                (DescriptorPayload::HeadRule(_), true)
                    | (DescriptorPayload::ConfigurationRule(_), false)
            )
        {
            continue;
        }
        let mut normalized = encoded(d);
        normalized.as_object_mut().unwrap().remove("provenance");
        normalize(&mut normalized, &names, false, Some(namespace));
        *counts
            .entry(normalized["descriptor_kind"].as_str().unwrap().to_owned())
            .or_default() += 1;
        descriptors.push(normalized);
        let declaration = bundle
            .declarations
            .iter()
            .find(|v| v.id() == &d.id)
            .ok_or("missing declaration metadata")?;
        let mut declaration = encoded(declaration);
        normalize(&mut declaration, &names, false, Some(namespace));
        declarations.push(declaration);
    }
    let ids = descriptors
        .iter()
        .map(|d| d["id"].to_string())
        .collect::<BTreeSet<_>>();
    if ids.len() != descriptors.len() || declarations.len() != descriptors.len() {
        return Err(
            "non-rule descriptors and declarations require unique covered identities".into(),
        );
    }
    descriptors.sort_by_key(Value::to_string);
    declarations.sort_by_key(Value::to_string);
    Ok(
        json!({"descriptors":descriptors,"declarations":declarations,"counts":counts,"subsort_count":relations.len()}),
    )
}

fn rule_transport(bundle: &DescriptorBundle, path: &[String], head: bool) -> QueryResult {
    let mut rules = BTreeMap::new();
    for d in &bundle.descriptors {
        if d.id.module_path() != path {
            continue;
        }
        let (kind, label) = match (&d.payload, head) {
            (DescriptorPayload::HeadRule(r), true) => (r.sentence_kind, r.label.as_ref()),
            (DescriptorPayload::ConfigurationRule(r), false) => (r.sentence_kind, r.label.as_ref()),
            _ => continue,
        };
        if kind != SentenceKind::Transition {
            return Err("rule transport requires transitions".into());
        }
        let label = label.ok_or("rule transport requires labels")?;
        let name =
            d.id.item_name()
                .strip_prefix("r#")
                .unwrap_or(d.id.item_name());
        if rules.insert(name, &label.name).is_some() {
            return Err("duplicate rule transport identity".into());
        }
    }
    Ok(json!(rules))
}

/// Remove precisely the bound suffixes recognized by the previous comparison:
/// replaced <k> K tails and preserved <env> Map remainders.
pub(super) fn frame_normalized(
    sentence: &DefinitionSentence,
    cells: &super::Context<'_>,
) -> Result<DefinitionSentence, Box<dyn std::error::Error>> {
    let DefinitionSentence::Rule(rule) = sentence else {
        return Ok(sentence.clone());
    };
    let DefinitionRuleBody::Configuration(body) = rule.relational_body() else {
        return Ok(sentence.clone());
    };
    let mut value = encoded(sentence);
    let mut removed = Vec::new();
    for (i, clause) in body.clauses().iter().enumerate() {
        let ((
            "k",
            CellContentFrame::KSequenceTail {
                binding: Some(binding),
                ..
            },
            CellPost::Replace { .. },
        )
        | (
            "env",
            CellContentFrame::MapRemainder {
                binding: Some(binding),
                ..
            },
            CellPost::Preserve,
        )) = (cells.cells[clause.cell()], clause.frame(), clause.after())
        else {
            continue;
        };
        removed.push(binding.as_str());
        value["sentence"]["body"]["clauses"][i]["frame"]
            .as_object_mut()
            .unwrap()
            .remove("binding");
    }
    value["sentence"]["variables"]
        .as_array_mut()
        .unwrap()
        .retain(|v| !removed.contains(&v["id"].as_str().unwrap()));
    // The rebuilt full definition below validates all remaining binder uses.
    Ok(krs_ir::json::from_slice(&serde_json::to_vec(&value)?)?)
}

fn sentence_multiset(
    definition: &DefinitionIr,
    name: &str,
) -> Result<BTreeMap<String, usize>, Box<dyn std::error::Error>> {
    let context = super::Context::new(definition);
    let mut value = encoded(definition);
    for (i, module) in definition.modules().iter().enumerate() {
        if module.id().as_str() == name {
            value["modules"][i]["sentences"] = json!(
                module
                    .sentences()
                    .iter()
                    .map(|s| frame_normalized(s, &context))
                    .collect::<Result<Vec<_>, _>>()?
            );
        }
    }
    let normalized: DefinitionIr = krs_ir::json::from_slice(&serde_json::to_vec(&value)?)?;
    let module = normalized
        .modules()
        .iter()
        .find(|m| m.id().as_str() == name)
        .ok_or("comparison module is absent")?;
    let mut rows = BTreeMap::new();
    for import in definition_module_imports(module) {
        rows.insert(format!("  imports {import}"), 1);
    }
    for sentence in module.sentences() {
        if matches!(sentence,DefinitionSentence::Rule(r) if r.kind()==SentenceKind::Claim) {
            continue;
        }
        let source = definition_sentence_source(&normalized, sentence)?;
        *rows.entry(source.trim_end().to_owned()).or_default() += 1;
    }
    Ok(rows)
}

pub(super) fn replacement_parity(
    reference: &Path,
    replacement: &Path,
    module: &str,
    path: &[String],
) -> QueryResult {
    let reference_bundle: DescriptorBundle = read(reference, krs_compiler::DESCRIPTOR_ARTIFACT)?;
    let replacement_bundle: DescriptorBundle =
        read(replacement, krs_compiler::DESCRIPTOR_ARTIFACT)?;
    let left = non_rules(&reference_bundle, path, true, module)?;
    let right = non_rules(&replacement_bundle, path, false, module)?;
    if left != right {
        return Err("normalized non-rule descriptors or declaration metadata differ".into());
    }
    let reference_rules = rule_transport(&reference_bundle, path, true)?;
    let replacement_rules = rule_transport(&replacement_bundle, path, false)?;
    let left_definition: DefinitionIr = read(reference, krs_compiler::DEFINITION_IR_ARTIFACT)?;
    let right_definition: DefinitionIr = read(replacement, krs_compiler::DEFINITION_IR_ARTIFACT)?;
    let left_sentences = sentence_multiset(&left_definition, module)?;
    let right_sentences = sentence_multiset(&right_definition, module)?;
    for (sentence, count) in &right_sentences {
        if left_sentences.get(sentence).copied().unwrap_or(0) < *count {
            return Err(format!("replacement sentence multiset differs: {sentence}").into());
        }
    }
    Ok(
        json!({"non_rule_counts":right["counts"],"non_rule_count":right["descriptors"].as_array().unwrap().len(),
        "subsort_count":right["subsort_count"],"reference_rules":reference_rules,"replacement_rules":replacement_rules,
        "sentence_count":right_sentences.values().sum::<usize>()}),
    )
}
