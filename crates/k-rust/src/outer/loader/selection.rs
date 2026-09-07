//! Module selection for fresh compilation, before backend exclusion and inner parsing.

use std::collections::BTreeSet;

use crate::{
    definition::{Definition, ModuleId, ResolvedDefinition, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode},
};

use super::{LoadError, LoadOptions, is_configuration_sentence};

pub(super) struct CompilationSelection<'a> {
    pub syntax_module: Option<&'a str>,
}

/// The syntax root and the optional missing-default diagnostic.
pub struct SyntaxModule {
    pub name: String,
    pub fallback_warning: Option<Diagnostic>,
}

/// Resolve explicit or default syntax selection using ParserUtils' missing-default fallback.
pub fn resolve_syntax_module(
    definition: &ResolvedDefinition,
    explicit: Option<&str>,
) -> Result<SyntaxModule, LoadError> {
    let main = definition.main_module();
    if let Some(name) = explicit {
        if definition.module_id(name).is_none() {
            return Err(LoadError::MissingSyntaxModule(name.into()));
        }
        return Ok(SyntaxModule {
            name: name.into(),
            fallback_warning: None,
        });
    }
    let default = format!("{}-SYNTAX", main.name);
    if definition.module_id(&default).is_some() {
        return Ok(SyntaxModule {
            name: default,
            fallback_warning: None,
        });
    }
    Ok(SyntaxModule {
        name: main.name.clone(),
        fallback_warning: Some(Diagnostic::warning_at(
            DiagnosticCode::MissingSyntaxModule,
            format!(
                "Could not find main syntax module with name {default} in definition.  Use --syntax-module to specify one. Using {} as default.",
                main.name
            ),
            &main.attributes,
        )),
    })
}

pub(super) fn select_modules(
    mut definition: Definition,
    resolved: &ResolvedDefinition,
    syntax: &str,
    options: &LoadOptions,
) -> Result<Definition, LoadError> {
    let main = resolved.main_module_id();
    let syntax = resolved
        .module_id(syntax)
        .expect("syntax selection was resolved");
    // Both roots are protected even when the default syntax module exists but is excluded.
    for attribute in &options.excluded_module_attributes {
        if resolved.module(main).attributes.get(attribute).is_some() {
            return Err(LoadError::ExcludedMainModule {
                module: resolved.module(main).name.clone(),
                attribute: attribute.clone(),
            });
        }
        if resolved.module(syntax).attributes.get(attribute).is_some() {
            return Err(LoadError::ExcludedSyntaxModule {
                module: resolved.module(syntax).name.clone(),
                attribute: attribute.clone(),
            });
        }
    }
    let configuration = options
        .configuration_module
        .as_deref()
        .unwrap_or(&definition.main_module);
    let configuration = resolved
        .module_id(configuration)
        .ok_or_else(|| LoadError::MissingConfigurationModule(configuration.into()))?;
    let mut roots = BTreeSet::from([main, syntax, configuration]);
    for name in ["K-REFLECTION", "STDIN-STREAM", "STDOUT-STREAM", "MAP"] {
        if let Some(module) = resolved.module_id(name) {
            roots.insert(module);
        }
    }

    // Bubble visibility follows all imports, including private imports, before tag filtering.
    // Dependency-first propagation avoids materializing and deduplicating visible sentences.
    let mut with_bubbles = BTreeSet::new();
    for &id in resolved.dependency_order() {
        if resolved
            .module(id)
            .local_sentences
            .iter()
            .any(|s| matches!(s, Sentence::Bubble { .. }))
            || resolved
                .direct_imports(id)
                .iter()
                .any(|import| with_bubbles.contains(&import.module))
        {
            with_bubbles.insert(id);
        } else {
            roots.insert(id);
        }
    }

    // Java supplies the original default configuration separately after selection/exclusion.
    // Retain its closure only when configuration resolution will need the fallback.
    if !has_configuration_after_exclusion(resolved, configuration, options)
        && let Some(default) = resolved.module_id("DEFAULT-CONFIGURATION")
        && !options
            .excluded_module_attributes
            .iter()
            .any(|tag| resolved.module(default).attributes.get(tag).is_some())
    {
        roots.insert(default);
    }
    let mut retained = BTreeSet::new();
    for root in roots {
        retained.insert(root);
        retained.extend(resolved.transitive_imports(root));
    }
    // Filter the original sequence. Rebuilding from resolved modules would deduplicate local
    // sentences and could change the first representative, production identity, or provenance.
    definition.modules.retain(|module| {
        retained.contains(
            &resolved
                .module_id(&module.name)
                .expect("resolved module exists"),
        )
    });
    Ok(definition)
}

fn has_configuration_after_exclusion(
    resolved: &ResolvedDefinition,
    root: ModuleId,
    options: &LoadOptions,
) -> bool {
    let mut visited = BTreeSet::new();
    let mut pending = vec![root];
    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            continue;
        }
        let module = resolved.module(id);
        if options
            .excluded_module_attributes
            .iter()
            .any(|tag| module.attributes.get(tag).is_some())
        {
            continue;
        }
        if module.local_sentences.iter().any(is_configuration_sentence) {
            return true;
        }
        pending.extend(
            resolved
                .direct_imports(id)
                .into_iter()
                .map(|import| import.module),
        );
    }
    false
}
