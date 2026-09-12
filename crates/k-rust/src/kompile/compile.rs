//! Host-independent orchestration of the ordered K frontend compilation pipeline.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    str::FromStr,
};

use crate::{
    definition::{
        CheckMode, Definition, FlatModule, ResolvedDefinition, Sentence, StructuralCheckBackend,
        StructuralCheckOptions,
        checks::{check_definition_with_options, check_singleton_overloads},
        expand_configurations_with_diagnostics,
    },
    diagnostic::{Diagnostic, DiagnosticCode, DiagnosticPolicy, Severity},
    kast::{Sort, Term},
    kore::printer::Printer as KorePrinter,
    outer::LoadedDefinition,
};

use super::module_to_kore::BUILTIN_HOOK_NAMESPACES;
use super::passes::number_sentence;
use super::{
    ModuleToKoreOptions, add_cool_like_attributes, add_implicit_computation_cell,
    add_semantics_module, add_sort_injections_to_definition, check_simplification_rules,
    concretize_cells, constant_fold, expand_macros, generate_sort_predicate_rules,
    generate_sort_predicate_syntax, generate_sort_projections, guard_or_patterns,
    minimize_term_construction, module_to_kore_from_resolved_with_options, number_sentences,
    propagate_macro_attributes, regenerate_sort_predicate_syntax, remove_unit, resolve_anon_vars,
    resolve_comm, resolve_config_var, resolve_contexts, resolve_fresh_config_constants,
    resolve_fresh_constants, resolve_fun, resolve_function_with_config,
    resolve_heat_cool_attributes, resolve_io, resolve_semantic_casts, resolve_strict,
    rust_backend_hook_namespaces, subsort_kitem,
};

/// Backend whose KORE input should be generated.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CompilationBackend {
    Llvm,
    /// The in-process symbolic backend. Its KORE is Java's Haskell-backend dialect (including
    /// the map definedness axioms `kompile --backend haskell` generates) plus the plugin hook
    /// namespaces the backend dispatches natively, so `haskell` names the same target.
    #[default]
    Rust,
}

impl CompilationBackend {
    /// Module attribute excluded before compilation for this backend.
    /// Plugin hook namespaces admitted as hooked symbols when `--hook-namespaces` is not given.
    ///
    /// The Rust backend dispatches its plugin hooks natively; other backends match a default
    /// Java `kompile`, which emits plugin hooks as ordinary symbols unless namespaces are named.
    pub fn default_hook_namespaces(self) -> Vec<String> {
        match self {
            Self::Rust => rust_backend_hook_namespaces(),
            Self::Llvm => Vec::new(),
        }
    }

    pub fn excluded_module_attribute(self) -> &'static str {
        match self {
            Self::Llvm => "symbolic",
            Self::Rust => "concrete",
        }
    }

    fn structural_check_options(
        self,
        mode: CheckMode,
        builtin_source_prefixes: Vec<String>,
    ) -> StructuralCheckOptions {
        match self {
            Self::Llvm => StructuralCheckOptions {
                builtin_source_prefixes,
                mode,
                symbolic: false,
                backend: StructuralCheckBackend::Other,
            },
            Self::Rust => StructuralCheckOptions {
                symbolic: true,
                backend: StructuralCheckBackend::Rust,
                builtin_source_prefixes,
                mode,
            },
        }
    }
}

impl fmt::Display for CompilationBackend {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Llvm => "llvm",
            Self::Rust => "rust",
        })
    }
}

impl FromStr for CompilationBackend {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "llvm" => Ok(Self::Llvm),
            "rust" | "haskell" => Ok(Self::Rust),
            _ => Err(format!(
                "unsupported compilation backend {value:?}; expected \"rust\" or \"llvm\""
            )),
        }
    }
}

/// Options affecting backend selection and textual KORE rendering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompileOptions {
    pub backend: CompilationBackend,
    pub kore_width: usize,
    /// Match `kprove` by treating bare claims as all-path reachability claims.
    pub default_claims_to_all_path: bool,
    /// Plugin hook namespaces to admit as hooked symbols (`kompile --hook-namespaces`); `None`
    /// uses [`CompilationBackend::default_hook_namespaces`].
    pub hook_namespaces: Option<Vec<String>>,
    /// Filtering and severity policy for diagnostics produced by compilation checks.
    pub diagnostics: DiagnosticPolicy,
    /// Definition-only or proof-module structural checks.
    pub check_mode: CheckMode,
    /// Canonical source prefixes whose declarations are supplied by the builtin catalog.
    pub builtin_source_prefixes: Vec<String>,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            backend: CompilationBackend::Rust,
            kore_width: 100,
            default_claims_to_all_path: false,
            hook_namespaces: None,
            diagnostics: DiagnosticPolicy::default(),
            check_mode: CheckMode::default(),
            builtin_source_prefixes: vec!["krust-builtin://".into()],
        }
    }
}

/// The three artifacts traditionally written by `krust kcompile`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompiledKoreArtifacts {
    pub definition_kore: String,
    pub syntax_definition_kore: String,
    pub macros_kore: String,
    pub diagnostics: Vec<Diagnostic>,
    /// Configuration variable sorts in the transformed main module.
    ///
    /// Names omit the leading `$`. Collection after the compiler passes makes variables generated
    /// for stream cells visible to execution clients.
    pub configuration_variables: BTreeMap<String, Sort>,
    /// The transformed execution definition before backend-only sort injection, unit removal,
    /// and term-construction minimization.
    ///
    /// Standalone surface patterns must use this exact context so macro expansion, cell syntax,
    /// and production identities agree with the compilation that emitted `definition_kore`.
    pub execution_definition: Definition,
    /// Executable semantic rewrite precedence from the transformed source definition.
    ///
    /// KORE emission structurally sorts rules, so source-backed execution joins this order to the
    /// emitted axioms by their final `UNIQUE_ID`. Equivalent duplicate rules occur only once.
    pub execution_rewrite_order: Vec<String>,
}

/// A compilation failure with its precise pipeline stage and any structured diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompileError {
    pub stage: &'static str,
    pub message: String,
    pub diagnostics: Vec<Diagnostic>,
}

impl CompileError {
    fn from_error(stage: &'static str, error: impl fmt::Display) -> Self {
        Self {
            stage,
            message: error.to_string(),
            diagnostics: Vec::new(),
        }
    }

    fn from_diagnostics(
        stage: &'static str,
        message: impl Into<String>,
        diagnostics: Vec<Diagnostic>,
    ) -> Self {
        Self {
            stage,
            message: message.into(),
            diagnostics,
        }
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "kcompile stage {:?} failed: {}",
            self.stage, self.message
        )
    }
}

impl std::error::Error for CompileError {}

fn stage<T>(name: &'static str, result: Result<T, impl fmt::Display>) -> Result<T, CompileError> {
    result.map_err(|error| CompileError::from_error(name, error))
}

macro_rules! diagnostic_stage {
    ($policy:expr, $name:literal, $result:expr) => {
        $result.map_err(|error| {
            let message = error.to_string();
            CompileError::from_diagnostics($name, message, $policy.apply(error.diagnostics))
        })?
    };
}

/// Compile an in-memory, backend-filtered definition into backend-facing textual KORE artifacts.
///
/// Hosts must load the definition with [`CompilationBackend::excluded_module_attribute`] before
/// calling this function. No filesystem or external backend process is used here.
pub fn compile_loaded_definition(
    loaded: &LoadedDefinition,
    options: CompileOptions,
) -> Result<CompiledKoreArtifacts, CompileError> {
    let (execution_definition, definition, mut diagnostics) =
        transform_loaded_definition(loaded, &options)?;
    let execution_rewrite_order = stage(
        "collect execution rewrite order",
        collect_execution_rewrite_order(&execution_definition),
    )?;
    let resolved = stage(
        "resolve transformed definition",
        ResolvedDefinition::resolve(&definition),
    )?;
    diagnostics.extend(
        options
            .diagnostics
            .apply(check_singleton_overloads(&resolved)),
    );
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err(CompileError::from_diagnostics(
            "post-compilation checks",
            "post-compilation checks failed",
            diagnostics,
        ));
    }
    let configuration_variables = stage(
        "collect configuration variables",
        configuration_variables(&resolved),
    )?;
    let hook_namespaces = options
        .hook_namespaces
        .clone()
        .unwrap_or_else(|| options.backend.default_hook_namespaces());
    diagnostics.extend(
        options
            .diagnostics
            .apply(unadmitted_hook_namespace_diagnostics(
                &resolved,
                &hook_namespaces,
            )),
    );
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err(CompileError::from_diagnostics(
            "hook namespace checks",
            "hook namespace checks failed",
            diagnostics,
        ));
    }
    let generated = stage(
        "emit KORE",
        module_to_kore_from_resolved_with_options(
            &resolved,
            &definition.main_module,
            ModuleToKoreOptions {
                generate_map_ceil_axioms: options.backend == CompilationBackend::Rust,
                default_claims_to_all_path: options.default_claims_to_all_path,
                hook_namespaces,
                definition_module: match &options.check_mode {
                    CheckMode::Proof { definition_module } => Some(definition_module.clone()),
                    CheckMode::Definition => None,
                },
            },
        ),
    )?;

    let printer = KorePrinter::pretty(options.kore_width);
    let definition_kore = with_newline(printer.print_definition(&generated.semantics_definition()));
    let syntax_definition_kore =
        with_newline(printer.print_definition(&generated.syntax_definition()));
    let macros_kore = with_newline(
        generated
            .macros
            .iter()
            .map(|sentence| printer.print_sentence(sentence))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    Ok(CompiledKoreArtifacts {
        definition_kore,
        syntax_definition_kore,
        macros_kore,
        diagnostics,
        configuration_variables,
        execution_definition,
        execution_rewrite_order,
    })
}

fn collect_execution_rewrite_order(definition: &Definition) -> Result<Vec<String>, String> {
    fn visit<'a>(
        name: &str,
        modules: &BTreeMap<&str, &'a FlatModule>,
        visiting: &mut Vec<&'a str>,
        visited: &mut BTreeSet<&'a str>,
        ordered: &mut Vec<&'a FlatModule>,
    ) -> Result<(), String> {
        if visited.contains(name) {
            return Ok(());
        }
        if let Some(start) = visiting.iter().position(|candidate| *candidate == name) {
            let mut cycle = visiting[start..].to_vec();
            cycle.push(visiting[start]);
            return Err(format!(
                "module import cycle while ordering rewrites: {}",
                cycle.join(" -> ")
            ));
        }
        let module = modules
            .get(name)
            .copied()
            .ok_or_else(|| format!("module {name} not found while ordering rewrites"))?;
        visiting.push(module.name.as_str());
        for import in &module.imports {
            visit(&import.name, modules, visiting, visited, ordered)?;
        }
        visiting.pop();
        visited.insert(module.name.as_str());
        ordered.push(module);
        Ok(())
    }

    struct Occurrence<'a> {
        sentence: &'a Sentence,
        module: &'a str,
        index: usize,
    }

    fn computed_unique_id(sentence: &Sentence) -> String {
        let mut sentence = sentence.clone();
        sentence.attributes_mut().remove("UNIQUE_ID");
        number_sentence(&mut sentence);
        sentence
            .attributes()
            .get_str("UNIQUE_ID")
            .expect("number_sentence assigns an identifier to every rule")
            .to_owned()
    }

    let modules = definition
        .modules
        .iter()
        .map(|module| (module.name.as_str(), module))
        .collect::<BTreeMap<_, _>>();
    let mut ordered = Vec::new();
    visit(
        &definition.main_module,
        &modules,
        &mut Vec::new(),
        &mut BTreeSet::new(),
        &mut ordered,
    )?;

    let mut occurrences = BTreeMap::<String, Occurrence<'_>>::new();
    let mut rewrite_order = Vec::new();
    for module in ordered {
        for (index, sentence) in module.local_sentences.iter().enumerate() {
            let Sentence::Rule { attributes, .. } = sentence else {
                continue;
            };
            let unique_id = attributes.get_str("UNIQUE_ID").ok_or_else(|| {
                format!(
                    "transformed rule in module {} at local sentence {index} has no UNIQUE_ID",
                    module.name
                )
            })?;
            if let Some(previous) = occurrences.get(unique_id) {
                if computed_unique_id(previous.sentence) != computed_unique_id(sentence) {
                    return Err(format!(
                        "conflicting rewrite-order UNIQUE_ID {unique_id:?} at module {} local sentence {} and module {} local sentence {index}",
                        previous.module, previous.index, module.name
                    ));
                }
                continue;
            }
            occurrences.insert(
                unique_id.to_owned(),
                Occurrence {
                    sentence,
                    module: &module.name,
                    index,
                },
            );
            rewrite_order.push(unique_id.to_owned());
        }
    }
    Ok(rewrite_order)
}

/// Match `CompiledDefinition.initializeConfigurationVariableDefaultSorts` on the transformed
/// main module, including configuration variables introduced by compiler passes.
pub fn configuration_variables(
    definition: &ResolvedDefinition,
) -> Result<BTreeMap<String, Sort>, String> {
    fn unwrap_singleton(mut term: &Term) -> &Term {
        loop {
            term = term.unannotated();
            match term {
                Term::Apply { label, arguments } if label.name == "inj" && arguments.len() == 1 => {
                    term = &arguments[0];
                }
                Term::Sequence(items) if items.len() == 1 => {
                    term = &items[0];
                }
                _ => return term,
            }
        }
    }

    fn lookup_name(term: &Term) -> Option<&str> {
        let Term::Apply { label, arguments } = unwrap_singleton(term) else {
            return None;
        };
        if label.name != "Map:lookup" {
            return None;
        }
        let [_, key] = arguments.as_slice() else {
            return None;
        };
        let Term::Token { token, sort } = unwrap_singleton(key) else {
            return None;
        };
        (sort.name == "KConfigVar").then_some(token.as_str())
    }

    fn is_generic_k(sort: &Sort) -> bool {
        sort.parameters.is_empty() && matches!(sort.name.as_str(), "K" | "KItem")
    }

    fn insert_sort(
        sorts: &mut BTreeMap<String, Sort>,
        name: String,
        sort: Sort,
    ) -> Result<(), String> {
        let Some(existing) = sorts.get(&name) else {
            sorts.insert(name, sort);
            return Ok(());
        };
        if existing == &sort {
            return Ok(());
        }
        match (is_generic_k(existing), is_generic_k(&sort)) {
            (true, false) => {
                sorts.insert(name, sort);
                Ok(())
            }
            (false, true) => Ok(()),
            (true, true) => {
                if sort.name == "KItem" {
                    sorts.insert(name, sort);
                }
                Ok(())
            }
            (false, false) => Err(format!(
                "configuration variable `${name}` is used at both sort {existing} and {sort}"
            )),
        }
    }

    fn collect(term: &Term, sorts: &mut BTreeMap<String, Sort>) -> Result<(), String> {
        match term.unannotated() {
            Term::Apply { label, arguments } => {
                if let Some(projected) = label.name.strip_prefix("project:")
                    && let [argument] = arguments.as_slice()
                    && let Some(name) = lookup_name(argument)
                {
                    insert_sort(
                        sorts,
                        name.strip_prefix('$').unwrap_or(name).to_owned(),
                        Sort::new(projected),
                    )?;
                }
                for argument in arguments {
                    collect(argument, sorts)?;
                }
            }
            Term::Rewrite { left, right } => {
                collect(left, sorts)?;
                collect(right, sorts)?;
            }
            Term::As { pattern, alias } => {
                collect(pattern, sorts)?;
                collect(alias, sorts)?;
            }
            Term::Sequence(items) => {
                for item in items {
                    collect(item, sorts)?;
                }
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!("unannotated terms are matched above"),
        }
        Ok(())
    }

    let mut sorts = BTreeMap::new();
    for sentence in definition.sentences(definition.main_module_id()) {
        if let crate::definition::Sentence::Rule { body, .. } = sentence {
            collect(body, &mut sorts)?;
        }
    }
    Ok(sorts)
}

fn unadmitted_hook_namespace_diagnostics(
    definition: &ResolvedDefinition,
    admitted: &[String],
) -> Vec<Diagnostic> {
    let mut seen = BTreeSet::new();
    let mut diagnostics = Vec::new();
    for sentence in definition.sentences(definition.main_module_id()) {
        let crate::definition::Sentence::Production { attributes, .. } = sentence else {
            continue;
        };
        if attributes.get("function").is_none() {
            continue;
        }
        let Some(hook) = attributes.get_str("hook") else {
            continue;
        };
        let Some((namespace, _)) = hook.split_once('.') else {
            continue;
        };
        if BUILTIN_HOOK_NAMESPACES.contains(&namespace)
            || admitted.iter().any(|candidate| candidate == namespace)
            || !seen.insert((namespace.to_owned(), hook.to_owned()))
        {
            continue;
        }
        diagnostics.push(Diagnostic::warning_at(
            DiagnosticCode::UnadmittedHookNamespace,
            format!(
                "hook namespace `{namespace}` of `hook({hook})` is neither builtin nor selected with --hook-namespaces; the production compiles as an unhooked function"
            ),
            attributes,
        ));
    }
    diagnostics
}

fn transform_loaded_definition(
    loaded: &LoadedDefinition,
    options: &CompileOptions,
) -> Result<(Definition, Definition, Vec<Diagnostic>), CompileError> {
    // Loader-produced definitions are already expanded, while structured embedders can construct
    // the public LoadedDefinition fields directly. Normalize both entry paths before checks.
    let (definition, configuration_diagnostics) = stage(
        "expand structured configurations",
        expand_configurations_with_diagnostics(&loaded.definition),
    )?;
    let resolved = stage(
        "resolve structured configurations",
        ResolvedDefinition::resolve(&definition),
    )?;
    let checked = options.diagnostics.apply(stage(
        "definition checks",
        check_definition_with_options(
            &resolved,
            options.backend.structural_check_options(
                options.check_mode.clone(),
                options.builtin_source_prefixes.clone(),
            ),
        ),
    )?);
    let mut diagnostics = loaded.diagnostics.clone();
    diagnostics.extend(options.diagnostics.apply(configuration_diagnostics));
    diagnostics.extend(checked);
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err(CompileError::from_diagnostics(
            "definition checks",
            "definition checks failed",
            diagnostics,
        ));
    }

    let definition = diagnostic_stage!(
        options.diagnostics,
        "resolve commutative rules",
        resolve_comm(&definition)
    );
    let definition = diagnostic_stage!(
        options.diagnostics,
        "resolve I/O streams",
        resolve_io(&definition)
    );
    let definition = diagnostic_stage!(
        options.diagnostics,
        "resolve local functions",
        resolve_fun(&definition)
    );
    let definition = stage(
        "seed sort predicate syntax",
        generate_sort_predicate_syntax(&definition),
    )?;
    let definition = diagnostic_stage!(
        options.diagnostics,
        "resolve function configuration",
        resolve_function_with_config(&definition)
    );
    let definition = diagnostic_stage!(
        options.diagnostics,
        "resolve strictness",
        resolve_strict(&definition)
    );
    let definition = resolve_anon_vars(&definition);
    let definition = diagnostic_stage!(
        options.diagnostics,
        "resolve contexts",
        resolve_contexts(&definition)
    );
    let definition = number_sentences(&definition);
    let definition = diagnostic_stage!(
        options.diagnostics,
        "resolve heat/cool attributes",
        resolve_heat_cool_attributes(&definition)
    );
    let definition = resolve_semantic_casts(&definition);
    let definition = stage("add KItem subsorts", subsort_kitem(&definition))?;
    let definition = diagnostic_stage!(
        options.diagnostics,
        "constant folding",
        constant_fold(&definition)
    );
    let definition = stage(
        "propagate macro attributes",
        propagate_macro_attributes(&definition),
    )?;
    let definition = stage("guard or-patterns", guard_or_patterns(&definition))?;
    let (definition, fresh_config_count) = diagnostic_stage!(
        options.diagnostics,
        "resolve fresh configuration constants",
        resolve_fresh_config_constants(&definition)
    );
    let definition = stage(
        "generate sort predicate syntax",
        generate_sort_predicate_syntax(&definition),
    )?;
    let definition = stage(
        "generate sort projections",
        generate_sort_projections(&definition),
    )?;
    let definition = diagnostic_stage!(
        options.diagnostics,
        "expand macros",
        expand_macros(&definition)
    );
    let definition = stage(
        "add implicit computation cell",
        add_implicit_computation_cell(&definition),
    )?;
    let definition = diagnostic_stage!(
        options.diagnostics,
        "resolve fresh constants",
        resolve_fresh_constants(&definition, fresh_config_count)
    );
    let definition = stage(
        "regenerate sort predicate syntax",
        regenerate_sort_predicate_syntax(&definition),
    )?;
    let definition = stage(
        "regenerate sort projections",
        generate_sort_projections(&definition),
    )?;
    let definition = diagnostic_stage!(
        options.diagnostics,
        "check simplification rules",
        check_simplification_rules(&definition)
    );
    let definition = stage("finalize KItem subsorts", subsort_kitem(&definition))?;
    let definition = diagnostic_stage!(
        options.diagnostics,
        "concretize cells",
        concretize_cells(&definition)
    );
    // Coverage instrumentation and the optional unsafe-anywhere removal are identity stages
    // because neither optional mode is exposed by the frontend API yet.
    let definition = stage("add semantics module", add_semantics_module(&definition))?;
    let definition = resolve_config_var(&definition);
    let definition = add_cool_like_attributes(&definition);
    let definition = generate_sort_predicate_rules(&definition);
    let definition = number_sentences(&definition);
    let execution_definition = definition;
    let definition = stage(
        "add sort injections",
        add_sort_injections_to_definition(&execution_definition),
    )?;
    let definition = stage("remove units", remove_unit(&definition))?;
    let definition = stage(
        "minimize term construction",
        minimize_term_construction(&definition),
    )?;
    Ok((execution_definition, definition, diagnostics))
}

fn with_newline(mut text: String) -> String {
    if !text.ends_with('\n') {
        text.push('\n');
    }
    text
}

#[cfg(test)]
mod tests {
    use k_rust_backend::definition::BackendDefinition;

    #[cfg(feature = "z3-inference")]
    use crate::{
        builtin::embedded,
        outer::{LoadOptions, load_with_options},
    };
    use crate::{
        definition::{Attributes, Definition, FlatImport, FlatModule, Sentence},
        kast::Term,
        kore::parser::parse_definition,
        outer::{ResolvedSource, load},
    };
    #[cfg(feature = "z3-inference")]
    use sha3::{Digest, Sha3_256};

    use super::*;

    fn ranked_rule(unique_id: Option<&str>, body_label: &str) -> Sentence {
        let mut attributes = Attributes::default();
        if let Some(unique_id) = unique_id {
            attributes.insert("UNIQUE_ID", serde_json::json!(unique_id));
        }
        Sentence::Rule {
            body: Term::apply(body_label, Vec::new()),
            requires: Term::apply("#Top", Vec::new()),
            ensures: Term::apply("#Top", Vec::new()),
            attributes,
        }
    }

    fn ranked_module(name: &str, imports: &[&str], rules: &[(Option<&str>, &str)]) -> FlatModule {
        FlatModule {
            name: name.into(),
            imports: imports
                .iter()
                .map(|name| FlatImport {
                    name: (*name).into(),
                    public: false,
                })
                .collect(),
            local_sentences: rules
                .iter()
                .map(|(unique_id, body)| ranked_rule(*unique_id, body))
                .collect(),
            attributes: Attributes::default(),
        }
    }

    #[test]
    fn execution_rewrite_order_follows_import_and_local_sentence_order() {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![
                ranked_module(
                    "MAIN",
                    &["LEFT", "RIGHT"],
                    &[
                        (Some("main-first"), "mainFirst"),
                        (Some("main-second"), "mainSecond"),
                    ],
                ),
                ranked_module(
                    "RIGHT",
                    &["BASE"],
                    &[(Some("base"), "base"), (Some("right"), "right")],
                ),
                ranked_module(
                    "LEFT",
                    &["BASE"],
                    &[
                        (Some("left-first"), "leftFirst"),
                        (Some("left-second"), "leftSecond"),
                    ],
                ),
                ranked_module("BASE", &[], &[(Some("base"), "base")]),
            ],
            attributes: Attributes::default(),
        };

        assert_eq!(
            collect_execution_rewrite_order(&definition).unwrap(),
            [
                "base",
                "left-first",
                "left-second",
                "right",
                "main-first",
                "main-second",
            ]
        );
    }

    #[test]
    fn execution_rewrite_order_rejects_conflicting_duplicate_ids() {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![ranked_module(
                "MAIN",
                &[],
                &[(Some("duplicate"), "first"), (Some("duplicate"), "second")],
            )],
            attributes: Attributes::default(),
        };

        let error = collect_execution_rewrite_order(&definition).unwrap_err();
        assert!(
            error.contains("module MAIN local sentence 0 and module MAIN local sentence 1"),
            "{error}"
        );
    }

    #[test]
    fn execution_rewrite_order_reports_missing_ids_at_their_source_position() {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![ranked_module("MAIN", &[], &[(None, "missing")])],
            attributes: Attributes::default(),
        };

        assert_eq!(
            collect_execution_rewrite_order(&definition).unwrap_err(),
            "transformed rule in module MAIN at local sentence 0 has no UNIQUE_ID"
        );
    }

    #[test]
    fn standalone_compilation_emits_verifiable_sort_predicates() {
        for bool_syntax in ["", "syntax Bool", "syntax Bool [token]"] {
            let source = format!(
                r#"module MAIN
                  {bool_syntax}
                  syntax State ::= "a" [function, symbol(a)] | "b" [symbol(b)]
                  rule a => b
                endmodule"#
            );
            let loaded = load(
                ResolvedSource::new("standalone.k", source),
                "MAIN",
                &mut |_: &str, required: &str| Err(format!("unexpected require {required}")),
            )
            .unwrap();
            let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
            for text in [
                &artifacts.definition_kore,
                &artifacts.syntax_definition_kore,
            ] {
                let kore = parse_definition(text).unwrap();
                BackendDefinition::internalize(&kore, "MAIN")
                    .expect("standalone KORE must satisfy the backend's definition contract");
            }
        }
    }

    #[cfg(feature = "z3-inference")]
    fn artifact_digest(text: &str) -> String {
        Sha3_256::digest(text.as_bytes())
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn provenance_plumbing_leaves_emitted_kore_unchanged() {
        let source = r#"
            module MAIN
              imports MAP
              syntax Int ::= r"[0-9]+" [token]
              syntax Exp ::= Int
              syntax Exp ::= Exp "+" Exp [symbol(_+_)]
              configuration <k> $PGM:Exp </k> <n> 0:KItem </n>
              rule <k> X:Exp + 0 => X:Exp </k> [label(right-zero)]
              claim <k> X:Exp => X:Exp </k> [one-path, label(reflexive)]
            endmodule
        "#;
        let prelude = embedded("prelude.md").unwrap();
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("provenance.k", source),
            "MAIN",
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![prelude],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .unwrap();

        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                check_mode: CheckMode::Proof {
                    definition_module: "MAIN".into(),
                },
                ..CompileOptions::default()
            },
        )
        .unwrap();

        assert_eq!(
            [
                artifact_digest(&artifacts.definition_kore),
                artifact_digest(&artifacts.syntax_definition_kore),
                artifact_digest(&artifacts.macros_kore),
            ],
            [
                String::from("d8d93d5451a04f4213ad94f8fdb2eba275db88249531bc08a7311d67987d1f2e",),
                String::from("2e7f3354ebe280754c47f057a728c4c03cde4ead9cc408da3f40585a62785278",),
                String::from("a78f2c566b2439463a2e7ca515bbfa3f92948506583cbadaebdd507f277542bd",),
            ],
        );
    }

    fn origin_receipts(definition: &Definition) -> Vec<serde_json::Value> {
        fn collect_term(term: &Term, receipts: &mut Vec<serde_json::Value>) {
            if let Some(origin) = term
                .metadata()
                .and_then(|metadata| metadata.origin.as_deref())
            {
                receipts.push(origin.to_value());
            }
            match term.unannotated() {
                Term::Rewrite { left, right } => {
                    collect_term(left, receipts);
                    collect_term(right, receipts);
                }
                Term::As { pattern, alias } => {
                    collect_term(pattern, receipts);
                    collect_term(alias, receipts);
                }
                Term::Sequence(items)
                | Term::Apply {
                    arguments: items, ..
                } => {
                    for item in items {
                        collect_term(item, receipts);
                    }
                }
                Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
                Term::Annotated { .. } => unreachable!(),
            }
        }

        let mut receipts = Vec::new();
        for sentence in definition
            .modules
            .iter()
            .flat_map(|module| &module.local_sentences)
        {
            if let Some(receipt) = sentence
                .attributes()
                .get(crate::provenance::ORIGIN_ATTRIBUTE)
            {
                receipts.push(receipt.clone());
            }
            match sentence {
                Sentence::Rule {
                    body,
                    requires,
                    ensures,
                    ..
                }
                | Sentence::Claim {
                    body,
                    requires,
                    ensures,
                    ..
                } => {
                    collect_term(body, &mut receipts);
                    collect_term(requires, &mut receipts);
                    collect_term(ensures, &mut receipts);
                }
                Sentence::Context { body, requires, .. }
                | Sentence::ContextAlias { body, requires, .. } => {
                    collect_term(body, &mut receipts);
                    collect_term(requires, &mut receipts);
                }
                Sentence::Configuration { body, ensures, .. } => {
                    collect_term(body, &mut receipts);
                    collect_term(ensures, &mut receipts);
                }
                _ => {}
            }
        }
        receipts
    }

    #[test]
    fn origin_records_are_deterministic_across_compiles() {
        let source = r#"
            module MAIN
              syntax Exp ::= "a" [symbol(a)]
                           | "b" [symbol(b)]
                           | "m(" Exp ")" [macro, symbol(m)]
              rule m(_X:Exp) => b
              rule m(a) => a [label(subject)]
            endmodule
        "#;
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
        let loaded = load(
            ResolvedSource::new("determinism.k", source),
            "MAIN",
            &mut resolver,
        )
        .unwrap();
        let options = CompileOptions::default();

        let (_, first, _) = transform_loaded_definition(&loaded, &options).unwrap();
        let (_, second, _) = transform_loaded_definition(&loaded, &options).unwrap();
        let first = origin_receipts(&first);
        let second = origin_receipts(&second);

        assert!(!first.is_empty());
        assert_eq!(first, second);
    }

    #[test]
    fn compiles_an_in_memory_definition_into_three_artifacts() {
        let source = r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax Exp ::= Int
            endmodule
        "#;
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
        let loaded = load(
            ResolvedSource::new("definition.k", source),
            "MAIN",
            &mut resolver,
        )
        .unwrap();

        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
        assert!(parse_definition(&artifacts.definition_kore).is_ok());
        assert!(parse_definition(&artifacts.syntax_definition_kore).is_ok());
        assert_eq!(artifacts.macros_kore, "\n");
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn configuration_variables_include_stream_variables() {
        let source = include_str!("../../tests/fixtures/reference/cli/io/io.k");
        let prelude = embedded("prelude.md").unwrap();
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("io.k", source),
            "IO",
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![prelude],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .unwrap();

        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
        assert_eq!(
            artifacts.configuration_variables,
            BTreeMap::from([
                ("IO".into(), crate::kast::Sort::new("String")),
                ("PGM".into(), crate::kast::Sort::new("Int")),
                ("STDIN".into(), crate::kast::Sort::new("String")),
            ])
        );
    }

    #[test]
    fn parses_backend_names() {
        assert_eq!("llvm".parse(), Ok(CompilationBackend::Llvm));
        assert_eq!("rust".parse(), Ok(CompilationBackend::Rust));
        assert_eq!("haskell".parse(), Ok(CompilationBackend::Rust));
        assert!("nope".parse::<CompilationBackend>().is_err());
        for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
            assert_eq!(backend.to_string().parse(), Ok(backend));
        }
    }

    #[test]
    fn rust_backend_emits_its_extension_hooks_as_hooked_symbols() {
        let source = r#"
            module MAIN
              syntax Value
              syntax Value ::= "krypto" [function, hook(KRYPTO.keccak256), symbol(krypto)]
                             | "hash" [function, hook(HASH.sha256), symbol(hash)]
                             | "secp256k1" [function, hook(SECP256K1.ecdsaRecover), symbol(secp256k1)]
            endmodule
        "#;
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
        let loaded = load(
            ResolvedSource::new("definition.k", source),
            "MAIN",
            &mut resolver,
        )
        .unwrap();

        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();

        for (symbol, hook) in [
            ("krypto", "KRYPTO.keccak256"),
            ("hash", "HASH.sha256"),
            ("secp256k1", "SECP256K1.ecdsaRecover"),
        ] {
            let symbol = crate::kompile::encode_kore_label(&crate::kast::Label::new(symbol)).name;
            assert!(
                artifacts
                    .definition_kore
                    .contains(&format!("hooked-symbol {symbol}")),
                "{symbol} was not emitted as a hooked symbol:\n{}",
                artifacts.definition_kore,
            );
            assert!(
                artifacts
                    .definition_kore
                    .contains(&format!(r#"hook{{}}("{hook}")"#)),
                "{symbol} did not retain its {hook} attribute",
            );
        }
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn emitted_symbolic_kore_internalizes_in_process() {
        let source = r#"
            module MAIN
              imports MAP
              syntax Int ::= r"[0-9]+" [token]
              syntax Exp ::= Int
              syntax Exp ::= Exp "+" Exp [symbol(_+_)]
              configuration <k> $PGM:Exp </k> <n> 0:KItem </n>
              rule <k> X:Exp + 0 => X:Exp </k> [label(right-zero)]
              claim <k> X:Exp => X:Exp </k> [one-path, label(reflexive)]
            endmodule
        "#;
        let prelude = embedded("prelude.md").unwrap();
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("definition.k", source),
            "MAIN",
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![prelude],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .unwrap();
        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                backend: CompilationBackend::Rust,
                check_mode: CheckMode::Proof {
                    definition_module: "MAIN".into(),
                },
                ..CompileOptions::default()
            },
        )
        .unwrap();
        let kore = parse_definition(&artifacts.definition_kore).unwrap();

        let backend = BackendDefinition::internalize(&kore, "MAIN")
            .expect("frontend KORE should internalize into the in-process backend");
        assert!(!backend.rewrite_theory.is_empty());
        assert_eq!(backend.reachability_claims.len(), 1);
    }
}
