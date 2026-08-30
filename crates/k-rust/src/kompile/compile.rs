//! Host-independent orchestration of the ordered K frontend compilation pipeline.

use std::{fmt, str::FromStr};

use crate::{
    definition::{
        ResolvedDefinition, StructuralCheckBackend, StructuralCheckOptions,
        checks::check_definition_with_options, expand_configurations,
    },
    diagnostic::{Diagnostic, Severity},
    kore::printer::Printer as KorePrinter,
    outer::LoadedDefinition,
};

use super::{
    ModuleToKoreOptions, add_cool_like_attributes, add_implicit_computation_cell,
    add_semantics_module, add_sort_injections_to_definition, check_simplification_rules,
    concretize_cells, constant_fold, expand_macros, generate_sort_predicate_rules,
    generate_sort_predicate_syntax, generate_sort_projections, guard_or_patterns,
    minimize_term_construction, module_to_kore_from_resolved_with_options, number_sentences,
    propagate_macro_attributes, remove_unit, resolve_anon_vars, resolve_comm, resolve_config_var,
    resolve_contexts, resolve_fresh_config_constants, resolve_fresh_constants, resolve_fun,
    resolve_function_with_config, resolve_heat_cool_attributes, resolve_io, resolve_semantic_casts,
    resolve_strict, rust_backend_hook_namespaces, subsort_kitem,
};

/// Backend whose KORE input should be generated.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CompilationBackend {
    Llvm,
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

    fn structural_check_options(self) -> StructuralCheckOptions {
        match self {
            Self::Llvm => StructuralCheckOptions::default(),
            Self::Rust => StructuralCheckOptions {
                symbolic: true,
                backend: StructuralCheckBackend::Rust,
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
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            backend: CompilationBackend::Rust,
            kore_width: 100,
            default_claims_to_all_path: false,
            hook_namespaces: None,
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
    ($name:literal, $result:expr) => {
        $result.map_err(|error| {
            let message = error.to_string();
            CompileError::from_diagnostics($name, message, error.diagnostics)
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
    // Loader-produced definitions are already expanded, while structured embedders can construct
    // the public LoadedDefinition fields directly. Normalize both entry paths before checks.
    let definition = stage(
        "expand structured configurations",
        expand_configurations(&loaded.definition),
    )?;
    let resolved = stage(
        "resolve structured configurations",
        ResolvedDefinition::resolve(&definition),
    )?;
    let diagnostics = stage(
        "definition checks",
        check_definition_with_options(&resolved, options.backend.structural_check_options()),
    )?;
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

    let definition = diagnostic_stage!("resolve commutative rules", resolve_comm(&definition));
    let definition = diagnostic_stage!("resolve I/O streams", resolve_io(&definition));
    let definition = diagnostic_stage!("resolve local functions", resolve_fun(&definition));
    let definition = diagnostic_stage!(
        "resolve function configuration",
        resolve_function_with_config(&definition)
    );
    let definition = diagnostic_stage!("resolve strictness", resolve_strict(&definition));
    let definition = resolve_anon_vars(&definition);
    let definition = diagnostic_stage!("resolve contexts", resolve_contexts(&definition));
    let definition = number_sentences(&definition);
    let definition = diagnostic_stage!(
        "resolve heat/cool attributes",
        resolve_heat_cool_attributes(&definition)
    );
    let definition = resolve_semantic_casts(&definition);
    let definition = stage("add KItem subsorts", subsort_kitem(&definition))?;
    let definition = diagnostic_stage!("constant folding", constant_fold(&definition));
    let definition = stage(
        "propagate macro attributes",
        propagate_macro_attributes(&definition),
    )?;
    let definition = stage("guard or-patterns", guard_or_patterns(&definition))?;
    let (definition, fresh_config_count) = diagnostic_stage!(
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
    let definition = diagnostic_stage!("expand macros", expand_macros(&definition));
    let definition = stage(
        "add implicit computation cell",
        add_implicit_computation_cell(&definition),
    )?;
    let definition = diagnostic_stage!(
        "resolve fresh constants",
        resolve_fresh_constants(&definition, fresh_config_count)
    );
    let definition = stage(
        "regenerate sort predicate syntax",
        generate_sort_predicate_syntax(&definition),
    )?;
    let definition = stage(
        "regenerate sort projections",
        generate_sort_projections(&definition),
    )?;
    let definition = diagnostic_stage!(
        "check simplification rules",
        check_simplification_rules(&definition)
    );
    let definition = stage("finalize KItem subsorts", subsort_kitem(&definition))?;
    let definition = diagnostic_stage!("concretize cells", concretize_cells(&definition));
    // Coverage instrumentation and the optional unsafe-anywhere removal are identity stages
    // because neither optional mode is exposed by the frontend API yet.
    let definition = add_semantics_module(&definition);
    let definition = resolve_config_var(&definition);
    let definition = add_cool_like_attributes(&definition);
    let definition = generate_sort_predicate_rules(&definition);
    let definition = number_sentences(&definition);
    let definition = stage(
        "add sort injections",
        add_sort_injections_to_definition(&definition),
    )?;
    let definition = stage("remove units", remove_unit(&definition))?;
    let definition = stage(
        "minimize term construction",
        minimize_term_construction(&definition),
    )?;
    let resolved = stage(
        "resolve transformed definition",
        ResolvedDefinition::resolve(&definition),
    )?;
    let generated = stage(
        "emit KORE",
        module_to_kore_from_resolved_with_options(
            &resolved,
            &definition.main_module,
            ModuleToKoreOptions {
                generate_map_ceil_axioms: options.backend == CompilationBackend::Rust,
                default_claims_to_all_path: options.default_claims_to_all_path,
                hook_namespaces: options
                    .hook_namespaces
                    .clone()
                    .unwrap_or_else(|| options.backend.default_hook_namespaces()),
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
    })
}

fn with_newline(mut text: String) -> String {
    if !text.ends_with('\n') {
        text.push('\n');
    }
    text
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "z3-inference")]
    use k_rust_backend::definition::BackendDefinition;

    #[cfg(feature = "z3-inference")]
    use crate::{
        builtin::embedded,
        outer::{LoadOptions, load_with_options},
    };
    use crate::{
        kore::parser::parse_definition,
        outer::{ResolvedSource, load},
    };

    use super::*;

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

    #[test]
    fn parses_backend_names() {
        assert_eq!("llvm".parse(), Ok(CompilationBackend::Llvm));
        assert_eq!("rust".parse(), Ok(CompilationBackend::Rust));
        assert_eq!("haskell".parse(), Ok(CompilationBackend::Rust));
        assert!("nope".parse::<CompilationBackend>().is_err());
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
