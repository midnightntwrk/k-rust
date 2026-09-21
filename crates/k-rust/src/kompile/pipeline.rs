//! Table-driven execution support for definition transformation passes.

use std::{convert::Infallible, fmt};

use crate::{
    definition::{Definition, DefinitionViews, ResolveError, ResolvedDefinition},
    diagnostic::Diagnostic,
    provenance::{GeneratingPass, record_generated_origins},
    timings::PhaseTimings,
};

use super::{CompileError, CompileOptions};

/// The common error carried across a pipeline stage boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PassError {
    pub message: String,
    pub diagnostics: Vec<Diagnostic>,
}

impl PassError {
    pub(crate) fn message(error: impl fmt::Display) -> Self {
        Self {
            message: error.to_string(),
            diagnostics: Vec::new(),
        }
    }
}

impl From<String> for PassError {
    fn from(message: String) -> Self {
        Self {
            message,
            diagnostics: Vec::new(),
        }
    }
}

impl From<ResolveError> for PassError {
    fn from(error: ResolveError) -> Self {
        Self::message(error)
    }
}

impl From<Infallible> for PassError {
    fn from(error: Infallible) -> Self {
        match error {}
    }
}

macro_rules! diagnostics_error {
    ($($error:path),+ $(,)?) => {$ (
        impl From<$error> for PassError {
            fn from(error: $error) -> Self {
                Self {
                    message: error.to_string(),
                    diagnostics: error.diagnostics,
                }
            }
        }
    )+ };
}

diagnostics_error!(
    super::ResolveCommError,
    super::ResolveIoError,
    super::ResolveFunError,
    super::ResolveFunctionWithConfigError,
    super::ResolveStrictError,
    super::ResolveContextsError,
    super::ResolveHeatCoolError,
    super::ConstantFoldingError,
    super::ResolveFreshConfigConstantsError,
    super::ResolveFreshConstantsError,
    super::ExpandMacrosError,
    super::CheckSimplificationError,
    super::ConcretizeCellsError,
);

macro_rules! display_error {
    ($($error:path),+ $(,)?) => {$ (
        impl From<$error> for PassError {
            fn from(error: $error) -> Self {
                Self::message(error)
            }
        }
    )+ };
}

display_error!(
    super::SubsortKItemError,
    super::SortInjectionError,
    super::TermConversionError,
);

/// Data produced by one stage for a later stage.
#[derive(Default)]
pub(crate) struct PipelineState {
    pub fresh_config_count: Option<usize>,
}

struct Current {
    definition: Definition,
    resolved: std::sync::OnceLock<Result<ResolvedDefinition, ResolveError>>,
}

impl Current {
    fn new(definition: Definition) -> Self {
        Self {
            definition,
            resolved: std::sync::OnceLock::new(),
        }
    }

    fn into_definition(self) -> Definition {
        self.definition
    }
}

/// The immutable input and lazily resolved views for one stage.
pub(crate) struct PassInput<'a> {
    pub definition: &'a Definition,
    current: &'a Current,
}

impl<'a> PassInput<'a> {
    fn new(current: &'a Current) -> Self {
        Self {
            definition: &current.definition,
            current,
        }
    }

    pub fn resolved(&self) -> Result<&ResolvedDefinition, PassError> {
        self.resolved_raw().map_err(PassError::message)
    }

    pub(crate) fn resolved_raw(&self) -> Result<&ResolvedDefinition, &ResolveError> {
        self.current
            .resolved
            .get_or_init(|| ResolvedDefinition::resolve(self.definition))
            .as_ref()
    }

    // A pass asks for this once and shares the returned memo among all of its algorithms.
    // Keeping the memo by value avoids a self-referential `Current`; resolution itself remains
    // cached for the full stage.
    pub fn views(&self) -> Result<DefinitionViews<'_>, PassError> {
        Ok(self.resolved()?.views())
    }
}

pub(crate) type PassFn = fn(&PassInput<'_>, &mut PipelineState) -> Result<Definition, PassError>;

#[derive(Clone, Copy)]
pub(crate) enum Provenance {
    None,
    Driver(GeneratingPass),
    Internal(&'static [GeneratingPass]),
}

pub(crate) struct Stage {
    pub name: &'static str,
    pub call: &'static str,
    pub run: PassFn,
    pub provenance: Provenance,
    pub behavior: &'static str,
}

pub(crate) fn run_stages(
    stages: &[Stage],
    start: Definition,
    state: &mut PipelineState,
    options: &CompileOptions,
    timings: &mut PhaseTimings,
) -> Result<Definition, CompileError> {
    let mut current = Current::new(start);
    for stage in stages {
        let output = timings.time(stage.name, || {
            let input = PassInput::new(&current);
            let output = (stage.run)(&input, state).map_err(|error| CompileError {
                stage: stage.name,
                message: error.message,
                diagnostics: options.diagnostics.apply(error.diagnostics),
            })?;
            Ok(match stage.provenance {
                Provenance::Driver(pass) => {
                    record_generated_origins(&current.definition, output, pass)
                }
                Provenance::None | Provenance::Internal(_) => output,
            })
        })?;
        current = Current::new(output);
    }
    Ok(current.into_definition())
}

pub(crate) fn run_standalone<E>(
    definition: &Definition,
    run: impl FnOnce(&PassInput<'_>, &mut PipelineState) -> Result<Definition, E>,
    provenance: Option<GeneratingPass>,
) -> Result<Definition, E> {
    let current = Current::new(definition.clone());
    let input = PassInput::new(&current);
    let mut state = PipelineState::default();
    let output = run(&input, &mut state)?;
    Ok(match provenance {
        Some(pass) => record_generated_origins(definition, output, pass),
        None => output,
    })
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use crate::{
        definition::{Definition, FlatModule},
        diagnostic::{Diagnostic, DiagnosticCode},
    };

    use super::*;

    fn definition() -> Definition {
        Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: Vec::new(),
                attributes: Default::default(),
            }],
            attributes: Default::default(),
        }
    }

    #[test]
    fn pass_input_resolves_once() {
        let current = Current::new(definition());
        let input = PassInput::new(&current);
        assert!(std::ptr::eq(
            input.resolved().unwrap(),
            input.resolved().unwrap()
        ));
    }

    #[test]
    fn pass_error_preserves_message_and_diagnostics() {
        let diagnostic = Diagnostic {
            severity: crate::diagnostic::Severity::Error,
            code: DiagnosticCode::InvalidAttribute,
            message: "bad attribute".into(),
            source: None,
            location: None,
        };
        let error = super::super::ResolveCommError {
            diagnostics: vec![diagnostic.clone()],
        };
        let converted = PassError::from(error);
        assert_eq!(
            converted.message,
            "commutative simplification resolution produced 1 errors"
        );
        assert_eq!(converted.diagnostics, vec![diagnostic]);
    }

    #[test]
    fn run_stages_names_the_failing_stage() {
        fn fail(_: &PassInput<'_>, _: &mut PipelineState) -> Result<Definition, PassError> {
            Err(PassError::from("failure".to_owned()))
        }
        let stages = [Stage {
            name: "named stage",
            call: "fail",
            run: fail,
            provenance: Provenance::None,
            behavior: "validation",
        }];
        let error = run_stages(
            &stages,
            definition(),
            &mut PipelineState::default(),
            &CompileOptions::default(),
            &mut PhaseTimings::default(),
        )
        .unwrap_err();
        assert_eq!(error.stage, "named stage");
        assert_eq!(error.message, "failure");
    }

    #[test]
    fn run_standalone_runs_one_pass() {
        static CALLS: AtomicUsize = AtomicUsize::new(0);
        let definition = definition();
        let output = run_standalone(
            &definition,
            |input, _| {
                CALLS.fetch_add(1, Ordering::Relaxed);
                Ok::<_, Infallible>(input.definition.clone())
            },
            None,
        )
        .unwrap();
        assert_eq!(CALLS.swap(0, Ordering::Relaxed), 1);
        assert_eq!(output, definition);
    }
}
