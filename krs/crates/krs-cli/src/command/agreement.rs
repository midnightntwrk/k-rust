//! The agreement test of `krs check` (`KRS_CHECK_AGREEMENT=1`).
//!
//! `krs check` claims that its verdict is the verdict of the commands it stands
//! in front of. With the variable set, each check also runs those commands'
//! own entry points on the same prepared definition: [`emit`] and [`build`]
//! into a temporary directory, for every backend the check judged, and, on the
//! `native-rust` route, the run commands' definition load ([`exec::judge`]) on
//! a fresh compile. It fails with [`CommandError::CheckDisagreement`] unless
//! the check passed exactly when all of them did.
//!
//! What is compared is the composition of each command: which judgements it
//! runs and which of their findings refuse the definition. k-rust's compile is
//! a deterministic function of the Definition IR and the backend, shared by
//! every command, so under the variable the process keeps each successful
//! compile ([`CompileMemo`]) and the commands after the check reuse it instead
//! of computing it again. The collection and lowering stages every command
//! shares run once and are not compared either: a failure there fails every
//! command alike. The feature fixture gates set the variable
//! (`krs/tests/support/fixture_gate.py`), so every fixture they check is
//! tested at the cost of the commands' work beyond the compile.

use std::ffi::OsStr;
use std::fmt::Write as _;
use std::sync::{Mutex, PoisonError};

use krs_ir::measure::{Measurement, Timings};
use krs_ir_levels::DefinitionIr;
use krs_k_rust::{Backend, CompiledArtifacts, ConfigurationContext, DefinitionCompileError, Route};

use super::{
    CommandError, PreparedDefinition, build, compile_for, compile_native, emit, exec, require_route,
};

/// Whether `KRS_CHECK_AGREEMENT=1` asks for the agreement test.
pub(super) fn enabled() -> bool {
    std::env::var_os("KRS_CHECK_AGREEMENT").as_deref() == Some(OsStr::new("1"))
}

/// k-rust's compile of one prepared definition, per backend; it keeps the
/// successful compiles only under `KRS_CHECK_AGREEMENT=1`.
pub(super) struct CompileMemo(Option<Mutex<Vec<Compiled>>>);

type Compiled = (Backend, CompiledArtifacts, ConfigurationContext);

impl CompileMemo {
    pub(super) fn new() -> Self {
        Self(enabled().then(Mutex::default))
    }

    /// k-rust's compile of `definition`, which is always the same prepared
    /// definition, for `backend`.
    pub(super) fn compile(
        &self,
        definition: &DefinitionIr,
        backend: Backend,
        timings: &mut Timings,
    ) -> Result<(CompiledArtifacts, ConfigurationContext), DefinitionCompileError> {
        let Some(memo) = &self.0 else {
            return compile_for(definition, backend, timings);
        };
        let kept = memo
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .iter()
            .find(|(kept, ..)| *kept == backend)
            .map(|(_, artifacts, context)| (artifacts.clone(), context.clone()));
        if let Some(compiled) = kept {
            return Ok(compiled);
        }
        let compiled = compile_for(definition, backend, timings)?;
        memo.lock().unwrap_or_else(PoisonError::into_inner).push((
            backend,
            compiled.0.clone(),
            compiled.1.clone(),
        ));
        Ok(compiled)
    }
}

/// Runs the commands a check with `backend` judges and compares their verdicts
/// with the check's, `checked` (the check's error text on failure).
pub(super) fn verify(
    prepared: &PreparedDefinition,
    backend: Option<Backend>,
    checked: Result<(), String>,
) -> Result<(), CommandError> {
    let scratch = tempfile::Builder::new()
        .prefix("krs-check-agreement-")
        .tempdir()
        .map_err(|source| CommandError::Io {
            path: std::env::temp_dir(),
            source,
        })?;
    let emitted = emit(
        prepared,
        &scratch.path().join("emit-k"),
        &mut Measurement::disabled(),
    );
    let mut verdicts = vec![("krs emit-k".to_owned(), emitted.map(drop))];
    // The commands the check claims to predict: `build` on the backend it
    // names, or on every backend `build` takes.
    let backends = backend.map_or_else(|| Backend::ALL.to_vec(), |backend| vec![backend]);
    for backend in backends {
        let output = scratch.path().join(backend.as_str());
        verdicts.push((
            format!("krs build --backend {}", backend.as_str()),
            build(prepared, backend, &output, &mut Measurement::disabled()).map(drop),
        ));
        if Route::native(backend) == Route::NativeRust {
            let mut timings = Timings::disabled();
            let load = require_route(prepared.lowered.definition(), Route::NativeRust)
                .and_then(|()| compile_native(prepared, backend, &mut timings))
                .and_then(|(artifacts, context, _)| {
                    exec::judge(prepared, artifacts, context, &mut timings)
                });
            verdicts.push((
                "the definition load of krs run, search, and prove".to_owned(),
                load,
            ));
        }
    }
    let accepted = verdicts.iter().all(|(_, verdict)| verdict.is_ok());
    if accepted == checked.is_ok() {
        return Ok(());
    }
    let mut message = match checked {
        Ok(()) => {
            "KRS_CHECK_AGREEMENT: krs check passed, but a command it judges refuses the definition:"
                .to_owned()
        }
        Err(error) => format!(
            "KRS_CHECK_AGREEMENT: krs check failed ({error}), but every command it judges accepts the definition:"
        ),
    };
    for (command, verdict) in verdicts {
        match verdict {
            Ok(()) => write!(message, "\n  {command}: accepted"),
            Err(error) => write!(message, "\n  {command}: refused: {error}"),
        }
        .expect("writing to a String cannot fail");
    }
    Err(CommandError::CheckDisagreement(message))
}
