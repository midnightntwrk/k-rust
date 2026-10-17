//! Mutant validation: kink-patch application followed by k-rust compilation.
//!
//! A mutant is compiled from the relinked loaded definition (`Mutant::to_loaded`),
//! not re-loaded: a loaded definition cannot be fed back through `load_structured`.
//! A KRS route that binds a pre-load definition with the embedded prelude waits
//! for the Z3-free structured compile (KRS-owned `z3-free-structured-compile`):
//! without Z3 the prelude does not load.
//!
//! Compiling ahead (re-pin L1-3, [`NativeValidator::compile_ahead`]) is the only stage of kink
//! that runs on several threads. Relinking and compiling are the only steps k-rust documents
//! as independent of the thread: they read only their arguments and no process-wide input,
//! several threads may run them at once on one shared loaded definition, each call returns what
//! the same call returns alone on one thread, and every compile stage runs on a stack sized from
//! the definition, so the artifacts do not depend on the calling thread's stack (k-rust 501f18b9
//! `docs/compatibility.md`, "Concurrency"; `crates/k-rust/tests/compile_concurrency.rs`). A
//! compile refusal can depend on the calling thread's stack (a pass that needs a segment past
//! the stack limit, "Compile"), so only a successful compile is taken ahead: every refusal comes
//! from the calling thread, as without compiling ahead. Everything after compile that loads a
//! definition or runs the simplifier (the consistency check, every backend build, every
//! execution) depends on the stack of the thread that runs it and on what other threads hold of
//! the simplifier's process-wide stack budget ("Execute"), and stays on the calling thread, one
//! mutant at a time: callers compile a chunk ahead and join every worker before any of it runs.

use std::{
    collections::BTreeMap,
    fmt,
    num::NonZeroUsize,
    panic::{AssertUnwindSafe, catch_unwind},
    sync::{
        Mutex, OnceLock, PoisonError,
        atomic::{AtomicUsize, Ordering},
    },
};

use k_rust::{
    definition::Definition,
    kompile::{CompileError, CompileOptions, CompiledKoreArtifacts, compile_loaded_definition},
    outer::{LoadError, LoadedDefinition},
};
use kink_patch::{Baseline, Patch, PatchFailure, SentenceOrigin, SentenceRef, apply};

/// Typed failure to compile the native baseline. No staged output is published.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NativeFailure {
    Compilation { stage: &'static str, detail: String },
}

impl fmt::Display for NativeFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Compilation { stage, detail } => {
                write!(
                    formatter,
                    "native compilation stage {stage:?} failed: {detail}"
                )
            }
        }
    }
}

impl std::error::Error for NativeFailure {}

/// An immutable loaded baseline and the compile options every side uses.
///
/// It also holds the memoised result of [`NativeValidator::compile_baseline`]. A clone
/// carries the result its source already holds, which is the compile of the same
/// baseline under the same options. It holds the mutants compiled ahead
/// ([`NativeValidator::compile_ahead`]) too; a clone starts without them.
#[derive(Debug)]
pub struct NativeValidator {
    baseline: Baseline,
    options: CompileOptions,
    compiled_baseline: OnceLock<Result<ValidatedDefinition, NativeFailure>>,
    ahead: Mutex<Vec<Ahead>>,
}

impl Clone for NativeValidator {
    fn clone(&self) -> Self {
        Self {
            baseline: self.baseline.clone(),
            options: self.options.clone(),
            compiled_baseline: self.compiled_baseline.clone(),
            ahead: Mutex::new(Vec::new()),
        }
    }
}

/// A mutant compiled ahead of its turn ([`NativeValidator::compile_ahead`]): its patch, its
/// compiled definition and how many more [`NativeValidator::validate`] calls take it.
#[derive(Debug)]
struct Ahead {
    patch: Patch,
    compiled: ValidatedDefinition,
    uses: usize,
}

/// The native stack and heap one compile is estimated to take besides its definition, for the
/// memory cap of [`NativeValidator::compile_workers`].
const COMPILE_BASE_BYTES: u64 = 64 << 20;

/// The bytes one compile is estimated to take per byte of the baseline's `definition.kore`.
const COMPILE_BYTES_PER_KORE_BYTE: u64 = 32;

impl NativeValidator {
    /// Captures `baseline`; its caller owns prelude policy.
    pub const fn bind(baseline: Baseline, options: CompileOptions) -> Self {
        Self {
            baseline,
            options,
            compiled_baseline: OnceLock::new(),
            ahead: Mutex::new(Vec::new()),
        }
    }

    pub const fn baseline(&self) -> &Baseline {
        &self.baseline
    }

    /// Compiles the unpatched baseline, once per validator.
    ///
    /// The first call compiles; every later call, on this validator or on a clone made
    /// after it, returns a clone of that result, success or failure. The memo has no key
    /// of its own because the validator is the key: its baseline and compile options are
    /// fixed at [`NativeValidator::bind`] and never change. Returning the memo instead of
    /// compiling again rests on k-rust compile determinism (the same loaded definition
    /// under the same options compiles to the same artifacts), a premise replay already
    /// takes. Mutant compiles ([`NativeValidator::validate`]) are never memoised, but a
    /// caller may compile some ahead ([`NativeValidator::compile_ahead`]).
    pub fn compile_baseline(&self) -> Result<ValidatedDefinition, NativeFailure> {
        self.compiled_baseline
            .get_or_init(|| self.compile_baseline_uncached())
            .clone()
    }

    /// How many threads [`NativeValidator::compile_ahead`] uses when `requested` are asked
    /// for: at most `requested`, the host's available parallelism, and the memory cap, and at
    /// least 1.
    ///
    /// The memory cap gives compiles half of the process's allowance (k-rust's
    /// `Allowance::of_process`: the smallest of the cgroup's `memory.max`, `RLIMIT_AS` or
    /// `RLIMIT_DATA` and physical memory), at an estimated 64 MiB plus 32 bytes per byte of the
    /// baseline's `definition.kore` for each compile. That is about twice what one more worker
    /// was measured to take (re-pin L1-3: 12 MiB plus about 25 bytes per byte, 31 MiB on
    /// `examples/imp`) and matches k-rust's 0.55-1.5 GiB per KEVM compile. k-rust promises no
    /// wall time or peak memory under concurrency, so the cap bounds memory; it never changes
    /// a result. A baseline that does not compile gets 1.
    pub fn compile_workers(&self, requested: usize) -> usize {
        if requested <= 1 {
            return 1;
        }
        let Ok(baseline) = self
            .compiled_baseline
            .get_or_init(|| self.compile_baseline_uncached())
        else {
            return 1;
        };
        let kore = u64::try_from(baseline.artifacts.definition_kore.len()).unwrap_or(u64::MAX);
        let per_compile = COMPILE_BYTES_PER_KORE_BYTE
            .saturating_mul(kore)
            .saturating_add(COMPILE_BASE_BYTES);
        let allowance = k_rust::k_rust_backend::allowance::Allowance::of_process().bytes();
        let cap = usize::try_from(allowance / 2 / per_compile).unwrap_or(usize::MAX);
        let threads = std::thread::available_parallelism().map_or(1, NonZeroUsize::get);
        requested.min(threads).min(cap).max(1)
    }

    /// Applies, relinks and compiles `patches` on up to
    /// [`compile_workers(workers)`](NativeValidator::compile_workers) threads, joins them all,
    /// and keeps each mutant that compiles for the
    /// [`NativeValidator::validate`] calls of an equal patch (one per time the patch is given;
    /// a patch already kept gains those calls without compiling again).
    ///
    /// With one worker it does nothing: every mutant then compiles in its `validate` call, as
    /// without compiling ahead. A patch that is refused (by kink-patch, at relinking or by the
    /// compiler) is not kept, and neither is one whose compile panics: its `validate` call
    /// compiles it again on the calling thread, which then gives today's refusal (or panic) at
    /// today's point. What is kept equals what `validate` would compile on the calling thread
    /// (see the module documentation), so compiling ahead changes no artifact, status or
    /// report; the premise is the one [`NativeValidator::compile_baseline`] and replay take.
    ///
    /// Memory grows with what is kept: callers compile a bounded chunk ahead, validate it, and
    /// drop the rest with [`NativeValidator::discard_ahead`].
    pub fn compile_ahead(&self, patches: &[Patch], workers: usize) {
        let workers = self.compile_workers(workers);
        if workers <= 1 {
            return;
        }
        let mut distinct: Vec<(&Patch, usize)> = Vec::new();
        {
            let mut held = self.ahead.lock().unwrap_or_else(PoisonError::into_inner);
            for patch in patches {
                if let Some(kept) = held.iter_mut().find(|kept| kept.patch == *patch) {
                    kept.uses += 1;
                } else if let Some((_, uses)) = distinct.iter_mut().find(|(p, _)| *p == patch) {
                    *uses += 1;
                } else {
                    distinct.push((patch, 1));
                }
            }
        }
        let compiled = distinct
            .iter()
            .map(|_| OnceLock::new())
            .collect::<Vec<OnceLock<ValidatedDefinition>>>();
        let next = AtomicUsize::new(0);
        std::thread::scope(|scope| {
            for _ in 0..workers.min(distinct.len()) {
                scope.spawn(|| {
                    loop {
                        let index = next.fetch_add(1, Ordering::Relaxed);
                        let Some((patch, _)) = distinct.get(index) else {
                            break;
                        };
                        if let Ok(Ok(side)) = catch_unwind(AssertUnwindSafe(|| self.compile(patch)))
                        {
                            let _ = compiled[index].set(side);
                        }
                    }
                });
            }
        });
        let mut held = self.ahead.lock().unwrap_or_else(PoisonError::into_inner);
        for ((patch, uses), side) in distinct.into_iter().zip(compiled) {
            if let Some(compiled) = side.into_inner() {
                held.push(Ahead {
                    patch: patch.clone(),
                    compiled,
                    uses,
                });
            }
        }
    }

    /// Drops every mutant compiled ahead that no `validate` call has taken yet.
    pub fn discard_ahead(&self) {
        self.ahead
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clear();
    }

    /// The mutant of an equal patch compiled ahead, if one is kept, counting this use.
    fn take_ahead(&self, patch: &Patch) -> Option<ValidatedDefinition> {
        let mut held = self.ahead.lock().unwrap_or_else(PoisonError::into_inner);
        let at = held.iter().position(|kept| kept.patch == *patch)?;
        held[at].uses -= 1;
        Some(if held[at].uses == 0 {
            held.remove(at).compiled
        } else {
            held[at].compiled.clone()
        })
    }

    fn compile_baseline_uncached(&self) -> Result<ValidatedDefinition, NativeFailure> {
        let loaded = self.baseline.loaded();
        let artifacts =
            self.compile_loaded(loaded)
                .map_err(|error| NativeFailure::Compilation {
                    stage: error.stage,
                    detail: error
                        .diagnostics
                        .iter()
                        .fold(error.message, |detail, diagnostic| {
                            format!("{detail}; {}", diagnostic.message)
                        }),
                })?;
        Ok(ValidatedDefinition {
            definition: loaded.definition().clone(),
            artifacts,
            options: self.options.clone(),
            origins: None,
        })
    }

    /// Applies `patch` to the baseline and compiles the mutant.
    ///
    /// Nothing escapes on failure: a rejection holds only diagnostics, and a
    /// patched definition is published only inside a [`ValidatedDefinition`].
    ///
    /// A mutant of an equal patch compiled ahead ([`NativeValidator::compile_ahead`]) is
    /// returned instead of compiling again; it is the same definition.
    pub fn validate(&self, patch: &Patch) -> Result<ValidatedDefinition, MutantRejection> {
        if let Some(side) = self.take_ahead(patch) {
            return Ok(side);
        }
        self.compile(patch)
    }

    /// Applies `patch` to the baseline, relinks and compiles the mutant, on this thread.
    fn compile(&self, patch: &Patch) -> Result<ValidatedDefinition, MutantRejection> {
        let mutant = apply(&self.baseline, patch).map_err(MutantRejection::Patch)?;
        let loaded = mutant
            .to_loaded(&self.baseline)
            .map_err(MutantRejection::Relink)?;
        let artifacts = self
            .compile_loaded(&loaded)
            .map_err(MutantRejection::Compilation)?;
        Ok(ValidatedDefinition {
            definition: loaded.into_definition(),
            artifacts,
            options: self.options.clone(),
            origins: Some(mutant.origins().clone()),
        })
    }

    fn compile_loaded(
        &self,
        loaded: &LoadedDefinition,
    ) -> Result<CompiledKoreArtifacts, CompileError> {
        compile_loaded_definition(loaded, self.options.clone())
    }
}

/// Why a patch did not yield a compiled mutant. It carries no definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MutantRejection {
    /// kink-patch rejected the patch; nothing was compiled.
    Patch(PatchFailure),
    /// k-rust rejected the patched definition; the error holds its stage
    /// and diagnostics only.
    Compilation(CompileError),
    /// k-rust refused to rebuild the patched definition at the loaded
    /// stage (`LoadedDefinition::with_definition`); nothing was compiled.
    Relink(LoadError),
}

impl fmt::Display for MutantRejection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Patch(failure) => write!(formatter, "patch rejected: {failure}"),
            Self::Compilation(error) => error.fmt(formatter),
            Self::Relink(error) => write!(formatter, "relink rejected: {error}"),
        }
    }
}

impl std::error::Error for MutantRejection {}

/// A compiled baseline or mutant. It is only built after compilation succeeded.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidatedDefinition {
    definition: Definition,
    artifacts: CompiledKoreArtifacts,
    options: CompileOptions,
    origins: Option<BTreeMap<SentenceRef, SentenceOrigin>>,
}

impl ValidatedDefinition {
    /// Execution-relevant identity of the four compiled KORE fields.
    pub fn kore_sha256(&self) -> kink_patch::Sha256Digest {
        let value = serde_json::json!({
            "definition": self.artifacts.definition_kore,
            "macros": self.artifacts.macros_kore,
            "rewrite_order": self.artifacts.execution_rewrite_order,
            "syntax": self.artifacts.syntax_definition_kore,
        });
        kink_patch::payload_digest(
            kink_patch::COMPILED_KORE_DOMAIN,
            kink_patch::canonical_json(&value).as_bytes(),
        )
    }

    /// The loaded source definition that was compiled.
    pub const fn definition(&self) -> &Definition {
        &self.definition
    }

    pub const fn artifacts(&self) -> &CompiledKoreArtifacts {
        &self.artifacts
    }

    /// Exact backend, KORE width, claims mode, and hook namespace profile used for lowering.
    pub const fn compile_options(&self) -> &CompileOptions {
        &self.options
    }

    /// For a mutant, where each of its sentences came from; `None` for the baseline.
    pub const fn origins(&self) -> Option<&BTreeMap<SentenceRef, SentenceOrigin>> {
        self.origins.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::support;
    use k_rust::{
        definition::Sentence,
        kast::{Sort, Term},
    };
    use kink_patch::{Edit, TermRef};

    fn held(validator: &NativeValidator) -> Vec<(Patch, usize)> {
        validator
            .ahead
            .lock()
            .unwrap()
            .iter()
            .map(|kept| (kept.patch.clone(), kept.uses))
            .collect()
    }

    /// Re-pin L1-3: a mutant compiled ahead is the mutant its `validate` call compiles alone, a
    /// patch given twice is compiled once and taken twice, a refused patch is not kept (its
    /// `validate` call gives the refusal from the calling thread), one worker keeps nothing,
    /// `discard_ahead` drops what is left, and a clone starts with nothing kept.
    #[test]
    fn compiled_ahead_mutants_are_their_own_compiles_and_refusals_are_not_kept() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let validator =
                    NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
                let baseline = validator.baseline();
                let at = support::rule(baseline, "COUNTER.branch");
                let false_term = Term::Token {
                    token: "false".into(),
                    sort: Sort::new("Bool"),
                };
                let mut replacement = baseline.sentence(&at).unwrap().clone();
                let Sentence::Rule { requires, .. } = &mut replacement else {
                    panic!("a rule");
                };
                *requires = false_term.clone();
                let compiles = Patch::new(vec![Edit::ReplaceSentence {
                    at: at.clone(),
                    replacement,
                }])
                .unwrap();
                // The requires clause is `B`, not `false`: kink-patch refuses the edit.
                let refused = Patch::new(vec![Edit::ReplaceTerm {
                    at: TermRef::new(at, [1]),
                    expected: false_term.clone(),
                    replacement: false_term,
                }])
                .unwrap();
                let alone = validator.validate(&compiles);
                let refusal = validator.validate(&refused);
                assert!(alone.is_ok(), "{alone:?}");
                assert!(refusal.is_err());

                validator.compile_ahead(std::slice::from_ref(&compiles), 1);
                assert!(
                    held(&validator).is_empty(),
                    "one worker compiles nothing ahead"
                );
                assert!(
                    validator.compile_workers(3) >= 2,
                    "the test host allows two compile workers"
                );

                validator.compile_ahead(&[compiles.clone(), refused.clone(), compiles.clone()], 3);
                assert_eq!(held(&validator), vec![(compiles.clone(), 2)]);
                assert_eq!(validator.validate(&compiles), alone);
                assert_eq!(held(&validator), vec![(compiles.clone(), 1)]);
                assert_eq!(validator.validate(&refused), refusal);
                assert_eq!(validator.clone().validate(&compiles), alone);
                assert_eq!(
                    held(&validator),
                    vec![(compiles.clone(), 1)],
                    "a clone holds none"
                );
                assert_eq!(validator.validate(&compiles), alone);
                assert!(held(&validator).is_empty());

                validator.compile_ahead(std::slice::from_ref(&compiles), 3);
                validator.compile_ahead(std::slice::from_ref(&compiles), 3);
                assert_eq!(
                    held(&validator),
                    vec![(compiles.clone(), 2)],
                    "kept, not recompiled"
                );
                validator.discard_ahead();
                assert!(held(&validator).is_empty());
                assert_eq!(validator.validate(&compiles), alone);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
