//! Mutant validation: kink-patch application followed by k-rust compilation.
//!
//! A mutant is compiled from the relinked loaded definition (`Mutant::to_loaded`),
//! not re-loaded: a loaded definition cannot be fed back through `load_structured`.
//! A KRS route that binds a pre-load definition with the embedded prelude waits
//! for the Z3-free structured compile (KRS-owned `z3-free-structured-compile`):
//! without Z3 the prelude does not load.
//!
//! Compiling ahead (re-pin L1-3, [`NativeValidator::compile_ahead`]) is the only stage of kink
//! that runs on several threads, and a worker thread runs exactly two steps: relinking the
//! applied mutant ([`Mutant::to_loaded`], k-rust's `LoadedDefinition::with_definition`) and
//! compiling it (`compile_loaded_definition`). They are the only steps k-rust documents as
//! independent of the thread: they read only their arguments and no process-wide input, several
//! threads may run them at once on one shared loaded definition, each call returns what the same
//! call returns alone on one thread, and every compile stage runs on a stack sized from the
//! definition, so the artifacts do not depend on the calling thread's stack (k-rust 501f18b9
//! `docs/compatibility.md`, "Concurrency"; `crates/k-rust/tests/compile_concurrency.rs`).
//! Applying the patch (kink-patch [`apply`]) is not among them and runs on the calling thread, in
//! the order the patches are given: it types each edited rule with k-rust's
//! `SentenceTyper::typing_in`, whose recursion over the rule's terms is not stack-guarded and
//! which "Concurrency" does not cover, so on a worker's default stack a deep edited rule would
//! overflow it and abort the process where the calling thread's large stack succeeds (review
//! L1-3-1 D1). A compile refusal can depend on the calling thread's stack (a pass that needs a
//! segment past the stack limit, "Compile"), so only a successful compile is taken ahead: every
//! refusal comes from the calling thread, as without compiling ahead. Everything after compile
//! that loads a definition or runs the simplifier (the consistency check, every backend build,
//! every execution) depends on the stack of the thread that runs it and on what other threads
//! hold of the simplifier's process-wide stack budget ("Execute"), and stays on the calling
//! thread, one mutant at a time: callers compile a chunk ahead and join every worker before any
//! of it runs.

use std::{
    collections::BTreeMap,
    fmt,
    num::NonZeroUsize,
    panic::{AssertUnwindSafe, catch_unwind},
    sync::{
        Mutex, OnceLock, PoisonError,
        atomic::{AtomicU64, AtomicUsize, Ordering},
    },
};

use k_rust::{
    definition::Definition,
    kompile::{CompileError, CompileOptions, CompiledKoreArtifacts, compile_loaded_definition},
    outer::{LoadError, LoadedDefinition},
};
use kink_patch::{Baseline, Mutant, Patch, PatchFailure, SentenceOrigin, SentenceRef, apply};

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
    next_chunk: AtomicU64,
}

impl Clone for NativeValidator {
    fn clone(&self) -> Self {
        Self {
            baseline: self.baseline.clone(),
            options: self.options.clone(),
            compiled_baseline: self.compiled_baseline.clone(),
            ahead: Mutex::new(Vec::new()),
            next_chunk: AtomicU64::new(0),
        }
    }
}

/// A mutant compiled ahead of its turn ([`NativeValidator::compile_ahead`]): its patch, its
/// compiled definition and, for each chunk that asked for it, how many more
/// [`NativeValidator::validate`] calls that chunk counts on taking it.
#[derive(Debug)]
struct Ahead {
    patch: Patch,
    compiled: ValidatedDefinition,
    uses: Vec<(u64, usize)>,
}

impl Ahead {
    fn add_uses(&mut self, chunk: u64, uses: usize) {
        if let Some((_, count)) = self.uses.iter_mut().find(|(owner, _)| *owner == chunk) {
            *count += uses;
        } else {
            self.uses.push((chunk, uses));
        }
    }
}

/// The mutants one [`NativeValidator::compile_ahead`] call keeps, for as long as this value
/// lives. Dropping it drops the uses its call added and every mutant no other chunk still counts
/// on; what other chunks (another caller's, say) keep stays kept.
#[must_use = "dropping the chunk drops its mutants compiled ahead"]
#[derive(Debug)]
pub struct AheadChunk<'v> {
    validator: &'v NativeValidator,
    id: u64,
}

impl Drop for AheadChunk<'_> {
    fn drop(&mut self) {
        self.validator.discard_chunk(self.id);
    }
}

/// How many candidates per compile worker a caller compiles ahead at once
/// ([`NativeValidator::compile_ahead`]; kink-campaign's runner and kink-flow chunk their
/// candidates and mutations by this): enough to keep the workers busy when compile times differ,
/// few enough that what a chunk keeps stays a small multiple of the workers.
pub const AHEAD_PER_WORKER: usize = 4;

/// The most mutants compiled ahead that one worker's share of the memory cap
/// ([`NativeValidator::compile_workers`]) holds: the patch and the claim-withdrawing patch of each
/// of its [`AHEAD_PER_WORKER`] candidates. [`NativeValidator::compile_ahead`] keeps no more than
/// this many per worker, whatever it is given.
pub const KEPT_PER_WORKER: usize = 2 * AHEAD_PER_WORKER;

/// The native stack and heap one compile in flight is estimated to take besides its definition,
/// for the memory cap of [`NativeValidator::compile_workers`].
const COMPILE_BASE_BYTES: u64 = 64 << 20;

/// The bytes one compile in flight is estimated to take per byte of the baseline's
/// `definition.kore`.
const COMPILE_BYTES_PER_KORE_BYTE: u64 = 32;

/// The bytes one mutant compiled ahead and kept is estimated to take besides its definition: its
/// applied mutant while it compiles, then its compiled definition (the relinked definition and
/// its KORE texts).
const KEPT_BASE_BYTES: u64 = 8 << 20;

/// The bytes one kept mutant is estimated to take per byte of the baseline's `definition.kore`.
const KEPT_BYTES_PER_KORE_BYTE: u64 = 8;

impl NativeValidator {
    /// Captures `baseline`; its caller owns prelude policy.
    pub const fn bind(baseline: Baseline, options: CompileOptions) -> Self {
        Self {
            baseline,
            options,
            compiled_baseline: OnceLock::new(),
            ahead: Mutex::new(Vec::new()),
            next_chunk: AtomicU64::new(0),
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
    /// The memory cap gives compiling ahead half of the process's allowance (k-rust's
    /// `Allowance::of_process`: the smallest of the cgroup's `memory.max`, `RLIMIT_AS` or
    /// `RLIMIT_DATA` and physical memory), and counts for each worker what its share of a chunk
    /// holds at once: one compile in flight, at an estimated 64 MiB plus 32 bytes per byte of the
    /// baseline's `definition.kore`, and the [`KEPT_PER_WORKER`] mutants compiled ahead that
    /// [`NativeValidator::compile_ahead`] keeps at most per worker, at an estimated 8 MiB plus 8
    /// bytes per byte each (the applied mutant while it compiles, then the compiled definition
    /// until its turn). The compile estimate is about twice what one more worker was measured to
    /// take (re-pin L1-3: 12 MiB plus about 25 bytes per byte, 31 MiB on `examples/imp`) and
    /// matches k-rust's 0.55-1.5 GiB per KEVM compile; the kept estimate is two to three times
    /// what a kept mutant was measured to take (re-pin L1-3-fix-1: 4.4 to 5.7 MiB, about 4 MiB
    /// plus 2.4 bytes per byte, on `examples/imp` and three flow fixtures; not measured on a large
    /// definition). k-rust promises no wall time or peak memory under concurrency, so the cap
    /// bounds memory; it never changes a result. A baseline that does not compile gets 1.
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
        let per_kept = KEPT_BYTES_PER_KORE_BYTE
            .saturating_mul(kore)
            .saturating_add(KEPT_BASE_BYTES);
        let per_worker = per_kept
            .saturating_mul(KEPT_PER_WORKER as u64)
            .saturating_add(per_compile);
        let allowance = k_rust::k_rust_backend::allowance::Allowance::of_process().bytes();
        let cap = usize::try_from(allowance / 2 / per_worker).unwrap_or(usize::MAX);
        let threads = std::thread::available_parallelism().map_or(1, NonZeroUsize::get);
        requested.min(threads).min(cap).max(1)
    }

    /// Compiles `patches` ahead of their [`NativeValidator::validate`] calls on up to
    /// [`compile_workers(workers)`](NativeValidator::compile_workers) threads, joins them all,
    /// and keeps each mutant that compiles for the `validate` calls of an equal patch (one per
    /// time the patch is given; a patch already kept gains those calls without compiling again)
    /// until they take it or the returned chunk is dropped.
    ///
    /// Each patch is applied on the calling thread, in the order given; a worker thread only
    /// relinks and compiles an applied mutant (see the module documentation). With one worker it
    /// does nothing: every mutant then compiles in its `validate` call, as without compiling
    /// ahead. A patch that is refused (by kink-patch, at relinking or by the compiler) is not
    /// kept, and neither is one whose application or compile panics: its `validate` call applies
    /// and compiles it again on the calling thread, which then gives today's refusal (or panic)
    /// at today's point. What is kept equals what `validate` would compile on the calling thread,
    /// so compiling ahead changes no artifact, status or report; the premise is the one
    /// [`NativeValidator::compile_baseline`] and replay take.
    ///
    /// At most [`KEPT_PER_WORKER`] times the workers' count of mutants are kept at once, counting
    /// those other chunks still keep: the patches past that are not compiled ahead, and compile
    /// in their `validate` call. That is what the memory cap of `compile_workers` counts.
    pub fn compile_ahead(&self, patches: &[Patch], workers: usize) -> AheadChunk<'_> {
        let workers = self.compile_workers(workers);
        self.compile_ahead_on(patches, workers, workers.saturating_mul(KEPT_PER_WORKER))
    }

    /// [`NativeValidator::compile_ahead`] with exactly `workers` threads (at most one per patch)
    /// keeping at most `kept` mutants at once.
    fn compile_ahead_on(&self, patches: &[Patch], workers: usize, kept: usize) -> AheadChunk<'_> {
        let chunk = AheadChunk {
            validator: self,
            id: self.next_chunk.fetch_add(1, Ordering::Relaxed),
        };
        if workers <= 1 {
            return chunk;
        }
        let mut distinct: Vec<(&Patch, usize)> = Vec::new();
        {
            let mut held = self.ahead.lock().unwrap_or_else(PoisonError::into_inner);
            for patch in patches {
                if let Some(kept) = held.iter_mut().find(|kept| kept.patch == *patch) {
                    kept.add_uses(chunk.id, 1);
                } else if let Some((_, uses)) = distinct.iter_mut().find(|(p, _)| *p == patch) {
                    *uses += 1;
                } else {
                    distinct.push((patch, 1));
                }
            }
            distinct.truncate(kept.saturating_sub(held.len()));
        }
        // Applying types each edited rule through a recursion with no stack guard: it stays on
        // the calling thread, in the order given.
        let applied = distinct
            .iter()
            .map(|(patch, _)| {
                catch_unwind(AssertUnwindSafe(|| apply(&self.baseline, patch)))
                    .ok()
                    .and_then(Result::ok)
            })
            .collect::<Vec<Option<Mutant>>>();
        let jobs = applied
            .iter()
            .enumerate()
            .filter_map(|(index, mutant)| mutant.as_ref().map(|mutant| (index, mutant)))
            .collect::<Vec<_>>();
        let compiled = distinct
            .iter()
            .map(|_| OnceLock::new())
            .collect::<Vec<OnceLock<ValidatedDefinition>>>();
        let next = AtomicUsize::new(0);
        std::thread::scope(|scope| {
            for _ in 0..workers.min(jobs.len()) {
                scope.spawn(|| {
                    loop {
                        let job = next.fetch_add(1, Ordering::Relaxed);
                        let Some(&(index, mutant)) = jobs.get(job) else {
                            break;
                        };
                        if let Ok(Ok(side)) =
                            catch_unwind(AssertUnwindSafe(|| self.compile_mutant(mutant)))
                        {
                            let _ = compiled[index].set(side);
                        }
                    }
                });
            }
        });
        drop(applied);
        let mut held = self.ahead.lock().unwrap_or_else(PoisonError::into_inner);
        for ((patch, uses), side) in distinct.into_iter().zip(compiled) {
            if let Some(compiled) = side.into_inner() {
                held.push(Ahead {
                    patch: patch.clone(),
                    compiled,
                    uses: vec![(chunk.id, uses)],
                });
            }
        }
        chunk
    }

    /// Drops the uses chunk `id` added, and every kept mutant no chunk counts on any more.
    fn discard_chunk(&self, id: u64) {
        let mut held = self.ahead.lock().unwrap_or_else(PoisonError::into_inner);
        held.retain_mut(|kept| {
            kept.uses.retain(|(owner, _)| *owner != id);
            !kept.uses.is_empty()
        });
    }

    /// The mutant of an equal patch compiled ahead, if one is kept, counting this use against
    /// the earliest chunk that still counts on one.
    fn take_ahead(&self, patch: &Patch) -> Option<ValidatedDefinition> {
        let mut held = self.ahead.lock().unwrap_or_else(PoisonError::into_inner);
        let at = held.iter().position(|kept| kept.patch == *patch)?;
        let uses = &mut held[at].uses;
        uses[0].1 -= 1;
        if uses[0].1 == 0 {
            uses.remove(0);
        }
        Some(if uses.is_empty() {
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
        self.compile_mutant(&mutant)
    }

    /// Relinks and compiles an applied mutant: the two steps a compile-ahead worker runs.
    fn compile_mutant(&self, mutant: &Mutant) -> Result<ValidatedDefinition, MutantRejection> {
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

    /// Each kept patch with the uses every chunk still counts on.
    fn held(validator: &NativeValidator) -> Vec<(Patch, usize)> {
        validator
            .ahead
            .lock()
            .unwrap()
            .iter()
            .map(|kept| (kept.patch.clone(), kept.uses.iter().map(|(_, n)| n).sum()))
            .collect()
    }

    /// `rule`'s `requires` clause replaced by `token`, as a whole-sentence edit.
    fn requires(baseline: &Baseline, rule: &str, token: &str) -> Patch {
        let at = support::rule(baseline, rule);
        let mut replacement = baseline.sentence(&at).unwrap().clone();
        let Sentence::Rule { requires, .. } = &mut replacement else {
            panic!("a rule");
        };
        *requires = Term::Token {
            token: token.into(),
            sort: Sort::new("Bool"),
        };
        Patch::new(vec![Edit::ReplaceSentence { at, replacement }]).unwrap()
    }

    mod kink_tier {
        use super::*;

        /// Re-pin L1-3 and L1-3-fix-1: a mutant compiled ahead is the mutant its `validate` call
        /// compiles alone, a patch given twice is compiled once and taken twice, a refused patch is
        /// not kept (its `validate` call gives the refusal from the calling thread), one worker keeps
        /// nothing, a chunk dropped drops only the uses it added (review L1-3-1 D4), no more than
        /// the kept bound is compiled ahead (review D2), and a clone starts with nothing kept. The
        /// worker count is forced, so a host that allows one compile worker still runs two threads
        /// (review D3).
        #[test]
        #[ignore = "kink"]
        fn compiled_ahead_mutants_are_their_own_compiles_and_refusals_are_not_kept() {
            std::thread::Builder::new()
                .stack_size(16 * 1024 * 1024)
                .spawn(|| {
                    let validator = NativeValidator::bind(
                        support::load("counter.k"),
                        CompileOptions::default(),
                    );
                    let baseline = validator.baseline();
                    let compiles = requires(baseline, "COUNTER.branch", "false");
                    let other = requires(baseline, "COUNTER.branch", "true");
                    let false_term = Term::Token {
                        token: "false".into(),
                        sort: Sort::new("Bool"),
                    };
                    // The requires clause is `B`, not `false`: kink-patch refuses the edit.
                    let refused = Patch::new(vec![Edit::ReplaceTerm {
                        at: TermRef::new(support::rule(baseline, "COUNTER.branch"), [1]),
                        expected: false_term.clone(),
                        replacement: false_term,
                    }])
                    .unwrap();
                    let alone = validator.validate(&compiles);
                    let other_alone = validator.validate(&other);
                    let refusal = validator.validate(&refused);
                    assert!(alone.is_ok(), "{alone:?}");
                    assert!(other_alone.is_ok(), "{other_alone:?}");
                    assert!(refusal.is_err());
                    let bound = 3 * KEPT_PER_WORKER;

                    let none =
                        validator.compile_ahead_on(std::slice::from_ref(&compiles), 1, bound);
                    assert!(
                        held(&validator).is_empty(),
                        "one worker compiles nothing ahead"
                    );
                    drop(none);

                    let chunk = validator.compile_ahead_on(
                        &[compiles.clone(), refused.clone(), compiles.clone()],
                        3,
                        bound,
                    );
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
                    drop(chunk);

                    let first =
                        validator.compile_ahead_on(std::slice::from_ref(&compiles), 3, bound);
                    let second =
                        validator.compile_ahead_on(std::slice::from_ref(&compiles), 3, bound);
                    assert_eq!(
                        held(&validator),
                        vec![(compiles.clone(), 2)],
                        "kept, not recompiled"
                    );
                    drop(second);
                    assert_eq!(
                        held(&validator),
                        vec![(compiles.clone(), 1)],
                        "a chunk drops only the uses it added"
                    );
                    drop(first);
                    assert!(held(&validator).is_empty());
                    assert_eq!(validator.validate(&compiles), alone);

                    let bounded =
                        validator.compile_ahead_on(&[compiles.clone(), other.clone()], 3, 1);
                    assert_eq!(
                        held(&validator),
                        vec![(compiles.clone(), 1)],
                        "no more than the bound is kept"
                    );
                    assert_eq!(validator.validate(&other), other_alone);
                    assert_eq!(validator.validate(&compiles), alone);
                    drop(bounded);

                    // The capped entry point gives the same mutants with whatever the host allows.
                    let capped = validator.compile_ahead(&[compiles.clone(), other.clone()], 3);
                    assert_eq!(validator.validate(&other), other_alone);
                    assert_eq!(validator.validate(&compiles), alone);
                    drop(capped);
                    assert!(held(&validator).is_empty());
                })
                .unwrap()
                .join()
                .unwrap();
        }

        /// Re-pin L1-3-fix-1 (review L1-3-1 D1): a patch of a rule 3000 terms deep, compiled ahead
        /// with 4 workers on their default stacks, gives what `validate` gives on the calling thread,
        /// with no abort. The patch is applied (and its edited rule typed, a recursion without a
        /// stack guard) on the calling thread; a worker only relinks and compiles, which k-rust runs
        /// on stacks sized from the definition. Before the fix the workers applied the patch, and
        /// every depth of 1500 or more overflowed a worker's stack and aborted the process.
        #[test]
        #[ignore = "kink"]
        fn a_deep_edited_rule_compiles_ahead_as_on_the_calling_thread() {
            const DEPTH: usize = 3000;
            std::thread::Builder::new()
                .stack_size(256 << 20)
                .spawn(|| {
                    let text = format!(
                        "module DEEP-SYNTAX\n  imports INT-SYNTAX\n  syntax Exp ::= Int\n               \
                         | \"go\" \"(\" Int \")\"\n               > left:\n                 Exp \"+\" \
                         Exp [strict, symbol(add)]\nendmodule\n\nmodule DEEP\n  imports \
                         DEEP-SYNTAX\n  imports INT\n  configuration <k> $PGM:Exp </k>\n  syntax \
                         KResult ::= Int\n  syntax Peano ::= \"z\" | s(Peano)\n  syntax Exp ::= \
                         deep(Peano)\n  rule [add]: I1:Int + I2:Int => I1 +Int I2\n  rule [big]: \
                         go(I:Int) => deep({}z{}) requires I >Int 100\nendmodule\n",
                        "s(".repeat(DEPTH),
                        ")".repeat(DEPTH)
                    );
                    let mut resolver = |_: &str, required: &str| {
                        k_rust::builtin::embedded(required)
                            .ok_or_else(|| format!("{required} is not embedded"))
                    };
                    let baseline = Baseline::load(
                        k_rust::outer::ResolvedSource::new("deep.k", text),
                        "DEEP",
                        None,
                        &mut resolver,
                        &support::options(),
                    )
                    .unwrap();
                    let validator = NativeValidator::bind(baseline, CompileOptions::default());
                    let patch = requires(validator.baseline(), "DEEP.big", "true");
                    let alone = validator.validate(&patch);
                    assert!(alone.is_ok(), "{alone:?}");
                    let chunk = validator.compile_ahead_on(
                        &[patch.clone(), patch.clone()],
                        4,
                        4 * KEPT_PER_WORKER,
                    );
                    assert_eq!(
                        held(&validator),
                        vec![(patch.clone(), 2)],
                        "a worker relinked and compiled the deep mutant"
                    );
                    assert_eq!(validator.validate(&patch), alone);
                    assert_eq!(validator.validate(&patch), alone);
                    drop(chunk);
                })
                .unwrap()
                .join()
                .unwrap();
        }
    }
}
