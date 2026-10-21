//! Typing views of one resolved definition: a generation aid and a diagnostic, never a verdict.
//!
//! k-rust's contract (docs/compatibility.md, the `SentenceTyper` paragraphs, at 501f18b9):
//! compilation injects every rule-like sentence of the main module's import closure with one
//! injector built for the main module, so the main module's typer,
//! `SentenceTyper::for_compilation(definition)`, built once per definition, gives compilation's
//! typing of each rule and claim of that closure through `typer.typing_in(sentence, module)`,
//! with `module` the module that declares the sentence (or that an edited sentence is relinked
//! into). k-rust states the contract as one-directional (a typing error implies compilation
//! fails, except `SentenceTypingError::CellCompletion`), but it is false at 501f18b9: when the
//! main module declares a second common supersort `D` of `A` and `B`, the cell-less rewrite
//! `a(X) => b(X)` gets `SentenceTypingError::Sort` ("cannot compute a unique least upper bound
//! for A, B") in compilation's view, whether the main module or an imported one declares it, and
//! compilation accepts the definition and runs it (review L2-2-review-1, probes lubbase and
//! lubmain; packet L2-2-fix-1).
//!
//! So kink never refuses on a typing error. A mutant is valid when it compiles: compilation
//! decides every patch, and kink-patch reads typing only
//! - to place site sorts ([`CompilationTyping::site_typing`]): compilation's view where it types
//!   the sentence, else the declaring module's own view (`SentenceTyper::new(definition,
//!   module)`, the reading before L2-2), else none, and a rule with no typing is a site without
//!   a sort, which a sort-selected discovery skips and reports as not exhaustive;
//! - as a diagnostic on an applied patch ([`CompilationTyping::error`]).
//!
//! A sentence's own module's view is not compilation's typing: its closure may lack `K`,
//! overloads or helpers that compilation sees (findings C-02, C-03 (a)), or may lack a supersort
//! that makes a least upper bound non-unique in compilation's view (the counterexample above).

use crate::stack::{StackRefusal, TYPING_STACK_PER_LEVEL, sentence_depth, with_stack};
use k_rust::definition::{ResolvedDefinition, Sentence};
use k_rust::kompile::{SentenceTyper, SentenceTyping, SentenceTypingError};
use std::collections::{BTreeMap, BTreeSet};

/// The per-level stack bound of [`CompilationTyping::site_typing`]: [`TYPING_STACK_PER_LEVEL`],
/// except in this crate's unit tests, which may raise it on their thread to force a refusal
/// ([`SITE_TYPING_PER_LEVEL`]).
fn site_typing_per_level() -> usize {
    #[cfg(test)]
    {
        SITE_TYPING_PER_LEVEL.with(std::cell::Cell::get)
    }
    #[cfg(not(test))]
    {
        TYPING_STACK_PER_LEVEL
    }
}

#[cfg(test)]
thread_local! {
    /// The bound [`site_typing_per_level`] gives on this thread (unit tests only).
    pub(crate) static SITE_TYPING_PER_LEVEL: std::cell::Cell<usize> =
        const { std::cell::Cell::new(TYPING_STACK_PER_LEVEL) };
}

/// The typer of the main module, the main module's import closure, and the own-module typers
/// built so far, of one resolved definition.
pub(crate) struct CompilationTyping<'a> {
    resolved: &'a ResolvedDefinition,
    typer: Option<SentenceTyper<'a>>,
    closure: BTreeSet<&'a str>,
    own: BTreeMap<String, Option<SentenceTyper<'a>>>,
}

impl<'a> CompilationTyping<'a> {
    pub(crate) fn new(resolved: &'a ResolvedDefinition) -> Self {
        let main = resolved.main_module_id();
        let closure = resolved
            .transitive_imports(main)
            .into_iter()
            .chain([main])
            .map(|id| resolved.module(id).name.as_str())
            .collect();
        Self {
            resolved,
            typer: SentenceTyper::for_compilation(resolved).ok(),
            closure,
            own: BTreeMap::new(),
        }
    }

    /// Compilation's typing of `sentence`, a rule or claim that `module` declares. `None` when
    /// `module` is outside the main module's import closure (compilation never emits the
    /// sentence) or the main module's typer could not be built.
    pub(crate) fn typing(
        &self,
        sentence: &Sentence,
        module: &str,
    ) -> Option<Result<SentenceTyping, SentenceTypingError>> {
        if !self.closure.contains(module) {
            return None;
        }
        Some(self.typer.as_ref()?.typing_in(sentence, module))
    }

    /// The typing error of `sentence` in compilation's view, a diagnostic only: compilation
    /// decides whether the sentence's definition is valid.
    pub(crate) fn error(&self, sentence: &Sentence, module: &str) -> Option<SentenceTypingError> {
        self.typing(sentence, module)?.err()
    }

    /// The typing site sorts are read from: compilation's view when it types `sentence`, else
    /// the view of `module`, the declaring module, else `None` (no site sorts). Neither view
    /// decides anything: a site sort only steers which candidates a generator builds, and
    /// compilation decides each of them.
    ///
    /// Both views type by a recursion over the sentence's terms that k-rust does not guard, so the
    /// typing runs on a stack sized from the sentence's depth, as [`crate::apply`]'s does
    /// ([`with_stack`]; re-pin L1-3-tail, review L1-3-fix-2-1 P1: on the calling thread a
    /// baseline rule about 230,000 terms deep aborted kink-corpus's universe resolution). A
    /// sentence too deep for the largest segment kink maps, or whose segment the system refuses,
    /// gets no typing: a rule without site sorts, which a sort-selected discovery skips and
    /// reports as not exhaustive, as for any rule neither view types. That case is `Err` with the
    /// refusal, which names kink's limit or the host's (re-pin L1-4, review L1-3-tail-1 D3: it was
    /// silent), so the universe and the discovery can say why the rule has no sort.
    pub(crate) fn site_typing(
        &mut self,
        sentence: &Sentence,
        module: &str,
    ) -> Result<Option<SentenceTyping>, StackRefusal> {
        with_stack(sentence_depth(sentence), site_typing_per_level(), || {
            self.site_typing_here(sentence, module)
        })
    }

    /// [`Self::site_typing`] on the calling thread's stack.
    fn site_typing_here(&mut self, sentence: &Sentence, module: &str) -> Option<SentenceTyping> {
        if let Some(Ok(typing)) = self.typing(sentence, module) {
            return Some(typing);
        }
        let resolved = self.resolved;
        self.own
            .entry(module.to_owned())
            .or_insert_with(|| SentenceTyper::new(resolved, module).ok())
            .as_ref()?
            .typing(sentence)
            .ok()
    }
}
