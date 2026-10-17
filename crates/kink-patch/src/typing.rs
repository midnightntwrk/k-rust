//! Compilation's typing view of one resolved definition.
//!
//! k-rust's contract (docs/compatibility.md, the `SentenceTyper` paragraphs, at 501f18b9):
//! compilation injects every rule-like sentence of the main module's import closure with one
//! injector built for the main module, so the main module's typer,
//! `SentenceTyper::for_compilation(definition)`, built once per definition, gives compilation's
//! typing of each rule and claim of that closure through `typer.typing_in(sentence, module)`,
//! with `module` the module that declares the sentence (or that an edited sentence is relinked
//! into). The contract is one-directional: if compilation accepts a definition, every such
//! sentence types; a typing error is an error compilation stops at, except
//! `SentenceTypingError::CellCompletion`, a shape compilation may accept. Sentences outside the
//! main closure are outside the contract: compilation never emits them.
//!
//! A sentence's own module's typer (`SentenceTyper::new(definition, module)`) is not
//! compilation's typing: its closure may lack `K`, overloads or helpers that compilation sees
//! (findings C-02, C-03 (a)).

use k_rust::definition::{ResolvedDefinition, Sentence};
use k_rust::kompile::{SentenceTyper, SentenceTyping, SentenceTypingError};
use std::collections::BTreeSet;

/// The typer of the main module and the main module's import closure, built once.
pub(crate) struct CompilationTyping<'a> {
    typer: Option<SentenceTyper<'a>>,
    closure: BTreeSet<&'a str>,
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
            typer: SentenceTyper::for_compilation(resolved).ok(),
            closure,
        }
    }

    /// Compilation's typing of `sentence`, a rule or claim that `module` declares. `None` when
    /// the contract says nothing about it: `module` is outside the main module's import
    /// closure, or the main module's typer could not be built (compilation then decides).
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

    /// The typing error of `sentence` in `module` that implies compilation fails: a sort or
    /// semantic-cast error on a rule or claim of the main closure. Every other answer (typed,
    /// `CellCompletion`, outside the contract) leaves the verdict to compilation.
    pub(crate) fn compilation_error(
        &self,
        sentence: &Sentence,
        module: &str,
    ) -> Option<SentenceTypingError> {
        match self.typing(sentence, module)? {
            Err(
                error @ (SentenceTypingError::Sort { .. } | SentenceTypingError::SemanticCasts(_)),
            ) => Some(error),
            Ok(_)
            | Err(
                SentenceTypingError::CellCompletion { .. }
                | SentenceTypingError::NotRuleLike
                | SentenceTypingError::MissingModule(_),
            ) => None,
        }
    }
}
