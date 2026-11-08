//! `[[coverage.invariant]]` in a KRS corpus: an argued obligation's invariant named with KRS's
//! spellings, as `[stop] when` names a condition ([`super::condition`]): the function by its KRS
//! path, the cells by Rust field path.
//!
//! The front end resolves an invariant through krs-exec's own resolver
//! ([`krs_exec::Semantics::invariant`]), in the corpus's definition, over the compile that reads
//! the corpus's typed inputs, so an invariant is refused exactly where krs-exec refuses a function
//! of cells, with its message (`invariant-unresolved`), and one whose declared result is not
//! `Bool` apart (`invariant-not-bool`). The definition is its own observer: an invariant is a
//! claim about the states of the definition the corpus runs, and kink-flow checks it against that
//! definition's equations. The resolution hands kink-flow the function's KORE symbol and each
//! cell's KORE path (the cell symbols from the configuration's top cell down), with which its
//! connection reads the invariant at a rule's left-hand side
//! ([`kink_flow::coverage::InvariantResolver`]).
//!
//! The identity an invariant's checks are about gains the function's full KRS path and the
//! definition's Definition IR digest ([`super::render::definition_digest`]), beside the execution
//! digest, the symbol and the cell paths kink-flow names: the path and the digest decide which
//! KRS function the corpus's spelling resolved to.

use std::sync::Arc;

use kink_flow::admit::AdmittedSpec;
use kink_flow::coverage::{InvariantRefusal, InvariantResolver, ResolvedInvariant};
use kink_flow::manifest::Invariant;
use serde_json::{Map, json};

use super::inputs::KrsInputs;
use super::render::definition_digest;

/// The resolver of a KRS corpus's invariants, over the compile of its typed inputs' decoder.
pub(crate) struct KrsInvariants {
    inputs: Arc<KrsInputs>,
}

impl KrsInvariants {
    /// The resolver of the corpus whose definition `inputs` reads.
    pub(crate) const fn new(inputs: Arc<KrsInputs>) -> Self {
        Self { inputs }
    }
}

impl InvariantResolver for KrsInvariants {
    fn resolve(
        &self,
        _spec: &AdmittedSpec,
        invariant: &Invariant,
    ) -> Result<ResolvedInvariant, InvariantRefusal> {
        let resolved = self
            .inputs
            .with_semantics("resolving an invariant", |semantics| {
                semantics.invariant(&invariant.function, &invariant.cells)
            })
            .map_err(InvariantRefusal::Unresolved)?;
        if !resolved.returns_bool() {
            return Err(InvariantRefusal::NotBool(format!(
                "`{}` does not return Bool; an invariant holds or does not at a state",
                resolved.function_decl()
            )));
        }
        let digest =
            definition_digest(self.inputs.definition()).map_err(InvariantRefusal::Unresolved)?;
        let mut identity = Map::new();
        identity.insert("function".into(), json!(resolved.function_path()));
        identity.insert("definition_ir".into(), json!(digest));
        Ok(ResolvedInvariant {
            symbol: resolved.function_symbol().to_owned(),
            cells: resolved.cell_symbols().map(<[String]>::to_vec).collect(),
            identity,
        })
    }
}
