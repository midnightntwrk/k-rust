//! A case's typed inputs, read by KRS's encoding: kink-flow's [`InputDecoder`] implemented with
//! krs-exec, the one implementation of the encoding (`krs run --case` reads the same documents).
//!
//! Each input is decoded at its `#[k::init]` parameter's declared type and given to kink as the
//! KAST term krs-exec's own configuration would bind ([`krs_exec::Semantics::input_term`]); kink
//! types the term in `definition.k`'s grammar and refuses it if a name does not resolve there,
//! so a disagreement between the two routes fails closed. The decoder needs the native compile
//! of the Definition IR, which is made on first use, only for a corpus with typed inputs, once
//! per thread that decodes (krs-exec's compiled definition is not shared across threads).

use std::cell::RefCell;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use k_rust::kast::Term;
use kink_flow::InputDecoder;
use krs_exec::{ConfigValue, Semantics};
use krs_ir_levels::DefinitionIr;

/// The decoder of one emission's typed inputs.
pub(crate) struct KrsInputs {
    /// Tells this decoder's compile apart from another's in a thread's cache.
    id: u64,
    definition: Arc<DefinitionIr>,
}

impl KrsInputs {
    pub(crate) fn new(definition: DefinitionIr) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Self {
            id: NEXT.fetch_add(1, Ordering::Relaxed),
            definition: Arc::new(definition),
        }
    }
}

thread_local! {
    /// Each decoder's compile on this thread, or why it failed, by decoder id.
    static COMPILED: RefCell<Vec<(u64, Result<Semantics, String>)>> = const { RefCell::new(Vec::new()) };
}

/// kink-flow's file reader seen as krs-exec's: the same contract (a path relative to the
/// document that names it, the resolved name and the bytes), with kink's containment rule.
struct ManifestFiles<'a>(&'a mut dyn kink_flow::admit::InputFiles);

impl krs_exec::InputFiles for ManifestFiles<'_> {
    fn read(&mut self, from: Option<&str>, path: &str) -> Result<(String, Vec<u8>), String> {
        self.0.read(from, path)
    }
}

impl InputDecoder for KrsInputs {
    fn decode(
        &self,
        name: &str,
        document: &toml::Value,
        files: &mut dyn kink_flow::admit::InputFiles,
    ) -> Result<(String, Term), String> {
        let document = krs_exec::toml_document(document).map_err(|error| error.to_string())?;
        COMPILED.with(|compiled| {
            let mut compiled = compiled.borrow_mut();
            let position =
                if let Some(position) = compiled.iter().position(|(id, _)| *id == self.id) {
                    position
                } else {
                    let semantics = Semantics::compile(&self.definition).map_err(|error| {
                        format!(
                            "krs cannot compile the definition natively, which reading a typed \
                         input needs: {error}"
                        )
                    });
                    compiled.push((self.id, semantics));
                    compiled.len() - 1
                };
            let semantics = compiled[position].1.as_ref().map_err(Clone::clone)?;
            let value = semantics
                .decode_input(name, &document, &mut ManifestFiles(files))
                .map_err(|error| error.to_string())?;
            let ConfigValue::Value(value) = value else {
                return Err(
                    "`$text` and `$text-file` are K text, which a case binds under `variables` \
                     (kink reads it by the rule krs-exec does); a typed input is data"
                        .to_owned(),
                );
            };
            semantics
                .input_term(name, &value)
                .map_err(|error| error.to_string())
        })
    }
}
