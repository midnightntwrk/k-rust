//! A case's typed inputs, read by KRS's encoding: kink-flow's [`InputDecoder`] implemented with
//! krs-exec, the one implementation of the encoding (`krs run --case` reads the same documents).
//!
//! Each input is decoded at its `#[k::init]` parameter's declared type and given to kink as the
//! KAST term krs-exec's own configuration would bind ([`krs_exec::Semantics::input_term`]); kink
//! types the term in `definition.k`'s grammar and refuses it if a name does not resolve there,
//! so a disagreement between the two routes fails closed. The decoder needs the native compile
//! of the Definition IR, which is made on first use, only where a typed input or a program needs
//! it, once per thread that decodes (krs-exec's compiled definition is not shared across
//! threads).
//!
//! A program file binds the main parameter of the `#[k::init]`, whatever its K name, as `krs run
//! FILE` binds it ([`krs_exec::Semantics::program_file`]): the file's bytes where its type is
//! exactly `Bytes`, and its text otherwise. Text needs only the Definition IR, so a corpus of
//! text programs compiles nothing; the bytes, the message for a file that is not text, and a
//! parameter type the Definition IR alone does not give ([`krs_exec::MainVariable`]) need the
//! native compile.
//!
//! A case that binds no value for an input with a declared default takes the default, as `krs
//! run` does ([`krs_exec::Semantics::configure`]): the decoder gives kink the KORE value the
//! native compile lowered for it ([`krs_exec::Semantics::input_defaults`]), which kink binds as
//! that value, so the case starts where binding the default by hand starts. Which inputs have a
//! default the Definition IR says, so a case that binds every input compiles nothing for it.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use k_rust::kast::Term;
use k_rust::kore::ast::Pattern;
use kink_flow::{InputDecoder, ProgramBinding};
use krs_exec::{ConfigValue, ExecError, MainVariable, ProgramFile, Semantics};
use krs_ir_levels::DefinitionIr;

/// The decoder of one emission's typed inputs and program files.
pub(crate) struct KrsInputs {
    /// Tells this decoder's compile apart from another's in a thread's cache.
    id: u64,
    definition: Arc<DefinitionIr>,
    /// The main parameter, read from the Definition IR.
    main: Option<MainVariable>,
    /// Whether a parameter's configuration variable is `$PGM`, read from the Definition IR.
    declares_pgm: bool,
    /// The K names of the inputs with a declared default, read from the Definition IR.
    defaulted: Vec<String>,
}

impl KrsInputs {
    pub(crate) fn new(definition: DefinitionIr) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Self {
            id: NEXT.fetch_add(1, Ordering::Relaxed),
            main: krs_exec::main_variable(&definition),
            declares_pgm: krs_exec::declares_variable(&definition, "PGM"),
            defaulted: krs_exec::defaulted_variables(&definition),
            definition: Arc::new(definition),
        }
    }

    /// The Definition IR the decoder reads.
    pub(crate) fn definition(&self) -> &DefinitionIr {
        &self.definition
    }

    /// `body` with this decoder's native compile on this thread, made on first use; `need` says
    /// what the compile is for, in the message of a compile that fails.
    pub(crate) fn with_semantics<T>(
        &self,
        need: &str,
        body: impl FnOnce(&Semantics) -> Result<T, String>,
    ) -> Result<T, String> {
        self.with_semantics_mut(need, |semantics| body(semantics))
    }

    /// [`Self::with_semantics`], the compile given mutably: a view's evaluation, which runs the
    /// backend, needs it.
    pub(crate) fn with_semantics_mut<T>(
        &self,
        need: &str,
        body: impl FnOnce(&mut Semantics) -> Result<T, String>,
    ) -> Result<T, String> {
        COMPILED.with(|compiled| {
            let mut compiled = compiled.borrow_mut();
            let position =
                if let Some(position) = compiled.iter().position(|(id, _)| *id == self.id) {
                    position
                } else {
                    let semantics =
                        Semantics::compile(&self.definition).map_err(|error| error.to_string());
                    compiled.push((self.id, semantics));
                    compiled.len() - 1
                };
            let semantics = compiled[position].1.as_mut().map_err(|error| {
                format!("krs cannot compile the definition natively, which {need} needs: {error}")
            })?;
            body(semantics)
        })
    }
}

thread_local! {
    /// Each decoder's compile on this thread, or why it failed, by decoder id.
    static COMPILED: RefCell<Vec<(u64, Result<Semantics, String>)>> = const { RefCell::new(Vec::new()) };
}

/// kink-flow's file reader seen as krs-exec's: the same contract (a path relative to the
/// document that names it, the resolved name and the bytes), with kink's containment rule.
pub(crate) struct ManifestFiles<'a>(pub(crate) &'a mut dyn kink_flow::admit::InputFiles);

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
        self.with_semantics("reading a typed input", |semantics| {
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

    /// The default of each input with one that `bound` does not name: the KORE value
    /// `krs run` binds for it ([`krs_exec::Semantics::input_defaults`]), from the native compile,
    /// which is made only where some default is taken.
    fn defaults(&self, bound: &BTreeSet<String>) -> Result<Vec<(String, Pattern)>, String> {
        let taken = self
            .defaulted
            .iter()
            .filter(|variable| !bound.contains(*variable))
            .collect::<Vec<_>>();
        if taken.is_empty() {
            return Ok(Vec::new());
        }
        self.with_semantics("binding an input's default", |semantics| {
            taken
                .into_iter()
                .map(|variable| {
                    semantics
                        .input_defaults()
                        .get(variable)
                        .map(|pattern| (variable.clone(), pattern.clone()))
                        .ok_or_else(|| {
                            format!(
                                "the Definition IR declares a default for ${variable}, and its \
                                 native compile carries none"
                            )
                        })
                })
                .collect()
        })
    }

    /// The main parameter's binding of a program: kink's own (`None`) where that parameter is
    /// `$PGM` and reads UTF-8 text, the text bound to it by name where it reads text under
    /// another name, and the file's bytes as the term `krs run FILE` binds where its type is
    /// exactly `Bytes`. Inline text under a `Bytes` main parameter is refused: a `Bytes` value has
    /// no text reading, and a case gives bytes inline as a typed input (`$hex`). Without a main
    /// parameter `krs run` refuses FILE, and so does kink's rule (`stray-program`) where no
    /// variable is `$PGM`; a `$PGM` that is not main would take the text under kink's rule, and
    /// is refused with `krs run`'s message instead.
    fn program(&self, name: Option<&str>, bytes: &[u8]) -> Option<Result<ProgramBinding, String>> {
        const NEED: &str = "binding a program to the main parameter";
        let Some(main) = &self.main else {
            return self.declares_pgm.then(|| {
                self.with_semantics(NEED, |semantics| {
                    // The compiled definition's parameters are the IR's, main included, so the
                    // main parameter is missing there too: krs-exec's message lists every
                    // parameter, typed, to bind by name instead.
                    Err(semantics.program_parameter().map_or_else(
                        |error| error.to_string(),
                        |parameter| format!("the main parameter is `{}`", parameter.name),
                    ))
                })
            });
        };
        let text = std::str::from_utf8(bytes).ok();
        match (main.reads_file_bytes, text) {
            (Some(false), Some(_)) if main.variable == "PGM" => None,
            (Some(false), Some(text)) => Some(Ok(ProgramBinding::Text {
                variable: main.variable.clone(),
                text: text.to_owned(),
            })),
            (Some(true), _) if name.is_none() => {
                Some(Err(inline_bytes_refusal(&main.name, &main.variable)))
            }
            _ => Some(self.with_semantics(NEED, |semantics| {
                let file = match semantics
                    .program_file(name.unwrap_or("the program text"), bytes.to_vec())
                {
                    Ok(file) => file,
                    // The program's file is named by the refusal kink-flow writes.
                    Err(ExecError::ProgramNotText { parameter, .. }) => {
                        return Err(format!(
                            "not UTF-8 text, and {}",
                            parameter.reads_file_text()
                        ));
                    }
                    Err(error) => return Err(error.to_string()),
                };
                match file {
                    ProgramFile::Bytes { parameter, .. } if name.is_none() => {
                        let variable = &semantics
                            .program_parameter()
                            .map_err(|error| error.to_string())?
                            .variable;
                        Err(inline_bytes_refusal(&parameter, variable))
                    }
                    ProgramFile::Bytes { parameter, value } => semantics
                        .input_term(&parameter, &value)
                        .map(|(variable, term)| ProgramBinding::Term { variable, term })
                        .map_err(|error| error.to_string()),
                    ProgramFile::Text(program) => Ok(ProgramBinding::Text {
                        variable: semantics
                            .program_parameter()
                            .map_err(|error| error.to_string())?
                            .variable
                            .clone(),
                        text: program.text,
                    }),
                }
            })),
        }
    }
}

/// The refusal of inline program text under the main parameter `name` (`$variable`), whose type
/// is exactly `Bytes`.
fn inline_bytes_refusal(name: &str, variable: &str) -> String {
    format!(
        "the main parameter `{name}` (${variable}: Bytes) takes a file's bytes, and inline text \
         has no reading as bytes; give the program as a file, or bind its bytes under `inputs` \
         instead: `{name} = {{ \"$hex\" = \"..\" }}`"
    )
}
