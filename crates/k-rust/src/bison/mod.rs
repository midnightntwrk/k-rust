mod grammar;
mod scanner;
mod toolchain;

use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::definition::{ResolvedDefinition, Sentence};
use crate::inner::{concretize_parametric_productions, prepared_bison_program_sentences};
use crate::kast::Sort;

use self::scanner::Scanner;

const MAIN_C: &str = include_str!("../../cparser/main.c");
const NODE_H: &str = include_str!("../../cparser/node.h");
const PARSING_ONLY_SUBSORT_ATTRIBUTE: &str = "#bisonParsingOnlySubsort";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mode {
    Lr,
    Glr,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Options {
    pub mode: Mode,
    pub stack_max_depth: u64,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            mode: Mode::Glr,
            stack_max_depth: 10_000,
        }
    }
}

#[derive(Debug)]
pub struct Error {
    message: String,
}

impl Error {
    fn render(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    fn io(operation: &str, error: std::io::Error) -> Self {
        Self::render(format!("{operation}: {error}"))
    }
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for Error {}

pub fn generate_program_parser(
    definition: &ResolvedDefinition,
    module: &str,
    start_sort: &Sort,
    output_directory: &Path,
    options: Options,
) -> Result<PathBuf, Error> {
    let module_id = definition
        .module_id(module)
        .ok_or_else(|| Error::render(format!("program syntax module {module:?} was not found")))?;
    let sentences =
        concrete_program_sentences(prepared_bison_program_sentences(definition, module_id));
    let grammar = grammar::prepare(&sentences)?;
    let scanner = Scanner::new(&grammar.scanner_sentences())?;
    let scanner_source = scanner.render()?;
    let parser_source = grammar::render(
        &grammar,
        &scanner,
        start_sort,
        options.mode,
        options.stack_max_depth,
    )?;

    fs::create_dir_all(output_directory)
        .map_err(|error| Error::io("could not create parser output directory", error))?;
    let output_directory = fs::canonicalize(output_directory)
        .map_err(|error| Error::io("could not resolve parser output directory", error))?;
    let stage = Stage::new(&output_directory)?;
    fs::write(stage.path.join("scanner.l"), scanner_source)
        .map_err(|error| Error::io("could not write scanner.l", error))?;
    fs::write(stage.path.join("parser.y"), parser_source)
        .map_err(|error| Error::io("could not write parser.y", error))?;
    fs::write(stage.path.join("main.c"), MAIN_C)
        .map_err(|error| Error::io("could not write parser runtime", error))?;
    fs::write(stage.path.join("node.h"), NODE_H)
        .map_err(|error| Error::io("could not write parser ABI header", error))?;

    let staged_executable = stage.path.join("parser");
    toolchain::compile(&stage.path, start_sort, &staged_executable)?;

    let primary_name = format!("parser_{}_{}", start_sort.name, module);
    let primary = output_directory.join(&primary_name);
    replace_file(&staged_executable, &primary)?;
    install_relative_link(&output_directory, "parser_PGM", &primary_name)?;
    Ok(primary)
}

fn concrete_program_sentences(sentences: Vec<Sentence>) -> Vec<Sentence> {
    let references = sentences.iter().collect::<Vec<_>>();
    let concretization = concretize_parametric_productions(&references);
    let mut output = sentences
        .iter()
        .filter(|sentence| {
            !matches!(sentence, Sentence::Production { parameters, .. } if !parameters.is_empty())
        })
        .cloned()
        .collect::<Vec<_>>();
    output.extend(
        concretization
            .families
            .into_iter()
            .flat_map(|family| family.instances)
            .map(|instance| instance.sentence),
    );
    output.extend(
        concretization
            .parsing_only_subsorts
            .into_iter()
            .map(|bridge| {
                let mut sentence = bridge.sentence;
                let Sentence::Production { attributes, .. } = &mut sentence else {
                    unreachable!()
                };
                attributes.insert(
                    PARSING_ONLY_SUBSORT_ATTRIBUTE,
                    serde_json::Value::String(String::new()),
                );
                sentence
            }),
    );
    output
}

fn replace_file(source: &Path, destination: &Path) -> Result<(), Error> {
    match fs::rename(source, destination) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            fs::remove_file(destination)
                .map_err(|error| Error::io("could not replace generated parser", error))?;
            fs::rename(source, destination)
                .map_err(|error| Error::io("could not install generated parser", error))
        }
        Err(error) => Err(Error::io("could not install generated parser", error)),
    }
}

fn install_relative_link(
    output_directory: &Path,
    link_name: &str,
    target_name: &str,
) -> Result<(), Error> {
    static NEXT_LINK: AtomicU64 = AtomicU64::new(0);
    let temporary_name = format!(
        ".{link_name}.{}.{}",
        std::process::id(),
        NEXT_LINK.fetch_add(1, Ordering::Relaxed)
    );
    let temporary = output_directory.join(temporary_name);
    create_file_symlink(Path::new(target_name), &temporary)
        .map_err(|error| Error::io("could not create generated parser link", error))?;
    let destination = output_directory.join(link_name);
    match fs::rename(&temporary, &destination) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            fs::remove_file(&destination)
                .map_err(|error| Error::io("could not replace generated parser link", error))?;
            fs::rename(&temporary, &destination)
                .map_err(|error| Error::io("could not install generated parser link", error))
        }
        Err(error) => {
            let _ = fs::remove_file(&temporary);
            Err(Error::io("could not install generated parser link", error))
        }
    }
}

#[cfg(unix)]
fn create_file_symlink(target: &Path, link: &Path) -> std::io::Result<()> {
    std::os::unix::fs::symlink(target, link)
}

#[cfg(windows)]
fn create_file_symlink(target: &Path, link: &Path) -> std::io::Result<()> {
    std::os::windows::fs::symlink_file(target, link)
}

struct Stage {
    path: PathBuf,
}

impl Stage {
    fn new(output_directory: &Path) -> Result<Self, Error> {
        static NEXT_STAGE: AtomicU64 = AtomicU64::new(0);
        for _ in 0..100 {
            let path = output_directory.join(format!(
                ".krust-bison.{}.{}",
                std::process::id(),
                NEXT_STAGE.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Ok(Self { path }),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    return Err(Error::io(
                        "could not create parser staging directory",
                        error,
                    ));
                }
            }
        }
        Err(Error::render("could not allocate parser staging directory"))
    }
}

impl Drop for Stage {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn quote_c_string(value: &str) -> String {
    let mut output = String::from("\"");
    for character in value.chars() {
        match character {
            '\\' => output.push_str("\\\\"),
            '"' => output.push_str("\\\""),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character.is_control() => {
                use std::fmt::Write;
                write!(output, "\\x{:02x}", character as u32)
                    .expect("writing to a string cannot fail");
            }
            character => output.push(character),
        }
    }
    output.push('"');
    output
}
