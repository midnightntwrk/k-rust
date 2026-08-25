//! Parsed-KORE support for the M4 native proof lane.
//!
//! This binary deliberately has a very small interface.  It extracts every
//! requested claim from a native definition into an independently parseable
//! one-claim specification, emits a claim-free executable definition, and
//! classifies a backend result only after parsing it as KORE.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::error::Error;
use std::ffi::OsString;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use k_rust::kore::ast::{Attributes, Definition, Module, Pattern, Sentence};
use k_rust::kore::parser::{parse_definition, parse_pattern};
use k_rust::kore::printer::Printer;

fn main() {
    if let Err(error) = run() {
        eprintln!("krs-m4-proof-support: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut arguments = env::args_os().skip(1);
    match utf8(arguments.next(), "missing command")?.as_str() {
        "split" => {
            let input = path(arguments.next(), "missing native definition.kore")?;
            let output = path(arguments.next(), "missing output directory")?;
            let module = utf8(arguments.next(), "missing semantic module")?;
            let spec_module = utf8(arguments.next(), "missing specification module")?;
            let labels = arguments
                .map(|value| utf8(Some(value), "claim label is not UTF-8"))
                .collect::<Result<Vec<_>, _>>()?;
            split(&input, &output, &module, &spec_module, &labels)
        }
        "classify" => {
            let result = path(arguments.next(), "missing proof result")?;
            no_more(arguments)?;
            classify(&result)
        }
        command => Err(failure(format!(
            "unknown command {command:?}; expected split or classify"
        ))),
    }
}

fn split(
    input: &Path,
    output: &Path,
    semantic_module: &str,
    spec_module: &str,
    labels: &[String],
) -> Result<(), Box<dyn Error>> {
    if output.exists() {
        return Err(failure(format!(
            "refusing to overwrite output directory {}",
            output.display()
        )));
    }
    if labels.is_empty() || labels.iter().any(String::is_empty) {
        return Err(failure("split requires one or more nonempty claim labels"));
    }
    let expected = labels.iter().cloned().collect::<BTreeSet<_>>();
    if expected.len() != labels.len() {
        return Err(failure("split claim labels are not unique"));
    }

    let mut definition = parse_definition(&fs::read_to_string(input)?)?;
    let matches = definition
        .modules
        .iter()
        .enumerate()
        .filter_map(|(index, module)| (module.name == semantic_module).then_some(index))
        .collect::<Vec<_>>();
    let [module_index] = matches.as_slice() else {
        return Err(failure(format!(
            "expected one semantic module {semantic_module:?}, found {}",
            matches.len()
        )));
    };

    let mut claims = BTreeMap::<String, Sentence>::new();
    for (index, module) in definition.modules.iter_mut().enumerate() {
        let mut retained = Vec::new();
        for sentence in module.sentences.drain(..) {
            if let Sentence::Claim { attributes, .. } = &sentence {
                let label = string_attribute(attributes, "label")?.ok_or_else(|| {
                    failure("native proof claim has no exact string label attribute")
                })?;
                if index != *module_index {
                    return Err(failure(format!(
                        "native claim {label:?} occurs outside {semantic_module:?}"
                    )));
                }
                if !expected.contains(label) {
                    return Err(failure(format!(
                        "unaccounted native claim {label:?}; split is fail-closed"
                    )));
                }
                if claims.insert(label.to_owned(), sentence).is_some() {
                    return Err(failure(format!("duplicate native claim {label:?}")));
                }
            } else {
                retained.push(sentence);
            }
        }
        module.sentences = retained;
    }
    if claims.keys().cloned().collect::<BTreeSet<_>>() != expected {
        let absent = expected.difference(&claims.keys().cloned().collect()).collect::<Vec<_>>();
        return Err(failure(format!("native claims are absent: {absent:?}")));
    }

    fs::create_dir_all(output.join("specs"))?;
    let printer = Printer::pretty(100);
    write_kore(
        &output.join("definition.kore"),
        printer.print_definition(&definition),
    )?;
    for label in labels {
        let sentence = claims
            .remove(label)
            .ok_or_else(|| failure(format!("native claim disappeared: {label:?}")))?;
        let spec = Definition {
            attributes: Attributes::default(),
            modules: vec![Module {
                name: spec_module.to_owned(),
                sentences: vec![
                    Sentence::Import {
                        module: semantic_module.to_owned(),
                        attributes: Attributes::default(),
                    },
                    sentence,
                ],
                attributes: Attributes::default(),
            }],
        };
        write_kore(
            &output.join("specs").join(format!("{label}.kore")),
            printer.print_definition(&spec),
        )?;
    }
    println!(
        "PASS native split: module={semantic_module} claims={} output={}",
        labels.len(),
        output.display()
    );
    Ok(())
}

fn classify(path: &Path) -> Result<(), Box<dyn Error>> {
    let pattern = parse_pattern(&fs::read_to_string(path)?)?;
    let status = match pattern {
        Pattern::Top { .. } => "proved",
        Pattern::Bottom { .. } => "failed",
        _ => "incomplete",
    };
    println!("{status}");
    Ok(())
}

fn string_attribute<'a>(
    attributes: &'a Attributes,
    name: &str,
) -> Result<Option<&'a str>, Box<dyn Error>> {
    let matches = attributes
        .0
        .iter()
        .filter_map(|attribute| match attribute {
            Pattern::Application { symbol, arguments } if symbol.name == name => Some(arguments),
            _ => None,
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [] => Ok(None),
        [arguments] => match arguments.as_slice() {
            [Pattern::String(value)] => Ok(Some(value)),
            _ => Err(failure(format!(
                "attribute {name:?} is not exactly one string"
            ))),
        },
        _ => Err(failure(format!("duplicate attribute {name:?}"))),
    }
}

fn write_kore(path: &Path, mut text: String) -> Result<(), Box<dyn Error>> {
    if !text.ends_with('\n') {
        text.push('\n');
    }
    fs::write(path, text)?;
    Ok(())
}

fn path(value: Option<OsString>, message: &str) -> Result<PathBuf, Box<dyn Error>> {
    value.map(PathBuf::from).ok_or_else(|| failure(message))
}

fn utf8(value: Option<OsString>, message: &str) -> Result<String, Box<dyn Error>> {
    value
        .ok_or_else(|| failure(message))?
        .into_string()
        .map_err(|_| failure(message))
}

fn no_more(mut arguments: impl Iterator<Item = OsString>) -> Result<(), Box<dyn Error>> {
    if arguments.next().is_none() {
        Ok(())
    } else {
        Err(failure("too many arguments"))
    }
}

fn failure(message: impl Into<String>) -> Box<dyn Error> {
    Box::new(io::Error::other(message.into()))
}
