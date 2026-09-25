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
use krs_m4_native_comparator::normalize_standalone_pattern;

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
        "assert-spec" => {
            let input = path(arguments.next(), "missing specification KORE")?;
            let spec_module = utf8(arguments.next(), "missing specification module")?;
            let semantic_module = utf8(arguments.next(), "missing semantic module")?;
            let claim_label = utf8(arguments.next(), "missing claim label")?;
            no_more(arguments)?;
            assert_spec(&input, &spec_module, &semantic_module, &claim_label)
        }
        "compare-patterns" => {
            let left = path(arguments.next(), "missing left proof result")?;
            let right = path(arguments.next(), "missing right proof result")?;
            no_more(arguments)?;
            compare_patterns(&left, &right)
        }
        command => Err(failure(format!(
            "unknown command {command:?}; expected split, classify, assert-spec, or compare-patterns"
        ))),
    }
}

fn assert_spec(
    input: &Path,
    spec_module: &str,
    semantic_module: &str,
    claim_label: &str,
) -> Result<(), Box<dyn Error>> {
    let definition = parse_definition(&fs::read_to_string(input)?)?;
    let [module] = definition.modules.as_slice() else {
        return Err(failure(format!(
            "specification must contain exactly one module; found {}",
            definition.modules.len()
        )));
    };
    if module.name != spec_module {
        return Err(failure(format!(
            "specification module differs: expected {spec_module:?}, found {:?}",
            module.name
        )));
    }

    let mut imports = 0_usize;
    let mut claims = 0_usize;
    for sentence in &module.sentences {
        match sentence {
            Sentence::Import { module, .. } if module == semantic_module => imports += 1,
            Sentence::Import { module, .. } => {
                return Err(failure(format!(
                    "specification imports unexpected module {module:?}"
                )));
            }
            Sentence::Claim { attributes, .. } => {
                let label = string_attribute(attributes, "label")?.ok_or_else(|| {
                    failure("specification claim has no exact string label attribute")
                })?;
                if label != claim_label {
                    return Err(failure(format!(
                        "specification claim label differs: expected {claim_label:?}, found {label:?}"
                    )));
                }
                claims += 1;
            }
            _ => {
                return Err(failure(
                    "specification contains a non-import, non-claim sentence",
                ));
            }
        }
    }
    if imports != 1 || claims != 1 {
        return Err(failure(format!(
            "specification must contain one semantic import and one claim; imports={imports}, claims={claims}"
        )));
    }
    println!("PASS proof spec: module={spec_module} claim={claim_label}");
    Ok(())
}

fn compare_patterns(left: &Path, right: &Path) -> Result<(), Box<dyn Error>> {
    let mut left_pattern = parse_pattern(&fs::read_to_string(left)?)?;
    let mut right_pattern = parse_pattern(&fs::read_to_string(right)?)?;
    normalize_residual_pattern(&mut left_pattern);
    normalize_residual_pattern(&mut right_pattern);
    normalize_standalone_pattern(&mut left_pattern);
    normalize_standalone_pattern(&mut right_pattern);
    if left_pattern != right_pattern {
        return Err(failure("normalized parsed proof-result patterns differ"));
    }
    println!("PASS proof patterns: normalized parsed results are identical");
    Ok(())
}

fn normalize_residual_pattern(pattern: &mut Pattern) {
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                normalize_residual_pattern(argument);
            }
        }
        Pattern::And { arguments, sort } => {
            for argument in arguments.iter_mut() {
                normalize_residual_pattern(argument);
            }
            let mut flattened = Vec::new();
            for mut argument in std::mem::take(arguments) {
                match &mut argument {
                    Pattern::And {
                        sort: child_sort,
                        arguments: child_arguments,
                    } if *child_sort == *sort => {
                        flattened.extend(std::mem::take(child_arguments));
                    }
                    _ => flattened.push(argument),
                }
            }
            flattened.sort();
            *arguments = flattened;
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => normalize_residual_pattern(argument),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            normalize_residual_pattern(left);
            normalize_residual_pattern(right);
        }
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => normalize_residual_pattern(body),
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }

    let Pattern::Application { symbol, arguments } = pattern else {
        return;
    };
    if symbol.name != "Lbl'Unds'Map'Unds'" {
        return;
    }
    let symbol = symbol.clone();
    let mut leaves = Vec::new();
    flatten_application(std::mem::take(arguments), &symbol, &mut leaves);
    leaves.sort();
    let Some(first) = leaves.first().cloned() else {
        return;
    };
    let mut rebuilt = leaves
        .into_iter()
        .skip(1)
        .fold(first, |left, right| Pattern::Application {
            symbol: symbol.clone(),
            arguments: vec![left, right],
        });
    if let Pattern::Application {
        arguments: rebuilt_arguments,
        ..
    } = &mut rebuilt
    {
        *arguments = std::mem::take(rebuilt_arguments);
    } else {
        *arguments = vec![rebuilt];
    }
}

fn flatten_application(
    arguments: Vec<Pattern>,
    symbol: &k_rust::kore::ast::Symbol,
    output: &mut Vec<Pattern>,
) {
    for mut argument in arguments {
        match &mut argument {
            Pattern::Application {
                symbol: child_symbol,
                arguments: child_arguments,
            } if *child_symbol == *symbol => {
                flatten_application(std::mem::take(child_arguments), symbol, output);
            }
            _ => output.push(argument),
        }
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
    let label_prefix = format!("{semantic_module}.");

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
                let qualified_label = string_attribute(attributes, "label")?.ok_or_else(|| {
                    failure("native proof claim has no exact string label attribute")
                })?;
                let label = qualified_label
                    .strip_prefix(&label_prefix)
                    .filter(|label| !label.is_empty() && !label.contains('.'))
                    .ok_or_else(|| {
                        failure(format!(
                            "native proof claim {qualified_label:?} is not exactly qualified by {semantic_module:?}"
                        ))
                    })?
                    .to_owned();
                if index != *module_index {
                    return Err(failure(format!(
                        "native claim {label:?} occurs outside {semantic_module:?}"
                    )));
                }
                if !expected.contains(&label) {
                    return Err(failure(format!(
                        "unaccounted native claim {label:?}; split is fail-closed"
                    )));
                }
                if claims.insert(label.clone(), sentence).is_some() {
                    return Err(failure(format!("duplicate native claim {label:?}")));
                }
            } else {
                retained.push(sentence);
            }
        }
        module.sentences = retained;
    }
    let present = claims.keys().cloned().collect::<BTreeSet<_>>();
    if present != expected {
        let absent = expected.difference(&present).collect::<Vec<_>>();
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
            [Pattern::String(value)] => value
                .as_utf8()
                .map(Some)
                .map_err(|_| failure(format!("attribute {name:?} is not UTF-8"))),
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

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::kore::ast::{Sort, Symbol};

    fn sort() -> Sort {
        Sort::Application {
            name: "SortGeneratedTopCell".to_owned(),
            arguments: Vec::new(),
        }
    }

    fn application(name: &str, arguments: Vec<Pattern>) -> Pattern {
        Pattern::Application {
            symbol: Symbol {
                name: name.to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments,
        }
    }

    #[test]
    fn residual_normalization_is_narrowly_and_map_associative_commutative() {
        let map = "Lbl'Unds'Map'Unds'";
        let a = Pattern::String("a".into());
        let b = Pattern::String("b".into());
        let c = Pattern::String("c".into());
        let mut left = Pattern::And {
            sort: sort(),
            arguments: vec![
                application(map, vec![b.clone(), a.clone()]),
                Pattern::And {
                    sort: sort(),
                    arguments: vec![c.clone(), a.clone()],
                },
            ],
        };
        let mut right = Pattern::And {
            sort: sort(),
            arguments: vec![a.clone(), c, application(map, vec![a.clone(), b])],
        };
        normalize_residual_pattern(&mut left);
        normalize_residual_pattern(&mut right);
        assert_eq!(left, right);

        let mut ordered = application("ordinary", vec![a.clone(), Pattern::String("b".into())]);
        let mut reversed = application("ordinary", vec![Pattern::String("b".into()), a]);
        normalize_residual_pattern(&mut ordered);
        normalize_residual_pattern(&mut reversed);
        assert_ne!(ordered, reversed);
    }
}
