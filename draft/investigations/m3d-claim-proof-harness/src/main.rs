use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    error::Error,
    fs,
    io,
    path::{Path, PathBuf},
};

use k_rust::kore::{
    ast::{Attributes, Definition, Module, Pattern, Sentence, Sort, Symbol, Variable, VariableKind},
    parser::parse_definition,
    printer::Printer,
};
use serde::Deserialize;

#[derive(Clone, Debug, Deserialize)]
struct Cases {
    cases: Vec<Case>,
}

#[derive(Clone, Debug, Deserialize)]
struct Case {
    name: String,
    native_label: String,
    source_module: String,
    source_claim: String,
    modality: String,
    circularity: bool,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("m3d-claim-kore: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut arguments = env::args_os().skip(1);
    let command = utf8(arguments.next(), "missing command")?;
    match command.as_str() {
        "split" => {
            let input = path(arguments.next(), "missing input definition.kore")?;
            let output = path(arguments.next(), "missing output directory")?;
            let semantic_module = utf8(arguments.next(), "missing semantic module")?;
            let cases = path(arguments.next(), "missing cases.json")?;
            no_more(arguments)?;
            split(&input, &output, &semantic_module, &read_cases(&cases)?)
        }
        "compare" => {
            let source = path(arguments.next(), "missing kprove spec.kore")?;
            let native = path(arguments.next(), "missing native spec.kore")?;
            let source_label = utf8(arguments.next(), "missing source label")?;
            let native_label = utf8(arguments.next(), "missing native label")?;
            no_more(arguments)?;
            compare(&source, &native, &source_label, &native_label)
        }
        "fixture-merge" => {
            let semantics = path(arguments.next(), "missing semantic definition.kore")?;
            let output = path(arguments.next(), "missing output definition.kore")?;
            let semantic_module = utf8(arguments.next(), "missing semantic module")?;
            let cases_path = path(arguments.next(), "missing cases.json")?;
            let specs = arguments.map(PathBuf::from).collect::<Vec<_>>();
            if specs.is_empty() {
                return Err(failure("fixture-merge needs at least one spec.kore"));
            }
            fixture_merge(
                &semantics,
                &output,
                &semantic_module,
                &read_cases(&cases_path)?,
                &specs,
            )
        }
        _ => Err(failure(format!(
            "unknown command {command:?}; expected split, compare, or fixture-merge"
        ))),
    }
}

fn split(
    input: &Path,
    output: &Path,
    semantic_module: &str,
    cases: &Cases,
) -> Result<(), Box<dyn Error>> {
    if output.exists() {
        return Err(failure(format!(
            "refusing to overwrite output directory {}",
            output.display()
        )));
    }
    validate_cases(cases)?;
    let mut definition = parse_definition(&fs::read_to_string(input)?)?;
    let module_index = unique_module_index(&definition, semantic_module)?;

    let mut selected = BTreeMap::<String, Sentence>::new();
    let mut retained = Vec::new();
    for sentence in definition.modules[module_index].sentences.drain(..) {
        if let Sentence::Claim { attributes, .. } = &sentence
            && let Some(label) = string_attribute(attributes, "label")?
            && cases.cases.iter().any(|case| case.native_label == label)
        {
            let label = label.to_owned();
            if selected.insert(label.clone(), sentence).is_some() {
                return Err(failure(format!("duplicate native claim label {label:?}")));
            }
        } else {
            retained.push(sentence);
        }
    }
    definition.modules[module_index].sentences = retained;

    let remaining_claims = definition.modules[module_index]
        .sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Claim { attributes, .. } => {
                string_attribute(attributes, "label").transpose()
            }
            _ => None,
        })
        .collect::<Result<Vec<_>, _>>()?;
    if !remaining_claims.is_empty() {
        return Err(failure(format!(
            "unowned claims remain in the execution module: {remaining_claims:?}; add each exact owned label to cases.json"
        )));
    }

    fs::create_dir_all(output.join("specs"))?;
    let printer = Printer::pretty(100);
    fs::write(
        output.join("definition.kore"),
        with_newline(printer.print_definition(&definition)),
    )?;

    for case in &cases.cases {
        let sentence = selected.remove(&case.native_label).ok_or_else(|| {
            failure(format!("missing native claim label {:?}", case.native_label))
        })?;
        validate_native_claim(&definition, &sentence, case)?;
        let spec = Definition {
            attributes: Attributes::default(),
            modules: vec![Module {
                name: case.source_module.clone(),
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
        fs::write(
            output.join("specs").join(format!("{}.kore", case.name)),
            with_newline(printer.print_definition(&spec)),
        )?;
    }
    if !selected.is_empty() {
        return Err(failure(format!(
            "selected claims were not consumed: {:?}",
            selected.keys().collect::<Vec<_>>()
        )));
    }
    println!(
        "SPLIT\tmodule={semantic_module}\tclaims={}\toutput={}",
        cases.cases.len(),
        output.display()
    );
    Ok(())
}

fn validate_native_claim(
    semantics: &Definition,
    claim: &Sentence,
    case: &Case,
) -> Result<(), Box<dyn Error>> {
    let Sentence::Claim {
        pattern,
        attributes,
        ..
    } = claim
    else {
        return Err(failure("selected sentence is not a KORE claim"));
    };
    let expected_wrapper = match case.modality.as_str() {
        "all-path" => "weakAlwaysFinally",
        "one-path" => "weakExistsFinally",
        other => return Err(failure(format!("unknown modality {other:?}"))),
    };
    let other_wrapper = if expected_wrapper == "weakAlwaysFinally" {
        "weakExistsFinally"
    } else {
        "weakAlwaysFinally"
    };
    if count_application(pattern, expected_wrapper) != 1
        || count_application(pattern, other_wrapper) != 0
    {
        return Err(failure(format!(
            "claim {:?} does not have exactly one {expected_wrapper} wrapper and no {other_wrapper} wrapper",
            case.native_label
        )));
    }
    if !has_attribute(attributes, &case.modality)
        || has_attribute(attributes, if case.modality == "all-path" { "one-path" } else { "all-path" })
    {
        return Err(failure(format!(
            "claim {:?} has inconsistent modality attributes",
            case.native_label
        )));
    }
    if has_attribute(attributes, "circularity") != case.circularity {
        return Err(failure(format!(
            "claim {:?} circularity differs from cases.json",
            case.native_label
        )));
    }
    let axiom_count = semantics
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter(|sentence| match sentence {
            Sentence::Axiom { attributes, .. } => {
                matches!(string_attribute(attributes, "label"), Ok(Some(label)) if label == case.native_label)
            }
            _ => false,
        })
        .count();
    if axiom_count != 0 {
        return Err(failure(format!(
            "claim label {:?} also labels {axiom_count} semantic axiom(s)",
            case.native_label
        )));
    }
    Ok(())
}

fn compare(
    source_path: &Path,
    native_path: &Path,
    source_label: &str,
    native_label: &str,
) -> Result<(), Box<dyn Error>> {
    let source = parse_definition(&fs::read_to_string(source_path)?)?;
    let native = parse_definition(&fs::read_to_string(native_path)?)?;
    let mut source_claim = unique_claim(&source, source_label)?.clone();
    let mut native_claim = unique_claim(&native, native_label)?.clone();
    normalize_claim(&mut source_claim);
    normalize_claim(&mut native_claim);
    if source_claim != native_claim {
        let printer = Printer::pretty(100);
        return Err(failure(format!(
            "normalized native Claim KORE differs from kprove Claim KORE\n--- kprove ---\n{}\n--- native ---\n{}",
            printer.print_sentence(&source_claim),
            printer.print_sentence(&native_claim)
        )));
    }
    println!("COMPARE\tsource={source_label}\tnative={native_label}\tequal=true");
    Ok(())
}

fn fixture_merge(
    semantics_path: &Path,
    output: &Path,
    semantic_module: &str,
    cases: &Cases,
    specs: &[PathBuf],
) -> Result<(), Box<dyn Error>> {
    validate_cases(cases)?;
    let mut semantics = parse_definition(&fs::read_to_string(semantics_path)?)?;
    let module_index = unique_module_index(&semantics, semantic_module)?;
    for case in &cases.cases {
        let mut matches = Vec::new();
        for spec in specs {
            let definition = parse_definition(&fs::read_to_string(spec)?)?;
            if let Ok(claim) = unique_claim(&definition, &case.source_claim) {
                matches.push(claim.clone());
            }
        }
        if matches.len() != 1 {
            return Err(failure(format!(
                "fixture expected one source claim {:?}, found {}",
                case.source_claim,
                matches.len()
            )));
        }
        let mut claim = matches.pop().expect("length checked");
        let Sentence::Claim { attributes, .. } = &mut claim else {
            unreachable!()
        };
        replace_string_attribute(attributes, "label", &case.native_label)?;
        if !has_attribute(attributes, &case.modality) {
            attributes.0.push(Pattern::Application {
                symbol: Symbol {
                    name: case.modality.clone(),
                    sort_parameters: Vec::new(),
                },
                arguments: Vec::new(),
            });
        }
        semantics.modules[module_index].sentences.push(claim);
    }
    fs::write(
        output,
        with_newline(Printer::pretty(100).print_definition(&semantics)),
    )?;
    println!("FIXTURE\tclaims={}\toutput={}", cases.cases.len(), output.display());
    Ok(())
}

fn validate_cases(cases: &Cases) -> Result<(), Box<dyn Error>> {
    let mut names = BTreeSet::new();
    let mut labels = BTreeSet::new();
    for case in &cases.cases {
        if !names.insert(&case.name) || !labels.insert(&case.native_label) {
            return Err(failure("duplicate case name or native label in cases.json"));
        }
        if !matches!(case.modality.as_str(), "all-path" | "one-path") {
            return Err(failure(format!(
                "unsupported modality {:?} for {}",
                case.modality, case.name
            )));
        }
    }
    Ok(())
}

fn unique_module_index(definition: &Definition, name: &str) -> Result<usize, Box<dyn Error>> {
    let matches = definition
        .modules
        .iter()
        .enumerate()
        .filter_map(|(index, module)| (module.name == name).then_some(index))
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [index] => Ok(*index),
        _ => Err(failure(format!(
            "expected one semantic KORE module {name:?}, found {}",
            matches.len()
        ))),
    }
}

fn unique_claim<'a>(definition: &'a Definition, label: &str) -> Result<&'a Sentence, Box<dyn Error>> {
    let mut matches = Vec::new();
    for sentence in definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
    {
        if let Sentence::Claim { attributes, .. } = sentence
            && string_attribute(attributes, "label")? == Some(label)
        {
            matches.push(sentence);
        }
    }
    match matches.as_slice() {
        [claim] => Ok(*claim),
        _ => Err(failure(format!(
            "expected one KORE claim labelled {label:?}, found {}",
            matches.len()
        ))),
    }
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
                "attribute {name:?} does not have one string argument"
            ))),
        },
        _ => Err(failure(format!("duplicate attribute {name:?}"))),
    }
}

fn replace_string_attribute(
    attributes: &mut Attributes,
    name: &str,
    replacement: &str,
) -> Result<(), Box<dyn Error>> {
    let mut count = 0;
    for attribute in &mut attributes.0 {
        if let Pattern::Application { symbol, arguments } = attribute
            && symbol.name == name
        {
            let [Pattern::String(value)] = arguments.as_mut_slice() else {
                return Err(failure(format!(
                    "attribute {name:?} does not have one string argument"
                )));
            };
            *value = replacement.to_owned();
            count += 1;
        }
    }
    if count != 1 {
        return Err(failure(format!(
            "expected one attribute {name:?}, found {count}"
        )));
    }
    Ok(())
}

fn has_attribute(attributes: &Attributes, name: &str) -> bool {
    attributes.0.iter().any(|attribute| {
        matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == name)
    })
}

fn count_application(pattern: &Pattern, name: &str) -> usize {
    let here = usize::from(matches!(
        pattern,
        Pattern::Application { symbol, .. } if symbol.name == name
    ));
    here + pattern_children(pattern)
        .into_iter()
        .map(|child| count_application(child, name))
        .sum::<usize>()
}

fn pattern_children(pattern: &Pattern) -> Vec<&Pattern> {
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => arguments.iter().collect(),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => vec![argument],
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => vec![left, right],
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => vec![body],
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => Vec::new(),
    }
}

fn normalize_claim(sentence: &mut Sentence) {
    let Sentence::Claim {
        pattern,
        attributes,
        ..
    } = sentence
    else {
        unreachable!()
    };
    const IGNORED: &[&str] = &[
        "label",
        "all-path",
        "one-path",
        "UNIQUE'Unds'ID",
        "org'Stop'kframework'Stop'attributes'Stop'Source",
        "org'Stop'kframework'Stop'attributes'Stop'Location",
        "org'Stop'kframework'Stop'definition'Stop'Production",
        "contentStartLine",
        "contentStartColumn",
        "digest",
        "productionID",
    ];
    attributes.0.retain(|attribute| {
        !matches!(attribute, Pattern::Application { symbol, .. } if IGNORED.contains(&symbol.name.as_str()))
    });
    attributes.0.sort();
    let mut variables = BTreeMap::<(VariableKind, String, Sort), String>::new();
    alpha_normalize_pattern(pattern, &mut variables);
    for attribute in &mut attributes.0 {
        alpha_normalize_pattern(attribute, &mut variables);
    }
}

fn alpha_normalize_pattern(
    pattern: &mut Pattern,
    names: &mut BTreeMap<(VariableKind, String, Sort), String>,
) {
    match pattern {
        Pattern::Variable(variable) => alpha_normalize_variable(variable, names),
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                alpha_normalize_pattern(argument, names);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => alpha_normalize_pattern(argument, names),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            alpha_normalize_pattern(left, names);
            alpha_normalize_pattern(right, names);
        }
        Pattern::Exists { variable, body, .. }
        | Pattern::Forall { variable, body, .. }
        | Pattern::Mu { variable, body }
        | Pattern::Nu { variable, body } => {
            alpha_normalize_variable(variable, names);
            alpha_normalize_pattern(body, names);
        }
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

fn alpha_normalize_variable(
    variable: &mut Variable,
    names: &mut BTreeMap<(VariableKind, String, Sort), String>,
) {
    let key = (variable.kind, variable.name.clone(), variable.sort.clone());
    let next = names.len();
    variable.name = names
        .entry(key)
        .or_insert_with(|| format!("VarAlpha{next}"))
        .clone();
}

fn read_cases(path: &Path) -> Result<Cases, Box<dyn Error>> {
    Ok(serde_json::from_str(&fs::read_to_string(path)?)?)
}

fn with_newline(mut text: String) -> String {
    if !text.ends_with('\n') {
        text.push('\n');
    }
    text
}

fn path(value: Option<std::ffi::OsString>, message: &str) -> Result<PathBuf, Box<dyn Error>> {
    value.map(PathBuf::from).ok_or_else(|| failure(message))
}

fn utf8(value: Option<std::ffi::OsString>, message: &str) -> Result<String, Box<dyn Error>> {
    value
        .ok_or_else(|| failure(message))?
        .into_string()
        .map_err(|_| failure("argument is not UTF-8"))
}

fn no_more(mut arguments: impl Iterator<Item = std::ffi::OsString>) -> Result<(), Box<dyn Error>> {
    if arguments.next().is_some() {
        Err(failure("too many arguments"))
    } else {
        Ok(())
    }
}

fn failure(message: impl Into<String>) -> Box<dyn Error> {
    Box::new(io::Error::other(message.into()))
}
