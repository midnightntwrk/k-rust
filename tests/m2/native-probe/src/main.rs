use std::{collections::BTreeMap, env, error::Error, fs, path::PathBuf};

use k_rust::{
    builtin,
    definition::json as definition_json,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{
        ast::{Attributes, Module, Pattern, Sentence},
        parser::parse_definition,
    },
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

fn main() {
    if let Err(error) = run() {
        eprintln!("native-reference-probe: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut arguments = env::args_os().skip(1);
    let command = arguments
        .next()
        .ok_or("missing command (compile or compare-kore)")?
        .into_string()
        .map_err(|_| "command is not UTF-8")?;
    match command.as_str() {
        "compile" => compile(arguments.collect()),
        "compare-kore" => compare_kore(arguments.collect()),
        _ => Err(format!("unknown command {command:?}").into()),
    }
}

fn compile(arguments: Vec<std::ffi::OsString>) -> Result<(), Box<dyn Error>> {
    let mut arguments = arguments.into_iter();
    let input = PathBuf::from(arguments.next().ok_or("missing DEFINITION argument")?);
    let module = arguments
        .next()
        .ok_or("missing MODULE argument")?
        .into_string()
        .map_err(|_| "MODULE is not UTF-8")?;
    let output = PathBuf::from(arguments.next().ok_or("missing OUTPUT argument")?);
    if arguments.next().is_some() {
        return Err("expected exactly DEFINITION MODULE OUTPUT".into());
    }

    let source = fs::read_to_string(&input)?;
    let entry = ResolvedSource::new(input.display().to_string(), source);
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("missing embedded source {required}"))
    };
    let loaded = load_with_options(
        entry,
        &module,
        &mut resolver,
        &LoadOptions {
            excluded_module_attributes: vec![
                CompilationBackend::Llvm
                    .excluded_module_attribute()
                    .into(),
            ],
            ..LoadOptions::default()
        },
    )?;
    let source_json = definition_json::to_string_pretty(&loaded.definition)?;
    definition_json::from_str(&source_json)?;
    let artifacts = compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Llvm,
            ..CompileOptions::default()
        },
    )?;

    parse_definition(&artifacts.definition_kore)?;
    parse_definition(&artifacts.syntax_definition_kore)?;
    fs::create_dir_all(&output)?;
    fs::write(output.join("source-definition.json"), source_json)?;
    fs::write(output.join("definition.kore"), artifacts.definition_kore)?;
    fs::write(
        output.join("syntaxDefinition.kore"),
        artifacts.syntax_definition_kore,
    )?;
    fs::write(output.join("macros.kore"), artifacts.macros_kore)?;
    println!(
        "native parse+compile+KORE-reparse passed (k-rust 0.3.0, K 7.1.337 pin)"
    );
    Ok(())
}

fn compare_kore(arguments: Vec<std::ffi::OsString>) -> Result<(), Box<dyn Error>> {
    let mut arguments = arguments.into_iter();
    let reference = PathBuf::from(arguments.next().ok_or("missing REFERENCE argument")?);
    let actual = PathBuf::from(arguments.next().ok_or("missing ACTUAL argument")?);
    let reference_module_name = arguments
        .next()
        .ok_or("missing REFERENCE_MODULE argument")?
        .into_string()
        .map_err(|_| "REFERENCE_MODULE is not UTF-8")?;
    let actual_module_name = arguments
        .next()
        .ok_or("missing ACTUAL_MODULE argument")?
        .into_string()
        .map_err(|_| "ACTUAL_MODULE is not UTF-8")?;
    if arguments.next().is_some() {
        return Err(
            "expected exactly compare-kore REFERENCE ACTUAL REFERENCE_MODULE ACTUAL_MODULE".into(),
        );
    }

    let reference_source = fs::read_to_string(reference)?;
    let actual_source = fs::read_to_string(actual)?;
    let reference = parse_definition(&reference_source)?;
    let actual = parse_definition(&actual_source)?;
    let reference = normalized_module(&reference.modules, &reference_module_name)?;
    let actual = normalized_module(&actual.modules, &actual_module_name)?;
    let reference = sentence_multiset(&reference.sentences);
    let actual = sentence_multiset(&actual.sentences);
    if reference != actual {
        let missing = multiset_difference(&reference, &actual);
        let extra = multiset_difference(&actual, &reference);
        return Err(format!(
            "normalized KORE sentence multiset differs for {reference_module_name} versus {actual_module_name}: reference={}, actual={}, missing={}, extra={}; first missing={:?}; first extra={:?}",
            reference.values().sum::<usize>(),
            actual.values().sum::<usize>(),
            missing.len(),
            extra.len(),
            missing.first().map(|value| excerpt(value, 600)),
            extra.first().map(|value| excerpt(value, 600)),
        )
        .into());
    }
    println!(
        "normalized KORE sentence multiset matches for {reference_module_name} versus {actual_module_name} ({} sentences)",
        reference.values().sum::<usize>()
    );
    Ok(())
}

fn normalized_module(modules: &[Module], name: &str) -> Result<Module, Box<dyn Error>> {
    let mut matches = modules.iter().filter(|module| module.name == name);
    let mut module = matches
        .next()
        .ok_or_else(|| format!("KORE module {name:?} is absent"))?
        .clone();
    if matches.next().is_some() {
        return Err(format!("KORE module {name:?} occurs more than once").into());
    }
    normalize_attributes(&mut module.attributes);
    for sentence in &mut module.sentences {
        let attributes = match sentence {
            Sentence::Import { attributes, .. }
            | Sentence::SortDeclaration { attributes, .. }
            | Sentence::SymbolDeclaration { attributes, .. }
            | Sentence::AliasDeclaration { attributes, .. }
            | Sentence::Axiom { attributes, .. }
            | Sentence::Claim { attributes, .. } => attributes,
        };
        normalize_attributes(attributes);
    }
    Ok(module)
}

fn normalize_attributes(attributes: &mut Attributes) {
    attributes.0.retain(|attribute| {
        !matches!(
            attribute,
            Pattern::Application { symbol, .. }
                if symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Location"
                    || symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Source"
                    || symbol.name == "UNIQUE'Unds'ID"
                    || symbol.name == "contentStartLine"
                    || symbol.name == "digest"
        )
    });
    attributes.0.sort();
}

fn sentence_multiset(sentences: &[Sentence]) -> BTreeMap<String, usize> {
    let mut result = BTreeMap::new();
    for sentence in sentences {
        *result.entry(canonical_sentence(sentence)).or_default() += 1;
    }
    result
}

fn canonical_sentence(sentence: &Sentence) -> String {
    let mut source = format!("{sentence:?}");
    for prefix in ["Var'Unds'Gen", "Var'Unds'DotVar"] {
        let mut canonical = String::with_capacity(source.len());
        let mut remaining = source.as_str();
        while let Some(index) = remaining.find(prefix) {
            canonical.push_str(&remaining[..index]);
            canonical.push_str(prefix);
            remaining = &remaining[index + prefix.len()..];
            remaining = remaining.trim_start_matches(|character: char| character.is_ascii_digit());
        }
        canonical.push_str(remaining);
        source = canonical;
    }
    source
}

fn multiset_difference(
    left: &BTreeMap<String, usize>,
    right: &BTreeMap<String, usize>,
) -> Vec<String> {
    left.iter()
        .flat_map(|(sentence, left_count)| {
            let count = left_count.saturating_sub(right.get(sentence).copied().unwrap_or_default());
            std::iter::repeat_n(sentence.clone(), count)
        })
        .collect()
}

fn excerpt(value: &str, limit: usize) -> String {
    let mut excerpt = value.chars().take(limit).collect::<String>();
    if value.chars().count() > limit {
        excerpt.push('…');
    }
    excerpt
}
