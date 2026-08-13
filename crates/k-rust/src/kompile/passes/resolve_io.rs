//! Java-compatible resolution of configuration cells marked with `stream`.

use std::{fmt, ops::Range};

use crate::{
    definition::{
        Definition, FlatImport, LabelHead, ModuleId, ResolvedDefinition, Sentence,
        sentence_equivalent,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveIoError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveIoError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "I/O stream resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveIoError {}

#[derive(Clone)]
struct StreamProduction {
    sort: Sort,
    label: Label,
    stream: String,
    sentence: Sentence,
}

struct MetadataOrigin {
    module: usize,
    sentences: Range<usize>,
    source: ModuleId,
}

/// Instantiate K's builtin `STDIN-STREAM` and `STDOUT-STREAM` modules for user stream cells.
///
/// This is the second ordered KORE-backend pass. It replaces generated cell initializers with the
/// builtin stream contents, synthesizes stdin-unblocking rules for the one pattern supported by
/// Java, imports selected stream sentences under the user's cell label, and empties the two
/// template modules after instantiation.
pub fn resolve_io(definition: &Definition) -> Result<Definition, ResolveIoError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| ResolveIoError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let mut output = definition.clone();
    let mut diagnostics = Vec::new();
    let mut metadata_origins = Vec::new();

    for module_index in 0..output.modules.len() {
        let module_name = output.modules[module_index].name.clone();
        if matches!(module_name.as_str(), "STDIN-STREAM" | "STDOUT-STREAM") {
            continue;
        }
        let module_id = resolved
            .module_id(&module_name)
            .expect("resolved definition contains every source module");
        let streams = stream_productions(resolved.sentences(module_id), &mut diagnostics);
        if streams.is_empty() {
            continue;
        }

        let local_has_stream = output.modules[module_index]
            .local_sentences
            .iter()
            .any(|sentence| stream_name(sentence).is_some());
        let mut sentences = output.modules[module_index].local_sentences.clone();
        let original_sentences = sentences.len();

        for stream in &streams {
            let Some(contents) = builtin_initializer_contents(definition, stream, &mut diagnostics)
            else {
                continue;
            };
            sentences = sentences
                .into_iter()
                .map(|sentence| replace_initializer(sentence, stream, &contents))
                .collect();
        }

        for stream in streams.iter().filter(|stream| stream.stream == "stdin") {
            let generated =
                stdin_unblocking_rules(definition, stream, &sentences, &mut diagnostics);
            let start = sentences.len();
            extend_unique(&mut sentences, generated);
            metadata_origins.push(MetadataOrigin {
                module: module_index,
                sentences: start..sentences.len(),
                source: module_id,
            });
        }

        if local_has_stream {
            for stream in &streams {
                let imported = stream_module_sentences(definition, stream, &mut diagnostics);
                let start = sentences.len();
                extend_unique(&mut sentences, imported);
                let source_name = format!("{}-STREAM", stream.stream.to_uppercase());
                if let Some(source) = resolved.module_id(&source_name) {
                    metadata_origins.push(MetadataOrigin {
                        module: module_index,
                        sentences: start..sentences.len(),
                        source,
                    });
                }
            }
        }

        metadata_origins.push(MetadataOrigin {
            module: module_index,
            sentences: 0..original_sentences,
            source: module_id,
        });

        output.modules[module_index].local_sentences = sentences;
        for import in ["K-IO", "K-REFLECTION"] {
            if definition
                .modules
                .iter()
                .any(|module| module.name == import)
            {
                if !output.modules[module_index]
                    .imports
                    .iter()
                    .any(|existing| existing.name == import)
                {
                    output.modules[module_index].imports.push(FlatImport {
                        name: import.into(),
                        public: true,
                    });
                }
            } else {
                diagnostics.push(plain_error(format!("no such module: {import}")));
            }
        }
    }

    for module in &mut output.modules {
        if matches!(module.name.as_str(), "STDIN-STREAM" | "STDOUT-STREAM") {
            module.imports.clear();
            module.local_sentences.clear();
        }
    }

    if diagnostics.is_empty() {
        let target = match ResolvedDefinition::resolve(&output) {
            Ok(target) => target,
            Err(error) => {
                diagnostics.push(plain_error(error.to_string()));
                return Err(ResolveIoError { diagnostics });
            }
        };
        for origin in metadata_origins {
            let source = resolved.production_catalog(origin.source);
            let target_name = output.modules[origin.module].name.clone();
            let target_module = target
                .module_id(&target_name)
                .expect("resolved output contains every output module");
            let target_catalog = target.production_catalog(target_module);
            for sentence in &mut output.modules[origin.module].local_sentences[origin.sentences] {
                if let Err(message) =
                    super::rebase_sentence(sentence, &source, &target_catalog, &sentence_equivalent)
                {
                    diagnostics.push(plain_error(format!(
                        "failed to rebase I/O metadata from {} into {}: {message}",
                        resolved.module(origin.source).name,
                        target_name,
                    )));
                }
            }
        }
    }

    if diagnostics.is_empty() {
        Ok(output)
    } else {
        diagnostics.sort();
        diagnostics.dedup();
        Err(ResolveIoError { diagnostics })
    }
}

fn stream_productions(
    sentences: Vec<&Sentence>,
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<StreamProduction> {
    let mut streams = Vec::new();
    for sentence in sentences {
        let Sentence::Production {
            label,
            sort,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        let Some(stream) = attributes.get_str("stream") else {
            continue;
        };
        if !matches!(stream, "stdin" | "stdout") {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidIoStream,
                format!(
                    "Make sure you give the correct stream names: {stream}\nIt should be one of [stdin, stdout]"
                ),
                sentence,
            ));
            continue;
        }
        let Some(label) = label else {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidIoStream,
                "A stream cell production must have a KLabel.",
                sentence,
            ));
            continue;
        };
        let stream = StreamProduction {
            sort: sort.clone(),
            label: label.clone(),
            stream: stream.into(),
            sentence: sentence.clone(),
        };
        if !streams.iter().any(|existing: &StreamProduction| {
            existing.stream == stream.stream
                && LabelHead::from(&existing.label) == LabelHead::from(&stream.label)
        }) {
            streams.push(stream);
        }
    }
    streams
}

fn stream_name(sentence: &Sentence) -> Option<&str> {
    match sentence {
        Sentence::Production { attributes, .. } => attributes.get_str("stream"),
        _ => None,
    }
}

fn builtin_initializer_contents(
    definition: &Definition,
    stream: &StreamProduction,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<Vec<Term>> {
    let module = stream_module(definition, &stream.stream, diagnostics)?;
    let builtin_cell = format!("<{}>", stream.stream);
    let builtin_init = format!("init{}Cell", capitalize(&stream.stream));
    let matches = module.local_sentences.iter().filter_map(|sentence| {
        let Sentence::Rule { body, .. } = sentence else {
            return None;
        };
        rewrite_applications(body).and_then(|(left, right)| {
            (left.0.name == builtin_init && right.0.name == builtin_cell).then(|| right.1.to_vec())
        })
    });
    let contents = matches.collect::<Vec<_>>();
    if contents.len() == 1 {
        contents.into_iter().next().map(|contents| {
            contents
                .into_iter()
                .map(without_production_metadata)
                .collect()
        })
    } else {
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::InvalidIoStream,
            format!(
                "expected exactly one initializer for {builtin_cell} in {}-STREAM, found {}",
                stream.stream.to_uppercase(),
                contents.len()
            ),
            &stream.sentence,
        ));
        None
    }
}

fn replace_initializer(
    sentence: Sentence,
    stream: &StreamProduction,
    contents: &[Term],
) -> Sentence {
    let Sentence::Rule {
        body,
        requires,
        ensures,
        attributes,
    } = sentence
    else {
        return sentence;
    };
    let init_label = format!("init{}", stream.sort.name);
    let body = replace_initializer_body(body, &init_label, &stream.label.name, contents);
    Sentence::Rule {
        body,
        requires,
        ensures,
        attributes,
    }
}

fn replace_initializer_body(
    body: Term,
    init_label: &str,
    cell_label: &str,
    contents: &[Term],
) -> Term {
    match body {
        Term::Annotated { term, metadata } => {
            replace_initializer_body(*term, init_label, cell_label, contents)
                .with_metadata(metadata)
        }
        Term::Rewrite { left, right } => {
            let is_initializer = matches!(left.unannotated(), Term::Apply { label, .. } if label.name == init_label)
                && matches!(right.unannotated(), Term::Apply { label, .. } if label.name == cell_label);
            if is_initializer {
                let right = replace_apply_arguments(*right, contents.to_vec());
                Term::Rewrite {
                    left,
                    right: Box::new(right),
                }
            } else {
                Term::Rewrite { left, right }
            }
        }
        body => body,
    }
}

fn replace_apply_arguments(term: Term, arguments: Vec<Term>) -> Term {
    match term {
        Term::Annotated { term, metadata } => {
            replace_apply_arguments(*term, arguments).with_metadata(metadata)
        }
        Term::Apply { label, .. } => Term::Apply { label, arguments },
        term => term,
    }
}

fn stream_module_sentences(
    definition: &Definition,
    stream: &StreamProduction,
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<Sentence> {
    let Some(module) = stream_module(definition, &stream.stream, diagnostics) else {
        return Vec::new();
    };
    let builtin_label = format!("<{}>", stream.stream);
    module
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } if attributes.get("stream").is_some() => Some(Sentence::Rule {
                body: rename_label(body.clone(), &builtin_label, &stream.label),
                requires: requires.clone(),
                ensures: ensures.clone(),
                attributes: attributes.clone(),
            }),
            Sentence::Rule { attributes, .. } if attributes.get("projection").is_some() => {
                Some(sentence.clone())
            }
            Sentence::Production {
                sort, attributes, ..
            } if sort.name == "Stream" || attributes.get("projection").is_some() => {
                Some(sentence.clone())
            }
            _ => None,
        })
        .collect()
}

fn stdin_unblocking_rules(
    definition: &Definition,
    stream: &StreamProduction,
    sentences: &[Sentence],
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<Sentence> {
    let Some(template) = stdin_unblock_template(definition, stream, diagnostics) else {
        return Vec::new();
    };
    let mut generated = Vec::new();
    for sentence in sentences {
        let Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } = sentence
        else {
            continue;
        };
        let mut occurrences = Vec::new();
        collect_stream_patterns(
            body,
            &stream.label.name,
            &mut occurrences,
            diagnostics,
            sentence,
        );
        if occurrences.len() > 1 {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidIoStream,
                "A stdin rule may match the stream cell at most once.",
                sentence,
            ));
            continue;
        }
        let Some(sort) = occurrences.into_iter().next() else {
            continue;
        };
        let replacement = instantiate_unblock(
            template.clone(),
            &stream.label,
            &sort,
            &format!("<{}>", stream.stream),
        );
        generated.push(Sentence::Rule {
            body: drop_rhs_and_replace_cell(body.clone(), &stream.label.name, &replacement),
            requires: requires.clone(),
            ensures: ensures.clone(),
            attributes: attributes.clone(),
        });
    }
    generated
}

fn stdin_unblock_template(
    definition: &Definition,
    stream: &StreamProduction,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<Term> {
    let module = stream_module(definition, "stdin", diagnostics)?;
    let templates = module
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("STDIN-STREAM.stdinUnblock") => {
                Some(without_production_metadata(body.clone()))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    if templates.len() == 1 {
        templates.into_iter().next()
    } else {
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::InvalidIoStream,
            format!(
                "expected exactly one STDIN-STREAM.stdinUnblock rule, found {}",
                templates.len()
            ),
            &stream.sentence,
        ));
        None
    }
}

fn collect_stream_patterns(
    term: &Term,
    cell_label: &str,
    sorts: &mut Vec<String>,
    diagnostics: &mut Vec<Diagnostic>,
    sentence: &Sentence,
) {
    let has_source_metadata = term
        .metadata()
        .is_some_and(|metadata| metadata.span.is_some());
    let term = term.unannotated();
    if let Term::Apply { label, arguments } = term
        && label.name == cell_label
    {
        if let Some(sort) = supported_stdin_pattern(arguments) {
            sorts.push(sort);
        } else if has_source_metadata {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidIoStream,
                "Unsupported matching pattern in stdin stream cell.\nThe currently supported pattern is: <in> ListItem(V:Sort) => .List ... </in>",
                sentence,
            ));
        }
    }
    match term {
        Term::Rewrite { left, right } => {
            collect_stream_patterns(left, cell_label, sorts, diagnostics, sentence);
            collect_stream_patterns(right, cell_label, sorts, diagnostics, sentence);
        }
        Term::As { pattern, alias } => {
            collect_stream_patterns(pattern, cell_label, sorts, diagnostics, sentence);
            collect_stream_patterns(alias, cell_label, sorts, diagnostics, sentence);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                collect_stream_patterns(item, cell_label, sorts, diagnostics, sentence);
            }
        }
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
        Term::Annotated { .. } => unreachable!(),
    }
}

fn supported_stdin_pattern(arguments: &[Term]) -> Option<String> {
    let [first, middle, last] = arguments else {
        return None;
    };
    if !is_nullary_apply(first, "#noDots") || !is_nullary_apply(last, "#dots") {
        return None;
    }
    let Term::Rewrite { left, right } = middle.unannotated() else {
        return None;
    };
    let Term::Apply {
        label: left_label,
        arguments: left_arguments,
    } = left.unannotated()
    else {
        return None;
    };
    if left_label.name != "ListItem"
        || left_arguments.len() != 1
        || !is_nullary_apply(right, ".List")
    {
        return None;
    }
    let Term::Apply {
        label: cast,
        arguments,
    } = left_arguments[0].unannotated()
    else {
        return None;
    };
    if !cast.name.starts_with("#SemanticCastTo")
        || arguments.len() != 1
        || !matches!(arguments[0].unannotated(), Term::Variable { .. })
    {
        return None;
    }
    cast.name.strip_prefix("#SemanticCastTo").map(str::to_owned)
}

fn is_nullary_apply(term: &Term, name: &str) -> bool {
    matches!(term.unannotated(), Term::Apply { label, arguments } if label.name == name && arguments.is_empty())
}

fn instantiate_unblock(term: Term, user_cell: &Label, sort: &str, builtin_cell: &str) -> Term {
    match term {
        Term::Annotated { term, metadata } => {
            instantiate_unblock(*term, user_cell, sort, builtin_cell).with_metadata(metadata)
        }
        Term::Apply { label, arguments }
            if label.name == "#SemanticCastToString" && arguments.len() == 1 =>
        {
            match arguments[0].unannotated() {
                Term::Variable { name, .. } if name == "?Sort" => Term::Token {
                    token: format!("\"{sort}\""),
                    sort: Sort::new("String"),
                },
                Term::Variable { name, .. } if name == "?Delimiters" => Term::Token {
                    token: "\" \\n\\t\\r\"".into(),
                    sort: Sort::new("String"),
                },
                _ => Term::Apply {
                    label,
                    arguments: arguments
                        .into_iter()
                        .map(|argument| {
                            instantiate_unblock(argument, user_cell, sort, builtin_cell)
                        })
                        .collect(),
                },
            }
        }
        Term::Apply { label, arguments } => Term::Apply {
            label: if label.name == builtin_cell {
                user_cell.clone()
            } else {
                label
            },
            arguments: arguments
                .into_iter()
                .map(|argument| instantiate_unblock(argument, user_cell, sort, builtin_cell))
                .collect(),
        },
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(instantiate_unblock(*left, user_cell, sort, builtin_cell)),
            right: Box::new(instantiate_unblock(*right, user_cell, sort, builtin_cell)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(instantiate_unblock(*pattern, user_cell, sort, builtin_cell)),
            alias: Box::new(instantiate_unblock(*alias, user_cell, sort, builtin_cell)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| instantiate_unblock(item, user_cell, sort, builtin_cell))
                .collect(),
        ),
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
    }
}

fn drop_rhs_and_replace_cell(term: Term, cell_label: &str, replacement: &Term) -> Term {
    match term {
        Term::Annotated { term, metadata } => {
            drop_rhs_and_replace_cell(*term, cell_label, replacement).with_metadata(metadata)
        }
        Term::Rewrite { left, .. } => drop_rhs_and_replace_cell(*left, cell_label, replacement),
        Term::Apply { label, .. } if label.name == cell_label => replacement.clone(),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| drop_rhs_and_replace_cell(argument, cell_label, replacement))
                .collect(),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(drop_rhs_and_replace_cell(*pattern, cell_label, replacement)),
            alias: Box::new(drop_rhs_and_replace_cell(*alias, cell_label, replacement)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| drop_rhs_and_replace_cell(item, cell_label, replacement))
                .collect(),
        ),
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
    }
}

fn rename_label(term: Term, from: &str, to: &Label) -> Term {
    match term {
        Term::Annotated { term, mut metadata } => {
            if matches!(term.unannotated(), Term::Apply { label, .. } if label.name == from) {
                metadata.production = None;
            }
            rename_label(*term, from, to).with_metadata(metadata)
        }
        Term::Apply { label, arguments } => Term::Apply {
            label: if label.name == from {
                to.clone()
            } else {
                label
            },
            arguments: arguments
                .into_iter()
                .map(|argument| rename_label(argument, from, to))
                .collect(),
        },
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(rename_label(*left, from, to)),
            right: Box::new(rename_label(*right, from, to)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rename_label(*pattern, from, to)),
            alias: Box::new(rename_label(*alias, from, to)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| rename_label(item, from, to))
                .collect(),
        ),
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
    }
}

fn without_production_metadata(term: Term) -> Term {
    match term {
        Term::Annotated { term, mut metadata } => {
            metadata.production = None;
            without_production_metadata(*term).with_metadata(metadata)
        }
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(without_production_metadata)
                .collect(),
        },
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(without_production_metadata(*left)),
            right: Box::new(without_production_metadata(*right)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(without_production_metadata(*pattern)),
            alias: Box::new(without_production_metadata(*alias)),
        },
        Term::Sequence(items) => {
            Term::Sequence(items.into_iter().map(without_production_metadata).collect())
        }
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
    }
}

type ApplicationRef<'a> = (&'a Label, &'a [Term]);

fn rewrite_applications(term: &Term) -> Option<(ApplicationRef<'_>, ApplicationRef<'_>)> {
    let Term::Rewrite { left, right } = term.unannotated() else {
        return None;
    };
    let Term::Apply {
        label: left_label,
        arguments: left_arguments,
    } = left.unannotated()
    else {
        return None;
    };
    let Term::Apply {
        label: right_label,
        arguments: right_arguments,
    } = right.unannotated()
    else {
        return None;
    };
    Some(((left_label, left_arguments), (right_label, right_arguments)))
}

fn stream_module<'a>(
    definition: &'a Definition,
    stream: &str,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<&'a crate::definition::FlatModule> {
    let name = format!("{}-STREAM", stream.to_uppercase());
    let module = definition.modules.iter().find(|module| module.name == name);
    if module.is_none() {
        diagnostics.push(plain_error(format!("no such module: {name}")));
    }
    module
}

fn extend_unique(sentences: &mut Vec<Sentence>, additions: Vec<Sentence>) {
    for sentence in additions {
        if !sentences.contains(&sentence) {
            sentences.push(sentence);
        }
    }
}

fn capitalize(value: &str) -> String {
    let mut chars = value.chars();
    chars
        .next()
        .map(|first| first.to_uppercase().chain(chars).collect())
        .unwrap_or_default()
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidIoStream,
        message: message.into(),
        source: None,
        location: None,
    }
}
