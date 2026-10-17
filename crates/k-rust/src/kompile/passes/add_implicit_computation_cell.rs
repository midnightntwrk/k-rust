//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Wrap cell-free semantic sentences in the declared computation cell.
#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::BTreeSet;

use std::fmt;

use crate::definition::AttributeKey;
use crate::{
    definition::{
        Definition, LabelHead, LabelResultSort, ProductionCatalog, ProductionItem, Sentence,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{GeneratedCell, InternalLabel, Label, Sort, Term},
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AddImplicitComputationCellError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for AddImplicitComputationCellError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "implicit computation cell insertion produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for AddImplicitComputationCellError {}

/// Wrap cell-free semantic sentences in the declared computation cell.
pub fn add_implicit_computation_cell(
    definition: &Definition,
) -> Result<Definition, AddImplicitComputationCellError> {
    super::super::pipeline::run_standalone(
        definition,
        add_implicit_computation_cell_pass,
        Some(GeneratingPass::AddImplicitComputationCell),
    )
}

pub(crate) fn add_implicit_computation_cell_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, AddImplicitComputationCellError> {
    let resolved = input
        .resolved_raw()
        .map_err(|error| AddImplicitComputationCellError {
            diagnostics: vec![plain_error(error.to_string())],
        })?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    // Configuration and label information are derived once from the main module's closure: a
    // syntax module may contain generated strictness rules without importing the configuration
    // itself, and those rules still run in the main definition's computation cell.
    let configuration_productions = views.production_catalog(resolved.main_module_id());
    let cells = ComputationCells::of(configuration_productions);
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);

        for sentence in &mut module.local_sentences {
            // Only rules, claims and contexts that are not skipped change. The kind is decided
            // before taking a mutable sentence, which copies a shared one, so every other
            // sentence stays shared.
            if skip_sentence(sentence) {
                continue;
            }
            match &**sentence {
                Sentence::Rule { .. } | Sentence::Context { .. } | Sentence::Claim { .. } => {}
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => continue,
            }
            let wrapping = cells.wrapping(sentence, productions, configuration_productions);
            let sentence = crate::definition::sentence_mut(sentence);
            let computation = match wrapping {
                Ok(None) => continue,
                Ok(Some(cell)) => cell.label,
                Err(message) => {
                    return Err(AddImplicitComputationCellError {
                        diagnostics: vec![Diagnostic::error_at(
                            DiagnosticCode::InvalidMainCell,
                            message,
                            sentence.attributes(),
                        )],
                    });
                }
            };
            let body = match sentence {
                Sentence::Rule { body, .. }
                | Sentence::Claim { body, .. }
                | Sentence::Context { body, .. } => body,
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => {
                    unreachable!("copy-on-write keeps the kind decided above")
                }
            };
            let item = flatten_cells(body)[0].clone();
            *body = incomplete_cell(computation, item);
        }
    }
    Ok(output)
}

/// The cells of a configuration that decide whether compilation wraps a sentence's body in the
/// computation cell ([`ComputationCells::wrapping`]): the sorts of its cells and its main
/// cells, computed once per configuration catalog.
pub(crate) struct ComputationCells {
    cell_sorts: BTreeSet<Sort>,
    /// Each main cell's sort, label and content sort (the sort of its production's one
    /// nonterminal, `None` when it has not exactly one).
    main_cells: BTreeSet<(Sort, Label, Option<Sort>)>,
}

/// The computation cell a body is wrapped in, and the sort its body is placed at there.
pub(crate) struct ComputationCell<'a> {
    pub(crate) label: &'a Label,
    pub(crate) content: Option<&'a Sort>,
}

impl ComputationCells {
    /// The cells of `configuration`, the catalog compilation reads the configuration's cells
    /// from (the main module's).
    pub(crate) fn of(configuration: &ProductionCatalog<'_>) -> Self {
        let cell_sorts = configuration
            .productions()
            .filter(|(_, production)| production.attributes().has(AttributeKey::Cell))
            .filter_map(|(_, production)| match production {
                Sentence::Production { sort, .. } => Some(sort.clone()),
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => None,
            })
            .collect::<BTreeSet<_>>();
        let main_cells = configuration
            .productions()
            .filter_map(|(_, production)| match production {
                Sentence::Production {
                    label: Some(label),
                    sort,
                    items,
                    attributes,
                    ..
                } if attributes.has(AttributeKey::Cell)
                    && attributes.has(AttributeKey::Maincell) =>
                {
                    let mut contents = items.iter().filter_map(|item| match item {
                        ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                        ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
                    });
                    let content = match (contents.next(), contents.next()) {
                        (Some(content), None) => Some(content),
                        _ => None,
                    };
                    Some((sort.clone(), label.clone(), content))
                }
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => None,
            })
            .collect::<BTreeSet<_>>();
        Self {
            cell_sorts,
            main_cells,
        }
    }

    /// The computation cell compilation wraps the body of `sentence` in, `Ok(None)` when it
    /// leaves the body as written, or the error it stops at when the body is to be wrapped and
    /// the configuration has no main cell or several.
    ///
    /// `sentence` is a sentence as this pass receives it (macro attributes propagated),
    /// `productions` the catalog of the module that declares it, and `configuration` the catalog
    /// these cells were read from. A rule, claim or context is wrapped when it is not macro-like,
    /// `anywhere` or a simplification, its body is not a function rule, and its body is one item
    /// (a claim's: one item and the generated counter cell) that is not a cell and, for a
    /// rewrite, whose sides hold no cell.
    pub(crate) fn wrapping(
        &self,
        sentence: &Sentence,
        productions: &ProductionCatalog<'_>,
        configuration: &ProductionCatalog<'_>,
    ) -> Result<Option<ComputationCell<'_>>, String> {
        if skip_sentence(sentence) {
            return Ok(None);
        }
        let (body, is_claim) = match sentence {
            Sentence::Rule { body, .. } | Sentence::Context { body, .. } => (body, false),
            Sentence::Claim { body, .. } => (body, true),
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => return Ok(None),
        };
        if is_function(body, productions) {
            return Ok(None);
        }
        let items = flatten_cells(body);
        if !should_consider(&items, is_claim)
            || !can_wrap(items[0], configuration, &self.cell_sorts)
        {
            return Ok(None);
        }
        match self.main_cells.len() {
            0 => Err("No main cell found".into()),
            1 => {
                let (_, label, content) = self.main_cells.first().expect("length checked");
                Ok(Some(ComputationCell {
                    label,
                    content: content.as_ref(),
                }))
            }
            _ => Err(format!(
                "Too many main cells: {}",
                self.main_cells
                    .iter()
                    .map(|(sort, _, _)| sort.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
        }
    }
}

fn skip_sentence(sentence: &Sentence) -> bool {
    sentence.attributes().has_any(&AttributeKey::MACRO_LIKE)
        || sentence.attributes().has(AttributeKey::Anywhere)
        || sentence.attributes().has(AttributeKey::Simplification)
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidMainCell,
        message: message.into(),
        source: None,
        location: None,
        input_addresses: Vec::new(),
    }
}

/// Whether `term`, a rule body, is a function application or a rewrite whose left side is one: a
/// function rule's body, which compilation emits as an equation rather than in a cell.
pub(crate) fn is_function(term: &Term, productions: &ProductionCatalog<'_>) -> bool {
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
    let application = match term.unannotated() {
        Term::Apply { label, .. } => Some((term, label)),
        Term::Rewrite { left, .. } => match left.unannotated() {
            Term::Apply { label, .. } => Some((left.as_ref(), label)),
            _ => None,
        },
        _ => None,
    };
    application.is_some_and(|(application, label)| {
        is_function_application(application, label, productions)
    })
}

fn is_function_application(
    application: &Term,
    label: &Label,
    productions: &ProductionCatalog<'_>,
) -> bool {
    if let Some(resolved) = application
        .metadata()
        .and_then(|metadata| metadata.production)
    {
        if let Some(production_id) = productions.lookup(&resolved) {
            let production = productions.production(production_id);
            if matches!(
                production,
                Sentence::Production { label: Some(candidate), .. } if candidate.name == label.name
            ) {
                return production.attributes().has(AttributeKey::Function);
            }
        }
        let candidates = productions.productions_for(&LabelHead::from(label));
        return candidates.len() == 1
            && productions
                .production(candidates[0])
                .attributes()
                .value(AttributeKey::Function)
                .is_some();
    }
    productions
        .function_labels()
        .contains(&LabelHead::from(label))
}

fn should_consider(items: &[&Term], is_claim: bool) -> bool {
    if items.len() == 1 {
        !is_claim
    } else if items.len() == 2 && is_claim {
        matches!(
            items[1].unannotated(),
            Term::Apply { label, .. } if label.name == GeneratedCell::Counter.label()
        )
    } else {
        false
    }
}

fn can_wrap(item: &Term, productions: &ProductionCatalog<'_>, cell_sorts: &BTreeSet<Sort>) -> bool {
    if is_cell(item, productions, cell_sorts) {
        return false;
    }
    if let Term::Rewrite { left, right } = item.unannotated() {
        return flatten_cells(left)
            .into_iter()
            .chain(flatten_cells(right))
            .all(|term| !is_cell(term, productions, cell_sorts));
    }
    true
}

fn is_cell(term: &Term, productions: &ProductionCatalog<'_>, cell_sorts: &BTreeSet<Sort>) -> bool {
    let Term::Apply { label, .. } = term.unannotated() else {
        return false;
    };
    match productions.result_sort_of(&LabelHead::from(label)) {
        Some(LabelResultSort::Closed(sort)) => cell_sorts.contains(sort),
        Some(LabelResultSort::Schematic { .. }) | None => false,
    }
}

fn flatten_cells(term: &Term) -> Vec<&Term> {
    // Invariant: `output` holds, in left-to-right order, the non-`Cells` subterms reached so far through nested internal `Cells` applications; each call descends one level into the finite `term`.
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
    fn flatten<'a>(term: &'a Term, output: &mut Vec<&'a Term>) {
        match term.unannotated() {
            Term::Apply { label, arguments } if label.is(InternalLabel::Cells) => {
                for argument in arguments {
                    flatten(argument, output);
                }
            }
            _ => output.push(term),
        }
    }
    let mut output = Vec::new();
    flatten(term, &mut output);
    output
}

fn incomplete_cell(label: &Label, body: Term) -> Term {
    Term::Apply {
        label: label.clone(),
        arguments: vec![
            Term::apply(InternalLabel::NoDots.as_str(), Vec::new()),
            body,
            Term::apply(InternalLabel::Dots.as_str(), Vec::new()),
        ],
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::{
        builtin::embedded,
        definition::{Definition, Sentence},
        kompile::{
            CompilationBackend, CompileOptions, SentenceTyper,
            compile::compile_loaded_definition_observed,
        },
        outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation},
        timings::PhaseTimings,
    };

    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/support/typing_corpus.rs"
    ));

    /// `source` loaded as `tests/sentence_typing.rs` loads the corpus: the embedded `kast.md`
    /// and `prelude.md` implicit, `requires` from the embedded sources, then from `directory`.
    fn load(
        name: &str,
        source: &str,
        main: &str,
        directory: Option<&std::path::Path>,
    ) -> LoadedDefinition {
        let mut resolver = |_: &str, required: &str| {
            embedded(required)
                .or_else(|| {
                    let path = directory?.join(required);
                    let text = std::fs::read_to_string(&path).ok()?;
                    Some(ResolvedSource::new(
                        path.to_string_lossy().into_owned(),
                        text,
                    ))
                })
                .ok_or_else(|| required.to_owned())
        };
        load_for_compilation(
            ResolvedSource::new(name, source.to_owned()),
            main,
            None,
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![
                    embedded("kast.md").unwrap(),
                    embedded("prelude.md").unwrap(),
                ],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust
                        .excluded_module_attribute()
                        .to_owned(),
                ],
                ..LoadOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{name}: {error}"))
        .0
    }

    /// A rule or claim by its module, kind and source position: the key that finds a loaded
    /// sentence among the sentences a stage receives.
    type Key = (String, bool, String, String);

    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "only rules and claims are typed"
    )]
    fn key(module: &str, sentence: &Sentence) -> Option<Key> {
        let is_claim = match sentence {
            Sentence::Rule { .. } => false,
            Sentence::Claim { .. } => true,
            _ => return None,
        };
        let attributes = sentence.attributes();
        Some((
            module.to_owned(),
            is_claim,
            attributes.source()?.to_owned(),
            format!("{:?}", attributes.location()?),
        ))
    }

    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "only rules and claims are typed"
    )]
    fn body(sentence: &Sentence) -> &crate::kast::Term {
        match sentence {
            Sentence::Rule { body, .. } | Sentence::Claim { body, .. } => body,
            _ => unreachable!("keyed sentences are rules and claims"),
        }
    }

    /// Whether the computation-cell stage wrapped each located rule and claim it received, from
    /// its input and output (the stage maps each sentence to one, in order).
    fn wrapped(input: &Definition, output: &Definition) -> BTreeMap<Key, Vec<bool>> {
        let mut wrapped = BTreeMap::<Key, Vec<bool>>::new();
        for (before, after) in input.modules.iter().zip(&output.modules) {
            assert_eq!(before.name, after.name);
            assert_eq!(before.local_sentences.len(), after.local_sentences.len());
            for (sentence, result) in before.local_sentences.iter().zip(&after.local_sentences) {
                if let Some(key) = key(&before.name, sentence) {
                    wrapped
                        .entry(key)
                        .or_default()
                        .push(body(sentence) != body(result));
                }
            }
        }
        wrapped
    }

    /// The instances the view reports for `sentence`, a rule it types inside the computation
    /// cell, that differ from those of the rule written with that cell around its body
    /// (`<k>(#noDots, body, #dots)`), at the corresponding paths (`[0, p..]` against
    /// `[0, 1, p..]`).
    fn authored_instances_differ(
        loaded: &LoadedDefinition,
        typer: &SentenceTyper<'_>,
        sentence: &Sentence,
        module: &str,
    ) -> Vec<String> {
        let resolved = loaded.resolved();
        let catalog = resolved.production_catalog(resolved.main_module_id());
        let cells = super::ComputationCells::of(&catalog);
        let cell = cells
            .main_cells
            .first()
            .map(|(_, label, _)| label.clone())
            .expect("a wrapped sentence has a main cell");
        let mut authored = sentence.clone();
        let (Sentence::Rule { body, .. } | Sentence::Claim { body, .. }) = &mut authored else {
            unreachable!("keyed sentences are rules and claims")
        };
        *body = super::incomplete_cell(&cell, body.clone());
        let typing = typer.typing_in(sentence, module).unwrap();
        let in_cell = typer.typing_in(&authored, module).unwrap();
        typing
            .instances
            .iter()
            .filter_map(|(path, instance)| {
                let mapped = match path.as_slice() {
                    [0, rest @ ..] => [0, 1].iter().chain(rest).copied().collect::<Vec<_>>(),
                    other => other.to_vec(),
                };
                (in_cell.instances.get(&mapped) != Some(instance)).then(|| {
                    format!(
                        "{module}: instance at {path:?} {instance:?} against {:?}",
                        in_cell.instances.get(&mapped)
                    )
                })
            })
            .collect()
    }

    /// The decision the typing view reads (`SentenceTyper::computation_cell_content`) on each
    /// loaded rule and claim of a compiled definition's main closure is what the computation-cell
    /// pass did to it in that compile, which decides on the sentence the earlier passes produce.
    #[test]
    fn the_shared_decision_matches_the_compiled_wrapping() {
        let mut checked = 0;
        let mut wrapped_rules = 0;
        let mut failures = Vec::new();
        for (name, text, main, directory) in corpus() {
            let loaded = load(&name, &text, &main, directory.as_deref());
            let mut stage = None;
            let compiled = compile_loaded_definition_observed(
                &loaded,
                CompileOptions::default(),
                &mut PhaseTimings::default(),
                &mut |ran, input, output| {
                    if ran.name == "add implicit computation cell"
                        && let Ok(output) = output
                    {
                        stage = Some(wrapped(input, output));
                    }
                },
            );
            if compiled.is_err() {
                continue;
            }
            let stage = stage.expect("the computation-cell stage ran");
            let resolved = loaded.resolved();
            let typer = SentenceTyper::for_compilation(resolved).unwrap();
            let main_id = resolved.main_module_id();
            let closure = resolved.transitive_imports(main_id);
            for module in &loaded.definition().modules {
                let id = resolved.module_id(&module.name).unwrap();
                if id != main_id && !closure.contains(&id) {
                    continue;
                }
                for sentence in &module.local_sentences {
                    let Some(key) = key(&module.name, sentence) else {
                        continue;
                    };
                    let Some(compiled) = stage.get(&key) else {
                        failures.push(format!(
                            "{name} {}: not among the stage's sentences: {sentence:?}",
                            module.name
                        ));
                        continue;
                    };
                    let decided = typer
                        .computation_cell_content(sentence, &module.name)
                        .unwrap()
                        .is_some();
                    if compiled.iter().any(|wrapped| *wrapped != decided) {
                        failures.push(format!(
                            "{name} {}: decided {decided}, compiled {compiled:?}: {sentence:?}",
                            module.name
                        ));
                    }
                    if decided {
                        failures.extend(authored_instances_differ(
                            &loaded,
                            &typer,
                            sentence,
                            &module.name,
                        ));
                    }
                    checked += 1;
                    wrapped_rules += usize::from(decided);
                }
            }
        }
        assert!(failures.is_empty(), "{failures:#?}");
        assert!(checked >= 500, "only {checked} sentences checked");
        assert!(
            wrapped_rules >= 20,
            "only {wrapped_rules} wrapped sentences"
        );
    }
}
