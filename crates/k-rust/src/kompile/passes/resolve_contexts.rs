//! Lower evaluation contexts into heat/cool rules and freezer productions.

use std::{collections::BTreeMap, collections::BTreeSet, fmt};

use serde_json::{Value, json};

use crate::{
    definition::{
        Attributes, Definition, LabelHead, ProductionCatalog, ProductionItem, ResolvedDefinition,
        Sentence,
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term},
};

use super::rebase_local_metadata;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveContextsError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveContextsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "context resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveContextsError {}

/// Apply Java's `ResolveContexts` definition transformation.
///
/// Visible contexts are materialized in the main module as a freezer production and paired heat
/// and cool rules. Imported modules remain unchanged, matching the reference definition-level
/// transformer.
pub fn resolve_contexts(definition: &Definition) -> Result<Definition, ResolveContextsError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(|error| ResolveContextsError {
            diagnostics: vec![plain_error(error.to_string())],
        })?;
    let main_id = resolved.main_module_id();
    let productions = resolved.production_catalog(main_id);
    let contexts = resolved
        .sentences(main_id)
        .into_iter()
        .filter(|sentence| matches!(sentence, Sentence::Context { .. }))
        .collect::<Vec<_>>();
    if contexts.is_empty() {
        return Ok(definition.clone());
    }

    let mut labels = productions
        .productions()
        .filter_map(|(_, sentence)| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let sentence_labels = resolved
        .sentences(main_id)
        .into_iter()
        .filter_map(|sentence| {
            sentence
                .attributes()
                .get_str("label")
                .map(|label| (label.to_owned(), sentence.attributes().clone()))
        })
        .collect::<BTreeMap<_, _>>();
    let mut generated = Vec::new();
    let mut diagnostics = Vec::new();
    for context in contexts {
        match resolve_context(context, &productions, &sentence_labels, &mut labels) {
            Ok(sentences) => extend_unique(&mut generated, sentences),
            Err(mut errors) => diagnostics.append(&mut errors),
        }
    }
    if !diagnostics.is_empty() {
        diagnostics.sort();
        diagnostics.dedup();
        return Err(ResolveContextsError { diagnostics });
    }

    let mut output = definition.clone();
    let main = output.main_module.clone();
    let main = output
        .modules
        .iter_mut()
        .find(|module| module.name == main)
        .expect("definition contains its main module");
    main.local_sentences
        .retain(|sentence| !matches!(sentence, Sentence::Context { .. }));
    if !generated.is_empty() {
        extend_unique(
            &mut generated,
            [Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::new("K"),
                attributes: Attributes::default(),
            }],
        );
        extend_unique(&mut main.local_sentences, generated);
    }
    rebase_local_metadata(definition, output).map_err(|message| ResolveContextsError {
        diagnostics: vec![plain_error(message)],
    })
}

fn resolve_context(
    context: &Sentence,
    productions: &ProductionCatalog<'_>,
    sentence_labels: &BTreeMap<String, Attributes>,
    labels: &mut BTreeSet<Label>,
) -> Result<Vec<Sentence>, Vec<Diagnostic>> {
    let Sentence::Context {
        body,
        requires,
        attributes,
    } = context
    else {
        unreachable!()
    };
    validate_context(body, attributes)?;
    let body = strip_metadata(body);
    let requires = strip_metadata(requires);
    let has_main_cell = contains_main_cell(&body, productions);
    let mut scan = HeatScan {
        productions,
        has_main_cell,
        in_main_cell: false,
        heated: None,
        hole: None,
        variables: BTreeMap::new(),
        current_hole_position: 0,
        final_hole_position: 0,
    };
    scan.visit(&body);
    let heated = scan
        .heated
        .or(scan.hole)
        .expect("validated contexts contain a hole");
    let variables = scan.variables;
    let left = rewrite_left(&body);
    let cooled = find_cooled(&left, productions).unwrap_or(left);
    let hint = freezer_hint(&cooled, scan.final_hole_position);
    let freezer_label = unique_freezer_label(labels, &hint);

    let mut freezer_items = vec![
        ProductionItem::Terminal(freezer_label.name.clone()),
        ProductionItem::Terminal("(".into()),
    ];
    for index in 0..variables.len() {
        if index > 0 {
            freezer_items.push(ProductionItem::Terminal(",".into()));
        }
        freezer_items.push(ProductionItem::NonTerminal {
            sort: Sort::new("K"),
            name: None,
        });
    }
    freezer_items.push(ProductionItem::Terminal(")".into()));
    let freezer = Sentence::Production {
        label: Some(freezer_label.clone()),
        parameters: Vec::new(),
        sort: Sort::new("KItem"),
        items: freezer_items,
        attributes: Attributes::default(),
    };
    let frozen = Term::Apply {
        label: freezer_label,
        arguments: variables.into_values().collect(),
    };

    let heat_attributes = rule_attributes(attributes, "heat", "-heat");
    let cool_attributes = rule_attributes(attributes, "cool", "-cool");
    for rule_attributes in [&heat_attributes, &cool_attributes] {
        if let Some(label) = rule_attributes.get_str("label")
            && let Some(conflict) = sentence_labels.get(label)
        {
            return Err(vec![error_at(
                format!(
                    "The generated label for a context rule conflicts with a user-defined label {label}. Please consider renaming."
                ),
                conflict,
            )]);
        }
    }

    let heated_and_frozen = Term::sequence([heated.clone(), frozen]);
    let heat_rewrite = Term::Rewrite {
        left: Box::new(cooled.clone()),
        right: Box::new(heated_and_frozen.clone()),
    };
    let cool_rewrite = Term::Rewrite {
        left: Box::new(heated_and_frozen),
        right: Box::new(cooled),
    };
    Ok(vec![
        freezer,
        Sentence::Rule {
            body: insert(body.clone(), heat_rewrite, productions).0,
            requires: requires.clone(),
            ensures: bool_token(true),
            attributes: heat_attributes,
        },
        Sentence::Rule {
            body: insert(body, cool_rewrite, productions).0,
            requires: bool_token(true),
            ensures: bool_token(true),
            attributes: cool_attributes,
        },
    ])
}

struct HeatScan<'a, 'definition> {
    productions: &'a ProductionCatalog<'definition>,
    has_main_cell: bool,
    in_main_cell: bool,
    heated: Option<Term>,
    hole: Option<Term>,
    variables: BTreeMap<String, Term>,
    current_hole_position: usize,
    final_hole_position: usize,
}

impl HeatScan<'_, '_> {
    fn visit(&mut self, term: &Term) {
        match term.unannotated() {
            Term::Rewrite { left, right } => {
                self.heated = Some((**right).clone());
                self.visit(left);
                self.visit(right);
            }
            Term::As { pattern, alias } => {
                self.visit(pattern);
                self.visit(alias);
            }
            Term::Sequence(items) => {
                for item in items {
                    self.visit(item);
                }
            }
            Term::Apply { label, arguments } => {
                let main_cell = is_main_cell(label, self.productions);
                if main_cell {
                    self.in_main_cell = true;
                }
                for argument in arguments {
                    self.visit(argument);
                }
                if main_cell {
                    self.in_main_cell = false;
                }
            }
            Term::Variable { name, .. } => {
                if self.in_main_cell || !self.has_main_cell {
                    if name == "HOLE" {
                        self.hole = Some(term.clone());
                        self.final_hole_position = self.current_hole_position;
                    } else {
                        self.variables.insert(name.clone(), term.clone());
                        self.current_hole_position += 1;
                    }
                }
            }
            Term::InjectedLabel(_) | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!(),
        }
    }
}

fn validate_context(body: &Term, attributes: &Attributes) -> Result<(), Vec<Diagnostic>> {
    let mut holes = BTreeSet::new();
    let mut rewrites = Vec::new();
    body.visit_preorder(&mut |term| match term.unannotated() {
        Term::Variable { name, .. } if name == "HOLE" => {
            holes.insert(term.clone());
        }
        Term::Rewrite { .. } if !rewrites.contains(&term.clone()) => rewrites.push(term.clone()),
        _ => {}
    });
    if holes.is_empty() {
        return Err(vec![error_at(
            "Contexts must have at least one HOLE.",
            attributes,
        )]);
    }
    if rewrites.len() > 1 {
        return Err(vec![error_at(
            "Cannot compile a context with multiple rewrites.",
            attributes,
        )]);
    }
    for rewrite in rewrites {
        let Term::Rewrite { left, .. } = rewrite.unannotated() else {
            unreachable!()
        };
        if !is_hole(left) {
            return Err(vec![error_at(
                "Only the HOLE can be rewritten in a context definition",
                attributes,
            )]);
        }
    }
    Ok(())
}

fn is_hole(term: &Term) -> bool {
    match term.unannotated() {
        Term::Variable { name, .. } => name == "HOLE",
        Term::Apply { label, arguments }
            if label.name.starts_with("#SemanticCastTo") && arguments.len() == 1 =>
        {
            matches!(
                arguments[0].unannotated(),
                Term::Variable { name, .. } if name == "HOLE"
            )
        }
        _ => false,
    }
}

fn contains_main_cell(term: &Term, productions: &ProductionCatalog<'_>) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        if let Term::Apply { label, .. } = term.unannotated()
            && is_main_cell(label, productions)
        {
            found = true;
        }
    });
    found
}

fn is_main_cell(label: &Label, productions: &ProductionCatalog<'_>) -> bool {
    productions
        .attributes_for(&LabelHead::from(label))
        .is_some_and(|attributes| attributes.get("maincell").is_some())
}

fn find_cooled(term: &Term, productions: &ProductionCatalog<'_>) -> Option<Term> {
    fn visit(term: &Term, productions: &ProductionCatalog<'_>, cooled: &mut Option<Term>) {
        match term.unannotated() {
            Term::Apply { label, arguments } => {
                if is_main_cell(label, productions)
                    && let Some(body) = arguments.get(1)
                {
                    *cooled = Some(body.clone());
                }
                for argument in arguments {
                    visit(argument, productions, cooled);
                }
            }
            Term::Rewrite { left, right }
            | Term::As {
                pattern: left,
                alias: right,
            } => {
                visit(left, productions, cooled);
                visit(right, productions, cooled);
            }
            Term::Sequence(items) => {
                for item in items {
                    visit(item, productions, cooled);
                }
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!(),
        }
    }
    let mut cooled = None;
    visit(term, productions, &mut cooled);
    cooled
}

fn freezer_hint(cooled: &Term, hole_position: usize) -> String {
    let Term::Apply { label, arguments } = cooled.unannotated() else {
        return String::new();
    };
    let name = if label.name == "#SemanticCastToK" {
        arguments
            .first()
            .and_then(|argument| match argument.unannotated() {
                Term::Apply { label, .. } => Some(label.name.as_str()),
                _ => None,
            })
            .unwrap_or(&label.name)
    } else {
        &label.name
    };
    format!("{name}{hole_position}")
}

fn unique_freezer_label(labels: &mut BTreeSet<Label>, hint: &str) -> Label {
    let mut attempt = 0usize;
    loop {
        let suffix = if attempt == 0 {
            String::new()
        } else {
            (attempt + 1).to_string()
        };
        let label = Label::new(format!("#freezer{hint}_{suffix}"));
        if labels.insert(label.clone()) {
            return label;
        }
        attempt += 1;
    }
}

fn rule_attributes(source: &Attributes, marker: &str, suffix: &str) -> Attributes {
    let mut attributes = source.clone();
    attributes.insert(marker, json!(""));
    if let Some(label) = source.get_str("label") {
        attributes.insert("label", Value::String(format!("{label}{suffix}")));
    }
    attributes
}

fn insert(term: Term, rewrite: Term, productions: &ProductionCatalog<'_>) -> (Term, bool) {
    let (inserted, found) = insert_inner(term, &rewrite, productions);
    if found {
        (inserted, true)
    } else {
        (rewrite, false)
    }
}

fn insert_inner(term: Term, rewrite: &Term, productions: &ProductionCatalog<'_>) -> (Term, bool) {
    match term {
        Term::Annotated { term, metadata } => {
            let (term, found) = insert_inner(*term, rewrite, productions);
            (term.with_metadata(metadata), found)
        }
        Term::Apply { label, arguments } if is_main_cell(&label, productions) => {
            if let [left, _, right] = arguments.as_slice() {
                (
                    Term::Apply {
                        label,
                        arguments: vec![left.clone(), rewrite.clone(), right.clone()],
                    },
                    true,
                )
            } else {
                (Term::Apply { label, arguments }, false)
            }
        }
        Term::Rewrite { left, right } => {
            let (left, left_found) = insert_inner(*left, rewrite, productions);
            let (right, right_found) = insert_inner(*right, rewrite, productions);
            (
                Term::Rewrite {
                    left: Box::new(left),
                    right: Box::new(right),
                },
                left_found || right_found,
            )
        }
        Term::As { pattern, alias } => {
            let (pattern, pattern_found) = insert_inner(*pattern, rewrite, productions);
            let (alias, alias_found) = insert_inner(*alias, rewrite, productions);
            (
                Term::As {
                    pattern: Box::new(pattern),
                    alias: Box::new(alias),
                },
                pattern_found || alias_found,
            )
        }
        Term::Sequence(items) => {
            let mut found = false;
            let items = items
                .into_iter()
                .map(|item| {
                    let (item, item_found) = insert_inner(item, rewrite, productions);
                    found |= item_found;
                    item
                })
                .collect();
            (Term::Sequence(items), found)
        }
        Term::Apply { label, arguments } => {
            let mut found = false;
            let arguments = arguments
                .into_iter()
                .map(|argument| {
                    let (argument, argument_found) = insert_inner(argument, rewrite, productions);
                    found |= argument_found;
                    argument
                })
                .collect();
            (Term::Apply { label, arguments }, found)
        }
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => {
            (leaf, false)
        }
    }
}

fn rewrite_left(term: &Term) -> Term {
    match term {
        Term::Annotated { term, metadata } => match term.unannotated() {
            Term::Rewrite { left, .. } => rewrite_left(left),
            _ => rewrite_left(term).with_metadata(metadata.clone()),
        },
        Term::Rewrite { left, .. } => rewrite_left(left),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments.iter().map(rewrite_left).collect(),
        },
        Term::Sequence(items) => Term::Sequence(items.iter().map(rewrite_left).collect()),
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rewrite_left(pattern)),
            alias: alias.clone(),
        },
        term => term.clone(),
    }
}

fn strip_metadata(term: &Term) -> Term {
    match term.unannotated() {
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(strip_metadata(left)),
            right: Box::new(strip_metadata(right)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(strip_metadata(pattern)),
            alias: Box::new(strip_metadata(alias)),
        },
        Term::Sequence(items) => Term::Sequence(items.iter().map(strip_metadata).collect()),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments.iter().map(strip_metadata).collect(),
        },
        term => term.clone(),
    }
}

fn bool_token(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::new("Bool"),
    }
}

fn extend_unique(target: &mut Vec<Sentence>, additions: impl IntoIterator<Item = Sentence>) {
    for sentence in additions {
        if !target.contains(&sentence) {
            target.push(sentence);
        }
    }
}

fn error_at(message: impl Into<String>, attributes: &Attributes) -> Diagnostic {
    Diagnostic::error_at(DiagnosticCode::InvalidContext, message, attributes)
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidContext,
        message: message.into(),
        source: None,
        location: None,
    }
}
