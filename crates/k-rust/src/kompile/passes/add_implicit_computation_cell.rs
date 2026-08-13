//! Wrap cell-free semantic sentences in the declared computation cell.

use std::collections::BTreeSet;

use crate::{
    definition::{Definition, LabelHead, ProductionCatalog, ResolvedDefinition, Sentence},
    kast::{Label, Sort, Term},
};

const GENERATED_COUNTER_CELL: &str = "<generatedCounter>";
const MACRO_ATTRIBUTES: &[&str] = &["macro", "macro-rec", "alias", "alias-rec"];

/// Apply Java's `AddImplicitComputationCell` definition transformation.
pub fn add_implicit_computation_cell(definition: &Definition) -> Result<Definition, String> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| error.to_string())?;
    let mut output = definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = resolved.production_catalog(module_id);
        let cell_sorts = productions
            .productions()
            .filter(|(_, production)| production.attributes().get("cell").is_some())
            .filter_map(|(_, production)| match production {
                Sentence::Production { sort, .. } => Some(sort.clone()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let computation_cells = productions
            .productions()
            .filter_map(|(_, production)| match production {
                Sentence::Production {
                    label: Some(label),
                    sort,
                    attributes,
                    ..
                } if attributes.get("cell").is_some() && attributes.get("maincell").is_some() => {
                    Some((sort.clone(), label.clone()))
                }
                _ => None,
            })
            .collect::<BTreeSet<_>>();

        for sentence in &mut module.local_sentences {
            if skip_sentence(sentence) {
                continue;
            }
            let (body, is_claim) = match sentence {
                Sentence::Rule { body, .. } => (body, false),
                Sentence::Claim { body, .. } => (body, true),
                Sentence::Context { body, .. } => (body, false),
                _ => continue,
            };
            if is_function(body, &productions) {
                continue;
            }
            let items = flatten_cells(body);
            if !should_consider(&items, is_claim) || !can_wrap(items[0], &productions, &cell_sorts)
            {
                continue;
            }
            let computation = computation_cell(&computation_cells)?;
            *body = incomplete_cell(computation, items[0].clone());
        }
    }
    Ok(output)
}

fn skip_sentence(sentence: &Sentence) -> bool {
    MACRO_ATTRIBUTES
        .iter()
        .any(|attribute| sentence.attributes().get(attribute).is_some())
        || sentence.attributes().get("anywhere").is_some()
        || sentence.attributes().get("simplification").is_some()
}

fn is_function(term: &Term, productions: &ProductionCatalog<'_>) -> bool {
    let label = match term.unannotated() {
        Term::Apply { label, .. } => Some(label),
        Term::Rewrite { left, .. } => match left.unannotated() {
            Term::Apply { label, .. } => Some(label),
            _ => None,
        },
        _ => None,
    };
    label.is_some_and(|label| {
        productions
            .function_labels()
            .contains(&LabelHead::from(label))
    })
}

fn should_consider(items: &[&Term], is_claim: bool) -> bool {
    if items.len() == 1 {
        !is_claim
    } else if items.len() == 2 && is_claim {
        matches!(
            items[1].unannotated(),
            Term::Apply { label, .. } if label.name == GENERATED_COUNTER_CELL
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
    productions
        .result_sort_for(&LabelHead::from(label))
        .is_some_and(|sort| cell_sorts.contains(sort))
}

fn flatten_cells(term: &Term) -> Vec<&Term> {
    fn flatten<'a>(term: &'a Term, output: &mut Vec<&'a Term>) {
        match term.unannotated() {
            Term::Apply { label, arguments } if label.name == "#cells" => {
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

fn computation_cell(cells: &BTreeSet<(Sort, Label)>) -> Result<&Label, String> {
    match cells.len() {
        0 => Err("No main cell found".into()),
        1 => Ok(&cells.first().expect("length checked").1),
        _ => Err(format!(
            "Too many main cells: {}",
            cells
                .iter()
                .map(|(sort, _)| sort.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

fn incomplete_cell(label: &Label, body: Term) -> Term {
    Term::Apply {
        label: label.clone(),
        arguments: vec![
            Term::apply("#noDots", Vec::new()),
            body,
            Term::apply("#dots", Vec::new()),
        ],
    }
}
