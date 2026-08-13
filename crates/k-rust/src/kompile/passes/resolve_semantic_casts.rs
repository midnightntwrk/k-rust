//! Remove semantic-cast applications while retaining their inferred sorts.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    definition::{Definition, Sentence},
    kast::{Sort, Term},
};

/// Apply the KORE backend form of Java's `ResolveSemanticCasts` pass.
///
/// The backend requests `skipSortPredicates = true`, so casts become compiler sort metadata but do
/// not add redundant `isSort` side conditions. Casted variables retain their inferred sort in the
/// public variable node as well.
pub fn resolve_semantic_casts(definition: &Definition) -> Definition {
    let mut output = definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            resolve_sentence(sentence);
        }
    }
    output
}

fn resolve_sentence(sentence: &mut Sentence) {
    let roots = match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => vec![body, requires, ensures],
        Sentence::Context { body, requires, .. } => vec![body, requires],
        _ => return,
    };

    let mut casts = BTreeSet::new();
    let mut typed_variables = BTreeMap::<String, Sort>::new();
    for root in &roots {
        root.visit_preorder(&mut |term| {
            let Term::Apply { label, arguments } = term.unannotated() else {
                return;
            };
            let Some(sort) = semantic_cast_sort(&label.name) else {
                return;
            };
            let [argument] = arguments.as_slice() else {
                return;
            };
            casts.insert(term.unannotated().clone());
            if let Term::Variable {
                name,
                sort: existing,
            } = argument.unannotated()
            {
                typed_variables.insert(name.clone(), existing.clone().unwrap_or(sort));
            }
        });
    }
    for root in roots {
        let taken = std::mem::replace(root, Term::Sequence(Vec::new()));
        *root = transform(taken, &casts, &typed_variables);
    }
}

fn transform(term: Term, casts: &BTreeSet<Term>, typed_variables: &BTreeMap<String, Sort>) -> Term {
    let source_metadata = term.metadata().cloned();
    if casts.contains(term.unannotated()) {
        let Term::Apply { label, arguments } = term.into_unannotated() else {
            unreachable!("the cast set contains applications only")
        };
        let sort = semantic_cast_sort(&label.name).expect("the cast set contains semantic casts");
        let [argument] = arguments
            .try_into()
            .unwrap_or_else(|_| unreachable!("only unary semantic casts enter the cast set"));
        return attach_sort(transform(argument, casts, typed_variables), sort);
    }

    let rebuilt = match term.into_unannotated() {
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(transform(*left, casts, typed_variables)),
            right: Box::new(transform(*right, casts, typed_variables)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(transform(*pattern, casts, typed_variables)),
            alias: Box::new(transform(*alias, casts, typed_variables)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| transform(item, casts, typed_variables))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| transform(argument, casts, typed_variables))
                .collect(),
        },
        Term::Variable { name, sort } => Term::Variable {
            sort: typed_variables.get(&name).cloned().or(sort),
            name,
        },
        leaf @ (Term::InjectedLabel(_) | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
    };
    source_metadata.map_or(rebuilt.clone(), |metadata| rebuilt.with_metadata(metadata))
}

fn attach_sort(term: Term, sort: Sort) -> Term {
    let metadata = term.metadata().cloned();
    match term.into_unannotated() {
        Term::Variable {
            name,
            sort: existing,
        } => {
            let variable = Term::Variable {
                name,
                sort: existing.or(Some(sort)),
            };
            metadata.map_or(variable.clone(), |metadata| {
                variable.with_metadata(metadata)
            })
        }
        term => {
            let mut metadata = metadata.unwrap_or_default();
            metadata.sort = Some(sort);
            term.with_metadata(metadata)
        }
    }
}

fn semantic_cast_sort(label: &str) -> Option<Sort> {
    label
        .strip_prefix("#SemanticCastTo")
        .filter(|name| !name.is_empty())
        .and_then(|name| crate::kast::parser::parse_sort_text(name).ok())
}
