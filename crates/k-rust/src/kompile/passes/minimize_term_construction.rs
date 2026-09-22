//! This D12 transformation pass resolves required views, transforms sentences and terms, records origins, and rebases metadata when needed.
//! Its named `--timings` phase measures total cost; kompile counters measure resolution, rebasing, and transformed sentences.
//!
//! Reuse LHS subterms that also occur on a rule RHS through `#as` aliases.

use std::collections::{BTreeMap, BTreeSet};

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{Definition, LabelHead, ProductionCatalog, Sentence},
    kast::{InternalLabel, Sort, Term},
    kompile::fresh_names::FreshNames,
    provenance::GeneratingPass,
};

use super::super::{TermConversionError, TermConverter};

/// Apply Java's final `MinimizeTermConstruction` transformation before KORE emission.
pub fn minimize_term_construction(
    definition: &Definition,
) -> Result<Definition, TermConversionError> {
    super::super::pipeline::run_standalone(
        definition,
        minimize_term_construction_pass,
        Some(GeneratingPass::MinimizeTermConstruction),
    )
}

pub(crate) fn minimize_term_construction_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, TermConversionError> {
    let resolved = input
        .resolved_raw()
        .map_err(|error| TermConversionError::Definition(error.clone()))?;
    // Java constructs one minimizer from the final main module and applies it to every
    // sentence visible through that module. In particular, compiler-generated symbols such as
    // `<generatedTop>` may be declared in the main module while occurring in imported rules.
    let main_module = resolved
        .module_id(&input.definition.main_module)
        .expect("resolved definition contains its main module");
    let views = resolved.views();
    let main_productions = views.production_catalog(main_module);
    let main_converter = TermConverter::with_views(&views, main_module)?;
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        let converter = TermConverter::with_views(&views, module_id)?;
        for sentence in &mut module.local_sentences {
            let sentence = crate::definition::sentence_mut(sentence);
            let Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } = sentence
            else {
                continue;
            };
            if attributes.has(AttributeKey::Simplification) {
                continue;
            }
            let fresh = FreshNames::for_terms([&*body, &*requires, &*ensures]);
            let mut minimizer = Minimizer::new(
                productions,
                &converter,
                main_productions,
                &main_converter,
                fresh,
            );
            minimizer.gather_terms(body, Position::Both, true, false)?;
            minimizer.gather_terms(requires, Position::Right, true, false)?;
            minimizer.gather_terms(ensures, Position::Right, true, false)?;
            minimizer.filter_rhs(body, Position::Both);
            minimizer.filter_rhs(requires, Position::Right);
            minimizer.filter_rhs(ensures, Position::Right);
            *body = minimizer.transform(body, Position::Both, false);
            *requires = minimizer.transform(requires, Position::Right, false);
            *ensures = minimizer.transform(ensures, Position::Right, false);
        }
    }
    Ok(output)
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Position {
    Both,
    Left,
    Right,
}

struct Minimizer<'use_, 'view, 'definition> {
    productions: &'use_ ProductionCatalog<'definition>,
    converter: &'use_ TermConverter<'view, 'definition>,
    main_productions: &'use_ ProductionCatalog<'definition>,
    main_converter: &'use_ TermConverter<'view, 'definition>,
    fresh: FreshNames,
    cache: BTreeMap<Term, Term>,
    used_on_rhs: BTreeSet<Term>,
}

impl<'use_, 'view, 'definition> Minimizer<'use_, 'view, 'definition> {
    fn new(
        productions: &'use_ ProductionCatalog<'definition>,
        converter: &'use_ TermConverter<'view, 'definition>,
        main_productions: &'use_ ProductionCatalog<'definition>,
        main_converter: &'use_ TermConverter<'view, 'definition>,
        fresh: FreshNames,
    ) -> Self {
        Self {
            productions,
            converter,
            main_productions,
            main_converter,
            fresh,
            cache: BTreeMap::new(),
            used_on_rhs: BTreeSet::new(),
        }
    }

    // Invariant: each recursive visit consumes one input node or follows an unvisited graph edge, so the finite input bounds the remaining visits.
    fn gather_terms(
        &mut self,
        term: &Term,
        position: Position,
        root: bool,
        in_bad: bool,
    ) -> Result<(), TermConversionError> {
        let term = term.unannotated();
        if position == Position::Left
            && !in_bad
            && !root
            && !matches!(term, Term::Variable { .. })
            && !is_true(term)
            && !self.cache.contains_key(term)
        {
            let sort = match self.converter.infer_sort(term) {
                Ok(sort) => sort,
                Err(local_error) => self
                    .main_converter
                    .infer_sort(term)
                    .map_err(|_| local_error)?,
            };
            let variable = self.new_variable(sort);
            self.cache.insert(term.clone(), variable);
        }
        match term {
            Term::Rewrite { left, right } => {
                self.gather_terms(left, Position::Left, root, in_bad)?;
                self.gather_terms(right, Position::Right, false, in_bad)?;
            }
            Term::As { pattern, alias } => {
                self.gather_terms(pattern, position, false, in_bad)?;
                self.gather_terms(alias, position, false, in_bad)?;
            }
            Term::Apply { label, arguments } => {
                let hook = self.hook(label);
                if is_blocked_collection_hook(hook) || label.is(InternalLabel::Or) {
                    return Ok(());
                }
                if hook == Some("MAP.element") {
                    if let Some(value) = arguments.get(1) {
                        self.gather_terms(value, position, false, in_bad)?;
                    }
                    return Ok(());
                }
                for argument in arguments {
                    self.gather_terms(argument, position, false, in_bad)?;
                }
            }
            Term::Sequence(items) => {
                for item in items {
                    self.gather_terms(item, position, false, in_bad)?;
                }
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!(),
        }
        Ok(())
    }

    // Invariant: each recursive call consumes one input node or follows an unvisited graph edge, so the finite input bounds the remaining calls.
    fn filter_rhs(&mut self, term: &Term, position: Position) {
        let term = term.unannotated();
        if position == Position::Right && self.cache.contains_key(term) {
            self.used_on_rhs.insert(term.clone());
            return;
        }
        match term {
            Term::Rewrite { left, right } => {
                self.filter_rhs(left, Position::Left);
                self.filter_rhs(right, Position::Right);
            }
            Term::As { pattern, alias } => {
                self.filter_rhs(pattern, position);
                self.filter_rhs(alias, position);
            }
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            } => {
                for item in items {
                    self.filter_rhs(item, position);
                }
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!(),
        }
    }

    // Invariant: each recursive visit consumes one input node or follows an unvisited graph edge, so the finite input bounds the remaining visits.
    fn transform(&self, term: &Term, position: Position, in_bad: bool) -> Term {
        if position == Position::Right
            && let Some(variable) = self.cache.get(term)
        {
            return variable.clone();
        }
        let metadata = term.metadata().cloned();
        let bare = term.unannotated();
        let transformed = match bare {
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.transform(left, Position::Left, in_bad)),
                right: Box::new(self.transform(right, Position::Right, in_bad)),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.transform(pattern, position, in_bad)),
                alias: Box::new(self.transform(alias, position, in_bad)),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .iter()
                    .map(|item| self.transform(item, position, in_bad))
                    .collect(),
            ),
            Term::Apply { label, arguments } => {
                let hook = self.hook(label);
                let arguments = if hook == Some("MAP.element") {
                    arguments
                        .iter()
                        .enumerate()
                        .map(|(index, argument)| self.transform(argument, position, index == 0))
                        .collect()
                } else {
                    let blocked =
                        in_bad || is_blocked_collection_hook(hook) || label.is(InternalLabel::Or);
                    arguments
                        .iter()
                        .map(|argument| self.transform(argument, position, blocked))
                        .collect()
                };
                Term::Apply {
                    label: label.clone(),
                    arguments,
                }
            }
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => {
                leaf.clone()
            }
            Term::Annotated { .. } => unreachable!(),
        };
        let transformed = metadata.map_or(transformed.clone(), |metadata| {
            transformed.with_metadata(metadata)
        });
        if position == Position::Left
            && !in_bad
            && self.used_on_rhs.contains(bare)
            && let Some(variable) = self.cache.get(bare)
        {
            Term::As {
                pattern: Box::new(transformed),
                alias: Box::new(variable.clone()),
            }
        } else {
            transformed
        }
    }

    fn new_variable(&mut self, sort: Sort) -> Term {
        Term::Variable {
            name: self.fresh.mint("_Gen"),
            sort: Some(sort),
        }
    }

    fn hook(&self, label: &crate::kast::Label) -> Option<&str> {
        self.productions
            .attributes_for(&LabelHead::from(label))
            .or_else(|| {
                self.main_productions
                    .attributes_for(&LabelHead::from(label))
            })
            .and_then(|attributes| attributes.string(AttributeKey::Hook))
    }
}

fn is_true(term: &Term) -> bool {
    matches!(
        term,
        Term::Token { token, sort } if token == "true" && sort.name == BuiltinSort::Bool.k_name()
    )
}

fn is_blocked_collection_hook(hook: Option<&str>) -> bool {
    matches!(
        hook,
        Some("SET.element" | "LIST.element" | "LIST.concat" | "MAP.concat" | "SET.concat")
    )
}
