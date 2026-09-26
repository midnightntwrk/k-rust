//! ```toml algorithm
//! id = "kompile.terms.minimize"
//! name = "minimization of repeated term construction"
//! sites = ["minimize_term_construction", "minimize_term_construction_pass", "Minimizer::gather_terms", "Minimizer::transform"]
//! variable = "N = rule term nodes; h = term height"
//! counters = []
//! no_counter = "term-construction minimization has no dedicated counter; the shared pass scaffolding bumps KompileResolveCalls, KompileSentenceCopies and KompilePartialOrdersBuilt, and KompileSentencesTransformed is added once per compile"
//!
//! [[cost]]
//! mode = "one rule"
//! bound = "O(N x h) subtree clones plus O(N log N) ordered-map probes keyed by whole subterms"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
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
            // Only non-simplification rules change; taking a mutable sentence copies a shared one.
            if !matches!(&**sentence, Sentence::Rule { attributes, .. }
                if !attributes.has(AttributeKey::Simplification))
            {
                continue;
            }
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

    // Invariant: `self.cache` maps each left-position subterm visited so far that is not the root, a variable, or `true`, and is not under `in_bad`, to a fresh variable; each call recurses into the immediate subterms of `term` except below blocked collection hooks and `Or`, so the finite `term` bounds the visit.
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

    // Invariant: `self.used_on_rhs` holds every right-position subterm visited so far that is a key of `self.cache`; the recursion stops at such a subterm and otherwise descends into the immediate subterms of `term`, so the finite `term` bounds the calls.
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

    // Invariant: a right-position `term` that is a key of `self.cache` becomes its variable without descending; otherwise each call rebuilds `term` from its transformed immediate subterms, so the finite `term` bounds the recursion.
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
        let transformed = match metadata {
            Some(metadata) => transformed.with_metadata(metadata),
            None => transformed,
        };
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
