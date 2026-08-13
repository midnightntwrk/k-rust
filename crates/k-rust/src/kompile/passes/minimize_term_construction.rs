//! Reuse LHS subterms that also occur on a rule RHS through `#as` aliases.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    definition::{Definition, LabelHead, ProductionCatalog, ResolvedDefinition, Sentence},
    kast::{Sort, Term},
};

use super::super::{TermConversionError, TermConverter};

/// Apply Java's final `MinimizeTermConstruction` transformation before KORE emission.
pub fn minimize_term_construction(
    definition: &Definition,
) -> Result<Definition, TermConversionError> {
    let resolved =
        ResolvedDefinition::resolve(definition).map_err(TermConversionError::Definition)?;
    let mut output = definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = resolved.production_catalog(module_id);
        let converter = TermConverter::new(&resolved, &module.name)?;
        for sentence in &mut module.local_sentences {
            let Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } = sentence
            else {
                continue;
            };
            if attributes.get("simplification").is_some() {
                continue;
            }
            let mut minimizer = Minimizer::new(&productions, &converter);
            minimizer.gather_variables(body);
            minimizer.gather_variables(requires);
            minimizer.gather_variables(ensures);
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

struct Minimizer<'a> {
    productions: &'a ProductionCatalog<'a>,
    converter: &'a TermConverter<'a>,
    variables: BTreeSet<(String, Option<Sort>)>,
    cache: BTreeMap<Term, Term>,
    used_on_rhs: BTreeSet<Term>,
    counter: usize,
}

impl<'a> Minimizer<'a> {
    fn new(productions: &'a ProductionCatalog<'a>, converter: &'a TermConverter<'a>) -> Self {
        Self {
            productions,
            converter,
            variables: BTreeSet::new(),
            cache: BTreeMap::new(),
            used_on_rhs: BTreeSet::new(),
            counter: 0,
        }
    }

    fn gather_variables(&mut self, term: &Term) {
        term.visit_preorder(&mut |term| {
            if let Term::Variable { name, sort } = term {
                self.variables.insert((name.clone(), sort.clone()));
            }
        });
    }

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
            let sort = self.converter.infer_sort(term)?;
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
                if is_blocked_collection_hook(hook) || label.name == "#Or" {
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
                    let blocked = in_bad || is_blocked_collection_hook(hook) || label.name == "#Or";
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
        loop {
            let name = format!("_Gen{}", self.counter);
            self.counter += 1;
            let key = (name.clone(), Some(sort.clone()));
            if self.variables.insert(key) {
                return Term::Variable {
                    name,
                    sort: Some(sort),
                };
            }
        }
    }

    fn hook(&self, label: &crate::kast::Label) -> Option<&str> {
        self.productions
            .attributes_for(&LabelHead::from(label))
            .and_then(|attributes| attributes.get_str("hook"))
    }
}

fn is_true(term: &Term) -> bool {
    matches!(
        term,
        Term::Token { token, sort } if token == "true" && sort.name == "Bool"
    )
}

fn is_blocked_collection_hook(hook: Option<&str>) -> bool {
    matches!(
        hook,
        Some("SET.element" | "LIST.element" | "LIST.concat" | "MAP.concat" | "SET.concat")
    )
}
