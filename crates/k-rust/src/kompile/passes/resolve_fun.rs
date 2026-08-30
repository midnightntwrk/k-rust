//! Lower local `#fun`, `#let`, and K-matching expressions into generated functions.

use std::{collections::BTreeSet, fmt};

use serde_json::json;

use crate::{
    definition::{Attributes, Definition, ProductionItem, ResolvedDefinition, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term},
    kompile::{SortInjectionError, SortInjector},
};

use super::rebase_local_metadata;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveFunError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveFunError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "local function resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveFunError {}

/// Resolve Java's local-function and K-matching constructs.
///
/// Each occurrence gets a definition-wide-unused `#lambda...` label, a generated function
/// production, and one or more defining rules. Variables used only on the pattern RHS become
/// explicit closure arguments. Generated sentences remain local to the module containing the
/// expression, exactly as in Java's `ResolveFun` module transformer.
pub fn resolve_fun(definition: &Definition) -> Result<Definition, ResolveFunError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| ResolveFunError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let mut output = definition.clone();
    let mut diagnostics = Vec::new();

    for module in &mut output.modules {
        let injector = match SortInjector::new(&resolved, &module.name) {
            Ok(injector) => injector,
            Err(error) => {
                diagnostics.push(sort_error(error));
                continue;
            }
        };
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains source module");
        let mut labels = resolved
            .production_catalog(module_id)
            .productions()
            .filter_map(|(_, production)| match production {
                Sentence::Production {
                    label: Some(label), ..
                } => Some(label.name.clone()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut resolver = Resolver {
            injector,
            labels: &mut labels,
            productions: Vec::new(),
            rules: Vec::new(),
            diagnostics: &mut diagnostics,
        };
        let mut sentences = Vec::with_capacity(module.local_sentences.len());
        for sentence in &module.local_sentences {
            sentences.push(resolver.transform_sentence(sentence.clone()));
        }
        extend_unique(&mut sentences, resolver.productions);
        extend_unique(&mut sentences, resolver.rules);
        module.local_sentences = sentences;
    }

    if diagnostics.is_empty() {
        rebase_local_metadata(definition, output).map_err(|message| ResolveFunError {
            diagnostics: vec![plain_error(message)],
        })
    } else {
        diagnostics.sort();
        diagnostics.dedup();
        Err(ResolveFunError { diagnostics })
    }
}

struct Resolver<'a, 'definition> {
    injector: SortInjector<'definition>,
    labels: &'a mut BTreeSet<String>,
    productions: Vec<Sentence>,
    rules: Vec<Sentence>,
    diagnostics: &'a mut Vec<Diagnostic>,
}

impl Resolver<'_, '_> {
    fn transform_sentence(&mut self, sentence: Sentence) -> Sentence {
        match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } => Sentence::Rule {
                body: self.transform(body),
                requires: self.transform(requires),
                ensures: self.transform(ensures),
                attributes,
            },
            Sentence::Context {
                body,
                requires,
                attributes,
            } => Sentence::Context {
                body: self.transform(body),
                requires: self.transform(requires),
                attributes,
            },
            Sentence::ContextAlias {
                body,
                requires,
                attributes,
            } => Sentence::ContextAlias {
                body: self.transform(body),
                requires: self.transform(requires),
                attributes,
            },
            sentence => sentence,
        }
    }

    fn transform(&mut self, term: Term) -> Term {
        if let Some((label, arguments)) = special_application(&term) {
            return self.resolve_application(label, arguments, Attributes::default());
        }
        match term {
            Term::Annotated { term, metadata } => self.transform(*term).with_metadata(metadata),
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.transform(*left)),
                right: Box::new(self.transform(*right)),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.transform(*pattern)),
                alias: Box::new(self.transform(*alias)),
            },
            Term::Sequence(items) => {
                Term::Sequence(items.into_iter().map(|item| self.transform(item)).collect())
            }
            Term::Apply { label, arguments } => Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.transform(argument))
                    .collect(),
            },
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        }
    }

    fn resolve_application(
        &mut self,
        source_label: Label,
        arguments: Vec<Term>,
        attributes: Attributes,
    ) -> Term {
        let (body, argument) = match (source_label.name.as_str(), arguments.as_slice()) {
            ("#fun3", [left, right, argument]) => (
                Term::Rewrite {
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                },
                argument.clone(),
            ),
            ("#let", [left, argument, right]) => (
                Term::Rewrite {
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                },
                argument.clone(),
            ),
            (_, [body, argument]) => (body.clone(), argument.clone()),
            _ => {
                self.diagnostics.push(Diagnostic::error_at(
                    DiagnosticCode::InvalidLocalFunction,
                    format!(
                        "{} has invalid arity {}; expected {}",
                        source_label.name,
                        arguments.len(),
                        if matches!(source_label.name.as_str(), "#fun3" | "#let") {
                            3
                        } else {
                            2
                        }
                    ),
                    &attributes,
                ));
                return Term::Apply {
                    label: source_label,
                    arguments,
                };
            }
        };

        let hint1 = underlying_variable(&argument)
            .map(|(name, _)| name)
            .unwrap_or_default();
        let hint2 = match body.unannotated() {
            Term::Apply { label, .. } => label.name.clone(),
            _ => String::new(),
        };
        let lambda = self.unique_lambda(&hint1, &hint2);
        let left = rewrite_left(&body);
        let right = rewrite_right(&body);
        let lhs_sort = self.term_sort(&left, &attributes);
        let argument_sort = self.term_sort(&argument, &attributes);
        // Java treats variables as an unknown `K` sort in this LUB. A local-function pattern
        // headed by a (possibly cast) variable therefore adopts the concrete argument sort
        // instead of widening two incidental parser annotations to KItem/K.
        let variable_pattern = underlying_variable(&left).is_some();
        let singleton_user_list_pattern = variable_pattern
            && matches!(
                (&lhs_sort, &argument_sort),
                (Some(lhs), Some(argument))
                    if lhs != argument && self.injector.is_user_list_sort(argument)
            );
        let parameter_sort = match (lhs_sort, argument_sort) {
            (_, Some(argument)) if variable_pattern => argument,
            (Some(lhs), Some(argument)) => self
                .injector
                .least_upper_bound(&[lhs.clone(), argument.clone()], None)
                .unwrap_or_else(|_| common_k_sort(&lhs, &argument)),
            _ => Sort::new("K"),
        };
        let closure = closure_variables(&body);
        let predicate = matches!(source_label.name.as_str(), "_:=K_" | "_:/=K_");

        let total = matches!(source_label.name.as_str(), "#fun2" | "#fun3" | "#let")
            && variable_pattern
            && !singleton_user_list_pattern;
        let result_sort = if predicate {
            Sort::new("Bool")
        } else {
            self.term_sort(&right, &attributes)
                .unwrap_or_else(|| Sort::new("K"))
        };
        self.productions.push(lambda_production(
            &lambda,
            &closure,
            parameter_sort.clone(),
            result_sort,
            total,
        ));

        if predicate {
            let positive = self.lambda_rule(
                &lambda,
                &body,
                &body,
                attributes.clone(),
                LambdaResult::Constant(bool_token(true)),
            );
            self.rules.push(positive);
            let owise_pattern = Term::apply(
                format!("#SemanticCastTo{parameter_sort}"),
                vec![Term::variable("#Owise")],
            );
            let mut owise = attributes.clone();
            owise.insert("owise", json!(""));
            let negative = self.lambda_rule(
                &lambda,
                &owise_pattern,
                &body,
                owise,
                LambdaResult::Constant(bool_token(false)),
            );
            self.rules.push(negative);
        } else {
            let rule = self.lambda_rule(
                &lambda,
                &body,
                &body,
                attributes,
                LambdaResult::PatternRight,
            );
            self.rules.push(rule);
        }

        let mut call_arguments = vec![self.transform(argument)];
        call_arguments.extend(closure.into_iter().map(|variable| variable.term()));
        let call = Term::Apply {
            label: lambda,
            arguments: call_arguments,
        };
        if source_label.name == "_:/=K_" {
            Term::apply("notBool_", vec![call])
        } else {
            call
        }
    }

    fn lambda_rule(
        &mut self,
        lambda: &Label,
        pattern: &Term,
        closure_source: &Term,
        attributes: Attributes,
        result: LambdaResult,
    ) -> Sentence {
        let resolved = self.transform(pattern.clone());
        let with_anonymous = resolve_anonymous(resolved);
        let closure = closure_variables(closure_source);
        let mut arguments = vec![rewrite_left(&with_anonymous)];
        arguments.extend(closure.into_iter().map(|variable| variable.term()));
        let right = match result {
            LambdaResult::PatternRight => rewrite_right(&with_anonymous),
            LambdaResult::Constant(term) => term,
        };
        let body = rename_fresh_constants(Term::Rewrite {
            left: Box::new(Term::Apply {
                label: lambda.clone(),
                arguments,
            }),
            right: Box::new(right),
        });
        Sentence::Rule {
            body,
            requires: bool_token(true),
            ensures: bool_token(true),
            attributes,
        }
    }

    fn term_sort(&mut self, term: &Term, attributes: &Attributes) -> Option<Sort> {
        match self.injector.term_sort(term, None) {
            Ok(sort) => Some(sort),
            Err(error) => {
                self.diagnostics.push(Diagnostic::error_at(
                    DiagnosticCode::InvalidLocalFunction,
                    format!("Could not compute sort of local-function term: {error}"),
                    attributes,
                ));
                None
            }
        }
    }

    fn unique_lambda(&mut self, hint1: &str, hint2: &str) -> Label {
        let mut attempt = 0usize;
        loop {
            let suffix = if attempt == 0 {
                String::new()
            } else {
                (attempt + 1).to_string()
            };
            let name = format!("#lambda{hint1}_{hint2}_{suffix}");
            if self.labels.insert(name.clone()) {
                return Label::new(name);
            }
            attempt += 1;
        }
    }
}

enum LambdaResult {
    PatternRight,
    Constant(Term),
}

fn special_application(term: &Term) -> Option<(Label, Vec<Term>)> {
    let Term::Apply { label, arguments } = term.unannotated() else {
        return None;
    };
    matches!(
        label.name.as_str(),
        "#fun2" | "#fun3" | "#let" | "_:=K_" | "_:/=K_"
    )
    .then(|| (label.clone(), arguments.clone()))
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ClosureVariable {
    name: String,
    sort: Option<Sort>,
}

impl ClosureVariable {
    fn term(self) -> Term {
        Term::Variable {
            name: self.name,
            sort: self.sort,
        }
    }
}

fn closure_variables(term: &Term) -> Vec<ClosureVariable> {
    let left = rewrite_left(term);
    let right = rewrite_right(term);
    let mut bound = BTreeSet::new();
    collect_variables(&left, None, &mut |variable| {
        if !is_anonymous(&variable.name) {
            bound.insert(variable);
        }
    });
    let mut result = Vec::new();
    let mut seen = BTreeSet::new();
    collect_variables(&right, None, &mut |variable| {
        if variable.name != "THIS_CONFIGURATION"
            && !variable.name.starts_with('?')
            && !bound.contains(&variable)
            && seen.insert(variable.clone())
        {
            result.push(variable);
        }
    });
    result
}

fn collect_variables(
    term: &Term,
    context: Option<&Sort>,
    visitor: &mut impl FnMut(ClosureVariable),
) {
    match term.unannotated() {
        Term::Variable { name, sort } => visitor(ClosureVariable {
            name: name.clone(),
            sort: context.cloned().or_else(|| sort.clone()),
        }),
        Term::Apply { label, arguments }
            if label.name.starts_with("#SemanticCastTo") && arguments.len() == 1 =>
        {
            let sort = Sort::new(label.name.trim_start_matches("#SemanticCastTo"));
            collect_variables(&arguments[0], Some(&sort), visitor);
        }
        Term::Rewrite { left, right } => {
            collect_variables(left, context, visitor);
            collect_variables(right, context, visitor);
        }
        Term::As { pattern, alias } => {
            collect_variables(pattern, context, visitor);
            collect_variables(alias, context, visitor);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                collect_variables(item, context, visitor);
            }
        }
        Term::InjectedLabel(_) | Term::Token { .. } => {}
        Term::Annotated { .. } => unreachable!(),
    }
}

fn lambda_production(
    lambda: &Label,
    closure: &[ClosureVariable],
    argument: Sort,
    result: Sort,
    total: bool,
) -> Sentence {
    let mut items = vec![
        ProductionItem::Terminal(lambda.name.clone()),
        ProductionItem::Terminal("(".into()),
        ProductionItem::NonTerminal {
            sort: argument,
            name: None,
        },
    ];
    for variable in closure {
        items.push(ProductionItem::Terminal(",".into()));
        items.push(ProductionItem::NonTerminal {
            sort: variable.sort.clone().unwrap_or_else(|| Sort::new("K")),
            name: None,
        });
    }
    items.push(ProductionItem::Terminal(")".into()));
    let mut attributes = Attributes::default();
    attributes.insert("function", json!(""));
    if total {
        attributes.insert("total", json!(""));
    }
    Sentence::Production {
        label: Some(lambda.clone()),
        parameters: Vec::new(),
        sort: result,
        items,
        attributes,
    }
}

fn underlying_variable(term: &Term) -> Option<(String, Option<Sort>)> {
    match term.unannotated() {
        Term::Variable { name, sort } => Some((name.clone(), sort.clone())),
        Term::Apply { label, arguments }
            if label.name.starts_with("#SemanticCastTo") && arguments.len() == 1 =>
        {
            underlying_variable(&arguments[0])
        }
        _ => None,
    }
}

fn rewrite_left(term: &Term) -> Term {
    match term.unannotated() {
        Term::Rewrite { left, .. } => (**left).clone(),
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

fn rewrite_right(term: &Term) -> Term {
    match term.unannotated() {
        Term::Rewrite { right, .. } => rewrite_right(right),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments.iter().map(rewrite_right).collect(),
        },
        Term::Sequence(items) => Term::Sequence(items.iter().map(rewrite_right).collect()),
        Term::As { alias, .. } => (**alias).clone(),
        term => term.clone(),
    }
}

fn resolve_anonymous(term: Term) -> Term {
    let mut used = BTreeSet::new();
    term.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term {
            used.insert(name.clone());
        }
    });
    fn transform(term: Term, used: &mut BTreeSet<String>, counter: &mut usize) -> Term {
        match term {
            Term::Annotated { term, metadata } => {
                transform(*term, used, counter).with_metadata(metadata)
            }
            Term::Variable { name, sort } if is_anonymous(&name) => {
                let prefix = name.strip_suffix('_').unwrap_or_default();
                loop {
                    let candidate = format!("{prefix}_Gen{counter}");
                    *counter += 1;
                    if used.insert(candidate.clone()) {
                        return Term::Variable {
                            name: candidate,
                            sort,
                        };
                    }
                }
            }
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(transform(*left, used, counter)),
                right: Box::new(transform(*right, used, counter)),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(transform(*pattern, used, counter)),
                alias: Box::new(transform(*alias, used, counter)),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| transform(item, used, counter))
                    .collect(),
            ),
            Term::Apply { label, arguments } => Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| transform(argument, used, counter))
                    .collect(),
            },
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        }
    }
    transform(term, &mut used, &mut 0)
}

fn rename_fresh_constants(term: Term) -> Term {
    match term {
        Term::Annotated { term, metadata } => rename_fresh_constants(*term).with_metadata(metadata),
        Term::Variable { name, sort } if name.starts_with('!') => Term::Variable {
            name: format!("#_{}", &name[1..]),
            sort,
        },
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(rename_fresh_constants(*left)),
            right: Box::new(rename_fresh_constants(*right)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rename_fresh_constants(*pattern)),
            alias: Box::new(rename_fresh_constants(*alias)),
        },
        Term::Sequence(items) => {
            Term::Sequence(items.into_iter().map(rename_fresh_constants).collect())
        }
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments.into_iter().map(rename_fresh_constants).collect(),
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
    }
}

fn common_k_sort(left: &Sort, right: &Sort) -> Sort {
    if left == right {
        left.clone()
    } else if left.name == "K" || right.name == "K" {
        Sort::new("K")
    } else {
        Sort::new("KItem")
    }
}

fn bool_token(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::new("Bool"),
    }
}

fn is_anonymous(name: &str) -> bool {
    matches!(name, "_" | "?_" | "!_" | "@_")
}

fn extend_unique(sentences: &mut Vec<Sentence>, additions: Vec<Sentence>) {
    for sentence in additions {
        if !sentences.contains(&sentence) {
            sentences.push(sentence);
        }
    }
}

fn sort_error(error: SortInjectionError) -> Diagnostic {
    plain_error(error.to_string())
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidLocalFunction,
        message: message.into(),
        source: None,
        location: None,
    }
}
