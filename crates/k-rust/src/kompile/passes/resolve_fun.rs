//! Lower local `#fun`, `#let`, and K-matching expressions into generated functions.

use std::{collections::BTreeSet, fmt};

use serde_json::json;

use crate::{
    definition::{Attributes, Definition, ProductionItem, ResolvedDefinition, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term},
    kompile::{SortInjectionError, SortInjector, fresh_names::FreshNames},
    provenance::{GeneratingPass, record_generated_origins},
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
    resolve_fun_inner(definition)
        .map(|output| record_generated_origins(definition, output, GeneratingPass::ResolveFun))
}

fn resolve_fun_inner(definition: &Definition) -> Result<Definition, ResolveFunError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| ResolveFunError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let mut output = definition.clone();
    let mut diagnostics = Vec::new();
    let mut labels = definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();

    for module in &mut output.modules {
        let injector = match SortInjector::new(&resolved, &module.name) {
            Ok(injector) => injector,
            Err(error) => {
                diagnostics.push(sort_error(error));
                continue;
            }
        };
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
        // Java treats an uncast variable pattern as the unknown `K` sort in this LUB, regardless
        // of the concrete argument sort.
        let variable_pattern = underlying_variable(&left).is_some();
        let parameter_sort = match (lhs_sort, argument_sort) {
            _ if matches!(left.unannotated(), Term::Variable { .. }) => Sort::new("K"),
            (Some(lhs), Some(argument)) => self
                .injector
                .least_upper_bound(&[lhs.clone(), argument.clone()], None)
                .unwrap_or_else(|_| common_k_sort(&lhs, &argument)),
            _ => Sort::new("K"),
        };
        let closure = closure_variables(&body);
        let predicate = matches!(source_label.name.as_str(), "_:=K_" | "_:/=K_");

        let total =
            matches!(source_label.name.as_str(), "#fun2" | "#fun3" | "#let") && variable_pattern;
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
    // Java's closure pass is rewrite-aware: every variable occurring in an LHS anywhere in
    // the body (including nested local-function patterns) is bound.  A flat walk over the RHS
    // would otherwise mistake an inner lambda's parameter for an outer closure variable.
    let mut bound = BTreeSet::new();
    collect_lhs_variables(term, false, &mut bound);
    let mut result = Vec::new();
    let mut seen = BTreeSet::new();
    collect_rhs_variables(term, None, false, &mut |variable| {
        if variable.name != "THIS_CONFIGURATION"
            && !variable.name.starts_with('?')
            && !bound.contains(&variable.name)
            && seen.insert(variable.name.clone())
        {
            result.push(variable);
        }
    });
    result
}

fn collect_lhs_variables(term: &Term, in_lhs: bool, bound: &mut BTreeSet<String>) {
    match term.unannotated() {
        Term::Variable { name, .. } if in_lhs && !is_anonymous(name) => {
            bound.insert(name.clone());
        }
        Term::Variable { .. } => {}
        Term::Apply { label, arguments }
            if label.name.starts_with("#SemanticCastTo") && arguments.len() == 1 =>
        {
            collect_lhs_variables(&arguments[0], in_lhs, bound);
        }
        Term::Rewrite { left, right } => {
            collect_lhs_variables(left, true, bound);
            collect_lhs_variables(right, false, bound);
        }
        Term::Apply { label, arguments } if label.name == "#fun3" && arguments.len() >= 3 => {
            collect_lhs_variables(&arguments[0], true, bound);
            collect_lhs_variables(&arguments[1], false, bound);
            collect_lhs_variables(&arguments[2], in_lhs, bound);
        }
        Term::Apply { label, arguments } if label.name == "#let" && arguments.len() >= 3 => {
            collect_lhs_variables(&arguments[0], true, bound);
            collect_lhs_variables(&arguments[1], in_lhs, bound);
            collect_lhs_variables(&arguments[2], false, bound);
        }
        Term::Apply { label, arguments } if label.name == "#fun2" && arguments.len() >= 2 => {
            collect_lhs_variables(&arguments[0], false, bound);
            collect_lhs_variables(&arguments[1], in_lhs, bound);
        }
        Term::As { pattern, alias } => {
            collect_lhs_variables(pattern, in_lhs, bound);
            collect_lhs_variables(alias, in_lhs, bound);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                collect_lhs_variables(item, in_lhs, bound);
            }
        }
        Term::InjectedLabel(_) | Term::Token { .. } => {}
        Term::Annotated { .. } => unreachable!(),
    }
}

fn collect_rhs_variables(
    term: &Term,
    context: Option<&Sort>,
    in_lhs: bool,
    visitor: &mut impl FnMut(ClosureVariable),
) {
    match term.unannotated() {
        Term::Variable { name, sort } if !in_lhs => visitor(ClosureVariable {
            name: name.clone(),
            sort: context.cloned().or_else(|| sort.clone()),
        }),
        Term::Variable { .. } => {}
        Term::Apply { label, arguments }
            if label.name.starts_with("#SemanticCastTo") && arguments.len() == 1 =>
        {
            let sort = Sort::new(label.name.trim_start_matches("#SemanticCastTo"));
            collect_rhs_variables(&arguments[0], Some(&sort), in_lhs, visitor);
        }
        Term::Rewrite { left, right } => {
            collect_rhs_variables(left, context, true, visitor);
            collect_rhs_variables(right, context, false, visitor);
        }
        Term::Apply { label, arguments } if label.name == "#fun3" && arguments.len() >= 3 => {
            collect_rhs_variables(&arguments[0], context, true, visitor);
            collect_rhs_variables(&arguments[1], context, false, visitor);
            collect_rhs_variables(&arguments[2], context, in_lhs, visitor);
        }
        Term::Apply { label, arguments } if label.name == "#let" && arguments.len() >= 3 => {
            collect_rhs_variables(&arguments[0], context, true, visitor);
            collect_rhs_variables(&arguments[1], context, in_lhs, visitor);
            collect_rhs_variables(&arguments[2], context, false, visitor);
        }
        Term::Apply { label, arguments } if label.name == "#fun2" && arguments.len() >= 2 => {
            collect_rhs_variables(&arguments[0], context, false, visitor);
            collect_rhs_variables(&arguments[1], context, in_lhs, visitor);
        }
        Term::As { pattern, alias } => {
            collect_rhs_variables(pattern, context, in_lhs, visitor);
            collect_rhs_variables(alias, context, in_lhs, visitor);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                collect_rhs_variables(item, context, in_lhs, visitor);
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
    fn transform(term: Term, fresh: &mut FreshNames) -> Term {
        match term {
            Term::Annotated { term, metadata } => transform(*term, fresh).with_metadata(metadata),
            Term::Variable { name, sort } if is_anonymous(&name) => {
                let prefix = name.strip_suffix('_').unwrap_or_default();
                Term::Variable {
                    name: fresh.mint(&format!("{prefix}_Gen")),
                    sort,
                }
            }
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(transform(*left, fresh)),
                right: Box::new(transform(*right, fresh)),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(transform(*pattern, fresh)),
                alias: Box::new(transform(*alias, fresh)),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| transform(item, fresh))
                    .collect(),
            ),
            Term::Apply { label, arguments } => Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| transform(argument, fresh))
                    .collect(),
            },
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        }
    }
    let mut fresh = FreshNames::for_terms([&term]);
    transform(term, &mut fresh)
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
