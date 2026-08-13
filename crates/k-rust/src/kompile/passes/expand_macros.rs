//! Expand compile-time macro and alias rules by structural matching.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use crate::{
    definition::{
        Attributes, Definition, LabelHead, ModuleId, ProductionCatalog, ResolvedDefinition,
        Sentence, SortCatalog,
        checks::{check_functions, check_smt_lemmas},
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term},
    kompile::SortInjector,
};

const MACRO_ATTRIBUTES: &[&str] = &["macro", "macro-rec", "alias", "alias-rec"];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpandMacrosError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ExpandMacrosError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "macro expansion produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ExpandMacrosError {}

#[derive(Clone)]
struct MacroRule {
    id: usize,
    sentence: Sentence,
    left: Term,
    right: Term,
    recursive: bool,
}

/// Apply Java's forward `ExpandMacros` sentence transformation.
pub fn expand_macros(definition: &Definition) -> Result<Definition, ExpandMacrosError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(|error| ExpandMacrosError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let mut output = definition.clone();
    let mut diagnostics = Vec::new();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let mut expander = match Expander::new(&resolved, module_id) {
            Ok(expander) => expander,
            Err(message) => {
                diagnostics.push(plain_error(message));
                continue;
            }
        };
        for sentence in &mut module.local_sentences {
            if matches!(sentence, Sentence::Rule { attributes, .. } if is_macro(attributes)) {
                continue;
            }
            if matches!(
                sentence,
                Sentence::Rule { .. } | Sentence::Claim { .. } | Sentence::Context { .. }
            ) {
                let original = sentence.clone();
                match expander.expand_sentence(original) {
                    Ok(expanded) => {
                        *sentence = expanded;
                        diagnostics.extend(check_functions(
                            &[sentence],
                            &expander.productions,
                            &expander.sorts,
                        ));
                        diagnostics.extend(check_smt_lemmas(&[sentence], &expander.productions));
                        if matches!(sentence, Sentence::Rule { .. } | Sentence::Claim { .. })
                            && contains_macro_symbol(sentence, &expander.productions)
                        {
                            diagnostics.push(Diagnostic::error(
                                DiagnosticCode::InvalidMacroExpansion,
                                "Rule contains macro symbol that was not expanded",
                                sentence,
                            ));
                        }
                    }
                    Err(message) => diagnostics.push(Diagnostic::error(
                        DiagnosticCode::InvalidMacroExpansion,
                        message,
                        sentence,
                    )),
                }
            }
        }
    }
    if diagnostics.is_empty() {
        Ok(output)
    } else {
        diagnostics.sort();
        diagnostics.dedup();
        Err(ExpandMacrosError { diagnostics })
    }
}

struct Expander<'a> {
    productions: ProductionCatalog<'a>,
    sorts: SortCatalog<'a>,
    injector: SortInjector<'a>,
    subsorts: crate::definition::PartialOrder<Sort>,
    overloads: crate::definition::OverloadOrder<'a>,
    macros: BTreeMap<Label, Vec<MacroRule>>,
    token_macros: BTreeMap<Sort, Vec<MacroRule>>,
    variables: BTreeSet<String>,
    counter: usize,
}

impl<'a> Expander<'a> {
    fn new(definition: &'a ResolvedDefinition, module: ModuleId) -> Result<Self, String> {
        let productions = definition.production_catalog(module);
        let sorts = definition.sort_catalog(module);
        let injector = SortInjector::new(definition, &definition.module(module).name)
            .map_err(|error| error.to_string())?;
        let subsorts = definition
            .subsorts(module)
            .map_err(|error| error.to_string())?;
        let overloads = definition
            .overloads(module)
            .map_err(|error| error.to_string())?;
        let all = definition
            .sentences(module)
            .into_iter()
            .enumerate()
            .filter_map(|(id, sentence)| macro_rule(id, sentence))
            .collect::<Vec<_>>();
        let priorities = all
            .iter()
            .map(|rule| macro_priority(rule.sentence.attributes()))
            .collect::<Result<Vec<_>, _>>()?;
        let mut all = all.into_iter().zip(priorities).collect::<Vec<_>>();
        all.sort_by_key(|(_, priority)| *priority);
        let mut macros = BTreeMap::<Label, Vec<MacroRule>>::new();
        let mut token_macros = BTreeMap::<Sort, Vec<MacroRule>>::new();
        for (rule, _) in all {
            match rule.left.unannotated() {
                Term::Apply { label, .. } => macros.entry(label.clone()).or_default().push(rule),
                Term::Token { sort, .. } => {
                    token_macros.entry(sort.clone()).or_default().push(rule)
                }
                Term::Variable { sort, .. } => {
                    let sort = sort.clone().or_else(|| {
                        rule.left
                            .metadata()
                            .and_then(|metadata| metadata.sort.clone())
                    });
                    if let Some(sort) = sort {
                        token_macros.entry(sort).or_default().push(rule);
                    }
                }
                _ => {}
            }
        }
        Ok(Self {
            productions,
            sorts,
            injector,
            subsorts,
            overloads,
            macros,
            token_macros,
            variables: BTreeSet::new(),
            counter: 0,
        })
    }

    fn expand_sentence(&mut self, sentence: Sentence) -> Result<Sentence, String> {
        self.variables.clear();
        for root in sentence_roots(&sentence) {
            root.visit_preorder(&mut |term| {
                if let Term::Variable { name, .. } = term.unannotated() {
                    self.variables.insert(name.clone());
                }
            });
        }
        match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } => Ok(Sentence::Rule {
                body: self.expand_term(body, &BTreeSet::new())?,
                requires: self.expand_term(requires, &BTreeSet::new())?,
                ensures: self.expand_term(ensures, &BTreeSet::new())?,
                attributes,
            }),
            Sentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            } => Ok(Sentence::Claim {
                body: self.expand_term(body, &BTreeSet::new())?,
                requires: self.expand_term(requires, &BTreeSet::new())?,
                ensures: self.expand_term(ensures, &BTreeSet::new())?,
                attributes,
            }),
            Sentence::Context {
                body,
                requires,
                attributes,
            } => Ok(Sentence::Context {
                body: self.expand_term(body, &BTreeSet::new())?,
                requires: self.expand_term(requires, &BTreeSet::new())?,
                attributes,
            }),
            sentence => Ok(sentence),
        }
    }

    fn expand_term(&mut self, term: Term, applied: &BTreeSet<usize>) -> Result<Term, String> {
        let metadata = term.metadata().cloned();
        match term.into_unannotated() {
            Term::Apply { label, arguments } => {
                let arguments = arguments
                    .into_iter()
                    .map(|argument| self.expand_term(argument, applied))
                    .collect::<Result<Vec<_>, _>>()?;
                let application = with_metadata(
                    Term::Apply {
                        label: label.clone(),
                        arguments,
                    },
                    metadata,
                );
                let rules = self.macros.get(&label).cloned();
                self.apply_rules(application, rules.as_deref(), applied)
            }
            Term::Token { token, sort } => {
                let token = with_metadata(
                    Term::Token {
                        token,
                        sort: sort.clone(),
                    },
                    metadata,
                );
                let rules = self.token_macros.get(&sort).cloned();
                self.apply_rules(token, rules.as_deref(), applied)
            }
            Term::Rewrite { left, right } => Ok(with_metadata(
                Term::Rewrite {
                    left: Box::new(self.expand_term(*left, applied)?),
                    right: Box::new(self.expand_term(*right, applied)?),
                },
                metadata,
            )),
            Term::As { pattern, alias } => Ok(with_metadata(
                Term::As {
                    pattern: Box::new(self.expand_term(*pattern, applied)?),
                    alias: Box::new(self.expand_term(*alias, applied)?),
                },
                metadata,
            )),
            Term::Sequence(items) => Ok(with_metadata(
                Term::Sequence(
                    items
                        .into_iter()
                        .map(|item| self.expand_term(item, applied))
                        .collect::<Result<_, _>>()?,
                ),
                metadata,
            )),
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. }) => {
                Ok(with_metadata(leaf, metadata))
            }
            Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
        }
    }

    fn apply_rules(
        &mut self,
        subject: Term,
        rules: Option<&[MacroRule]>,
        applied: &BTreeSet<usize>,
    ) -> Result<Term, String> {
        let Some(rules) = rules else {
            return Ok(subject);
        };
        for rule in rules {
            let Sentence::Rule { requires, .. } = &rule.sentence else {
                unreachable!()
            };
            if requires != &truth() {
                return Err("Cannot compute macros with side conditions.".into());
            }
            let mut substitution = BTreeMap::new();
            let matched = self.matches(&mut substitution, &rule.left, &subject)?;
            if matched && (rule.recursive || !applied.contains(&rule.id)) {
                let mut next_applied = applied.clone();
                next_applied.insert(rule.id);
                let substituted = self.substitute(rule.right.clone(), &mut substitution);
                return self.expand_term(substituted, &next_applied);
            }
        }
        Ok(subject)
    }

    fn matches(
        &self,
        substitution: &mut BTreeMap<String, Term>,
        pattern: &Term,
        subject: &Term,
    ) -> Result<bool, String> {
        let metadata_sort = pattern
            .metadata()
            .and_then(|metadata| metadata.sort.as_ref());
        match pattern.unannotated() {
            Term::Variable { name, sort } => {
                if let Some(existing) = substitution.get(name) {
                    return Ok(existing == subject);
                }
                if let Some(pattern_sort) = sort.as_ref().or(metadata_sort) {
                    let subject_sort = self
                        .injector
                        .term_sort(subject, None)
                        .map_err(|error| error.to_string())?;
                    if !self.subsorts.less_than_eq(&subject_sort, pattern_sort) {
                        return Ok(false);
                    }
                }
                substitution.insert(name.clone(), subject.clone());
                Ok(true)
            }
            Term::Apply {
                label: pattern_label,
                arguments: pattern_arguments,
            } => {
                let Term::Apply {
                    label: subject_label,
                    arguments: subject_arguments,
                } = subject.unannotated()
                else {
                    return Ok(false);
                };
                if pattern_label.name != subject_label.name
                    && !self.pattern_overloads_subject(pattern_label, subject_label)
                {
                    return Ok(false);
                }
                if pattern_arguments.len() != subject_arguments.len() {
                    return Ok(false);
                }
                for (pattern, subject) in pattern_arguments.iter().zip(subject_arguments) {
                    if !self.matches(substitution, pattern, subject)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Term::Token { .. } => Ok(pattern == subject),
            _ if matches!(
                subject.unannotated(),
                Term::Variable { .. } | Term::Token { .. }
            ) =>
            {
                Ok(false)
            }
            _ => Err(
                "Cannot compute macros with terms that are not KApply, KToken, or KVariable."
                    .into(),
            ),
        }
    }

    fn pattern_overloads_subject(&self, pattern: &Label, subject: &Label) -> bool {
        let Some(pattern) = self
            .productions
            .productions_for(&LabelHead::from(pattern))
            .first()
        else {
            return false;
        };
        let Some(subject) = self
            .productions
            .productions_for(&LabelHead::from(subject))
            .first()
        else {
            return false;
        };
        self.overloads.order().greater_than(pattern, subject)
    }

    fn substitute(&mut self, term: Term, substitution: &mut BTreeMap<String, Term>) -> Term {
        let metadata = term.metadata().cloned();
        let rebuilt = match term.into_unannotated() {
            Term::Variable { name, sort } => {
                if let Some(term) = substitution.get(&name) {
                    return term.clone();
                }
                if name == "#Configuration" {
                    Term::Variable { name, sort }
                } else {
                    let fresh = loop {
                        let fresh = format!("_Gen{}", self.counter);
                        self.counter += 1;
                        if self.variables.insert(fresh.clone()) {
                            break fresh;
                        }
                    };
                    let variable = Term::Variable { name: fresh, sort };
                    substitution.insert(name, variable.clone());
                    variable
                }
            }
            Term::Apply { label, arguments } => Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.substitute(argument, substitution))
                    .collect(),
            },
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.substitute(*left, substitution)),
                right: Box::new(self.substitute(*right, substitution)),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.substitute(*pattern, substitution)),
                alias: Box::new(self.substitute(*alias, substitution)),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.substitute(item, substitution))
                    .collect(),
            ),
            leaf @ (Term::InjectedLabel(_) | Term::Token { .. }) => leaf,
            Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
        };
        metadata.map_or(rebuilt.clone(), |metadata| rebuilt.with_metadata(metadata))
    }
}

fn macro_rule(id: usize, sentence: &Sentence) -> Option<MacroRule> {
    let Sentence::Rule {
        body, attributes, ..
    } = sentence
    else {
        return None;
    };
    if !is_macro(attributes) {
        return None;
    }
    Some(MacroRule {
        id,
        sentence: sentence.clone(),
        left: rewrite_projection(body, false),
        right: rewrite_projection(body, true),
        recursive: attributes.get("macro-rec").is_some() || attributes.get("alias-rec").is_some(),
    })
}

fn rewrite_projection(term: &Term, right: bool) -> Term {
    match term.unannotated() {
        Term::Rewrite {
            left,
            right: rewrite_right,
        } => rewrite_projection(if right { rewrite_right } else { left }, right),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments
                .iter()
                .map(|argument| rewrite_projection(argument, right))
                .collect(),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rewrite_projection(pattern, right)),
            alias: Box::new(rewrite_projection(alias, right)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| rewrite_projection(item, right))
                .collect(),
        ),
        _ => term.clone(),
    }
}

fn sentence_roots(sentence: &Sentence) -> Vec<&Term> {
    match sentence {
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
        _ => Vec::new(),
    }
}

fn contains_macro_symbol(sentence: &Sentence, productions: &ProductionCatalog<'_>) -> bool {
    let mut found = false;
    for root in sentence_roots(sentence) {
        root.visit_preorder(&mut |term| {
            if let Term::Apply { label, .. } = term.unannotated()
                && productions
                    .attributes_for(&LabelHead::from(label))
                    .is_some_and(is_macro)
            {
                found = true;
            }
        });
    }
    found
}

fn is_macro(attributes: &Attributes) -> bool {
    MACRO_ATTRIBUTES
        .iter()
        .any(|attribute| attributes.get(attribute).is_some())
}

fn macro_priority(attributes: &Attributes) -> Result<i64, String> {
    if let Some(value) = attributes.get_str("priority") {
        value.parse().map_err(|_| {
            format!("Invalid value for priority attribute: {value}. Must be an integer.")
        })
    } else if attributes.get("owise").is_some() {
        Ok(200)
    } else {
        Ok(50)
    }
}

fn with_metadata(term: Term, metadata: Option<crate::kast::TermMetadata>) -> Term {
    metadata.map_or(term.clone(), |metadata| term.with_metadata(metadata))
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidMacroExpansion,
        message: message.into(),
        source: None,
        location: None,
    }
}
