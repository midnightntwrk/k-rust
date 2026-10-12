//! ```toml algorithm-site
//! id = "kompile.sort_injections.insert"
//! role = "part"
//! sites = ["compile_search_pattern"]
//! ```
//!
//! ```toml algorithm-site
//! id = "kompile.kore.convert_term"
//! role = "part"
//! sites = ["compile_search_pattern"]
//! ```
//!
//! Search-pattern compilation applies sort injection and term-to-KORE conversion to one pattern.
//! Complexity: the sort-injection and term-conversion cards state the cost of the enclosed algorithms.
//! It adds no worklist of its own; the enclosed algorithms determine its cost.
//!
//! Compilation of one surface K search pattern into a verified-shape KORE target.

use std::collections::BTreeSet;
use std::fmt;

use crate::definition::{Attributes, LabelHead, ResolvedDefinition, Sentence};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::inner::{RuleError, parse_rule_content};
use crate::kast::{Sort, Term, TermParts, identifier};
use crate::kore::ast::{Pattern, VariableKind};
use crate::names::BuiltinSort;

use super::fresh_names::GeneratedVariableIdentity;
use super::passes::{
    ResolveSemanticCastsError, expand_macros_in_terms_from_resolved, resolve_anon_vars_in_sentence,
    resolve_semantic_casts_with_predicates_in_sentence,
};
use super::sort_injections::{GroundInput, SortInjectionError, SortInjector, rewrite_projection};
use super::term_to_kore::{TermConversionError, TermConverter};
use super::{ConcretizeCellsError, concretize_cells_in_sentence};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct KoreVariableIdentity {
    pub kind: VariableKind,
    pub name: String,
}

impl KoreVariableIdentity {
    pub fn element(name: impl Into<String>) -> Self {
        Self {
            kind: VariableKind::Element,
            name: name.into(),
        }
    }

    pub fn set(name: impl Into<String>) -> Self {
        Self {
            kind: VariableKind::Set,
            name: name.into(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompiledSearchPattern {
    pub pattern: Pattern,
    pub generated_anonymous_variables: BTreeSet<KoreVariableIdentity>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CompileSearchPatternError {
    Rule(RuleError),
    MissingExecutionModule(String),
    CellConcretization(ConcretizeCellsError),
    SemanticCasts(ResolveSemanticCastsError),
    MacroExpansion(String),
    SortInjection(SortInjectionError),
    TermConversion(TermConversionError),
    ExpectedGeneratedTopCell {
        actual: Sort,
    },
    /// The pattern writes text that takes no part in what it denotes: a named variable that
    /// occurs only on a rewrite's right side, or an `ensures` other than `true`
    /// ([`DiagnosticCode::InvalidSearchPattern`](crate::diagnostic::DiagnosticCode)).
    Denotation(Box<Diagnostic>),
}

impl fmt::Display for CompileSearchPatternError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rule(error) => error.fmt(formatter),
            Self::MissingExecutionModule(module) => {
                write!(
                    formatter,
                    "compiled execution module {module:?} was not found"
                )
            }
            Self::CellConcretization(error) => error.fmt(formatter),
            Self::SemanticCasts(error) => error.fmt(formatter),
            Self::MacroExpansion(message) => {
                write!(
                    formatter,
                    "search-pattern macro expansion failed: {message}"
                )
            }
            Self::SortInjection(error @ SortInjectionError::UndeterminedInstance(_)) => write!(
                formatter,
                "search pattern has an undetermined instance: {error}"
            ),
            Self::SortInjection(error) => error.fmt(formatter),
            Self::TermConversion(error) => error.fmt(formatter),
            Self::ExpectedGeneratedTopCell { actual } => write!(
                formatter,
                "search pattern body has sort {actual}; expected GeneratedTopCell"
            ),
            Self::Denotation(diagnostic) => {
                match (&diagnostic.source, diagnostic.location) {
                    (Some(source), Some(location)) => write!(
                        formatter,
                        "{source}:{}:{}: ",
                        location.start_line, location.start_column
                    )?,
                    (Some(source), None) => write!(formatter, "{source}: ")?,
                    _ => {}
                }
                formatter.write_str(&diagnostic.message)
            }
        }
    }
}

impl std::error::Error for CompileSearchPatternError {}

impl From<RuleError> for CompileSearchPatternError {
    fn from(error: RuleError) -> Self {
        Self::Rule(error)
    }
}

impl From<ConcretizeCellsError> for CompileSearchPatternError {
    fn from(error: ConcretizeCellsError) -> Self {
        Self::CellConcretization(error)
    }
}

impl From<ResolveSemanticCastsError> for CompileSearchPatternError {
    fn from(error: ResolveSemanticCastsError) -> Self {
        Self::SemanticCasts(error)
    }
}

impl From<SortInjectionError> for CompileSearchPatternError {
    fn from(error: SortInjectionError) -> Self {
        Self::SortInjection(error)
    }
}

impl From<TermConversionError> for CompileSearchPatternError {
    fn from(error: TermConversionError) -> Self {
        Self::TermConversion(error)
    }
}

/// Compile a complete `#RuleContent` surface pattern in the parsing and execution contexts
/// produced by one definition compilation.
pub fn compile_search_pattern(
    parsing_definition: &ResolvedDefinition,
    execution_definition: &ResolvedDefinition,
    module: &str,
    contents: &str,
    attributes: Attributes,
) -> Result<CompiledSearchPattern, CompileSearchPatternError> {
    let sentence = parse_rule_content(parsing_definition, module, contents, attributes)?;
    reject_undenoted_text(&sentence)?;
    let module_id = execution_definition
        .module_id(module)
        .ok_or_else(|| CompileSearchPatternError::MissingExecutionModule(module.to_owned()))?;
    let views = execution_definition.views();
    let subsorts = views.subsorts(module_id).map_err(|cycle| {
        CompileSearchPatternError::SemanticCasts(ResolveSemanticCastsError {
            diagnostics: vec![crate::diagnostic::Diagnostic::error(
                crate::diagnostic::DiagnosticCode::InvalidSemanticCast,
                format!("cannot determine subsorts for module {module}: {cycle}"),
                &sentence,
            )],
        })
    })?;

    let (sentence, mut generated) = resolve_anon_vars_in_sentence(sentence);
    let sentence = resolve_semantic_casts_with_predicates_in_sentence(subsorts, sentence)?;
    let (sentence, cell_generated) =
        concretize_cells_in_sentence(execution_definition, module, sentence)?;
    generated.extend(cell_generated);

    let Sentence::Rule {
        body,
        requires,
        ensures: _,
        attributes: _,
    } = sentence
    else {
        unreachable!("parse_rule_content always returns a Rule sentence")
    };
    let body = rewrite_projection(&body, false, subsorts);
    let top = Sort::builtin(BuiltinSort::GeneratedTopCell);
    let bool_sort = Sort::builtin(BuiltinSort::Bool);
    let expanded = expand_macros_in_terms_from_resolved(
        execution_definition,
        module,
        vec![(body, top.clone()), (requires, bool_sort.clone())],
    )
    .map_err(CompileSearchPatternError::MacroExpansion)?;
    generated.extend(expanded.generated_variables);
    let [body, requires]: [Term; 2] = expanded
        .terms
        .try_into()
        .expect("two input roots produce two expanded roots");

    let injector = SortInjector::new(execution_definition, module)?;
    let actual = injector.term_sort(&body, None)?;
    if actual != top {
        return Err(CompileSearchPatternError::ExpectedGeneratedTopCell { actual });
    }
    // The pattern is matched against states, as a rule's left side is, so it is injected as one.
    // A key it is given names only the item it matches, so it is anonymous like the variables
    // generated above.
    let (body, minted) = injector.inject_pattern(&body, &top, [&requires])?;
    generated.extend(minted.into_iter().map(GeneratedVariableIdentity::element));
    injector.require_ground(&body, GroundInput::SearchPattern)?;
    // The condition holds when it equals `true`. Cast and cell-fragment resolution conjoin the
    // sort tests they add with `_andBool_`, which the module declares only when it sees `BOOL`.
    // Without it, every `_andBool_` on the condition's spine was generated (the user's condition
    // could not have parsed with one), and `#Equals(A andBool B, true)` holds exactly when both
    // `#Equals(A, true)` and `#Equals(B, true)` do, so each conjunct becomes its own equation.
    let and_bool = LabelHead::new(AND_BOOL);
    let conjuncts = if views
        .production_catalog(module_id)
        .productions_for(&and_bool)
        .is_empty()
    {
        let mut conjuncts = Vec::new();
        split_conjunction(requires, &mut conjuncts);
        conjuncts
    } else {
        vec![requires]
    };
    let requires = conjuncts
        .into_iter()
        .filter(|conjunct| !is_true(conjunct))
        .map(|conjunct| {
            let conjunct = injector.inject(&conjunct, &bool_sort)?;
            injector.require_ground(&conjunct, GroundInput::SearchPattern)?;
            Ok(conjunct)
        })
        .collect::<Result<Vec<_>, CompileSearchPatternError>>()?;

    let converter =
        TermConverter::new_with_generated_anonymous(execution_definition, module, &generated)?;
    let body = converter.convert(&body)?;
    let top_kore = converter.convert_sort(&top)?;
    let bool_kore = converter.convert_sort(&bool_sort)?;
    let mut arguments = vec![body];
    // Invariant: `arguments` holds the body and the equation of every conjunct of `requires`
    // before `conjunct`; each iteration converts one conjunct.
    for conjunct in &requires {
        arguments.push(Pattern::Equals {
            operand_sort: Box::new(bool_kore.clone()),
            result_sort: top_kore.clone(),
            left: Box::new(converter.convert(conjunct)?),
            right: Box::new(Pattern::DomainValue {
                sort: bool_kore.clone(),
                value: "true".into(),
            }),
        });
    }
    if requires.is_empty() {
        arguments.push(Pattern::Top {
            sort: top_kore.clone(),
        });
    }
    let pattern = Pattern::And {
        sort: top_kore,
        arguments,
    };

    let occurring = variable_identities(&pattern);
    let generated_anonymous_variables = generated
        .into_iter()
        .map(encode_generated_identity)
        .filter(|identity| occurring.contains(identity))
        .collect();
    Ok(CompiledSearchPattern {
        pattern,
        generated_anonymous_variables,
    })
}

/// Reject a pattern that writes text taking no part in what it denotes.
///
/// A search pattern denotes the configurations its body's left side matches, under its
/// `requires`: a rewrite in it denotes its left side, and nothing describes a later state.
/// So a named variable that occurs only on a rewrite's right side is constrained by nothing the
/// pattern denotes, and a test of it (such as the sort test its cast adds) holds whenever it is
/// satisfiable at all: `<k> X => Y:Bool </k>` and `<k> X => Y:Int </k>` would find the same
/// configurations. An `ensures` states what holds after a step, which a pattern does not
/// describe. A variable that occurs in `requires` and not in the body is an existential that
/// constrains the body (`<k> X </k> requires X ==Int Y +Int 1 andBool Y >Int 0`), so it stays
/// legal; anonymous variables name nothing.
fn reject_undenoted_text(sentence: &Sentence) -> Result<(), CompileSearchPatternError> {
    let Sentence::Rule {
        body,
        requires,
        ensures,
        ..
    } = sentence
    else {
        unreachable!("parse_rule_content always returns a Rule sentence")
    };
    if !is_true(ensures) {
        return Err(CompileSearchPatternError::Denotation(Box::new(
            Diagnostic::error(
                DiagnosticCode::InvalidSearchPattern,
                "a search pattern cannot have an `ensures` clause: it denotes the configurations its left side matches under its `requires`, and describes no later state",
                sentence,
            ),
        )));
    }
    let mut denoted = BTreeSet::new();
    let mut right_only = BTreeSet::new();
    collect_named_variables(body, false, &mut denoted, &mut right_only);
    collect_named_variables(requires, false, &mut denoted, &mut right_only);
    let unbound = right_only
        .difference(&denoted)
        .map(String::as_str)
        .collect::<Vec<_>>();
    if unbound.is_empty() {
        return Ok(());
    }
    Err(CompileSearchPatternError::Denotation(Box::new(
        Diagnostic::error(
            DiagnosticCode::InvalidSearchPattern,
            format!(
                "variable{} {} of the search pattern occur{} only on the right side of a rewrite; a search pattern denotes the left side of its rewrites, so nothing it denotes constrains {}",
                if unbound.len() == 1 { "" } else { "s" },
                unbound.join(", "),
                if unbound.len() == 1 { "s" } else { "" },
                if unbound.len() == 1 { "it" } else { "them" },
            ),
            sentence,
        ),
    )))
}

/// Add the named variables of `term` to `right_only` when they stand on the right side of a
/// rewrite (`right` says whether `term` does), and to `denoted` otherwise.
fn collect_named_variables(
    term: &Term,
    right: bool,
    denoted: &mut BTreeSet<String>,
    right_only: &mut BTreeSet<String>,
) {
    let mut pending = vec![(term, right)];
    // Invariant: every variable of the visited subterms is in `denoted` or `right_only`, as its
    // position says, and `pending` holds the unvisited subterms with their positions; each step
    // replaces one subterm by its direct subterms.
    while let Some((term, right)) = pending.pop() {
        match term.unannotated() {
            Term::Variable { name, .. } => {
                if !matches!(name.as_str(), "_" | "?_" | "!_" | "@_") {
                    if right {
                        right_only.insert(name.clone());
                    } else {
                        denoted.insert(name.clone());
                    }
                }
            }
            Term::Rewrite { left, right: built } => {
                pending.push((left, right));
                pending.push((built, true));
            }
            Term::As { pattern, alias } => {
                pending.push((pattern, right));
                pending.push((alias, right));
            }
            Term::Apply { arguments, .. } => {
                pending.extend(arguments.iter().map(|argument| (argument, right)));
            }
            Term::Sequence(items) => pending.extend(items.iter().map(|item| (item, right))),
            Term::Token { .. } | Term::InjectedLabel(_) => {}
            Term::Annotated { .. } => unreachable!("unannotated strips metadata"),
        }
    }
}

/// The label of `BOOL`'s conjunction, with which generated sort tests are conjoined.
const AND_BOOL: &str = "_andBool_";

/// Push onto `conjuncts`, left to right, the operands of the `_andBool_` applications on the
/// spine of `term`, or `term` itself when it is no conjunction.
fn split_conjunction(term: Term, conjuncts: &mut Vec<Term>) {
    let conjunction = matches!(
        term.unannotated(),
        Term::Apply { label, arguments } if label.name == AND_BOOL && arguments.len() == 2
    );
    if !conjunction {
        conjuncts.push(term);
        return;
    }
    let TermParts::Apply { arguments, .. } = term.into_unannotated().into_parts() else {
        unreachable!("a conjunction is an application")
    };
    for argument in arguments {
        split_conjunction(argument, conjuncts);
    }
}

fn is_true(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Token { token, sort } if token == "true" && sort.is_builtin(BuiltinSort::Bool)
    )
}

fn encode_generated_identity(identity: GeneratedVariableIdentity) -> KoreVariableIdentity {
    match identity.kind {
        VariableKind::Element => KoreVariableIdentity::element(identifier::encode_variable(
            &identity.name,
            VariableKind::Element,
        )),
        VariableKind::Set => {
            let name = identity.name.strip_prefix('@').unwrap_or(&identity.name);
            KoreVariableIdentity::set(identifier::encode_variable(name, VariableKind::Set))
        }
    }
}

fn variable_identities(pattern: &Pattern) -> BTreeSet<KoreVariableIdentity> {
    // stack-accepted(search-pattern-variables): one level per level of the search pattern a user writes on the command line, which is shallow. See docs/backend-port.md#stack-bounds.
    // Invariant: each call visits one node of `pattern` and recurses only into its direct subpatterns, so the finite `pattern` bounds the calls; `output` holds every free or bound variable identity met so far.
    fn collect(pattern: &Pattern, output: &mut BTreeSet<KoreVariableIdentity>) {
        match pattern {
            Pattern::Variable(variable) => {
                output.insert(KoreVariableIdentity {
                    kind: variable.kind,
                    name: variable.name.clone(),
                });
            }
            Pattern::Application { arguments, .. }
            | Pattern::And { arguments, .. }
            | Pattern::Or { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => {
                for argument in arguments {
                    collect(argument, output);
                }
            }
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => collect(argument, output),
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                collect(left, output);
                collect(right, output);
            }
            Pattern::Exists { variable, body, .. }
            | Pattern::Forall { variable, body, .. }
            | Pattern::Mu { variable, body }
            | Pattern::Nu { variable, body } => {
                output.insert(KoreVariableIdentity {
                    kind: variable.kind,
                    name: variable.name.clone(),
                });
                collect(body, output);
            }
            Pattern::String(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    }

    let mut output = BTreeSet::new();
    collect(pattern, &mut output);
    output
}
