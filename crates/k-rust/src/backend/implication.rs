//! Shared implication validation, checking, and condition results.

#![deny(clippy::wildcard_enum_match_arm)]

use std::{collections::BTreeSet, error::Error};

use k_rust_backend::{
    definition::{Admission, DefinitionError},
    externalize::{self, ConjunctionShape, External, Printable, ResultSort},
    implication::{
        Bindings, ImplicationCondition, ImplicationError, ImplicationRequestError,
        ImplicationStatus, ImplicationVerdict, Side, SpecialConsequent, bottom_antecedent,
        check_implication_with_existentials_complete, check_negated_consequent,
        grade_bottom_consequent, special_consequent, validate_request,
    },
    rule::Predicate,
    stop::Stoppable,
    substitution::Substitution,
    term::{Name, Sort, Term, TermKind, Variable},
};
use k_rust_kore::{
    json_tree::{self, Node},
    kore::{
        ast::{Pattern as KorePattern, Pattern},
        json as kore_json,
        node::materialize,
    },
};

use super::{Backend, BackendError, admit, error, simplification::stopped_operation};
use k_rust_backend::evaluation::{EvaluationMode, EvaluationScope};

pub fn check(
    definition: &k_rust_backend::definition::BackendDefinition,
    antecedent: &k_rust_backend::rewrite::Pattern,
    antecedent_existentials: &BTreeSet<k_rust_backend::term::Variable>,
    consequent: &k_rust_backend::rewrite::Pattern,
    consequent_existentials: &BTreeSet<k_rust_backend::term::Variable>,
    solver: &dyn k_rust_backend::smt::SmtSolver,
) -> Stoppable<Result<ImplicationVerdict, ImplicationError>> {
    // A proof route (`k_rust_backend::evaluation`).
    let _proof = EvaluationScope::enter(EvaluationMode::Proof);
    check_implication_with_existentials_complete(
        definition,
        antecedent,
        antecedent_existentials,
        consequent,
        consequent_existentials,
        solver,
    )
}

impl Backend {
    /// Validate, internalize, and check one implication through the selected module's cached solver.
    ///
    /// The sort variables of the two patterns are parameters of the implication, so each side is
    /// admitted, as `admission` decides, under the sort variables of both: the context it is
    /// internalized with.
    ///
    /// The verdict holds internal terms built from the two patterns, which the caller drops on
    /// its own stack; [`Self::implies_kore_with`] reads the verdict inside the operation.
    pub fn implies_kore(
        &mut self,
        module: Option<&str>,
        antecedent: &Pattern,
        consequent: &Pattern,
        admission: Admission,
    ) -> Result<(ImplicationVerdict, Sort), BackendError> {
        self.implies_kore_with(
            module,
            antecedent,
            consequent,
            admission,
            |verdict, sort| Ok((verdict, sort)),
        )
    }

    /// [`Self::implies_kore`], with `finish` turning the verdict and the result sort into the
    /// operation's result inside the operation, on the stack that the backend provides for the
    /// two patterns (`Backend::with_solver_over`), where the verdict is also dropped.
    pub fn implies_kore_with<T>(
        &mut self,
        module: Option<&str>,
        antecedent: &Pattern,
        consequent: &Pattern,
        admission: Admission,
        finish: impl FnOnce(ImplicationVerdict, Sort) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        // A proof route (`k_rust_backend::evaluation`).
        let _proof = EvaluationScope::enter(EvaluationMode::Proof);
        self.with_solver_over(module, &[antecedent, consequent], |definition, solver| {
            let (verdict, sort) =
                check_kore(definition, solver, antecedent, consequent, admission)?;
            // As in `simplify_kore_with`: a cancellation set aside during the work is the answer.
            k_rust_backend::stop::check().map_err(stopped_operation)?;
            finish(verdict, sort)
        })
    }
}

fn check_kore(
    definition: &k_rust_backend::definition::BackendDefinition,
    solver: &dyn k_rust_backend::smt::SmtSolver,
    antecedent: &Pattern,
    consequent: &Pattern,
    admission: Admission,
) -> Result<(ImplicationVerdict, Sort), BackendError> {
    validate_request(definition, antecedent, consequent).map_err(|request_error| {
        BackendError::new(match request_error {
            ImplicationRequestError::MacroOrAlias { side, name } => format!(
                "invalid implication {}: {}",
                match side {
                    Side::Antecedent => "antecedent",
                    Side::Consequent => "consequent",
                },
                DefinitionError::MacroOrAliasInImplication(name)
            ),
            ImplicationRequestError::NonFunctionLikeAntecedent => {
                "implication antecedent must be function-like".into()
            }
            ImplicationRequestError::NonSingletonConsequent => {
                "implication consequent must contain exactly one pattern".into()
            }
            ImplicationRequestError::ExistentialCapture { captured, .. } => format!(
                "consequent existentials capture antecedent variables: {}",
                captured.join(", ")
            ),
            ImplicationRequestError::SortMismatch {
                antecedent,
                consequent,
            } => format!("antecedent and consequent sorts differ: {antecedent} and {consequent}"),
        })
    })?;
    let sort_variables = antecedent
        .sort_variables()
        .into_iter()
        .chain(consequent.sort_variables())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(Name::from)
        .collect::<Vec<_>>();
    let antecedent_admitted = admit(
        definition,
        antecedent,
        &sort_variables,
        admission,
        "implication antecedent",
    )?;
    let consequent_admitted = admit(
        definition,
        consequent,
        &sort_variables,
        admission,
        "implication consequent",
    )?;
    if let Some(verdict) = bottom_antecedent(antecedent) {
        let (_, result_sort) = antecedent_admitted
            .internalize_predicate()
            .map_err(error("could not internalize implication antecedent"))?;
        return Ok((verdict, result_sort));
    }
    let (antecedent_pattern, antecedent_existentials) = antecedent_admitted
        .internalize_implication_pattern()
        .map_err(error("could not internalize implication antecedent"))?;
    let result_sort = antecedent_pattern.term.sort();
    let verdict = match special_consequent(consequent) {
        Some(SpecialConsequent::Top) => ImplicationVerdict::Valid(Bindings::default()),
        Some(SpecialConsequent::Bottom) => {
            grade_bottom_consequent(definition, &antecedent_pattern, solver)
                .map_err(stopped_operation)?
        }
        Some(SpecialConsequent::Not) => check_negated_consequent(
            definition,
            &antecedent_pattern,
            &antecedent_existentials,
            consequent_admitted,
            solver,
        )
        .map_err(stopped_operation)?
        .map_err(error("could not internalize implication consequent"))?,
        None => {
            let (consequent_pattern, consequent_existentials) = consequent_admitted
                .internalize_implication_pattern()
                .map_err(error("could not internalize implication consequent"))?;
            if antecedent_pattern.term.sort() != consequent_pattern.term.sort() {
                return Err(BackendError::new(format!(
                    "antecedent and consequent sorts differ after internalization: {} and {}",
                    externalize::sort(&antecedent_pattern.term.sort()),
                    externalize::sort(&consequent_pattern.term.sort())
                )));
            }
            check_implication_with_existentials_complete(
                definition,
                &antecedent_pattern,
                &antecedent_existentials,
                &consequent_pattern,
                &consequent_existentials,
                solver,
            )
            .map_err(stopped_operation)?
            .map_err(error("could not check implication"))?
        }
    };
    Ok((verdict, result_sort))
}

/// Render the CLI implication contract while the surface retains only file and stdout handling.
///
/// The output is a JSON tree built, written, and dropped with explicit stacks, so its depth is
/// bounded by memory rather than by the native stack. Every object's members are in key order
/// at every level (`kore_json::to_node_source`, and the literal objects here), the order of a
/// `serde_json::Value` object, and the tree is written with the project's one pretty layout.
pub fn cli_output(
    antecedent: &KorePattern,
    consequent: &KorePattern,
    result_sort: &Sort,
    verdict: ImplicationVerdict,
) -> Result<String, Box<dyn Error>> {
    let status = match verdict.status() {
        ImplicationStatus::Valid => "valid",
        ImplicationStatus::Invalid => "invalid",
        ImplicationStatus::Indeterminate => "unknown",
    };
    let implication = KorePattern::Implies {
        sort: externalize::sort(result_sort),
        left: Box::new(antecedent.clone()),
        right: Box::new(consequent.clone()),
    };
    let mut members = Vec::with_capacity(3);
    if let Some(condition) = verdict.into_condition() {
        let sides = ImplicationSides::new(antecedent, consequent);
        members.push((
            "condition".to_owned(),
            cli_condition_node(&condition, result_sort, &sides),
        ));
    }
    members.push((
        "implication".to_owned(),
        kore_json::to_node_source(&implication),
    ));
    members.push(("status".to_owned(), Node::String(status.to_owned())));
    Ok(json_tree::to_string(&Node::Object(members), true))
}

pub fn cli_condition_output(
    condition: &ImplicationCondition,
    result_sort: &Sort,
    sides: &ImplicationSides,
) -> Result<serde_json::Value, Box<dyn Error>> {
    Ok(cli_condition_node(condition, result_sort, sides).into_value())
}

/// The condition's JSON object, its members in key order. Each member is encoded from
/// [`External`] sources that read the backend's terms node by node, so no KORE pattern of the
/// condition is materialized: the substitution and the witnesses as the left-nested conjunction
/// of their equations (`condition_bindings`), the predicate as the flat conjunction of its
/// predicates other than `\top`, each written as `externalize::predicate_pattern` writes it, and
/// `\top` at the result sort for an empty one.
fn cli_condition_node(
    condition: &ImplicationCondition,
    result_sort: &Sort,
    sides: &ImplicationSides,
) -> Node {
    let sort = externalize::sort(result_sort);
    let substitution = condition_bindings(&condition.substitution, sides);
    let substitution = equation_sources(&substitution, result_sort);
    let witnesses = condition_bindings(&condition.witnesses, sides);
    let witnesses = equation_sources(&witnesses, result_sort);
    let printable = condition
        .predicates
        .iter()
        .filter(|predicate| !matches!(predicate, Predicate::True))
        .map(Printable::predicate)
        .collect::<Vec<_>>();
    let predicates = printable
        .iter()
        .map(|predicate| External::Predicate {
            predicate: predicate.source(),
            sort: ResultSort::Given(result_sort),
            preserve_terms: false,
        })
        .collect::<Vec<_>>();
    let member = |operands: &[External<'_>], shape| {
        kore_json::to_node_source(
            externalize::connective_source(&sort, operands, shape, true)
                .unwrap_or(External::Top(&sort)),
        )
    };
    Node::Object(vec![
        (
            "predicate".to_owned(),
            member(&predicates, ConjunctionShape::Flat),
        ),
        (
            "substitution".to_owned(),
            member(&substitution, ConjunctionShape::LeftNested),
        ),
        (
            "witnesses".to_owned(),
            member(&witnesses, ConjunctionShape::LeftNested),
        ),
    ])
}

/// What the printer of an implication's condition needs from the request's two sides.
///
/// The check renames each existential `X` of the consequent to a local name `X!exists{N}`,
/// which no name read from KORE can be (KORE identifiers contain no `!`). The printer writes
/// such a name back as its binder `X`, so the condition names the consequent's own variable,
/// unless `X` is also the name of another variable the condition can mention: a free variable
/// of either side, or a leading existential of the antecedent, which the check holds as a
/// variable of the antecedent and binds the consequent's existentials to terms over. The
/// binding would then read as an equation about that other variable, so the local name is
/// printed escaped (`X-bexists0`), a spelling the check gives no variable of the request.
#[derive(Clone, Debug, Default)]
pub struct ImplicationSides {
    /// The antecedent's variable when the antecedent is one variable under its existentials.
    antecedent_variable: Option<String>,
    /// The names of the variables other than the consequent's existentials that a condition
    /// can mention: the free variables of both sides and the antecedent's leading existentials.
    other_names: BTreeSet<String>,
    consequent_binders: BTreeSet<k_rust_kore::kore::ast::Variable>,
}

impl ImplicationSides {
    pub fn new(antecedent: &KorePattern, consequent: &KorePattern) -> Self {
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "KorePattern is syntax; only the listed variants are special here"
        )]
        let antecedent_variable = match antecedent.strip_exists() {
            KorePattern::Variable(variable) => Some(variable.name.clone()),
            _ => None,
        };
        Self {
            antecedent_variable,
            other_names: antecedent
                .free_variables()
                .into_iter()
                .chain(consequent.free_variables())
                .map(|variable| variable.name)
                .chain(
                    antecedent
                        .leading_existentials()
                        .1
                        .into_iter()
                        .map(|variable| variable.name.clone()),
                )
                .collect(),
            consequent_binders: consequent
                .leading_existentials()
                .1
                .into_iter()
                .cloned()
                .collect(),
        }
    }

    /// The consequent binder that `variable`, a local name of the check, renames, when the
    /// binder's name can be printed for it.
    fn consequent_existential_name<'a>(&self, variable: &'a Variable) -> Option<&'a str> {
        let (name, counter) = variable.name.rsplit_once("!exists")?;
        if counter.is_empty() || !counter.bytes().all(|byte| byte.is_ascii_digit()) {
            return None;
        }
        if self.other_names.contains(name) {
            return None;
        }
        let KorePattern::Variable(ref binder) =
            externalize::term(&Term::variable(variable.with_name(name)))
        else {
            unreachable!("a variable externalizes as a variable");
        };
        self.consequent_binders.contains(binder).then_some(name)
    }
}

/// One binding of an implication's condition as the condition prints it: the variable under the
/// name it is printed with (`ImplicationSides`), its value, and whether the value is written on
/// the left of the equation.
struct ConditionBinding<'s> {
    variable: Variable,
    value: &'s Term,
    value_first: bool,
}

/// The bindings of `substitution` as the condition prints them, ordered by variable name then
/// sort.
///
/// A binding of a consequent existential is printed under the existential's own name when that
/// name is free for it. When it binds that existential to the antecedent's variable, the
/// equation is written with the antecedent's variable on the left, so it reads as the
/// consequent's variable instantiated by the antecedent.
fn condition_bindings<'s>(
    substitution: &'s Substitution,
    sides: &ImplicationSides,
) -> Vec<ConditionBinding<'s>> {
    let mut bindings = substitution.iter().collect::<Vec<_>>();
    bindings.sort_by_key(|(variable, _)| (variable.name.clone(), variable.sort.clone()));
    bindings
        .into_iter()
        .map(|(variable, value)| {
            let mut output_variable = variable.clone();
            let consequent_existential = sides.consequent_existential_name(variable);
            if let Some(name) = consequent_existential {
                output_variable.name = Name::from(name);
            }
            // A request variable keeps its KORE name inside the backend, so the names compare.
            let value_first = consequent_existential.is_some()
                && matches!(
                    value.kind(),
                    TermKind::Variable(value)
                        if sides.antecedent_variable.as_deref() == Some(value.name.as_ref())
                );
            ConditionBinding {
                variable: output_variable,
                value,
                value_first,
            }
        })
        .collect()
}

/// The equation of each binding at `result_sort`, as a pattern source.
fn equation_sources<'t>(
    bindings: &'t [ConditionBinding<'_>],
    result_sort: &'t Sort,
) -> Vec<External<'t>> {
    bindings
        .iter()
        .map(|binding| External::Equation {
            variable: &binding.variable,
            value: binding.value,
            value_first: binding.value_first,
            sort: result_sort,
        })
        .collect()
}

/// The left-nested conjunction at `result_sort` of the equations of the bindings of
/// `substitution` (`condition_bindings`), or `None` when it has none.
pub fn condition_substitution(
    substitution: &Substitution,
    result_sort: &Sort,
    sides: &ImplicationSides,
) -> Option<KorePattern> {
    let bindings = condition_bindings(substitution, sides);
    let equations = equation_sources(&bindings, result_sort);
    let sort = externalize::sort(result_sort);
    externalize::connective_source(&sort, &equations, ConjunctionShape::LeftNested, true)
        .map(materialize)
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::parse_pattern;

    use super::*;
    use crate::backend::BackendOptions;

    const DEFINITION: &str = r#"[]
        module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
        endmodule []"#;

    fn implies(
        antecedent: &str,
        consequent: &str,
        admission: Admission,
    ) -> Result<(ImplicationVerdict, Sort), BackendError> {
        let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::default())
            .expect("implication definition should internalize");
        backend.implies_kore(
            None,
            &parse_pattern(antecedent).expect("antecedent should parse"),
            &parse_pattern(consequent).expect("consequent should parse"),
            admission,
        )
    }

    #[test]
    fn a_verified_schematic_implication_reads_its_sort_variables_as_parameters() {
        let (verdict, _) = implies(r"\bottom{S}()", r"\top{S}()", Admission::Verified)
            .expect("a schematic implication is well formed under its own sort variables");
        assert_eq!(verdict.status(), ImplicationStatus::Valid);
    }

    #[test]
    fn a_verified_consequent_has_one_sort_per_variable() {
        let consequent = r#"\and{S}(
            \equals{SortInt{}, S}(X:SortInt{}, \dv{SortInt{}}("1")),
            \equals{SortBool{}, S}(X:SortBool{}, \dv{SortBool{}}("true")))"#;
        let error = implies(r"\bottom{S}()", consequent, Admission::Verified)
            .expect_err("one variable name at two sorts is not a well-formed consequent");
        assert!(
            error
                .message()
                .starts_with("invalid implication consequent: ")
                && error.message().contains("Inconsistent free variable usage"),
            "{error}"
        );
        assert!(implies(r"\bottom{S}()", consequent, Admission::Unverified).is_ok());
    }

    const CHAIN: &str = r#"[]
        module MAIN
            sort SortK{} []
            symbol c{}(SortK{}) : SortK{} [constructor{}(), functional{}()]
            symbol z{}() : SortK{} [constructor{}(), functional{}()]
        endmodule []"#;

    /// `c^depth(z{}())` as KORE text.
    fn chain(depth: usize) -> String {
        format!("{}z{{}}(){}", "c{}(".repeat(depth), ")".repeat(depth))
    }

    fn chain_implication(
        antecedent: &str,
        consequent: &str,
    ) -> (KorePattern, KorePattern, ImplicationVerdict, Sort) {
        let mut backend = Backend::new(CHAIN, "MAIN", BackendOptions::default())
            .expect("the chain definition should internalize");
        let antecedent = parse_pattern(antecedent).expect("antecedent should parse");
        let consequent = parse_pattern(consequent).expect("consequent should parse");
        let (verdict, sort) = backend
            .implies_kore(None, &antecedent, &consequent, Admission::Verified)
            .expect("the implication should be checked");
        (antecedent, consequent, verdict, sort)
    }

    /// The CLI output as `serde_json` values would hold it, every object's members ordered by
    /// key, written with the project's pretty layout: the text the JSON tree must reproduce.
    fn value_output(
        antecedent: &KorePattern,
        consequent: &KorePattern,
        sort: &Sort,
        verdict: ImplicationVerdict,
    ) -> String {
        let status = match verdict.status() {
            ImplicationStatus::Valid => "valid",
            ImplicationStatus::Invalid => "invalid",
            ImplicationStatus::Indeterminate => "unknown",
        };
        let top = || KorePattern::Top {
            sort: externalize::sort(sort),
        };
        let value = |pattern: &KorePattern| kore_json::to_value(pattern).unwrap();
        let implication = KorePattern::Implies {
            sort: externalize::sort(sort),
            left: Box::new(antecedent.clone()),
            right: Box::new(consequent.clone()),
        };
        let mut output = serde_json::json!({
            "status": status,
            "implication": value(&implication),
        });
        if let Some(condition) = verdict.into_condition() {
            let sides = ImplicationSides::new(antecedent, consequent);
            let substitution = condition_substitution(&condition.substitution, sort, &sides);
            let witnesses = condition_substitution(&condition.witnesses, sort, &sides);
            let predicate = externalize::predicates_pattern(
                &condition.predicates,
                sort,
                |predicate| externalize::predicate_pattern(predicate, sort),
                ConjunctionShape::Flat,
            );
            output["condition"] = serde_json::json!({
                "substitution": value(&substitution.unwrap_or_else(top)),
                "predicate": value(&predicate.unwrap_or_else(top)),
                "witnesses": value(&witnesses.unwrap_or_else(top)),
            });
        }
        json_tree::to_string_pretty(&output).unwrap()
    }

    /// The CLI output is the text of the same output held as `serde_json` values, byte for byte:
    /// with a substitution, with witnesses, with a renamed existential, and without a condition.
    #[test]
    fn the_cli_output_is_the_text_of_its_json_value() {
        let cases = [
            (chain(3), "X:SortK{}".to_owned()),
            (
                chain(2),
                r"\exists{SortK{}}(Y:SortK{}, c{}(Y:SortK{}))".to_owned(),
            ),
            (
                "X:SortK{}".to_owned(),
                r"\exists{SortK{}}(Z:SortK{}, Z:SortK{})".to_owned(),
            ),
            (chain(1), chain(2)),
        ];
        for (antecedent, consequent) in cases {
            let (antecedent, consequent, verdict, sort) =
                chain_implication(&antecedent, &consequent);
            let expected = value_output(&antecedent, &consequent, &sort, verdict.clone());
            let output = cli_output(&antecedent, &consequent, &sort, verdict).unwrap();
            assert_eq!(output, expected);
        }
    }

    /// A condition binding a term 200,000 levels deep is written on an 8 MiB stack: the output is
    /// built, written, and dropped without native recursion over the term.
    #[test]
    fn the_cli_output_of_a_deep_condition_takes_no_native_stack_per_level() {
        const DEPTH: usize = 200_000;
        let output = std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn(|| {
                let (antecedent, consequent, verdict, sort) =
                    chain_implication(&chain(DEPTH), "X:SortK{}");
                cli_output(&antecedent, &consequent, &sort, verdict).unwrap()
            })
            .unwrap()
            .join()
            .unwrap();
        // The term is written twice: in the implication and in the condition's substitution.
        assert_eq!(output.matches(r#""name": "c""#).count(), 2 * DEPTH);
    }
}
