//! In-process Z3 implementation of the backend SMT interface.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    str::FromStr,
    sync::{Arc, Mutex},
};

#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};

use num_bigint::BigInt;
use z3::{
    Model, Params, SatResult, Solver,
    ast::{Bool, Int},
};

use super::{
    ModelResult, Satisfiability, SmtError, SmtPrelude, SmtSolver, TranslatedQuery, Validity,
};
use crate::{
    cancellation::cancellation_requested,
    rule::Predicate,
    substitution::Substitution,
    term::{Sort, Term, Variable},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Z3Options {
    pub timeout_ms: u32,
    pub retry_limit: u32,
}

impl Default for Z3Options {
    fn default() -> Self {
        Self {
            timeout_ms: 125,
            retry_limit: 3,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Z3Solver {
    prelude: SmtPrelude,
    options: Z3Options,
    result_cache: Arc<Mutex<SolverResultCache>>,
    #[cfg(test)]
    uncached_solve_count: Arc<AtomicUsize>,
}

const RESULT_CACHE_ENTRY_LIMIT: usize = 256;
const RESULT_CACHE_KEY_BYTE_LIMIT: usize = 8 * 1024 * 1024;

#[derive(Debug)]
struct SolverResultCache {
    entries: BTreeMap<Arc<str>, Satisfiability>,
    insertion_order: VecDeque<Arc<str>>,
    key_bytes: usize,
    entry_limit: usize,
    key_byte_limit: usize,
}

impl SolverResultCache {
    fn new(entry_limit: usize, key_byte_limit: usize) -> Self {
        Self {
            entries: BTreeMap::new(),
            insertion_order: VecDeque::new(),
            key_bytes: 0,
            entry_limit,
            key_byte_limit,
        }
    }

    fn get(&self, script: &str) -> Option<Satisfiability> {
        self.entries.get(script).cloned()
    }

    fn insert(&mut self, script: &str, result: &Satisfiability) {
        if !matches!(result, Satisfiability::Sat | Satisfiability::Unsat)
            || self.entry_limit == 0
            || script.len() > self.key_byte_limit
            || self.entries.contains_key(script)
        {
            return;
        }

        while self.entries.len() >= self.entry_limit
            || self.key_bytes + script.len() > self.key_byte_limit
        {
            let Some(evicted) = self.insertion_order.pop_front() else {
                return;
            };
            if self.entries.remove(evicted.as_ref()).is_some() {
                self.key_bytes -= evicted.len();
            }
        }

        let script: Arc<str> = Arc::from(script);
        self.key_bytes += script.len();
        self.entries.insert(script.clone(), result.clone());
        self.insertion_order.push_back(script);
    }
}

impl Z3Solver {
    pub fn new(definition: &crate::definition::BackendDefinition) -> Result<Self, SmtError> {
        Self::with_options(definition, Z3Options::default())
    }

    pub fn with_options(
        definition: &crate::definition::BackendDefinition,
        options: Z3Options,
    ) -> Result<Self, SmtError> {
        Self::with_options_and_prelude(definition, options, None)
    }

    pub fn with_prelude(
        definition: &crate::definition::BackendDefinition,
        prelude: &str,
    ) -> Result<Self, SmtError> {
        Self::with_options_and_prelude(definition, Z3Options::default(), Some(prelude))
    }

    pub fn with_options_and_prelude(
        definition: &crate::definition::BackendDefinition,
        options: Z3Options,
        prelude: Option<&str>,
    ) -> Result<Self, SmtError> {
        let solver = Self {
            prelude: match prelude {
                Some(prelude) => SmtPrelude::from_definition_with_prelude(definition, prelude)?,
                None => SmtPrelude::from_definition(definition)?,
            },
            options,
            result_cache: Arc::new(Mutex::new(SolverResultCache::new(
                RESULT_CACHE_ENTRY_LIMIT,
                RESULT_CACHE_KEY_BYTE_LIMIT,
            ))),
            #[cfg(test)]
            uncached_solve_count: Arc::new(AtomicUsize::new(0)),
        };
        match solver.solve_uncached(&solver.prelude.declarations().join("\n")) {
            Satisfiability::Sat => Ok(solver),
            Satisfiability::Unsat => Err(SmtError::InconsistentPrelude),
            Satisfiability::Unknown(reason) => Err(SmtError::UnknownPrelude(reason)),
        }
    }

    fn solve(&self, script: &str) -> Satisfiability {
        if cancellation_requested() {
            return Satisfiability::Unknown("request cancelled".into());
        }
        if let Some(result) = self
            .result_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get(script)
        {
            return result;
        }

        let result = self.solve_uncached(script);
        self.result_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .insert(script, &result);
        result
    }

    fn solve_uncached(&self, script: &str) -> Satisfiability {
        #[cfg(test)]
        self.uncached_solve_count.fetch_add(1, Ordering::Relaxed);

        let mut timeout = self.options.timeout_ms;
        for attempt in 0..=self.options.retry_limit {
            if cancellation_requested() {
                return Satisfiability::Unknown("request cancelled".into());
            }
            let solver = Solver::new();
            let mut parameters = Params::new();
            parameters.set_u32("timeout", timeout);
            solver.set_params(&parameters);
            solver.from_string(script);
            match solver.check() {
                SatResult::Sat => return Satisfiability::Sat,
                SatResult::Unsat => return Satisfiability::Unsat,
                SatResult::Unknown if attempt < self.options.retry_limit => {
                    timeout = timeout.saturating_mul(2);
                }
                SatResult::Unknown => {
                    return Satisfiability::Unknown(
                        solver
                            .get_reason_unknown()
                            .unwrap_or_else(|| "Z3 returned unknown".into()),
                    );
                }
            }
        }
        unreachable!("the retry loop always returns")
    }

    fn solve_query(&self, query: &TranslatedQuery, assertion: Option<&str>) -> Satisfiability {
        let mut script = query.base.clone();
        if let Some(assertion) = assertion {
            script.push_str("\n(assert ");
            script.push_str(assertion);
            script.push(')');
        }
        self.solve(&script)
    }

    fn solve_model(
        &self,
        query: &TranslatedQuery,
        variables: &BTreeSet<Variable>,
    ) -> Result<ModelResult, SmtError> {
        let mut timeout = self.options.timeout_ms;
        for attempt in 0..=self.options.retry_limit {
            if cancellation_requested() {
                return Ok(ModelResult::Unknown("request cancelled".into()));
            }
            let solver = Solver::new();
            let mut parameters = Params::new();
            parameters.set_u32("timeout", timeout);
            solver.set_params(&parameters);
            solver.from_string(query.base.as_str());
            match solver.check() {
                SatResult::Sat => {
                    let model = solver.get_model().ok_or(SmtError::MissingModel)?;
                    return self.extract_model(&model, &query.mappings, variables);
                }
                SatResult::Unsat => return Ok(ModelResult::Unsat),
                SatResult::Unknown if attempt < self.options.retry_limit => {
                    timeout = timeout.saturating_mul(2);
                }
                SatResult::Unknown => {
                    return Ok(ModelResult::Unknown(
                        solver
                            .get_reason_unknown()
                            .unwrap_or_else(|| "Z3 returned unknown".into()),
                    ));
                }
            }
        }
        unreachable!("the retry loop always returns")
    }

    fn extract_model(
        &self,
        model: &Model,
        mappings: &BTreeMap<Term, String>,
        variables: &BTreeSet<Variable>,
    ) -> Result<ModelResult, SmtError> {
        let mut substitution = Substitution::new();
        for variable in variables {
            let term = Term::variable(variable.clone());
            let value = match &variable.sort {
                sort if sort == &Sort::simple("SortInt") => {
                    let name = mappings
                        .get(&term)
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    let value = model
                        .eval(&Int::new_const(name.clone()), true)
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    let rendered = normalize_integer(&value.to_string()).ok_or_else(|| {
                        SmtError::InvalidModelValue {
                            variable: variable.clone(),
                            value: value.to_string(),
                        }
                    })?;
                    Term::domain_value(variable.sort.clone(), rendered)
                }
                sort if sort == &Sort::simple("SortBool") => {
                    let name = mappings
                        .get(&term)
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    let value = model
                        .eval(&Bool::new_const(name.clone()), true)
                        .and_then(|value| value.as_bool())
                        .ok_or_else(|| SmtError::MissingModelValue(variable.clone()))?;
                    Term::domain_value(variable.sort.clone(), value.to_string())
                }
                _ => term,
            };
            substitution.insert(variable.clone(), value);
        }
        Ok(ModelResult::Sat(substitution))
    }
}

fn normalize_integer(rendered: &str) -> Option<String> {
    if let Ok(value) = BigInt::from_str(rendered) {
        return Some(value.to_string());
    }
    let magnitude = rendered.strip_prefix("(- ")?.strip_suffix(')')?;
    BigInt::from_str(magnitude)
        .ok()
        .map(|value| (-value).to_string())
}

impl SmtSolver for Z3Solver {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Result<Satisfiability, SmtError> {
        let query = self.prelude.query(predicates, substitution, &[], false)?;
        Ok(self.solve_query(&query, None))
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Result<Validity, SmtError> {
        if checked.is_empty() {
            return Ok(Validity::Valid);
        }
        let query = self.prelude.query(known, substitution, checked, true)?;
        match self.solve_query(&query, None) {
            Satisfiability::Unsat => return Ok(Validity::InconsistentGroundTruth),
            Satisfiability::Unknown(reason) => return Ok(Validity::Unknown(reason)),
            Satisfiability::Sat => {}
        }
        let checked = query.checked.to_string();
        let positive = self.solve_query(&query, Some(&checked));
        let negative = self.solve_query(&query, Some(&format!("(not {checked})")));
        let (positive, negative) = match (positive, negative) {
            (Satisfiability::Unsat, _) => (Satisfiability::Unsat, Satisfiability::Sat),
            (_, Satisfiability::Unsat) => (Satisfiability::Sat, Satisfiability::Unsat),
            results => results,
        };
        Ok(match (positive, negative) {
            (Satisfiability::Sat, Satisfiability::Unsat) => Validity::Valid,
            (Satisfiability::Unsat, Satisfiability::Sat) => Validity::Invalid,
            (Satisfiability::Sat, Satisfiability::Sat) => Validity::Indeterminate,
            (Satisfiability::Unsat, Satisfiability::Unsat) => Validity::InconsistentGroundTruth,
            (Satisfiability::Unknown(reason), _) | (_, Satisfiability::Unknown(reason)) => {
                Validity::Unknown(reason)
            }
        })
    }

    fn get_model(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Result<ModelResult, SmtError> {
        if predicates.is_empty() && substitution.is_empty() {
            return Ok(ModelResult::Sat(Substitution::new()));
        }
        let variables = substitution
            .keys()
            .cloned()
            .chain(predicates.iter().flat_map(Predicate::free_variables))
            .collect::<BTreeSet<_>>();
        let query = self.prelude.query(predicates, substitution, &[], false)?;
        self.solve_model(&query, &variables)
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::{
        cancellation::CancellationToken, definition::BackendDefinition, rule::Predicate,
        term::Variable,
    };

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortS{} []
                symbol opaque{}(SortInt{}) : SortInt{} [function{}()]
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn term(definition: &BackendDefinition, source: &str) -> crate::term::Term {
        definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize")
    }

    fn x() -> Variable {
        Variable::new("X", crate::term::Sort::simple("SortInt"))
    }

    #[test]
    fn quantified_opaque_terms_retain_their_bound_variable_dependence() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        // f(x) = x + 1 is a model; replacing f(x) by a constant would make this false.
        let no_fixed_point = Predicate::Not(Box::new(Predicate::Exists(
            x(),
            Box::new(Predicate::Equals(
                term(&definition, "opaque{}(X:SortInt{})"),
                Term::variable(x()),
            )),
        )));
        assert_eq!(
            solver.is_sat(&[no_fixed_point], &Substitution::new()),
            Ok(Satisfiability::Sat)
        );
    }

    #[test]
    fn quantified_opaque_predicates_can_hold_for_some_values_and_fail_for_others() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        for name in ["X", "Y"] {
            let some_defined = Predicate::Exists(
                x(),
                Box::new(Predicate::Ceil(term(&definition, "opaque{}(X:SortInt{})"))),
            );
            let some_undefined = Predicate::Exists(
                Variable::new(name, Sort::simple("SortInt")),
                Box::new(Predicate::Not(Box::new(Predicate::Ceil(term(
                    &definition,
                    &format!("opaque{{}}({name}:SortInt{{}})"),
                ))))),
            );
            assert_eq!(
                solver.is_sat(&[some_defined, some_undefined], &Substitution::new()),
                Ok(Satisfiability::Sat)
            );
        }
    }

    #[test]
    fn alpha_equivalent_opaque_predicates_share_an_abstraction_without_capturing_free_variables() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let quantified = |bound: &str, free: &str| {
            Predicate::Exists(
                Variable::new(bound, Sort::simple("SortInt")),
                Box::new(Predicate::In(
                    Term::variable(Variable::new(bound, Sort::simple("SortInt"))),
                    Term::variable(Variable::new(free, Sort::simple("SortInt"))),
                )),
            )
        };
        // Include the internal template prefix as a free backend variable name.
        let left = quantified("X", "#SMT-bound-0");
        let renamed = quantified("Y", "#SMT-bound-0");
        let different = quantified("Y", "F");
        assert_eq!(
            solver.check_predicates(
                std::slice::from_ref(&left),
                &Substitution::new(),
                &[renamed]
            ),
            Ok(Validity::Valid)
        );
        assert_eq!(
            solver.check_predicates(&[left], &Substitution::new(), &[different]),
            Ok(Validity::Indeterminate)
        );
    }

    #[test]
    fn nested_shadowing_restores_the_enclosing_and_free_variable_scopes() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let equals = |value: &str| {
            Predicate::Equals(
                Term::variable(x()),
                Term::domain_value(Sort::simple("SortInt"), value),
            )
        };
        let constraints = [
            equals("7"),
            Predicate::Exists(
                x(),
                Box::new(Predicate::And(vec![
                    equals("1"),
                    Predicate::Exists(x(), Box::new(equals("2"))),
                    equals("1"),
                ])),
            ),
            equals("7"),
        ];
        let model = solver
            .get_model(&constraints, &Substitution::new())
            .unwrap();
        assert_eq!(
            model,
            ModelResult::Sat(Substitution::from([(
                x(),
                Term::domain_value(Sort::simple("SortInt"), "7")
            )]))
        );
    }

    #[test]
    fn quantified_abstractions_follow_binder_order_and_shadowing() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let nested = |outer: &str, inner: &str| {
            let outer = Variable::new(outer, Sort::simple("SortInt"));
            let inner = Variable::new(inner, Sort::simple("SortInt"));
            Predicate::Exists(
                outer.clone(),
                Box::new(Predicate::Forall(
                    inner.clone(),
                    Box::new(Predicate::In(Term::variable(outer), Term::variable(inner))),
                )),
            )
        };
        assert_eq!(
            solver.check_predicates(
                &[nested("X", "Y")],
                &Substitution::new(),
                &[nested("Y", "X")]
            ),
            Ok(Validity::Valid)
        );
        let diagonal = Predicate::Forall(
            x(),
            Box::new(Predicate::In(Term::variable(x()), Term::variable(x()))),
        );
        assert_eq!(
            solver.check_predicates(&[nested("Y", "Y")], &Substitution::new(), &[diagonal]),
            Ok(Validity::Valid)
        );
    }

    #[test]
    fn proves_and_refutes_predicates_under_a_substitution() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
        ))];

        assert_eq!(
            solver.check_predicates(
                &[],
                &Substitution::from([(x(), term(&definition, r#"\dv{SortInt{}}("5")"#))]),
                &checked,
            ),
            Ok(Validity::Valid)
        );
        assert_eq!(
            solver.check_predicates(
                &[],
                &Substitution::from([(x(), term(&definition, r#"\dv{SortInt{}}("15")"#))]),
                &checked,
            ),
            Ok(Validity::Invalid)
        );
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), &checked),
            Ok(Validity::Indeterminate)
        );
    }

    #[test]
    fn proves_native_collection_sizes_are_nonnegative() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortList{} []
                symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                hooked-symbol abstractSize{}(SortList{}) : SortInt{}
                    [function{}(), total{}(), hook{}("LIST.size")]
                hooked-symbol translatedSize{}(SortList{}) : SortInt{}
                    [function{}(), total{}(), hook{}("LIST.size"), smtlib{}("list-size")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let solver = Z3Solver::new(&definition).unwrap();

        for size in ["abstractSize", "translatedSize"] {
            let checked = [Predicate::Term(term(
                &definition,
                &format!(r#"lt{{}}(\dv{{SortInt{{}}}}("-1"), {size}{{}}(L:SortList{{}}))"#),
            ))];
            assert_eq!(
                solver.check_predicates(&[], &Substitution::new(), &checked),
                Ok(Validity::Valid),
                "{size} should be nonnegative"
            );
        }
    }

    #[test]
    fn distinguishes_unsatisfiable_and_inconsistent_constraints() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let x_term = term(&definition, "X:SortInt{}");
        let five = term(&definition, r#"\dv{SortInt{}}("5")"#);
        let six = term(&definition, r#"\dv{SortInt{}}("6")"#);
        let inconsistent = [
            Predicate::Equals(x_term.clone(), five),
            Predicate::Equals(x_term, six),
        ];

        assert_eq!(
            solver.is_sat(&inconsistent, &Substitution::new()),
            Ok(Satisfiability::Unsat)
        );
        assert_eq!(
            solver.check_predicates(
                &inconsistent,
                &Substitution::new(),
                &[Predicate::Term(term(
                    &definition,
                    r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
                ))],
            ),
            Ok(Validity::InconsistentGroundTruth)
        );
    }

    #[test]
    fn validity_filters_ground_truth_unrelated_to_the_checked_variables() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
        ))];
        let unrelated = term(&definition, "Z:SortInt{}");
        let contradictory = [
            Predicate::Equals(
                unrelated.clone(),
                term(&definition, r#"\dv{SortInt{}}("1")"#),
            ),
            Predicate::Equals(unrelated, term(&definition, r#"\dv{SortInt{}}("2")"#)),
        ];

        assert_eq!(
            solver.check_predicates(
                &contradictory,
                &Substitution::from([(x(), term(&definition, r#"\dv{SortInt{}}("5")"#))]),
                &checked,
            ),
            Ok(Validity::Valid)
        );
    }

    #[test]
    fn rejects_an_inconsistent_smt_lemma_prelude() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol f{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), smtlib{}("f")]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(
                            \dv{SortInt{}}("1"),
                            \top{SortInt{}}()
                        )
                    )
                ) [simplification{}(), smt-lemma{}(), label{}("f-is-one")]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(
                            \dv{SortInt{}}("2"),
                            \top{SortInt{}}()
                        )
                    )
                ) [simplification{}(), smt-lemma{}(), label{}("f-is-two")]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        assert!(matches!(
            Z3Solver::new(&definition),
            Err(SmtError::InconsistentPrelude)
        ));
    }

    #[test]
    fn loads_external_smt_preludes_and_rejects_inconsistent_ones() {
        let definition = definition();
        let consistent = "(declare-const a Int)\n(assert (> a 0))";
        let inconsistent = "(declare-const a Int)\n(assert (> a 0))\n(assert (< a 0))";

        assert!(Z3Solver::with_prelude(&definition, consistent).is_ok());
        assert!(matches!(
            Z3Solver::with_prelude(&definition, inconsistent),
            Err(SmtError::InconsistentPrelude)
        ));
    }

    #[test]
    fn extracts_arbitrary_precision_integer_and_boolean_models() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let integer = Variable::new("X", Sort::simple("SortInt"));
        let boolean = Variable::new("B", Sort::simple("SortBool"));
        let expected_integer = "-99999999999999999999999999999999999999";
        let predicates = [
            Predicate::Equals(
                Term::variable(integer.clone()),
                Term::domain_value(Sort::simple("SortInt"), expected_integer),
            ),
            Predicate::Equals(
                Term::variable(boolean.clone()),
                Term::domain_value(Sort::simple("SortBool"), "true"),
            ),
        ];

        let ModelResult::Sat(model) = solver
            .get_model(&predicates, &Substitution::new())
            .expect("model should be extracted")
        else {
            panic!("constraints should be satisfiable")
        };

        assert_eq!(
            model.get(&integer),
            Some(&Term::domain_value(
                Sort::simple("SortInt"),
                expected_integer
            ))
        );
        assert_eq!(
            model.get(&boolean),
            Some(&Term::domain_value(Sort::simple("SortBool"), "true"))
        );
    }

    #[test]
    fn model_results_distinguish_empty_unsatisfiable_and_untranslated_inputs() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();

        assert_eq!(
            solver.get_model(&[], &Substitution::new()),
            Ok(ModelResult::Sat(Substitution::new()))
        );

        let integer = Variable::new("X", Sort::simple("SortInt"));
        let integer_term = Term::variable(integer);
        assert_eq!(
            solver.get_model(
                &[
                    Predicate::Equals(
                        integer_term.clone(),
                        Term::domain_value(Sort::simple("SortInt"), "1"),
                    ),
                    Predicate::Equals(
                        integer_term,
                        Term::domain_value(Sort::simple("SortInt"), "2"),
                    ),
                ],
                &Substitution::new(),
            ),
            Ok(ModelResult::Unsat)
        );

        let opaque = Variable::new("Y", Sort::simple("SortS"));
        let opaque_term = Term::variable(opaque.clone());
        let ModelResult::Sat(model) = solver
            .get_model(
                &[Predicate::Equals(opaque_term.clone(), opaque_term)],
                &Substitution::new(),
            )
            .unwrap()
        else {
            panic!("reflexive opaque equality should be satisfiable")
        };
        assert_eq!(model.get(&opaque), Some(&Term::variable(opaque.clone())));
    }

    #[test]
    fn reuses_conclusive_exact_scripts() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);
        let x_term = Term::variable(x());
        let one = Term::domain_value(Sort::simple("SortInt"), "1");
        let two = Term::domain_value(Sort::simple("SortInt"), "2");
        let satisfiable = [Predicate::Equals(x_term.clone(), one.clone())];
        let unsatisfiable = [
            Predicate::Equals(x_term.clone(), one),
            Predicate::Equals(x_term, two),
        ];

        for _ in 0..2 {
            assert_eq!(
                solver.is_sat(&satisfiable, &Substitution::new()),
                Ok(Satisfiability::Sat)
            );
            assert_eq!(
                solver.is_sat(&unsatisfiable, &Substitution::new()),
                Ok(Satisfiability::Unsat)
            );
        }

        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed) - baseline,
            2,
            "each distinct complete script should reach Z3 once"
        );
    }

    #[test]
    fn does_not_conflate_distinct_scripts() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);
        let x_term = Term::variable(x());
        let equals = |value| {
            [Predicate::Equals(
                x_term.clone(),
                Term::domain_value(Sort::simple("SortInt"), value),
            )]
        };

        assert_eq!(
            solver.is_sat(&equals("1"), &Substitution::new()),
            Ok(Satisfiability::Sat)
        );
        assert_eq!(
            solver.is_sat(&equals("2"), &Substitution::new()),
            Ok(Satisfiability::Sat)
        );
        assert_eq!(
            solver.is_sat(&equals("1"), &Substitution::new()),
            Ok(Satisfiability::Sat)
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed) - baseline,
            2
        );
    }

    #[test]
    fn cancelled_exact_hit_returns_unknown() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let predicates = [Predicate::Equals(
            Term::variable(x()),
            Term::domain_value(Sort::simple("SortInt"), "1"),
        )];
        assert_eq!(
            solver.is_sat(&predicates, &Substitution::new()),
            Ok(Satisfiability::Sat)
        );
        let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);
        let token = CancellationToken::new();
        token.cancel();

        assert_eq!(
            token.scope(|| solver.is_sat(&predicates, &Substitution::new())),
            Ok(Satisfiability::Unknown("request cancelled".into()))
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed),
            baseline
        );
        assert_eq!(
            solver.is_sat(&predicates, &Substitution::new()),
            Ok(Satisfiability::Sat)
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed),
            baseline
        );
    }

    #[test]
    fn result_cache_excludes_unknown_and_bounds_keys_by_fifo_order() {
        let mut cache = SolverResultCache::new(2, usize::MAX);
        cache.insert("A", &Satisfiability::Sat);
        cache.insert("B", &Satisfiability::Unsat);
        assert_eq!(cache.get("A"), Some(Satisfiability::Sat));
        cache.insert("C", &Satisfiability::Sat);

        assert_eq!(cache.get("A"), None, "hits must not refresh FIFO order");
        assert_eq!(cache.get("B"), Some(Satisfiability::Unsat));
        assert_eq!(cache.get("C"), Some(Satisfiability::Sat));

        cache.insert("unknown", &Satisfiability::Unknown("timeout".into()));
        assert_eq!(cache.get("unknown"), None);

        let mut byte_bounded = SolverResultCache::new(2, 2);
        byte_bounded.insert("abc", &Satisfiability::Sat);
        assert_eq!(byte_bounded.get("abc"), None);

        let mut cumulative_bytes = SolverResultCache::new(3, 5);
        cumulative_bytes.insert("aa", &Satisfiability::Sat);
        cumulative_bytes.insert("bbb", &Satisfiability::Unsat);
        cumulative_bytes.insert("cc", &Satisfiability::Sat);
        assert_eq!(cumulative_bytes.get("aa"), None);
        assert_eq!(cumulative_bytes.get("bbb"), Some(Satisfiability::Unsat));
        assert_eq!(cumulative_bytes.get("cc"), Some(Satisfiability::Sat));
        assert_eq!(cumulative_bytes.key_bytes, 5);

        cumulative_bytes.insert("dddd", &Satisfiability::Unsat);
        assert_eq!(cumulative_bytes.get("bbb"), None);
        assert_eq!(cumulative_bytes.get("cc"), None);
        assert_eq!(cumulative_bytes.get("dddd"), Some(Satisfiability::Unsat));
        assert_eq!(cumulative_bytes.key_bytes, 4);
    }

    #[test]
    fn clones_share_cached_results_and_remain_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Z3Solver>();

        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let predicates = [Predicate::Equals(
            Term::variable(x()),
            Term::domain_value(Sort::simple("SortInt"), "1"),
        )];
        assert_eq!(
            solver.is_sat(&predicates, &Substitution::new()),
            Ok(Satisfiability::Sat)
        );
        let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);
        let clone = solver.clone();

        assert_eq!(
            clone.is_sat(&predicates, &Substitution::new()),
            Ok(Satisfiability::Sat)
        );
        assert_eq!(
            solver.uncached_solve_count.load(Ordering::Relaxed),
            baseline
        );
    }

    #[test]
    fn validity_subqueries_reuse_only_exact_scripts() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let checked = [Predicate::Term(term(
            &definition,
            r#"lt{}(X:SortInt{}, \dv{SortInt{}}("10"))"#,
        ))];
        for (substitution, expected) in [
            (Substitution::new(), Validity::Indeterminate),
            (
                Substitution::from([(x(), Term::domain_value(Sort::simple("SortInt"), "5"))]),
                Validity::Valid,
            ),
            (
                Substitution::from([(x(), Term::domain_value(Sort::simple("SortInt"), "15"))]),
                Validity::Invalid,
            ),
        ] {
            assert_eq!(
                solver.check_predicates(&[], &substitution, &checked),
                Ok(expected.clone())
            );
            let baseline = solver.uncached_solve_count.load(Ordering::Relaxed);
            assert_eq!(
                solver.check_predicates(&[], &substitution, &checked),
                Ok(expected)
            );
            assert_eq!(
                solver.uncached_solve_count.load(Ordering::Relaxed),
                baseline
            );
        }
    }

    #[test]
    fn cached_satisfiability_does_not_replace_model_check() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let predicates = [Predicate::Equals(
            Term::variable(x()),
            Term::domain_value(Sort::simple("SortInt"), "7"),
        )];
        assert_eq!(
            solver.is_sat(&predicates, &Substitution::new()),
            Ok(Satisfiability::Sat)
        );

        assert_eq!(
            solver.get_model(&predicates, &Substitution::new()),
            Ok(ModelResult::Sat(Substitution::from([(
                x(),
                Term::domain_value(Sort::simple("SortInt"), "7")
            )])))
        );
    }
}
