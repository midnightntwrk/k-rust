//! Sort-aware one-way matching for rewrite rules and equations.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::{
    substitution::{Substitution, substitute},
    term::{Name, Sort, SymbolType, Term, TermKind, Variable},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MatchMode {
    Rewrite,
    Evaluate,
    Implies,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MatchResult {
    Success(Substitution),
    Failed(FailReason),
    Indeterminate {
        substitution: Substitution,
        remainder: Vec<(Term, Term)>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FailReason {
    DifferentValues(Term, Term),
    DifferentSymbols(Term, Term),
    DifferentSorts(Term, Term),
    VariableRecursion(Variable, Term),
    VariableConflict(Variable, Term, Term),
    SharedVariables(BTreeSet<Variable>),
    Subsorting(SortError),
    ArgumentLengthsDiffer(Term, Term),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SortError {
    FoundSortVariable(Name),
    FoundUnknownSort(Sort),
}

/// Reflexive-transitive subsort closure keyed by the supersort name.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SortGraph {
    subsorts: BTreeMap<Name, BTreeSet<Name>>,
}

impl SortGraph {
    pub fn insert(&mut self, supersort: impl Into<Name>, subsorts: impl IntoIterator<Item = Name>) {
        let supersort = supersort.into();
        let mut closure = subsorts.into_iter().collect::<BTreeSet<_>>();
        closure.insert(supersort.clone());
        self.subsorts.insert(supersort, closure);
    }

    pub fn check_subsort(&self, sub: &Sort, sup: &Sort) -> Result<bool, SortError> {
        if sub == sup {
            return Ok(true);
        }
        let Sort::Application {
            name: sub_name,
            arguments: sub_arguments,
        } = sub
        else {
            let Sort::Variable(name) = sub else {
                unreachable!()
            };
            return Err(SortError::FoundSortVariable(name.clone()));
        };
        let Sort::Application {
            name: sup_name,
            arguments: sup_arguments,
        } = sup
        else {
            let Sort::Variable(name) = sup else {
                unreachable!()
            };
            return Err(SortError::FoundSortVariable(name.clone()));
        };
        let Some(subsorts) = self.subsorts.get(sup_name) else {
            return Err(SortError::FoundUnknownSort(sup.clone()));
        };
        if !subsorts.contains(sub_name) {
            return Ok(false);
        }
        if sub_arguments.len() != sup_arguments.len() {
            return Ok(false);
        }
        for (sub_argument, sup_argument) in sub_arguments.iter().zip(sup_arguments) {
            if !self.check_subsort(sub_argument, sup_argument)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn overlap(&self, left: &Sort, right: &Sort) -> bool {
        let (
            Sort::Application {
                name: left,
                arguments: left_arguments,
            },
            Sort::Application {
                name: right,
                arguments: right_arguments,
            },
        ) = (left, right)
        else {
            return true;
        };
        if !left_arguments.is_empty() || !right_arguments.is_empty() {
            return true;
        }
        match (self.subsorts.get(left), self.subsorts.get(right)) {
            (Some(left), Some(right)) => !left.is_disjoint(right),
            _ => true,
        }
    }
}

pub fn match_terms(
    mode: MatchMode,
    sorts: &SortGraph,
    pattern: &Term,
    subject: &Term,
) -> MatchResult {
    let shared_variables = pattern
        .attributes()
        .variables
        .intersection(&subject.attributes().variables)
        .cloned()
        .collect::<BTreeSet<_>>();
    if mode != MatchMode::Implies && !shared_variables.is_empty() {
        return match mode {
            MatchMode::Rewrite => MatchResult::Indeterminate {
                substitution: Substitution::new(),
                remainder: shared_variables
                    .into_iter()
                    .map(|variable| {
                        let term = Term::variable(variable);
                        (term.clone(), term)
                    })
                    .collect(),
            },
            MatchMode::Evaluate => {
                MatchResult::Failed(FailReason::SharedVariables(shared_variables))
            }
            MatchMode::Implies => unreachable!(),
        };
    }

    let mut matcher = Matcher {
        mode,
        sorts,
        substitution: Substitution::new(),
        queue: VecDeque::from([(pattern.clone(), subject.clone())]),
        indeterminate: Vec::new(),
    };
    if let Err(reason) = matcher.run() {
        return MatchResult::Failed(reason);
    }
    if matcher.indeterminate.is_empty() {
        MatchResult::Success(matcher.substitution)
    } else {
        matcher.indeterminate.reverse();
        MatchResult::Indeterminate {
            substitution: matcher.substitution,
            remainder: matcher.indeterminate,
        }
    }
}

struct Matcher<'a> {
    mode: MatchMode,
    sorts: &'a SortGraph,
    substitution: Substitution,
    queue: VecDeque<(Term, Term)>,
    indeterminate: Vec<(Term, Term)>,
}

impl Matcher<'_> {
    fn run(&mut self) -> Result<(), FailReason> {
        while let Some((pattern, subject)) = self.queue.pop_front() {
            self.match_one(pattern, subject)?;
        }
        Ok(())
    }

    fn match_one(&mut self, pattern: Term, subject: Term) -> Result<(), FailReason> {
        if self.mode == MatchMode::Implies && pattern == subject {
            return Ok(());
        }
        if self.mode == MatchMode::Evaluate && matches!(subject.kind(), TermKind::And(..)) {
            return self.defer(pattern, subject);
        }
        if self.mode == MatchMode::Evaluate
            && matches!(pattern.kind(), TermKind::And(..))
            && matches!(subject.kind(), TermKind::Variable(_))
        {
            return self.defer(pattern, subject);
        }
        if let TermKind::And(left, right) = pattern.kind() {
            self.enqueue(left.clone(), subject.clone());
            self.enqueue(right.clone(), subject);
            return Ok(());
        }
        if let TermKind::And(left, right) = subject.kind() {
            self.enqueue(pattern.clone(), left.clone());
            self.enqueue(pattern, right.clone());
            return Ok(());
        }
        if let TermKind::Variable(variable) = pattern.kind() {
            return self.match_variable(variable.clone(), pattern, subject);
        }
        if matches!(subject.kind(), TermKind::Variable(_)) {
            return self.defer(pattern, subject);
        }

        match (pattern.kind(), subject.kind()) {
            (
                TermKind::DomainValue {
                    sort: pattern_sort,
                    value: pattern_value,
                },
                TermKind::DomainValue {
                    sort: subject_sort,
                    value: subject_value,
                },
            ) => {
                if pattern_value != subject_value {
                    Err(FailReason::DifferentValues(pattern, subject))
                } else if pattern_sort != subject_sort {
                    Err(FailReason::DifferentSorts(pattern, subject))
                } else {
                    Ok(())
                }
            }
            (
                TermKind::Injection {
                    source: pattern_source,
                    target: pattern_target,
                    term: pattern_term,
                },
                TermKind::Injection {
                    source: subject_source,
                    target: subject_target,
                    term: subject_term,
                },
            ) => {
                if pattern_target != subject_target {
                    return Err(FailReason::DifferentSorts(pattern, subject));
                }
                if pattern_source == subject_source {
                    self.enqueue(pattern_term.clone(), subject_term.clone());
                    return Ok(());
                }
                self.match_differing_injections(pattern, subject)
            }
            (
                TermKind::Application {
                    symbol: pattern_symbol,
                    sort_arguments: pattern_sorts,
                    arguments: pattern_arguments,
                },
                TermKind::Application {
                    symbol: subject_symbol,
                    sort_arguments: subject_sorts,
                    arguments: subject_arguments,
                },
            ) if (is_constructor(&pattern) && is_constructor(&subject))
                || (self.mode == MatchMode::Evaluate
                    && is_function(&pattern)
                    && is_function(&subject)) =>
            {
                if pattern_symbol.name != subject_symbol.name {
                    if self.mode == MatchMode::Rewrite
                        || (is_constructor(&pattern) && is_constructor(&subject))
                    {
                        return Err(FailReason::DifferentSymbols(pattern, subject));
                    }
                    return self.defer(pattern, subject);
                }
                if pattern_arguments.len() != subject_arguments.len() {
                    return Err(FailReason::ArgumentLengthsDiffer(pattern, subject));
                }
                if pattern_sorts != subject_sorts {
                    return Err(FailReason::DifferentSorts(pattern, subject));
                }
                if self.mode != MatchMode::Rewrite
                    && (pattern_symbol.attributes.associative
                        || pattern_symbol.attributes.idempotent)
                {
                    return self.defer(pattern, subject);
                }
                for (pattern, subject) in pattern_arguments.iter().zip(subject_arguments) {
                    self.enqueue(pattern.clone(), subject.clone());
                }
                Ok(())
            }
            (
                TermKind::Map {
                    definition: left,
                    entries: left_entries,
                    rest: left_rest,
                },
                TermKind::Map {
                    definition: right,
                    entries: right_entries,
                    rest: right_rest,
                },
            ) if left == right
                && left_entries.is_empty()
                && right_entries.is_empty()
                && left_rest.is_none()
                && right_rest.is_none() =>
            {
                Ok(())
            }
            (
                TermKind::List {
                    definition: left,
                    heads: left_heads,
                    rest: left_rest,
                },
                TermKind::List {
                    definition: right,
                    heads: right_heads,
                    rest: right_rest,
                },
            ) if left == right
                && left_heads.is_empty()
                && right_heads.is_empty()
                && left_rest.is_none()
                && right_rest.is_none() =>
            {
                Ok(())
            }
            (
                TermKind::Set {
                    definition: left,
                    elements: left_elements,
                    rest: left_rest,
                },
                TermKind::Set {
                    definition: right,
                    elements: right_elements,
                    rest: right_rest,
                },
            ) if left == right
                && left_elements.is_empty()
                && right_elements.is_empty()
                && left_rest.is_none()
                && right_rest.is_none() =>
            {
                Ok(())
            }
            (left, right) if same_collection_category(left, right) => {
                if collection_definition_matches(left, right) {
                    self.defer(pattern, subject)
                } else {
                    Err(FailReason::DifferentSorts(pattern, subject))
                }
            }
            (TermKind::Injection { .. }, right)
                if self.mode == MatchMode::Evaluate && is_collection(right) =>
            {
                self.defer(pattern, subject)
            }
            (left, TermKind::Injection { .. })
                if self.mode == MatchMode::Evaluate && is_collection(left) =>
            {
                self.defer(pattern, subject)
            }
            (left, right) if is_rigid(left) && is_rigid(right) => {
                Err(FailReason::DifferentSymbols(pattern, subject))
            }
            _ => self.defer(pattern, subject),
        }
    }

    fn match_differing_injections(
        &mut self,
        pattern: Term,
        subject: Term,
    ) -> Result<(), FailReason> {
        let (
            TermKind::Injection {
                source: pattern_source,
                term: pattern_term,
                ..
            },
            TermKind::Injection {
                source: subject_source,
                term: subject_term,
                ..
            },
        ) = (pattern.kind(), subject.kind())
        else {
            unreachable!()
        };
        let pattern_is_subsort = self
            .sorts
            .check_subsort(pattern_source, subject_source)
            .map_err(FailReason::Subsorting)?;
        let subject_is_subsort = self
            .sorts
            .check_subsort(subject_source, pattern_source)
            .map_err(FailReason::Subsorting)?;
        if !pattern_is_subsort && !subject_is_subsort {
            return Err(FailReason::DifferentSorts(
                pattern_term.clone(),
                subject_term.clone(),
            ));
        }
        if pattern_is_subsort
            && (is_function(subject_term) || matches!(subject_term.kind(), TermKind::Variable(_)))
        {
            return self.defer(pattern_term.clone(), subject_term.clone());
        }
        if subject_is_subsort {
            if let TermKind::Variable(variable) = pattern_term.kind() {
                return self.bind(
                    variable.clone(),
                    Term::injection(
                        subject_source.clone(),
                        pattern_source.clone(),
                        subject_term.clone(),
                    ),
                );
            }
            if is_function(pattern_term) {
                return self.defer(pattern_term.clone(), subject_term.clone());
            }
        }
        Err(FailReason::DifferentSorts(pattern, subject))
    }

    fn match_variable(
        &mut self,
        variable: Variable,
        pattern: Term,
        subject: Term,
    ) -> Result<(), FailReason> {
        if let TermKind::Variable(subject_variable) = subject.kind()
            && variable.name == subject_variable.name
            && variable.sort != subject_variable.sort
        {
            return Err(FailReason::VariableConflict(
                variable.clone(),
                Term::variable(variable),
                subject,
            ));
        }
        let subject_sort = subject.sort();
        match self.sorts.check_subsort(&subject_sort, &variable.sort) {
            Ok(true) => {
                let subject = if subject_sort == variable.sort {
                    subject
                } else {
                    Term::injection(subject_sort, variable.sort.clone(), subject)
                };
                self.bind(variable, subject)
            }
            Ok(false)
                if (is_function(&subject) || matches!(subject.kind(), TermKind::Variable(_)))
                    && self.sorts.overlap(&subject_sort, &variable.sort) =>
            {
                self.defer(pattern, subject)
            }
            Ok(false) => Err(FailReason::DifferentSorts(pattern, subject)),
            Err(error) => Err(FailReason::Subsorting(error)),
        }
    }

    fn bind(&mut self, variable: Variable, term: Term) -> Result<(), FailReason> {
        if let Some(old) = self.substitution.get(&variable).cloned() {
            if old == term {
                return Ok(());
            }
            if old.attributes().constructor_like && term.attributes().constructor_like {
                return Err(FailReason::VariableConflict(variable, old, term));
            }
            return self.defer(old, term);
        }

        let term = substitute(&term, &self.substitution);
        if term.attributes().variables.contains(&variable) {
            return Err(FailReason::VariableRecursion(variable, term));
        }
        let singleton = Substitution::from([(variable.clone(), term.clone())]);
        for value in self.substitution.values_mut() {
            *value = substitute(value, &singleton);
        }
        self.substitution.insert(variable, term);
        Ok(())
    }

    fn enqueue(&mut self, pattern: Term, subject: Term) {
        self.queue.push_back((pattern, subject));
    }

    fn defer(&mut self, pattern: Term, subject: Term) -> Result<(), FailReason> {
        self.indeterminate.push((pattern, subject));
        Ok(())
    }
}

fn is_constructor(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::Application { symbol, .. }
            if symbol.attributes.symbol_type == SymbolType::Constructor
    )
}

fn is_function(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::Application { symbol, .. }
            if matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
    )
}

fn is_collection(kind: &TermKind) -> bool {
    matches!(
        kind,
        TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. }
    )
}

fn is_rigid(kind: &TermKind) -> bool {
    matches!(
        kind,
        TermKind::DomainValue { .. }
            | TermKind::Injection { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. }
    ) || matches!(
        kind,
        TermKind::Application { symbol, .. }
            if symbol.attributes.symbol_type == SymbolType::Constructor
    )
}

fn same_collection_category(left: &TermKind, right: &TermKind) -> bool {
    matches!(
        (left, right),
        (TermKind::Map { .. }, TermKind::Map { .. })
            | (TermKind::List { .. }, TermKind::List { .. })
            | (TermKind::Set { .. }, TermKind::Set { .. })
    )
}

fn collection_definition_matches(left: &TermKind, right: &TermKind) -> bool {
    match (left, right) {
        (
            TermKind::Map {
                definition: left, ..
            },
            TermKind::Map {
                definition: right, ..
            },
        ) => left == right,
        (
            TermKind::List {
                definition: left, ..
            },
            TermKind::List {
                definition: right, ..
            },
        )
        | (
            TermKind::Set {
                definition: left, ..
            },
            TermKind::Set {
                definition: right, ..
            },
        ) => left == right,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::term::{
        CollectionSymbols, FunctionType, ListDefinition, MapDefinition, Symbol, SymbolAttributes,
    };

    use super::*;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Outcome {
        Success,
        Failed,
        Indeterminate,
    }

    fn outcome(result: MatchResult) -> Outcome {
        match result {
            MatchResult::Success(_) => Outcome::Success,
            MatchResult::Failed(_) => Outcome::Failed,
            MatchResult::Indeterminate { .. } => Outcome::Indeterminate,
        }
    }

    fn sort() -> Sort {
        Sort::simple("SomeSort")
    }

    fn subsort() -> Sort {
        Sort::simple("ASubsort")
    }

    fn variable(name: &str, sort: Sort) -> Variable {
        Variable::new(name, sort)
    }

    fn var(name: &str, sort: Sort) -> Term {
        Term::variable(variable(name, sort))
    }

    fn domain_value(sort: Sort, value: &str) -> Term {
        Term::domain_value(sort, value)
    }

    fn constructor() -> Arc<Symbol> {
        Arc::new(Symbol::constructor("con1", vec![sort()], sort()))
    }

    fn function() -> Arc<Symbol> {
        Arc::new(Symbol {
            name: "f1".into(),
            sort_variables: Vec::new(),
            argument_sorts: vec![sort()],
            result_sort: sort(),
            attributes: SymbolAttributes {
                symbol_type: SymbolType::Function(FunctionType::Total),
                associative: false,
                idempotent: false,
                macro_or_alias: false,
                has_evaluators: true,
                hook: None,
            },
        })
    }

    fn application(symbol: Arc<Symbol>, argument: Term) -> Term {
        Term::application(symbol, Vec::new(), vec![argument])
    }

    fn collection_symbols(prefix: &str) -> CollectionSymbols {
        CollectionSymbols {
            unit: format!("{prefix}Unit").into(),
            element: format!("{prefix}Element").into(),
            concat: format!("{prefix}Concat").into(),
        }
    }

    fn kinds() -> Vec<(&'static str, Term, Term)> {
        let subject_constructor = application(constructor(), domain_value(sort(), "constructor"));
        let map_definition = Arc::new(MapDefinition {
            symbols: collection_symbols("map"),
            key_sort: "MapKey".into(),
            value_sort: "MapValue".into(),
            map_sort: "MapSort".into(),
        });
        let list_definition = Arc::new(ListDefinition {
            symbols: collection_symbols("list"),
            element_sort: "ListElement".into(),
            list_sort: "ListSort".into(),
        });
        let set_definition = Arc::new(ListDefinition {
            symbols: collection_symbols("set"),
            element_sort: "SetElement".into(),
            list_sort: "SetSort".into(),
        });
        vec![
            (
                "And",
                Term::and(var("P1", sort()), var("P2", sort())),
                Term::and(subject_constructor.clone(), subject_constructor.clone()),
            ),
            (
                "DomainValue",
                domain_value(sort(), "domain"),
                domain_value(sort(), "domain"),
            ),
            (
                "Injection",
                Term::injection(subsort(), sort(), var("PI", subsort())),
                Term::injection(subsort(), sort(), domain_value(subsort(), "injected")),
            ),
            (
                "Map",
                Term::map(map_definition.clone(), Vec::new(), None),
                Term::map(map_definition, Vec::new(), None),
            ),
            (
                "List",
                Term::list(list_definition.clone(), Vec::new(), None),
                Term::list(list_definition, Vec::new(), None),
            ),
            (
                "Set",
                Term::set(set_definition.clone(), Vec::new(), None),
                Term::set(set_definition, Vec::new(), None),
            ),
            (
                "Constructor",
                application(constructor(), var("PC", sort())),
                subject_constructor,
            ),
            (
                "Function",
                application(function(), var("PF", sort())),
                application(function(), domain_value(sort(), "function")),
            ),
            ("Variable", var("PX", sort()), var("SY", sort())),
        ]
    }

    fn sort_graph() -> SortGraph {
        let mut graph = SortGraph::default();
        graph.insert("SomeSort", [Name::from("ASubsort")]);
        graph.insert("ASubsort", []);
        for name in ["MapSort", "ListSort", "SetSort"] {
            graph.insert(name, []);
        }
        graph
    }

    fn expected(mode: MatchMode) -> [[Outcome; 9]; 9] {
        use Outcome::{Failed as F, Indeterminate as I, Success as S};
        match mode {
            MatchMode::Rewrite => [
                [S, S, S, F, F, F, S, S, S],
                [F, S, F, F, F, F, F, I, I],
                [F, F, S, F, F, F, F, I, I],
                [F, F, F, S, F, F, F, I, I],
                [F, F, F, F, S, F, F, I, I],
                [F, F, F, F, F, S, F, I, I],
                [S, F, F, F, F, F, S, I, I],
                [I, I, I, I, I, I, I, I, I],
                [S, S, S, F, F, F, S, S, S],
            ],
            MatchMode::Evaluate => [
                [I, S, S, F, F, F, S, S, I],
                [I, S, F, F, F, F, F, I, I],
                [I, F, S, I, I, I, F, I, I],
                [I, F, I, S, F, F, F, I, I],
                [I, F, I, F, S, F, F, I, I],
                [I, F, I, F, F, S, F, I, I],
                [I, F, F, F, F, F, S, I, I],
                [I, I, I, I, I, I, I, S, I],
                [I, S, S, F, F, F, S, S, S],
            ],
            MatchMode::Implies => [
                [S, S, S, F, F, F, S, S, S],
                [F, S, F, F, F, F, F, I, I],
                [F, F, S, F, F, F, F, I, I],
                [F, F, F, S, F, F, F, I, I],
                [F, F, F, F, S, F, F, I, I],
                [F, F, F, F, F, S, F, I, I],
                [S, F, F, F, F, F, S, I, I],
                [I, I, I, I, I, I, I, I, I],
                [S, S, S, F, F, F, S, S, S],
            ],
        }
    }

    #[test]
    fn matches_the_reference_dispatch_grid() {
        let kinds = kinds();
        let sorts = sort_graph();
        for mode in [MatchMode::Rewrite, MatchMode::Evaluate, MatchMode::Implies] {
            for ((pattern_name, pattern, _), expected_row) in kinds.iter().zip(expected(mode)) {
                for ((subject_name, _, subject), expected) in kinds.iter().zip(expected_row) {
                    assert_eq!(
                        outcome(match_terms(mode, &sorts, pattern, subject)),
                        expected,
                        "{mode:?}: {pattern_name} vs {subject_name}"
                    );
                }
            }
        }
    }

    #[test]
    fn returns_the_reference_oriented_substitution() {
        let pattern = application(constructor(), var("X", sort()));
        let subject = application(constructor(), domain_value(sort(), "value"));
        assert_eq!(
            match_terms(MatchMode::Rewrite, &sort_graph(), &pattern, &subject),
            MatchResult::Success(Substitution::from([(
                variable("X", sort()),
                domain_value(sort(), "value"),
            )]))
        );
    }
}
