//! Portable SMT-LIB translation shared by native Z3 and solver-free builds.

use std::{collections::BTreeMap, fmt};

#[cfg(feature = "z3")]
use std::collections::BTreeSet;

use crate::{
    definition::BackendDefinition,
    rule::{Predicate, RewriteRule, RuleRhs, Theory},
    substitution::Substitution,
    term::{Sort, Term, TermKind, Variable},
};

#[cfg(feature = "z3")]
mod z3;

#[cfg(feature = "z3")]
pub use z3::{Z3Options, Z3Solver};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SmtType {
    Lib(String),
    Hook(SExpr),
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

impl SExpr {
    pub fn atom(value: impl Into<String>) -> Self {
        Self::Atom(value.into())
    }

    pub fn parse(source: &str) -> Result<Self, SExprError> {
        let mut parser = SExprParser::new(source);
        let expression = parser.expression()?;
        parser.skip_whitespace();
        if parser.peek().is_some() {
            return Err(SExprError::TrailingInput(parser.offset));
        }
        Ok(expression)
    }

    fn application(operator: impl Into<String>, arguments: Vec<Self>) -> Self {
        let mut items = Vec::with_capacity(arguments.len() + 1);
        items.push(Self::atom(operator));
        items.extend(arguments);
        Self::List(items)
    }
}

impl fmt::Display for SExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Atom(atom) => formatter.write_str(atom),
            Self::List(items) => {
                formatter.write_str("(")?;
                for (index, item) in items.iter().enumerate() {
                    if index != 0 {
                        formatter.write_str(" ")?;
                    }
                    write!(formatter, "{item}")?;
                }
                formatter.write_str(")")
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SExprError {
    UnexpectedEnd,
    UnexpectedClose(usize),
    UnterminatedList(usize),
    EmptyAtom(usize),
    TrailingInput(usize),
}

impl fmt::Display for SExprError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

struct SExprParser<'a> {
    source: &'a str,
    offset: usize,
}

impl<'a> SExprParser<'a> {
    fn new(source: &'a str) -> Self {
        Self { source, offset: 0 }
    }

    fn expression(&mut self) -> Result<SExpr, SExprError> {
        self.skip_whitespace();
        match self.peek() {
            None => Err(SExprError::UnexpectedEnd),
            Some('(') => self.list(),
            Some(')') => Err(SExprError::UnexpectedClose(self.offset)),
            Some(_) => self.atom(),
        }
    }

    fn list(&mut self) -> Result<SExpr, SExprError> {
        let start = self.offset;
        self.bump();
        let mut items = Vec::new();
        loop {
            self.skip_whitespace();
            match self.peek() {
                Some(')') => {
                    self.bump();
                    return Ok(SExpr::List(items));
                }
                None => return Err(SExprError::UnterminatedList(start)),
                Some(_) => items.push(self.expression()?),
            }
        }
    }

    fn atom(&mut self) -> Result<SExpr, SExprError> {
        let start = self.offset;
        while self.peek().is_some_and(|character| {
            !character.is_whitespace() && !matches!(character, '(' | ')' | ';')
        }) {
            self.bump();
        }
        if self.offset == start {
            return Err(SExprError::EmptyAtom(start));
        }
        Ok(SExpr::atom(&self.source[start..self.offset]))
    }

    fn skip_whitespace(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.bump();
        }
    }

    fn peek(&self) -> Option<char> {
        self.source[self.offset..].chars().next()
    }

    fn bump(&mut self) {
        if let Some(character) = self.peek() {
            self.offset += character.len_utf8();
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TranslationState {
    pub mappings: BTreeMap<Term, String>,
    counter: usize,
}

impl Default for TranslationState {
    fn default() -> Self {
        Self::new()
    }
}

impl TranslationState {
    pub fn new() -> Self {
        Self {
            mappings: BTreeMap::new(),
            counter: 1,
        }
    }

    pub fn translate_term(&mut self, term: &Term) -> Result<SExpr, TranslationError> {
        match term.kind() {
            TermKind::And(left, right)
                if left.sort() == Sort::simple("SortBool")
                    && right.sort() == Sort::simple("SortBool") =>
            {
                Ok(SExpr::application(
                    "and",
                    vec![self.translate_term(left)?, self.translate_term(right)?],
                ))
            }
            TermKind::And(..) => Err(TranslationError::NonBooleanAnd(term.clone())),
            TermKind::Application {
                symbol, arguments, ..
            } => match &symbol.attributes.smt {
                None => Ok(self.abstract_term(term)),
                Some(SmtType::Lib(name)) => self.translate_application(name, arguments),
                Some(SmtType::Hook(SExpr::Atom(name))) => {
                    self.translate_application(name, arguments)
                }
                Some(SmtType::Hook(expression)) => {
                    let arguments = arguments
                        .iter()
                        .map(|argument| self.translate_term(argument))
                        .collect::<Result<Vec<_>, _>>()?;
                    fill_placeholders(expression, &arguments)
                }
            },
            TermKind::DomainValue { sort, value }
                if sort == &Sort::simple("SortBool") || sort == &Sort::simple("SortInt") =>
            {
                Ok(SExpr::atom(value.as_ref()))
            }
            TermKind::DomainValue { .. }
            | TermKind::Variable(_)
            | TermKind::Injection { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. } => Ok(self.abstract_term(term)),
        }
    }

    pub fn translate_predicate(
        &mut self,
        predicate: &Predicate,
    ) -> Result<SExpr, TranslationError> {
        match predicate {
            Predicate::True => Ok(SExpr::atom("true")),
            Predicate::False => Ok(SExpr::atom("false")),
            Predicate::Term(term) => self.translate_term(term),
            Predicate::Equals(left, right) => Ok(SExpr::application(
                "=",
                vec![self.translate_term(left)?, self.translate_term(right)?],
            )),
            Predicate::Not(inner) => Ok(SExpr::application(
                "not",
                vec![self.translate_predicate(inner)?],
            )),
            Predicate::And(inner) => self.translate_predicates("and", inner),
            Predicate::Or(inner) => self.translate_predicates("or", inner),
            Predicate::Implies(left, right) => Ok(SExpr::application(
                "=>",
                vec![
                    self.translate_predicate(left)?,
                    self.translate_predicate(right)?,
                ],
            )),
            Predicate::Iff(left, right) => Ok(SExpr::application(
                "=",
                vec![
                    self.translate_predicate(left)?,
                    self.translate_predicate(right)?,
                ],
            )),
            Predicate::Ceil(term) if term.attributes().constructor_like => Ok(SExpr::atom("true")),
            Predicate::Ceil(_) => Err(TranslationError::UnsupportedPredicate("ceil")),
            Predicate::Floor(_) => Err(TranslationError::UnsupportedPredicate("floor")),
            Predicate::In(..) => Err(TranslationError::UnsupportedPredicate("in")),
            Predicate::Exists(..) => Err(TranslationError::UnsupportedPredicate("exists")),
            Predicate::Forall(..) => Err(TranslationError::UnsupportedPredicate("forall")),
        }
    }

    fn translate_predicates(
        &mut self,
        operator: &str,
        predicates: &[Predicate],
    ) -> Result<SExpr, TranslationError> {
        Ok(SExpr::application(
            operator,
            predicates
                .iter()
                .map(|predicate| self.translate_predicate(predicate))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }

    fn translate_application(
        &mut self,
        name: &str,
        arguments: &[Term],
    ) -> Result<SExpr, TranslationError> {
        if arguments.is_empty() {
            return Ok(SExpr::atom(name));
        }
        Ok(SExpr::application(
            name,
            arguments
                .iter()
                .map(|argument| self.translate_term(argument))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }

    fn abstract_term(&mut self, term: &Term) -> SExpr {
        if let Some(name) = self.mappings.get(term) {
            return SExpr::atom(name);
        }
        let name = format!("SMT-{}", self.counter);
        self.counter += 1;
        self.mappings.insert(term.clone(), name.clone());
        SExpr::atom(name)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TranslationError {
    NonBooleanAnd(Term),
    PlaceholderOutOfBounds {
        placeholder: usize,
        arguments: usize,
    },
    UnsupportedPredicate(&'static str),
    ParametricSort(Sort),
    SmtLemmaSurplusMappings {
        rule_id: String,
        terms: Vec<Term>,
    },
    MissingSmtLemmaVariable {
        rule_id: String,
        variable: Variable,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmtPrelude {
    declarations: Vec<String>,
}

impl SmtPrelude {
    pub fn from_definition(definition: &BackendDefinition) -> Result<Self, TranslationError> {
        let mut declarations = definition
            .sorts
            .iter()
            .filter(|(name, _)| name.as_ref() != "SortInt" && name.as_ref() != "SortBool")
            .map(|(name, info)| format!("(declare-sort {} {})", quote(name), info.parameters.len()))
            .collect::<Vec<_>>();
        for symbol in definition.symbols.values() {
            let Some(SmtType::Lib(name)) = &symbol.attributes.smt else {
                continue;
            };
            let arguments = symbol
                .argument_sorts
                .iter()
                .map(smt_sort)
                .collect::<Result<Vec<_>, _>>()?;
            declarations.push(format!(
                "(declare-fun {name} ({}) {})",
                arguments.join(" "),
                smt_sort(&symbol.result_sort)?
            ));
        }
        for rule in smt_lemmas(definition) {
            declarations.push(format!("(assert {})", translate_smt_lemma(rule)?));
        }
        Ok(Self { declarations })
    }

    pub fn declarations(&self) -> &[String] {
        &self.declarations
    }

    #[cfg(feature = "z3")]
    fn query(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
        filter_for_checked: bool,
    ) -> Result<TranslatedQuery, TranslationError> {
        let mut translation = TranslationState::new();
        let substitution = substitution
            .iter()
            .map(|(variable, term)| {
                Ok(SExpr::application(
                    "=",
                    vec![
                        translation.translate_term(&Term::variable(variable.clone()))?,
                        translation.translate_term(term)?,
                    ],
                ))
            })
            .collect::<Result<Vec<_>, TranslationError>>()?;
        let known = known
            .iter()
            .map(|predicate| translation.translate_predicate(predicate))
            .collect::<Result<Vec<_>, _>>()?;
        let checked = checked
            .iter()
            .map(|predicate| translation.translate_predicate(predicate))
            .collect::<Result<Vec<_>, _>>()?;
        let checked = SExpr::application("and", checked);
        let (substitution, known) = if filter_for_checked {
            let interesting = smt_variables(&checked);
            (
                closure_over(&interesting, substitution),
                closure_over(&interesting, known),
            )
        } else {
            (substitution, known)
        };
        let mut base = self.declarations.clone();
        for (term, name) in &translation.mappings {
            base.push(format!(
                "(declare-const {name} {})",
                smt_sort(&term.sort())?
            ));
        }
        base.extend(
            substitution
                .into_iter()
                .chain(known)
                .map(|expression| format!("(assert {expression})")),
        );
        Ok(TranslatedQuery {
            base: base.join("\n"),
            checked,
        })
    }
}

#[cfg(feature = "z3")]
fn smt_variables(expression: &SExpr) -> BTreeSet<String> {
    match expression {
        SExpr::Atom(atom) if atom.starts_with("SMT-") => BTreeSet::from([atom.clone()]),
        SExpr::Atom(_) => BTreeSet::new(),
        SExpr::List(items) => items.iter().flat_map(smt_variables).collect(),
    }
}

#[cfg(feature = "z3")]
fn closure_over(interesting: &BTreeSet<String>, expressions: Vec<SExpr>) -> Vec<SExpr> {
    let mut variables = interesting.clone();
    let mut remaining = expressions.into_iter().collect::<BTreeSet<_>>();
    let mut selected = BTreeSet::new();
    loop {
        let added = remaining
            .iter()
            .filter(|expression| !smt_variables(expression).is_disjoint(&variables))
            .cloned()
            .collect::<Vec<_>>();
        if added.is_empty() {
            return selected.into_iter().collect();
        }
        for expression in added {
            remaining.remove(&expression);
            variables.extend(smt_variables(&expression));
            selected.insert(expression);
        }
    }
}

fn smt_lemmas(definition: &BackendDefinition) -> Vec<&RewriteRule> {
    fn theory_rules(theory: &Theory) -> impl Iterator<Item = &RewriteRule> {
        theory
            .values()
            .flat_map(|priorities| priorities.values())
            .flatten()
            .map(AsRef::as_ref)
    }
    theory_rules(&definition.function_theory)
        .chain(theory_rules(&definition.simplification_theory))
        .filter(|rule| rule.attributes.smt_lemma)
        .collect()
}

fn translate_smt_lemma(rule: &RewriteRule) -> Result<SExpr, TranslationError> {
    let RuleRhs::Term(rhs) = &rule.rhs else {
        return Err(TranslationError::UnsupportedPredicate("ceil SMT lemma"));
    };
    let mut translation = TranslationState::new();
    let equality = SExpr::application(
        "=",
        vec![
            translation.translate_term(&rule.lhs)?,
            translation.translate_term(rhs)?,
        ],
    );
    let body = if rule.requires.is_empty() {
        equality
    } else {
        let requires = rule
            .requires
            .iter()
            .map(|predicate| translation.translate_predicate(predicate))
            .collect::<Result<Vec<_>, _>>()?;
        SExpr::application("=>", vec![SExpr::application("and", requires), equality])
    };
    let mut binders = Vec::new();
    for variable in &rule.lhs.attributes().variables {
        let term = Term::variable(variable.clone());
        let Some(name) = translation.mappings.remove(&term) else {
            return Err(TranslationError::MissingSmtLemmaVariable {
                rule_id: rule.attributes.unique_id.clone(),
                variable: variable.clone(),
            });
        };
        binders.push(SExpr::List(vec![
            SExpr::atom(name),
            SExpr::atom(smt_sort(&variable.sort)?),
        ]));
    }
    if !translation.mappings.is_empty() {
        return Err(TranslationError::SmtLemmaSurplusMappings {
            rule_id: rule.attributes.unique_id.clone(),
            terms: translation.mappings.into_keys().collect(),
        });
    }
    if binders.is_empty() {
        Ok(body)
    } else {
        Ok(SExpr::List(vec![
            SExpr::atom("forall"),
            SExpr::List(binders),
            body,
        ]))
    }
}

fn smt_sort(sort: &Sort) -> Result<String, TranslationError> {
    match sort {
        Sort::Variable(_) => Err(TranslationError::ParametricSort(sort.clone())),
        Sort::Application { name, .. } if name.as_ref() == "SortInt" => Ok("Int".into()),
        Sort::Application { name, .. } if name.as_ref() == "SortBool" => Ok("Bool".into()),
        Sort::Application { name, arguments } if arguments.is_empty() => Ok(quote(name)),
        Sort::Application { name, arguments } => Ok(format!(
            "({} {})",
            quote(name),
            arguments
                .iter()
                .map(smt_sort)
                .collect::<Result<Vec<_>, _>>()?
                .join(" ")
        )),
    }
}

fn quote(name: &str) -> String {
    format!("|{name}|")
}

#[cfg(feature = "z3")]
struct TranslatedQuery {
    base: String,
    checked: SExpr,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Satisfiability {
    Sat,
    Unsat,
    Unknown(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Validity {
    Valid,
    Invalid,
    InconsistentGroundTruth,
    Indeterminate,
    Unknown(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SmtError {
    Translation(TranslationError),
    Unavailable,
    InconsistentPrelude,
    UnknownPrelude(String),
    Unknown(String),
    InconsistentGroundTruth,
}

impl From<TranslationError> for SmtError {
    fn from(error: TranslationError) -> Self {
        Self::Translation(error)
    }
}

pub trait SmtSolver {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Result<Satisfiability, SmtError>;

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Result<Validity, SmtError>;
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NoSolver;

impl SmtSolver for NoSolver {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Result<Satisfiability, SmtError> {
        Err(SmtError::Unavailable)
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        checked: &[Predicate],
    ) -> Result<Validity, SmtError> {
        if checked.is_empty() {
            Ok(Validity::Valid)
        } else {
            Err(SmtError::Unavailable)
        }
    }
}

fn fill_placeholders(expression: &SExpr, arguments: &[SExpr]) -> Result<SExpr, TranslationError> {
    match expression {
        SExpr::Atom(atom) => {
            let Some(index) = atom
                .strip_prefix('#')
                .and_then(|index| index.parse::<usize>().ok())
            else {
                return Ok(expression.clone());
            };
            if index == 0 || index > arguments.len() {
                return Err(TranslationError::PlaceholderOutOfBounds {
                    placeholder: index,
                    arguments: arguments.len(),
                });
            }
            Ok(arguments[index - 1].clone())
        }
        SExpr::List(items) => Ok(SExpr::List(
            items
                .iter()
                .map(|item| fill_placeholders(item, arguments))
                .collect::<Result<Vec<_>, _>>()?,
        )),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::term::{FunctionType, Symbol, SymbolAttributes, SymbolType, Variable};

    fn symbol(name: &str, smt: Option<SmtType>, arguments: Vec<Sort>, result: Sort) -> Arc<Symbol> {
        Arc::new(Symbol {
            name: name.into(),
            sort_variables: Vec::new(),
            argument_sorts: arguments,
            result_sort: result,
            attributes: SymbolAttributes {
                symbol_type: SymbolType::Function(FunctionType::Total),
                associative: false,
                idempotent: false,
                macro_or_alias: false,
                has_evaluators: true,
                smt,
                hook: None,
                collection: None,
            },
        })
    }

    fn integer(value: &str) -> Term {
        Term::domain_value(Sort::simple("SortInt"), value)
    }

    #[test]
    fn parses_and_renders_nested_s_expressions() {
        let source = "(ite (< #1 0) (- 0 #1) #1)";
        assert_eq!(SExpr::parse(source).unwrap().to_string(), source);
        assert!(matches!(
            SExpr::parse("(+ #1 #2) trailing"),
            Err(SExprError::TrailingInput(_))
        ));
    }

    #[test]
    fn expands_smt_hook_placeholders_recursively() {
        let int = Sort::simple("SortInt");
        let absolute = Term::application(
            symbol(
                "absolute",
                Some(SmtType::Hook(
                    SExpr::parse("(ite (< #1 0) (- 0 #1) #1)").unwrap(),
                )),
                vec![int.clone()],
                int,
            ),
            Vec::new(),
            vec![integer("-5")],
        );

        assert_eq!(
            TranslationState::new()
                .translate_term(&absolute)
                .unwrap()
                .to_string(),
            "(ite (< -5 0) (- 0 -5) -5)"
        );
    }

    #[test]
    fn abstracts_uninterpreted_terms_stably_and_preserves_their_sorts() {
        let variable = Term::variable(Variable::new("X", Sort::simple("SortInt")));
        let predicate = Predicate::Equals(variable.clone(), variable.clone());
        let mut translation = TranslationState::new();

        assert_eq!(
            translation
                .translate_predicate(&predicate)
                .unwrap()
                .to_string(),
            "(= SMT-1 SMT-1)"
        );
        assert_eq!(translation.mappings.get(&variable), Some(&"SMT-1".into()));
        assert_eq!(variable.sort(), Sort::simple("SortInt"));
    }

    #[test]
    fn rejects_out_of_range_placeholders() {
        assert_eq!(
            fill_placeholders(&SExpr::atom("#2"), &[SExpr::atom("one")]),
            Err(TranslationError::PlaceholderOutOfBounds {
                placeholder: 2,
                arguments: 1,
            })
        );
    }
}
