//! Portable SMT-LIB translation shared by native Z3 and solver-free builds: one pass per query
//! script; a responsibility, not an algorithm; no counter of its own, no worklist.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use k_rust_kore::names::BuiltinSort;

use crate::{
    definition::BackendDefinition,
    rewrite::substitute_predicates,
    rule::{Predicate, RewriteRule, RuleRhs, Theory},
    stop::PreludeSignal,
    substitution::Substitution,
    term::{FunctionType, Sort, Symbol, SymbolType, Term, TermKind, Variable},
};

#[cfg(feature = "z3")]
mod query;
#[cfg(feature = "z3")]
mod z3;

#[cfg(feature = "z3")]
use query::TranslatedQuery;

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

/// Whether an SMT-LIB translation denotes exactly the predicates it was made from.
///
/// Every abstraction of the translation over-approximates: a term or predicate without an SMT
/// translation becomes an unrelated fresh constant (no congruence or constructor injectivity), a
/// free or quantified variable of a sort other than `Int` or `Bool` ranges over an
/// uninterpreted sort that need not have the K sort's values, and an `smtlib` symbol becomes an
/// uninterpreted function that retains only congruence. Every K valuation that satisfies the
/// predicates therefore induces a model of the translation, so `Unsat` refutes the predicates
/// whatever the exactness. A model is a K valuation of the predicates only when the translation
/// is `Exact`.
///
/// A partial function translated as a total SMT operation is not an over-approximation: an atom
/// over an undefined term denotes `\bottom` in K and some value in SMT. It is `Approximate` for
/// the purpose of reading a model; `Unsat` stays conclusive for it only under the definedness
/// premise that `SmtSolver::check_predicates` documents.
/// SMT hook translations, SMT lemma axioms and the user prelude are trusted.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Exactness {
    Approximate,
    Exact,
}

impl Exactness {
    /// The exactness of a translation made of two parts: exact only when both parts are.
    pub const fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::Exact, Self::Exact) => Self::Exact,
            (Self::Approximate, _) | (_, Self::Approximate) => Self::Approximate,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TranslationState {
    pub mappings: BTreeMap<Term, String>,
    predicate_mappings: Vec<(Predicate, String)>,
    dependent_mappings: BTreeMap<(Predicate, Vec<Sort>), String>,
    bound_variables: Vec<(Variable, String)>,
    counter: usize,
    /// The exactness of everything translated so far; lowered by each site that approximates.
    exactness: Exactness,
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
            predicate_mappings: Vec::new(),
            dependent_mappings: BTreeMap::new(),
            bound_variables: Vec::new(),
            counter: 1,
            exactness: Exactness::Exact,
        }
    }

    /// The exactness of everything this state has translated and declared so far.
    pub fn exactness(&self) -> Exactness {
        self.exactness
    }

    fn approximate(&mut self, exactness: Exactness) {
        self.exactness = self.exactness.and(exactness);
    }

    pub fn translate_term(&mut self, term: &Term) -> Result<SExpr, TranslationError> {
        match term.kind() {
            TermKind::And(left, right)
                if left.sort().is_builtin(BuiltinSort::Bool)
                    && right.sort().is_builtin(BuiltinSort::Bool) =>
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
                None => Ok(self.abstract_term(term, Exactness::Approximate)),
                Some(SmtType::Lib(name)) => {
                    self.translate_application(name, arguments, Exactness::Approximate)
                }
                Some(SmtType::Hook(SExpr::Atom(name))) => {
                    self.translate_application(name, arguments, symbol_exactness(symbol))
                }
                Some(SmtType::Hook(expression)) => {
                    self.approximate(symbol_exactness(symbol));
                    let arguments = arguments
                        .iter()
                        .map(|argument| self.translate_term(argument))
                        .collect::<Result<Vec<_>, _>>()?;
                    fill_placeholders(expression, &arguments)
                }
            },
            TermKind::DomainValue { sort, value }
                if sort.is_builtin(BuiltinSort::Bool) || sort.is_builtin(BuiltinSort::Int) =>
            {
                let value = value.as_utf8().map_err(|_| {
                    TranslationError::UnsupportedPredicate("non-UTF-8 Bool or Int SMT literal")
                })?;
                Ok(SExpr::atom(value))
            }
            TermKind::Variable(variable) => {
                match self
                    .bound_variables
                    .iter()
                    .rev()
                    .find(|(bound, _)| bound == variable)
                {
                    Some((_, name)) => Ok(SExpr::atom(name.clone())),
                    // A free variable stands for itself; the sort of its constant is recorded
                    // where the constant is declared (`mapping_declarations`).
                    None => Ok(self.abstract_term(term, Exactness::Exact)),
                }
            }
            TermKind::DomainValue { .. }
            | TermKind::Injection { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. } => Ok(self.abstract_term(term, Exactness::Approximate)),
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
            predicate @ Predicate::Ceil(_) => Ok(self.abstract_predicate(predicate)),
            predicate @ (Predicate::Floor(_) | Predicate::In(..)) => {
                Ok(self.abstract_predicate(predicate))
            }
            Predicate::Exists(variable, inner) => {
                self.translate_quantifier("exists", variable, inner)
            }
            Predicate::Forall(variable, inner) => {
                self.translate_quantifier("forall", variable, inner)
            }
        }
    }

    fn translate_quantifier(
        &mut self,
        quantifier: &str,
        variable: &Variable,
        body: &Predicate,
    ) -> Result<SExpr, TranslationError> {
        let sort = self.smt_sort(&variable.sort)?;
        let variable_name = self.fresh_name();
        self.bound_variables
            .push((variable.clone(), variable_name.clone()));
        let body = self.translate_predicate(body);
        self.bound_variables.pop();
        Ok(SExpr::List(vec![
            SExpr::atom(quantifier),
            SExpr::List(vec![SExpr::List(vec![
                SExpr::atom(variable_name),
                SExpr::atom(sort),
            ])]),
            body?,
        ]))
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

    /// Applies the SMT operation `name` to the translated arguments. `exactness` states whether
    /// the operation denotes the symbol exactly (`symbol_exactness`).
    fn translate_application(
        &mut self,
        name: &str,
        arguments: &[Term],
        exactness: Exactness,
    ) -> Result<SExpr, TranslationError> {
        self.approximate(exactness);
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

    /// The constant (or, under a binder it mentions, the function of the bound variables) that
    /// stands for `term`. `exactness` is `Exact` only for a free variable, which the constant
    /// denotes exactly up to its sort; every other abstracted term is `Approximate`, because the
    /// constant forgets its structure.
    fn abstract_term(&mut self, term: &Term, exactness: Exactness) -> SExpr {
        self.approximate(exactness);
        if !self.bound_variables.is_empty()
            && let Some(expression) = self.abstract_dependent(&Predicate::Term(term.clone()))
        {
            return expression;
        }
        if let Some(name) = self.mappings.get(term) {
            return SExpr::atom(name);
        }
        let name = self.fresh_name();
        self.mappings.insert(term.clone(), name.clone());
        SExpr::atom(name)
    }

    /// A Boolean constant that stands for a predicate without an SMT translation; it forgets
    /// what the predicate says, so the translation is `Approximate`.
    fn abstract_predicate(&mut self, predicate: &Predicate) -> SExpr {
        self.approximate(Exactness::Approximate);
        if !self.bound_variables.is_empty()
            && let Some(expression) = self.abstract_dependent(predicate)
        {
            return expression;
        }
        if let Some((_, name)) = self
            .predicate_mappings
            .iter()
            .find(|(mapped, _)| mapped == predicate)
        {
            return SExpr::atom(name);
        }
        let name = self.fresh_name();
        self.predicate_mappings
            .push((predicate.clone(), name.clone()));
        SExpr::atom(name)
    }

    fn fresh_name(&mut self) -> String {
        let name = format!("SMT-{}", self.counter);
        self.counter += 1;
        name
    }

    /// Like Kore.Rewrite.SMT.Evaluator's SMTDependentAtom, an opaque atom under a
    /// quantifier must be a function of the bound variables it mentions. A constant
    /// would erase that dependence and could make a satisfiable formula unsatisfiable.
    /// Cache its template modulo bound-variable spelling, retaining free variables.
    fn abstract_dependent(&mut self, predicate: &Predicate) -> Option<SExpr> {
        let variables = predicate.free_variables();
        let mut seen = BTreeSet::new();
        let mut dependencies = self
            .bound_variables
            .iter()
            .rev()
            .filter(|(variable, _)| variables.contains(variable) && seen.insert(variable.clone()))
            .cloned()
            .collect::<Vec<_>>();
        dependencies.reverse();
        if dependencies.is_empty() {
            return None;
        }
        // An uninterpreted function of the bound variables retains only congruence.
        self.approximate(Exactness::Approximate);
        let free = variables.difference(&seen).collect::<Vec<_>>();
        let mut substitution = Substitution::new();
        let mut sorts = Vec::new();
        let mut arguments = Vec::new();
        for (index, (variable, name)) in dependencies.into_iter().enumerate() {
            let mut placeholder = format!("#SMT-bound-{index}");
            while free
                .iter()
                .any(|variable| variable.name.as_ref() == placeholder)
            {
                placeholder.push('_');
            }
            substitution.insert(
                variable.clone(),
                Term::variable(variable.with_name(placeholder)),
            );
            sorts.push(variable.sort);
            arguments.push(SExpr::atom(name));
        }
        // Only atomic predicates reach this method, so this substitution crosses no binder.
        let template = substitute_predicates(std::slice::from_ref(predicate), &substitution)
            .pop()
            .unwrap();
        let key = (template, sorts);
        let name = if let Some(name) = self.dependent_mappings.get(&key) {
            name.clone()
        } else {
            let name = self.fresh_name();
            self.dependent_mappings.insert(key, name.clone());
            name
        };
        Some(SExpr::application(name, arguments))
    }

    /// The SMT-LIB sort that stands for `sort` in a query. `Int` and `Bool` denote the K sort's
    /// values; every other sort is declared as an uninterpreted sort, whose models need not have
    /// them, so naming it records `Approximate`. Every sort of a query is named here.
    fn smt_sort(&mut self, sort: &Sort) -> Result<String, TranslationError> {
        let (name, exactness) = sort_denotation(sort)?;
        self.approximate(exactness);
        Ok(name)
    }

    /// The declarations of the constants and functions that stand for abstracted terms and
    /// predicates, each sort named through `smt_sort`.
    fn mapping_declarations(&mut self) -> Result<Vec<String>, TranslationError> {
        let constants = self
            .mappings
            .iter()
            .map(|(term, name)| (term.sort(), name.clone(), collection_size_term(term)))
            .collect::<Vec<_>>();
        let functions = self
            .dependent_mappings
            .iter()
            .map(|((predicate, arguments), name)| {
                let result = match predicate {
                    Predicate::Term(term) => Some(term.sort()),
                    _ => None,
                };
                (result, arguments.clone(), name.clone())
            })
            .collect::<Vec<_>>();
        let mut declarations = Vec::new();
        for (sort, name, collection_size) in constants {
            declarations.push(format!("(declare-const {name} {})", self.smt_sort(&sort)?));
            if collection_size {
                declarations.push(format!("(assert (>= {name} 0))"));
            }
        }
        for (_, name) in &self.predicate_mappings {
            declarations.push(format!("(declare-const {name} Bool)"));
        }
        for (result, arguments, name) in functions {
            let result = match result {
                Some(sort) => self.smt_sort(&sort)?,
                None => "Bool".into(),
            };
            let arguments = arguments
                .iter()
                .map(|sort| self.smt_sort(sort))
                .collect::<Result<Vec<_>, _>>()?;
            declarations.push(format!(
                "(declare-fun {name} ({}) {result})",
                arguments.join(" ")
            ));
        }
        Ok(declarations)
    }
}

/// `Approximate` for a symbol whose SMT operation does not denote it exactly: an `smtlib`
/// symbol is an uninterpreted function, and a partial function is a total SMT operation that
/// has a value where the function has none.
fn symbol_exactness(symbol: &Symbol) -> Exactness {
    let uninterpreted = matches!(symbol.attributes.smt, Some(SmtType::Lib(_)));
    let partial = symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial);
    if uninterpreted || partial {
        Exactness::Approximate
    } else {
        Exactness::Exact
    }
}

/// A query's translation, with its mappings declared, and the parts `SmtPrelude::query`
/// assembles into a script: the mapping declarations, the substitution's equations, the known
/// assertions and the checked conjunction.
type QueryTranslation = (TranslationState, Vec<String>, Vec<SExpr>, Vec<SExpr>, SExpr);

/// Translates a query and declares its mappings: the one translation `SmtPrelude::query` poses
/// and `translation_exactness` reads.
fn translate_query(
    known: &[Predicate],
    substitution: &Substitution,
    checked: &[Predicate],
) -> Result<QueryTranslation, TranslationError> {
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
    let declarations = translation.mapping_declarations()?;
    Ok((translation, declarations, substitution, known, checked))
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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
    SmtLemmaSurplusPredicates {
        rule_id: String,
        predicates: Vec<Predicate>,
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
            .filter(|(name, _)| {
                name.as_ref() != BuiltinSort::Int.kore_name()
                    && name.as_ref() != BuiltinSort::Bool.kore_name()
            })
            .map(|(name, info)| format!("(declare-sort {} {})", quote(name), info.parameters.len()))
            .collect::<Vec<_>>();
        for symbol in definition.symbols.values() {
            let Some(SmtType::Lib(name)) = &symbol.attributes.smt else {
                continue;
            };
            let arguments = symbol
                .argument_sorts
                .iter()
                .map(prelude_smt_sort)
                .collect::<Result<Vec<_>, _>>()?;
            declarations.push(format!(
                "(declare-fun {name} ({}) {})",
                arguments.join(" "),
                prelude_smt_sort(&symbol.result_sort)?
            ));
            if collection_size_hook(symbol.attributes.hook.as_deref())
                && symbol.argument_sorts.len() == 1
                && symbol.result_sort.is_builtin(BuiltinSort::Int)
            {
                declarations.push(format!(
                    "(assert (forall ((KRUST-COLLECTION {})) (>= ({name} KRUST-COLLECTION) 0)))",
                    arguments[0]
                ));
            }
        }
        for rule in smt_lemmas(definition) {
            declarations.push(format!("(assert {})", translate_smt_lemma(rule)?));
        }
        Ok(Self { declarations })
    }

    pub fn from_definition_with_prelude(
        definition: &BackendDefinition,
        prelude: &str,
    ) -> Result<Self, TranslationError> {
        let mut generated = Self::from_definition(definition)?;
        if !prelude.trim().is_empty() {
            generated.declarations.push(prelude.to_owned());
        }
        Ok(generated)
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
        let (mut translation, declarations, substitution, known, checked) =
            translate_query(known, substitution, checked)?;
        let (substitution, known) = if filter_for_checked {
            let interesting = smt_variables(&checked);
            let (substitution, substitution_exactness) = closure_over(&interesting, substitution);
            let (known, known_exactness) = closure_over(&interesting, known);
            translation.approximate(substitution_exactness.and(known_exactness));
            (substitution, known)
        } else {
            (substitution, known)
        };
        let mut base = self.declarations.clone();
        base.extend(declarations);
        base.extend(
            substitution
                .into_iter()
                .chain(known)
                .map(|expression| format!("(assert {expression})")),
        );
        Ok(TranslatedQuery::new(base.join("\n"), checked, translation))
    }
}

/// The exactness of the translation of `predicates`, read from the same translation and
/// declarations `SmtPrelude::query` poses; `Approximate` when they do not translate.
///
/// A `Sat` answer for `predicates` shows a K valuation of them only when this is `Exact`
/// (see [`Exactness`]).
///
/// The partial-function approximation also affects `SmtSolver::check_predicates`: a `Valid`
/// answer holds for the total operation, including on instances where the partial function has
/// no value. It is sound for a predicate only when the definedness of its partial terms is
/// explicit in the predicate. The rewrite and equation condition callers make it explicit before
/// deciding (`definedness::condition_definedness` on every `requires` and `ensures`).
#[must_use]
pub fn translation_exactness(predicates: &[Predicate]) -> Exactness {
    translate_query(predicates, &Substitution::new(), &[])
        .map_or(Exactness::Approximate, |(translation, ..)| {
            translation.exactness()
        })
}

fn collection_size_hook(hook: Option<&str>) -> bool {
    matches!(hook, Some("LIST.size" | "MAP.size" | "SET.size"))
}

fn collection_size_term(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::Application { symbol, .. }
            if collection_size_hook(symbol.attributes.hook.as_deref())
                && term.sort().is_builtin(BuiltinSort::Int)
    )
}

#[cfg(feature = "z3")]
fn smt_variables(expression: &SExpr) -> BTreeSet<String> {
    match expression {
        SExpr::Atom(atom) if atom.starts_with("SMT-") => BTreeSet::from([atom.clone()]),
        SExpr::Atom(_) => BTreeSet::new(),
        SExpr::List(items) => items.iter().flat_map(smt_variables).collect(),
    }
}

/// The expressions that share an SMT constant with `interesting`, transitively. Dropping a
/// conjunct weakens the query, so its `Sat` need not hold for the whole conjunction: the
/// selection is `Exact` only when nothing was dropped.
#[cfg(feature = "z3")]
fn closure_over(
    interesting: &BTreeSet<String>,
    expressions: Vec<SExpr>,
) -> (Vec<SExpr>, Exactness) {
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
            let exactness = if remaining.is_empty() {
                Exactness::Exact
            } else {
                Exactness::Approximate
            };
            return (selected.into_iter().collect(), exactness);
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
    theory_rules(definition.function_theory())
        .chain(theory_rules(definition.simplification_theory()))
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
            SExpr::atom(prelude_smt_sort(&variable.sort)?),
        ]));
    }
    if !translation.mappings.is_empty() {
        return Err(TranslationError::SmtLemmaSurplusMappings {
            rule_id: rule.attributes.unique_id.clone(),
            terms: translation.mappings.into_keys().collect(),
        });
    }
    if !translation.predicate_mappings.is_empty() || !translation.dependent_mappings.is_empty() {
        return Err(TranslationError::SmtLemmaSurplusPredicates {
            rule_id: rule.attributes.unique_id.clone(),
            predicates: translation
                .predicate_mappings
                .into_iter()
                .map(|(predicate, _)| predicate)
                .chain(
                    translation
                        .dependent_mappings
                        .into_keys()
                        .map(|(predicate, _)| predicate),
                )
                .collect(),
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

/// The SMT-LIB sort that stands for `sort`, and whether it denotes the K sort's values: `Int`
/// and `Bool` do; every other sort is declared as an uninterpreted sort
/// (`SmtPrelude::from_definition`).
fn sort_denotation(sort: &Sort) -> Result<(String, Exactness), TranslationError> {
    match sort {
        Sort::Variable(_) => Err(TranslationError::ParametricSort(sort.clone())),
        _ if sort.is_builtin(BuiltinSort::Int) => Ok(("Int".into(), Exactness::Exact)),
        _ if sort.is_builtin(BuiltinSort::Bool) => Ok(("Bool".into(), Exactness::Exact)),
        Sort::Application { name, arguments } if arguments.is_empty() => {
            Ok((quote(name), Exactness::Approximate))
        }
        Sort::Application { name, arguments } => Ok((
            format!(
                "({} {})",
                quote(name),
                arguments
                    .iter()
                    .map(prelude_smt_sort)
                    .collect::<Result<Vec<_>, _>>()?
                    .join(" ")
            ),
            Exactness::Approximate,
        )),
    }
}

/// The SMT-LIB sort that stands for `sort` in the prelude, which declares the trusted
/// signatures of `smtlib` symbols and the SMT lemmas, not a query, and so records nothing.
fn prelude_smt_sort(sort: &Sort) -> Result<String, TranslationError> {
    sort_denotation(sort).map(|(name, _)| name)
}

fn quote(name: &str) -> String {
    format!("|{name}|")
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Satisfiability {
    /// The translation has a model. It is a K valuation of the predicates only when the
    /// translation is exact (`translation_exactness`).
    Sat,
    /// The predicates have no K valuation.
    Unsat,
    Unknown(String),
}

/// The answer of `SmtSolver::check_predicates(known, substitution, checked)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Validity {
    /// `known ∧ ¬checked` is unsatisfiable: every instance of `known` satisfies `checked`.
    Valid,
    /// `known ∧ checked` is unsatisfiable: no instance of `known` satisfies `checked`.
    /// `known` is not shown empty; it may be empty when its own satisfiability came from an
    /// approximate translation. This is a refutation, not a counterexample.
    Refuted,
    /// `known` is unsatisfiable.
    InconsistentGroundTruth,
    /// Neither `checked` nor its negation is refuted under `known`: both have SMT models.
    /// With an approximate translation neither model need be a K valuation, so this answer
    /// shows no instance on either side.
    Contingent,
    Unknown(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModelResult {
    Sat(Substitution),
    Unsat,
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
    MissingModel,
    MissingModelValue(Variable),
    InvalidModelValue { variable: Variable, value: String },
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

    /// A `Sat` substitution must satisfy `predicates` and `substitution` in K.
    /// An approximate SMT model is reported as `Unknown` instead.
    fn get_model(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Result<ModelResult, SmtError> {
        Err(SmtError::Unavailable)
    }

    /// The prelude-failure signal an operation using this solver installs
    /// (`stop::operation`); `None` for a solver without a prelude that can fail.
    fn prelude_signal(&self) -> Option<&PreludeSignal> {
        None
    }
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
            attributes: {
                let mut attributes = SymbolAttributes::constructor().with_declared_function(true);
                attributes.symbol_type = SymbolType::Function(FunctionType::Total);
                attributes.smt = smt;
                attributes
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
    fn translates_quantified_predicates_with_typed_binders() {
        let variable = Variable::new("X", Sort::simple("SortInt"));
        let predicate = Predicate::Exists(
            variable.clone(),
            Box::new(Predicate::Equals(Term::variable(variable), integer("1"))),
        );

        assert_eq!(
            TranslationState::new()
                .translate_predicate(&predicate)
                .unwrap()
                .to_string(),
            "(exists ((SMT-1 Int)) (= SMT-1 1))"
        );
    }

    #[test]
    fn exactness_rejects_uninterpreted_smtlib_symbols_at_any_predicate_depth() {
        let int = Sort::simple("SortInt");
        let variable = Variable::new("X", int.clone());
        let application = |smt| {
            Term::application(
                symbol("bitwise", smt, vec![int.clone(), int.clone()], int.clone()),
                Vec::new(),
                vec![Term::variable(variable.clone()), integer("1")],
            )
        };
        let equality = |term| Predicate::Equals(term, integer("2"));
        let uninterpreted = application(Some(SmtType::Lib("andInt".into())));
        let hooked = application(Some(SmtType::Hook(SExpr::atom("+"))));

        assert_eq!(
            translation_exactness(&[equality(uninterpreted.clone())]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[Predicate::Not(Box::new(Predicate::Exists(
                variable,
                Box::new(Predicate::Or(vec![equality(uninterpreted)])),
            )))]),
            Exactness::Approximate
        );
        assert_eq!(translation_exactness(&[equality(hooked)]), Exactness::Exact);
    }

    #[test]
    fn exactness_rejects_quantifiers_over_uninterpreted_sorts() {
        let nat = Variable::new("N", Sort::simple("SortNat"));
        let int = Variable::new("I", Sort::simple("SortInt"));
        let body = |variable: &Variable| {
            Predicate::Equals(
                Term::variable(variable.clone()),
                Term::variable(variable.clone()),
            )
        };

        assert_eq!(
            translation_exactness(&[Predicate::Forall(nat.clone(), Box::new(body(&nat)))]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[Predicate::Exists(nat, Box::new(Predicate::True))]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[Predicate::Exists(
                int.clone(),
                Box::new(Predicate::Equals(Term::variable(int), integer("1"))),
            )]),
            Exactness::Exact
        );
    }

    #[test]
    fn exactness_rejects_free_variables_of_uninterpreted_sorts() {
        let nat = Term::variable(Variable::new("N", Sort::simple("SortNat")));
        let int = Term::variable(Variable::new("I", Sort::simple("SortInt")));
        let boolean = Term::variable(Variable::new("B", Sort::simple("SortBool")));

        assert_eq!(
            translation_exactness(&[Predicate::Equals(nat.clone(), nat)]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[
                Predicate::Equals(int, integer("1")),
                Predicate::Term(boolean),
            ]),
            Exactness::Exact
        );
    }

    #[test]
    fn exactness_rejects_abstracted_terms_predicates_and_partial_operations() {
        let int = Sort::simple("SortInt");
        let variable = Term::variable(Variable::new("X", int.clone()));
        let equality = |term| Predicate::Equals(term, integer("2"));
        let opaque = Term::application(
            symbol("opaque", None, vec![int.clone()], int.clone()),
            Vec::new(),
            vec![variable.clone()],
        );
        let mut partial_symbol = symbol(
            "division",
            Some(SmtType::Hook(SExpr::atom("div"))),
            vec![int.clone(), int.clone()],
            int.clone(),
        );
        Arc::make_mut(&mut partial_symbol).attributes.symbol_type =
            SymbolType::Function(FunctionType::Partial);
        let partial = Term::application(
            partial_symbol,
            Vec::new(),
            vec![variable.clone(), integer("1")],
        );

        assert_eq!(
            translation_exactness(&[equality(opaque)]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[equality(partial)]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[Predicate::Ceil(variable.clone())]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[equality(variable)]),
            Exactness::Exact
        );
    }

    #[test]
    fn abstracts_symbolic_definedness_as_a_stable_boolean() {
        let variable = Term::variable(Variable::new("X", Sort::simple("SortInt")));
        let predicate = Predicate::Ceil(variable);
        let mut translation = TranslationState::new();

        assert_eq!(
            translation
                .translate_predicate(&predicate)
                .unwrap()
                .to_string(),
            "SMT-1"
        );
        assert_eq!(
            translation
                .translate_predicate(&predicate)
                .unwrap()
                .to_string(),
            "SMT-1"
        );
        assert_eq!(translation.predicate_mappings.len(), 1);
    }

    #[test]
    fn abstracts_symbolic_membership_as_a_stable_boolean() {
        let element = Term::variable(Variable::new("X", Sort::simple("SortElement")));
        let collection = Term::variable(Variable::new("S", Sort::simple("SortSet")));
        let membership = Predicate::In(element, collection);
        let negated = Predicate::Not(Box::new(membership.clone()));
        let mut translation = TranslationState::new();

        assert_eq!(
            translation
                .translate_predicate(&membership)
                .unwrap()
                .to_string(),
            "SMT-1"
        );
        assert_eq!(
            translation
                .translate_predicate(&negated)
                .unwrap()
                .to_string(),
            "(not SMT-1)"
        );
        assert_eq!(translation.predicate_mappings.len(), 1);
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
