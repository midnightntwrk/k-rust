//! Portable SMT-LIB translation shared by native Z3 and solver-free builds: one pass per query
//! script, and one reachability search over its conjuncts' constants for the conjuncts a validity
//! check sends (`closure_over`); a responsibility, not an algorithm; no counter of its own.

#![deny(clippy::wildcard_enum_match_arm)]

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use k_rust_kore::names::BuiltinSort;

use crate::{
    definition::BackendDefinition,
    model::ModelQuery,
    rewrite::substitute_predicates,
    rule::{Predicate, RewriteRule, RuleRhs, Theory},
    stop::{PreludeSignal, Stoppable},
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

/// Offsets are zero-based byte offsets into the parsed text.
impl fmt::Display for SExprError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEnd => {
                formatter.write_str("the text ends where an expression is expected")
            }
            Self::UnexpectedClose(offset) => {
                write!(formatter, "the ')' at byte offset {offset} closes no list")
            }
            Self::UnterminatedList(offset) => write!(
                formatter,
                "the list opened at byte offset {offset} is not closed"
            ),
            Self::EmptyAtom(offset) => write!(
                formatter,
                "the character at byte offset {offset} cannot begin an expression"
            ),
            Self::TrailingInput(offset) => write!(
                formatter,
                "text follows the expression at byte offset {offset}"
            ),
        }
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
/// uninterpreted function that retains only congruence. Abstraction alone therefore lets every K
/// valuation that satisfies the predicates induce a model of the translation. A model is a K
/// valuation of the predicates only when the translation is `Exact`.
///
/// A partial function translated as a total SMT operation is not an over-approximation: an atom
/// over an undefined term denotes `\bottom` in K and some value in SMT. It is `Approximate` for
/// the purpose of reading a model, and `Unsat` refutes the predicates only when they are
/// definedness-faithful, which their definedness-explicit form ensures: each atom over a partial
/// term is a conjunct of a conjunction enclosing it that also holds that term's definedness, or
/// a top-level atom that shows its term defined (docs/compatibility.md, "Solver decisions over
/// partial operations").
/// SMT hook translations, SMT lemma axioms and the user prelude are trusted, except that a power
/// is read as itself only where an integer is its value (`guard_powers`).
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
            // A term-level `\and` denotes the intersection of its operands' values, `\bottom` where
            // they differ, not their Boolean conjunction: `true /\ false` is `\bottom`, not
            // `false`. A Boolean one is therefore an unrelated constant, as any term without a
            // translation. That over-approximates only where the intersection is defined: under
            // a negation, `\not(c = true) /\ \not(c = false)` has no model while it holds in K
            // where the operands differ. A request with such an atom is refused (`Admitted`), and
            // K source never writes one in a condition, so only a condition written in KORE can
            // reach this unfaithful reading.
            TermKind::And(left, right)
                if left.sort().is_builtin(BuiltinSort::Bool)
                    && right.sort().is_builtin(BuiltinSort::Bool) =>
            {
                Ok(self.abstract_term(term, Exactness::Approximate))
            }
            TermKind::And(..) => Err(TranslationError::NonBooleanAnd(term.clone())),
            TermKind::Application {
                symbol, arguments, ..
            } => match &symbol.attributes.smt {
                None => Ok(self.abstract_term(term, Exactness::Approximate)),
                Some(SmtType::Lib(name)) => {
                    self.translate_application(name, arguments, Exactness::Approximate)
                }
                Some(SmtType::Hook(SExpr::Atom(name))) if name != POWER => {
                    self.translate_application(name, arguments, symbol_exactness(symbol))
                }
                Some(SmtType::Hook(expression)) => {
                    self.approximate(symbol_exactness(symbol));
                    let template = match expression {
                        SExpr::Atom(name) => SExpr::application(
                            name.clone(),
                            (1..=arguments.len())
                                .map(|index| SExpr::atom(format!("#{index}")))
                                .collect(),
                        ),
                        SExpr::List(_) => expression.clone(),
                    };
                    let arguments = arguments
                        .iter()
                        .map(|argument| self.translate_term(argument))
                        .collect::<Result<Vec<_>, _>>()?;
                    let (template, guarded) = guard_powers(&template, &arguments);
                    if guarded {
                        // The power's value outside the integers is an uninterpreted function.
                        self.approximate(Exactness::Approximate);
                    }
                    fill_placeholders(&template, arguments)
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
            Predicate::Implies(left, right) if !matches!(**right, Predicate::Implies(..)) => {
                Ok(SExpr::application(
                    "=>",
                    vec![
                        self.translate_predicate(left)?,
                        self.translate_predicate(right)?,
                    ],
                ))
            }
            Predicate::Implies(..) => self.translate_implication_spine(predicate),
            Predicate::Iff(left, right) => Ok(SExpr::application(
                "=",
                vec![
                    self.translate_predicate(left)?,
                    self.translate_predicate(right)?,
                ],
            )),
            Predicate::Ceil(term) | Predicate::Defined(term)
                if term.attributes().constructor_like =>
            {
                Ok(SExpr::atom("true"))
            }
            predicate @ Predicate::Ceil(_) => Ok(self.abstract_predicate(predicate)),
            // A deferred atom is the opaque atom of `\ceil(t)`, never a translation of `t`, under
            // which an uninterpreted application would read as defined.
            Predicate::Defined(term) => Ok(self.abstract_predicate(&Predicate::Ceil(term.clone()))),
            // An absence is opaque to the solver: one Boolean per key and rest.
            predicate @ (Predicate::Floor(_) | Predicate::In(..) | Predicate::Absent(_)) => {
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

    /// Translates a right-nested implication spine `l1 => (l2 => ... => (ln => r))`, n >= 2, as
    /// the one disjunction `(or (not l1) ... (not ln) r)`.
    ///
    /// `a => b` is `¬a ∨ b`, so the spine is `¬l1 ∨ (¬l2 ∨ (... ∨ (¬ln ∨ r)))`, and `∨` is
    /// associative: `a ⇒ (b ⇒ c) ≡ ¬a ∨ ¬b ∨ c`. The flat formula is the same Boolean function
    /// of the same atoms, so an assertion containing it has exactly the models it had. The
    /// operands are translated in the order the nested translation visits them (l1, ..., ln,
    /// then r), so the abstraction constants get the same names and declarations, the first
    /// untranslatable operand is the same, and so is the exactness of the query.
    ///
    /// A single implication keeps its `=>` text. The nested text of a longer spine made the
    /// solver's construction of the assertion quadratic in n; the flat text is linear, and the
    /// loop below walks the spine without native recursion.
    fn translate_implication_spine(
        &mut self,
        spine: &Predicate,
    ) -> Result<SExpr, TranslationError> {
        let mut disjuncts = Vec::new();
        let mut rest = spine;
        while let Predicate::Implies(premise, conclusion) = rest {
            disjuncts.push(SExpr::application(
                "not",
                vec![self.translate_predicate(premise)?],
            ));
            rest = conclusion;
        }
        disjuncts.push(self.translate_predicate(rest)?);
        Ok(SExpr::application("or", disjuncts))
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

    /// An opaque atom under a quantifier must be a function of the bound variables it
    /// mentions, since its value can differ for each value they take. A constant
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
        #[expect(
            clippy::disallowed_methods,
            reason = "a renaming to placeholder variables; a variable denotes an element"
        )]
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
                #[expect(
                    clippy::wildcard_enum_match_arm,
                    reason = "Predicate is syntax; only the listed variants are special here"
                )]
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

/// The SMT-LIB power operation as an `smt-hook` names it.
const POWER: &str = "^";

/// The uninterpreted function that stands for a power where no integer is its value
/// (`guard_powers`), declared in the prelude of a definition whose `smt-hook`s use [`POWER`].
const POWER_OUTSIDE_THE_INTEGERS: &str = "|KRUST-POWER-OUTSIDE-THE-INTEGERS|";

/// `expression` with every binary power `(^ a b)` read as
/// `(ite (or (>= b 0) (= a 1) (= a (- 1))) (^ a b) (KRUST-POWER-OUTSIDE-THE-INTEGERS a b))`, and
/// whether it had one.
///
/// An `smt-hook` is trusted to state its hook's operation wherever the hook has a value; where
/// the hook has none, the solver must not decide anything that depends on a value. SMT-LIB's own
/// partial operations leave such a value unconstrained (`div` and `mod` by zero), so a validity
/// answer holds for whatever it is. Z3's `^` on two integers does not: it is the real power,
/// which has a value (`(^ 2 (- 1))` is `1/2`, and `mod` reads its integer part, 0) exactly where
/// no integer is the power and `^Int` is undefined. The guard is the set where an integer power
/// exists, a nonnegative exponent or a base of magnitude 1, and there `^` is that integer; outside
/// it the power is an uninterpreted function of its operands, as a division by zero is. The
/// function is Real-valued, as Z3's `^` is, so both branches and every context have its sort.
/// The guard names each operand several times; `fill_placeholders` states each argument once.
///
/// A power whose exponent is a numeral, written in the template or as the argument a
/// placeholder names (`arguments` are the translated arguments), has an integer value for every
/// base. A positive numeral leaves it as it is: its guard is constantly true, and Z3 reads it as
/// the product of that many bases, 0 included. The numeral 0 makes it the constant `1.0` (of the
/// sort of Z3's `^`): `X ^Int 0` is 1 for every integer `X`, `0 ^Int 0` included, while Z3 leaves
/// `(^ 0 0)` uninterpreted, so the power itself would not be an exact reading there.
fn guard_powers(expression: &SExpr, arguments: &[SExpr]) -> (SExpr, bool) {
    match expression {
        SExpr::Atom(_) => (expression.clone(), false),
        SExpr::List(items) => {
            let mut guarded = false;
            let items = items
                .iter()
                .map(|item| {
                    let (item, inner) = guard_powers(item, arguments);
                    guarded |= inner;
                    item
                })
                .collect::<Vec<_>>();
            match items.as_slice() {
                [SExpr::Atom(operator), _, exponent]
                    if operator == POWER
                        && numeral(exponent, arguments)
                            .is_some_and(|value| value.bytes().all(|digit| digit == b'0')) =>
                {
                    // The base is dropped, and with it any guard it held.
                    (SExpr::atom("1.0"), false)
                }
                [SExpr::Atom(operator), base, exponent]
                    if operator == POWER && numeral(exponent, arguments).is_none() =>
                {
                    let integer = |value: &str| SExpr::atom(value);
                    let condition = SExpr::application(
                        "or",
                        vec![
                            SExpr::application(">=", vec![exponent.clone(), integer("0")]),
                            SExpr::application("=", vec![base.clone(), integer("1")]),
                            SExpr::application(
                                "=",
                                vec![base.clone(), SExpr::application("-", vec![integer("1")])],
                            ),
                        ],
                    );
                    let outside = SExpr::application(
                        POWER_OUTSIDE_THE_INTEGERS,
                        vec![base.clone(), exponent.clone()],
                    );
                    (
                        SExpr::application(
                            "ite",
                            vec![condition, SExpr::List(items.clone()), outside],
                        ),
                        true,
                    )
                }
                _ => (SExpr::List(items), guarded),
            }
        }
    }
}

/// The template operand `operand` when it is a numeral, a nonnegative integer literal, by itself
/// or as the argument it names.
fn numeral<'a>(operand: &'a SExpr, arguments: &'a [SExpr]) -> Option<&'a str> {
    let SExpr::Atom(atom) = operand else {
        return None;
    };
    let value = match placeholder(atom) {
        Some(index) => match index.checked_sub(1).and_then(|index| arguments.get(index)) {
            Some(SExpr::Atom(argument)) => argument,
            Some(SExpr::List(_)) | None => return None,
        },
        None => atom,
    };
    (!value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit())).then_some(value.as_str())
}

/// Whether `expression` applies [`POWER`], so that its translation uses
/// [`POWER_OUTSIDE_THE_INTEGERS`].
fn applies_power(expression: &SExpr) -> bool {
    match expression {
        SExpr::Atom(name) => name == POWER,
        SExpr::List(items) => items.iter().any(applies_power),
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
            .sorts()
            .iter()
            .filter(|(name, _)| {
                name.as_ref() != BuiltinSort::Int.kore_name()
                    && name.as_ref() != BuiltinSort::Bool.kore_name()
            })
            .map(|(name, info)| format!("(declare-sort {} {})", quote(name), info.parameters.len()))
            .collect::<Vec<_>>();
        if definition.symbols().values().any(|symbol| {
            matches!(&symbol.attributes.smt, Some(SmtType::Hook(expression)) if applies_power(expression))
        }) {
            declarations.push(format!(
                "(declare-fun {POWER_OUTSIDE_THE_INTEGERS} (Int Int) Real)"
            ));
        }
        for symbol in definition.symbols().values() {
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
/// The partial-function approximation also affects `SmtSolver::is_sat` and
/// `SmtSolver::check_predicates`: an `Unsat`, `Valid` or `Refuted` answer holds for the total
/// operation, including on instances where the partial function has no value. It is sound for a
/// predicate only when the predicate is definedness-faithful (see [`Exactness`]). The rewrite and
/// equation condition callers make it so before deciding (`definedness::condition_definedness`
/// on every `requires` and `ensures`), and so do the admission of a request's predicates
/// (`definition::Admitted`, `definedness::request_definedness`) and the internalization of a
/// claim's constraints (`claim::with_explicit_definedness`); docs/compatibility.md, "Solver
/// decisions over partial operations", lists every source and the remaining gaps: an `\equals` of
/// two possibly undefined terms in a rule or equation condition, and an `\equals` in a
/// definition's axioms that reads a term as a predicate.
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

/// The SMT constants `expression` mentions, in one walk of it.
#[cfg(feature = "z3")]
fn smt_variables(expression: &SExpr) -> BTreeSet<&str> {
    fn collect<'a>(expression: &'a SExpr, names: &mut BTreeSet<&'a str>) {
        match expression {
            SExpr::Atom(atom) if atom.starts_with("SMT-") => {
                names.insert(atom);
            }
            SExpr::Atom(_) => {}
            SExpr::List(items) => {
                for item in items {
                    collect(item, names);
                }
            }
        }
    }
    let mut names = BTreeSet::new();
    collect(expression, &mut names);
    names
}

/// The expressions that share an SMT constant with `interesting`, transitively, each once and in
/// `SExpr` order. Dropping a conjunct weakens the query, so its `Sat` need not hold for the whole
/// conjunction: the selection is `Exact` only when nothing was dropped.
///
/// The selection is the set of expressions reachable from `interesting` in the graph that links
/// each distinct expression to the constants it mentions. Each expression's constants are read
/// once and indexed by constant, and a breadth-first search follows each constant once, however
/// long the chains of shared constants are.
#[cfg(feature = "z3")]
fn closure_over(interesting: &BTreeSet<&str>, expressions: Vec<SExpr>) -> (Vec<SExpr>, Exactness) {
    let distinct = expressions
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let selected = {
        let names = distinct.iter().map(smt_variables).collect::<Vec<_>>();
        let mut mentioning = BTreeMap::<&str, Vec<usize>>::new();
        for (index, expression_names) in names.iter().enumerate() {
            for &name in expression_names {
                mentioning.entry(name).or_default().push(index);
            }
        }
        let mut selected = vec![false; distinct.len()];
        let mut followed = BTreeSet::new();
        let mut pending = interesting
            .iter()
            .copied()
            .collect::<std::collections::VecDeque<&str>>();
        while let Some(name) = pending.pop_front() {
            if !followed.insert(name) {
                continue;
            }
            for &index in mentioning.get(name).into_iter().flatten() {
                if !selected[index] {
                    selected[index] = true;
                    pending.extend(names[index].iter().copied());
                }
            }
        }
        selected
    };
    let exactness = if selected.iter().all(|&chosen| chosen) {
        Exactness::Exact
    } else {
        Exactness::Approximate
    };
    let chosen = distinct
        .into_iter()
        .zip(selected)
        .filter_map(|(expression, chosen)| chosen.then_some(expression))
        .collect();
    (chosen, exactness)
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

#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Satisfiability {
    /// The translation has a model. It is a K valuation of the predicates only when the
    /// translation is exact (`translation_exactness`).
    Sat,
    /// No K valuation satisfies the predicates, when they are definedness-faithful
    /// (docs/compatibility.md, "Solver decisions over partial operations"); otherwise only the
    /// translation has no model. Every predicate the backend poses is, except over a definition
    /// whose rule or equation condition equates two possibly undefined terms or whose axioms hold
    /// an `\equals` that reads a term as a predicate or a condition over a Boolean term-level
    /// `\and` (that section's gaps).
    Unsat,
    /// The solver ran within its own per-query bounds (its timeout, resource limit and retries)
    /// and did not decide the query; the payload is its reason. Never a stop: a query that stopped (a
    /// cancelled request, a passed step deadline, a failed prelude) returns the stop on the outer
    /// layer of [`SmtSolver::is_sat`] instead.
    Unknown(String),
}

/// The answer of `SmtSolver::check_predicates(known, substitution, checked)`.
#[must_use]
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
    /// The solver ran within its own per-query bounds and decided neither side; the payload is
    /// its reason. Never a stop, which [`SmtSolver::check_predicates`] returns on its outer layer.
    Unknown(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModelResult {
    Sat(Substitution),
    Unsat,
    /// No model was obtained: the solver ran within its own per-query bounds and did not decide
    /// the query, or its model was of an approximate translation and so no K valuation (the
    /// payload says which). Never a stop, which [`SmtSolver::get_model`] returns on its outer
    /// layer.
    Unknown(String),
}

/// A failure of one solver query: a fact about the query and the backend's capabilities. A stop
/// is not a failure (design CBC-04): a failed solver prelude, in particular, is
/// `stop::StopCause::SolverPrelude`, because it belongs to every operation using the solver.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum SmtError {
    Translation(TranslationError),
    Unavailable,
    /// The solver ran within its own per-query bounds and returned unknown where the query's
    /// consumer needed an answer. Never a stop.
    Unknown(String),
    InconsistentGroundTruth,
    MissingModel,
    MissingModelValue(Variable),
    InvalidModelValue {
        variable: Variable,
        value: String,
    },
}

impl From<TranslationError> for SmtError {
    fn from(error: TranslationError) -> Self {
        Self::Translation(error)
    }
}

/// A decision procedure for predicates under the definition's `smt-lemma` axioms and prelude.
///
/// Each query answers in two layers: the outer `Err` is a [`Stop`](crate::stop::Stop), the
/// query ended before answering because a resource of its owner ran out or failed (the request
/// was cancelled, the step deadline passed, the solver's prelude failed); the inner `Result` is
/// the answer or the query's own failure. A consumer that falls back on a failure writes its
/// fallback against the inner layer, after `?`, so the fallback cannot see a stop. The
/// single-layer shape no longer compiles:
///
/// ```compile_fail,E0308
/// use k_rust_backend::{
///     smt::{NoSolver, Satisfiability, SmtSolver},
///     stop::Stoppable,
///     substitution::Substitution,
/// };
///
/// fn refuted() -> Stoppable<bool> {
///     Ok(matches!(NoSolver.is_sat(&[], &Substitution::new()), Ok(Satisfiability::Unsat)))
/// }
/// ```
///
/// The same decision with the stop propagated first:
///
/// ```
/// use k_rust_backend::{
///     smt::{NoSolver, Satisfiability, SmtSolver},
///     stop::{Stop, Stoppable},
///     substitution::Substitution,
/// };
///
/// fn refuted() -> Stoppable<bool> {
///     Ok(matches!(NoSolver.is_sat(&[], &Substitution::new())?, Ok(Satisfiability::Unsat)))
/// }
/// assert_eq!(refuted().map_err(Stop::into_cause), Ok(false));
/// ```
///
/// An implementation that does work a stop should interrupt polls `stop::check()?` before it.
pub trait SmtSolver {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>>;

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>>;

    /// A model of `query`'s residual: a `Sat` substitution must satisfy its predicates and its
    /// substitution in K. An approximate SMT model is reported as `Unknown` instead.
    ///
    /// Only [`model_of`](crate::model::model_of) builds a [`ModelQuery`], after the definition
    /// has decided what it can of the predicate, so this is never asked about a predicate whose
    /// answer depends on equations or constructor freeness the solver does not see.
    fn get_model(&self, _query: &ModelQuery<'_>) -> Stoppable<Result<ModelResult, SmtError>> {
        Ok(Err(SmtError::Unavailable))
    }

    /// The prelude-failure signal an operation using this solver installs
    /// (`stop::operation`); `None` for a solver without a prelude that can fail.
    fn prelude_signal(&self) -> Option<&PreludeSignal> {
        None
    }
}

/// The solver of a build without one: every query that needs a solver fails with `Unavailable`,
/// immediately, so there is no work for a stop to interrupt.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoSolver;

impl SmtSolver for NoSolver {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        Ok(Err(SmtError::Unavailable))
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        Ok(if checked.is_empty() {
            Ok(Validity::Valid)
        } else {
            Err(SmtError::Unavailable)
        })
    }
}

/// The argument index that a template atom `#i` names, when it is a placeholder.
fn placeholder(atom: &str) -> Option<usize> {
    atom.strip_prefix('#')
        .and_then(|index| index.parse::<usize>().ok())
}

/// The prefix of the name that states an argument named more than once in an `smt-hook`
/// template (`fill_placeholders`).
const HOOK_ARGUMENT: &str = "KRUST-HOOK-ARGUMENT-";

/// The `smt-hook` template `expression` applied to the translations of its `arguments`.
///
/// A template is a function of its arguments, and one that names an argument several times
/// names one value several times (`/Int` names each argument five times, the power guard of
/// `guard_powers` its base four times). Written as a copy at every occurrence, a nesting of such
/// hooks would be exponentially long in its depth; so an argument named more than once whose
/// translation is not an atom is stated once, in a `let` around the template, and named by its
/// binding. `let` denotes substitution, so the formula is the one the copies write. No binding
/// captures a name: an argument's translation is closed (it binds every `let` name it uses), and
/// the template names only its own bindings.
///
/// The translations are taken by value and each is moved to the one place that states it, its
/// single occurrence or its binding; only an atom named several times is copied. A nesting of
/// hooks then builds each level from its own template and its arguments' translations, and
/// copies none of the levels below it.
fn fill_placeholders(expression: &SExpr, arguments: Vec<SExpr>) -> Result<SExpr, TranslationError> {
    /// How the template states one argument.
    enum Slot {
        /// The translation itself, with the occurrences that still name it: an atom, or a list
        /// named at most once. The last occurrence takes it.
        Stated {
            value: Option<SExpr>,
            remaining: usize,
        },
        /// A list named more than once: the name of its `let` binding.
        Bound(SExpr),
    }
    fn count(expression: &SExpr, uses: &mut [usize]) {
        match expression {
            SExpr::Atom(atom) => {
                if let Some(slot) = placeholder(atom)
                    .and_then(|index| index.checked_sub(1))
                    .and_then(|index| uses.get_mut(index))
                {
                    *slot += 1;
                }
            }
            SExpr::List(items) => items.iter().for_each(|item| count(item, uses)),
        }
    }
    fn substitute(expression: &SExpr, slots: &mut [Slot]) -> Result<SExpr, TranslationError> {
        match expression {
            SExpr::Atom(atom) => {
                let Some(index) = placeholder(atom) else {
                    return Ok(expression.clone());
                };
                if index == 0 || index > slots.len() {
                    return Err(TranslationError::PlaceholderOutOfBounds {
                        placeholder: index,
                        arguments: slots.len(),
                    });
                }
                Ok(match &mut slots[index - 1] {
                    Slot::Bound(name) => name.clone(),
                    Slot::Stated { value, remaining } => {
                        *remaining -= 1;
                        if *remaining == 0 {
                            value.take()
                        } else {
                            value.clone()
                        }
                        .expect("an argument is taken by its last occurrence only")
                    }
                })
            }
            SExpr::List(items) => Ok(SExpr::List(
                items
                    .iter()
                    .map(|item| substitute(item, slots))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
        }
    }

    let mut uses = vec![0; arguments.len()];
    count(expression, &mut uses);
    let mut bindings = Vec::new();
    let mut slots = arguments
        .into_iter()
        .zip(uses)
        .enumerate()
        .map(|(index, (argument, uses))| {
            if uses > 1 && matches!(argument, SExpr::List(_)) {
                let name = SExpr::atom(format!("{HOOK_ARGUMENT}{}", index + 1));
                bindings.push(SExpr::List(vec![name.clone(), argument]));
                Slot::Bound(name)
            } else {
                Slot::Stated {
                    value: Some(argument),
                    remaining: uses,
                }
            }
        })
        .collect::<Vec<_>>();
    let body = substitute(expression, &mut slots)?;
    Ok(if bindings.is_empty() {
        body
    } else {
        SExpr::application("let", vec![SExpr::List(bindings), body])
    })
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
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
        Term::raw_domain_value(Sort::simple("SortInt"), value)
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

    /// A malformed `smt-hook` is reported by where its text goes wrong, in words.
    #[test]
    fn s_expression_errors_state_where_the_text_goes_wrong() {
        let message = |source: &str| SExpr::parse(source).unwrap_err().to_string();
        assert_eq!(
            message("  "),
            "the text ends where an expression is expected"
        );
        assert_eq!(message(")"), "the ')' at byte offset 0 closes no list");
        assert_eq!(
            message("(+ #1"),
            "the list opened at byte offset 0 is not closed"
        );
        assert_eq!(
            message("(+ ;)"),
            "the character at byte offset 3 cannot begin an expression"
        );
        assert_eq!(
            message("(+ #1 #2) trailing"),
            "text follows the expression at byte offset 10"
        );
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

    /// Every power of an `smt-hook`, written as the hook's operation or inside its expression, is
    /// read as itself only where an integer is its value, and as an uninterpreted function
    /// elsewhere; the uninterpreted part makes the translation approximate even for a total
    /// symbol. A power whose exponent is a numeral has an integer value, and is read as itself.
    #[test]
    fn reads_a_power_as_itself_only_where_an_integer_is_its_value() {
        let int = Sort::simple("SortInt");
        let power = symbol(
            "power",
            Some(SmtType::Hook(SExpr::atom("^"))),
            vec![int.clone(), int.clone()],
            int.clone(),
        );
        let power_modulo = symbol(
            "powerModulo",
            Some(SmtType::Hook(SExpr::parse("(mod (^ #1 #2) #3)").unwrap())),
            vec![int.clone(), int.clone(), int.clone()],
            int.clone(),
        );
        let exponent = Term::variable(Variable::new("B", int.clone()));
        let guarded = |base: &str, exponent: &str| {
            format!(
                "(ite (or (>= {exponent} 0) (= {base} 1) (= {base} (- 1))) (^ {base} {exponent}) \
                 (|KRUST-POWER-OUTSIDE-THE-INTEGERS| {base} {exponent}))"
            )
        };

        let mut translation = TranslationState::new();
        let translated = translation
            .translate_term(&Term::application(
                power.clone(),
                Vec::new(),
                vec![integer("2"), exponent.clone()],
            ))
            .unwrap();
        assert_eq!(translated.to_string(), guarded("2", "SMT-1"));
        assert_eq!(translation.exactness(), Exactness::Approximate);

        let mut translation = TranslationState::new();
        let translated = translation
            .translate_term(&Term::application(
                power_modulo,
                Vec::new(),
                vec![integer("3"), exponent, integer("7")],
            ))
            .unwrap();
        assert_eq!(
            translated.to_string(),
            format!("(mod {} 7)", guarded("3", "SMT-1"))
        );

        // A positive numeral exponent, as the argument or in the template, leaves the power as it
        // is: the guard holds, and Z3 reads it as a product. The exponent 0 is the constant 1, of
        // the sort of Z3's power, for every base: Z3 leaves `(^ 0 0)` uninterpreted, and K's
        // `0 ^Int 0` is 1. A negative literal is not a numeral.
        let x = Term::variable(Variable::new("X", Sort::simple("SortInt")));
        for (arguments, expected) in [
            (vec![x.clone(), integer("2")], "(^ SMT-1 2)"),
            (vec![x.clone(), integer("0")], "1.0"),
        ] {
            let mut translation = TranslationState::new();
            let translated = translation
                .translate_term(&Term::application(power.clone(), Vec::new(), arguments))
                .unwrap();
            assert_eq!(translated.to_string(), expected);
            assert_eq!(translation.exactness(), Exactness::Exact);
        }
        assert_eq!(
            TranslationState::new()
                .translate_term(&Term::application(
                    power.clone(),
                    Vec::new(),
                    vec![integer("2"), integer("-1")],
                ))
                .unwrap()
                .to_string(),
            guarded("2", "-1")
        );
        let squared_modulo = symbol(
            "squaredModulo",
            Some(SmtType::Hook(SExpr::parse("(mod (^ #1 2) #2)").unwrap())),
            vec![int.clone(), int.clone()],
            int.clone(),
        );
        assert_eq!(
            TranslationState::new()
                .translate_term(&Term::application(
                    squared_modulo,
                    Vec::new(),
                    vec![x.clone(), integer("7")],
                ))
                .unwrap()
                .to_string(),
            "(mod (^ SMT-1 2) 7)"
        );
        let zeroth_modulo = symbol(
            "zerothModulo",
            Some(SmtType::Hook(SExpr::parse("(mod (^ #1 0) #2)").unwrap())),
            vec![int.clone(), int.clone()],
            int,
        );
        assert_eq!(
            TranslationState::new()
                .translate_term(&Term::application(
                    zeroth_modulo,
                    Vec::new(),
                    vec![x, integer("7")],
                ))
                .unwrap()
                .to_string(),
            "(mod 1.0 7)"
        );
        assert!(applies_power(&SExpr::atom("^")));
        assert!(applies_power(&SExpr::parse("(mod (^ #1 #2) #3)").unwrap()));
        assert!(!applies_power(&SExpr::parse("(mod #1 #2)").unwrap()));
    }

    /// An `smt-hook` template that names an argument several times states it once, in a `let`,
    /// so a nesting of such hooks translates to text linear in its depth, not exponential: a
    /// power names its base four times and its exponent three times through its guard, and
    /// `/Int`'s template in `domains.md` names each argument five times. An atom is written in
    /// place.
    #[test]
    fn states_each_hook_argument_once_however_hooks_nest() {
        const DEPTH: usize = 8;
        const LEVEL: usize = 600;
        let int = Sort::simple("SortInt");
        let binary = |name: &str, template: SExpr| {
            symbol(
                name,
                Some(SmtType::Hook(template)),
                vec![int.clone(), int.clone()],
                int.clone(),
            )
        };
        let power = binary("power", SExpr::atom("^"));
        let division = binary(
            "division",
            SExpr::parse(
                "(ite (or (= 0 (mod #1 #2)) (>= #1 0)) (div #1 #2) \
                 (ite (> #2 0) (+ (div #1 #2) 1) (- (div #1 #2) 1)))",
            )
            .unwrap(),
        );
        let plus = binary("plus", SExpr::atom("+"));
        let x = Term::variable(Variable::new("X", int.clone()));
        let y = Term::variable(Variable::new("Y", int.clone()));

        for symbol in [&power, &division] {
            let mut nested = x.clone();
            for _ in 0..DEPTH {
                nested = Term::application(symbol.clone(), Vec::new(), vec![nested, y.clone()]);
            }
            let text = TranslationState::new()
                .translate_term(&nested)
                .unwrap()
                .to_string();
            assert!(
                text.len() <= DEPTH * LEVEL,
                "{} nested {:?}: {} characters",
                DEPTH,
                symbol.name,
                text.len()
            );
        }

        let base = Term::application(plus, Vec::new(), vec![x, integer("1")]);
        let translated = TranslationState::new()
            .translate_term(&Term::application(power, Vec::new(), vec![base, y]))
            .unwrap();
        let name = "KRUST-HOOK-ARGUMENT-1";
        assert_eq!(
            translated.to_string(),
            format!(
                "(let (({name} (+ SMT-1 1))) (ite (or (>= SMT-2 0) (= {name} 1) (= {name} (- 1))) \
                 (^ {name} SMT-2) (|KRUST-POWER-OUTSIDE-THE-INTEGERS| {name} SMT-2)))"
            )
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

    /// A term-level `\and` is the intersection of its operands, `\bottom` where they differ, so a
    /// Boolean one is not their conjunction: `\equals(true /\ false, false)` is false in K, while
    /// `(= (and true false) false)` holds. It translates as an unrelated constant.
    #[test]
    fn a_boolean_term_conjunction_is_not_translated_as_a_conjunction() {
        let boolean = Sort::simple("SortBool");
        let operand = |name: &str| Term::variable(Variable::new(name, boolean.clone()));
        let predicate = Predicate::Equals(
            Term::and(operand("B1"), operand("B2")),
            Term::raw_domain_value(boolean.clone(), "false"),
        );
        let mut state = TranslationState::new();
        let translated = state.translate_predicate(&predicate).unwrap().to_string();
        assert!(!translated.contains("(and"), "{translated}");
        assert_eq!(state.exactness(), Exactness::Approximate);
    }

    #[test]
    fn translates_quantified_predicates_with_typed_binders() {
        let variable = Variable::new("X", Sort::simple("SortInt"));
        let predicate = Predicate::Exists(
            variable.clone(),
            Arc::new(Predicate::Equals(Term::variable(variable), integer("1"))),
        );

        assert_eq!(
            TranslationState::new()
                .translate_predicate(&predicate)
                .unwrap()
                .to_string(),
            "(exists ((SMT-1 Int)) (= SMT-1 1))"
        );
    }

    /// A right-nested implication spine is one disjunction of the negated premises and the
    /// conclusion, its operands named in the order the nested form names them; a single
    /// implication, and an implication in a premise, keep their `=>`.
    #[test]
    fn translates_an_implication_spine_as_one_flat_disjunction() {
        let int = Sort::simple("SortInt");
        let atom = |name: &str| {
            Predicate::Equals(
                Term::variable(Variable::new(name, int.clone())),
                integer("0"),
            )
        };
        let implies =
            |left: Predicate, right: Predicate| Predicate::Implies(Arc::new(left), Arc::new(right));
        let translate = |predicate: &Predicate| {
            TranslationState::new()
                .translate_predicate(predicate)
                .unwrap()
                .to_string()
        };

        assert_eq!(
            translate(&implies(atom("A"), atom("B"))),
            "(=> (= SMT-1 0) (= SMT-2 0))"
        );
        assert_eq!(
            translate(&implies(
                atom("A"),
                implies(implies(atom("B"), atom("C")), implies(atom("D"), atom("A")))
            )),
            "(or (not (= SMT-1 0)) (not (=> (= SMT-2 0) (= SMT-3 0))) (not (= SMT-4 0)) (= SMT-1 0))"
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
            translation_exactness(&[Predicate::Not(Arc::new(Predicate::Exists(
                variable,
                Arc::new(Predicate::Or(vec![equality(uninterpreted)].into())),
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
            translation_exactness(&[Predicate::Forall(nat.clone(), Arc::new(body(&nat)))]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[Predicate::Exists(nat, Arc::new(Predicate::True))]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[Predicate::Exists(
                int.clone(),
                Arc::new(Predicate::Equals(Term::variable(int), integer("1"))),
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
        // `\in{S1,S2}(P1:S1, P2:S1)`: both operands have the operand sort.
        let element = Term::variable(Variable::new("X", Sort::simple("SortElement")));
        let pattern = Term::variable(Variable::new("P", Sort::simple("SortElement")));
        let membership = Predicate::In(element, pattern);
        let negated = Predicate::Not(Arc::new(membership.clone()));
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

    /// The absence of one key from one rest is one Boolean, wherever it was stated, and
    /// another key or rest is another Boolean.
    #[test]
    fn abstracts_an_absence_as_one_boolean_per_key_and_rest() {
        use std::sync::Arc;

        use crate::rule::{Absence, KeyedCollection};
        use crate::term::{CollectionSymbols, MapDefinition};

        let map = KeyedCollection::Map(Arc::new(MapDefinition {
            symbols: CollectionSymbols {
                unit: "mapUnit".into(),
                element: "mapItem".into(),
                concat: "mapConcat".into(),
            },
            key_sort: Sort::simple("SortKey"),
            value_sort: Sort::simple("SortValue"),
            map_sort: "SortMap".into(),
        }));
        let variable =
            |name: &str, sort: &str| Term::variable(Variable::new(name, Sort::simple(sort)));
        let absence = |key: &str, rest: &str| {
            Absence::predicate(
                map.clone(),
                variable(key, "SortKey"),
                variable(rest, "SortMap"),
            )
        };
        let mut translation = TranslationState::new();
        let mut translate = |predicate: Predicate| {
            translation
                .translate_predicate(&predicate)
                .unwrap()
                .to_string()
        };

        assert_eq!(translate(absence("K", "M")), "SMT-1");
        assert_eq!(translate(absence("K", "M")), "SMT-1");
        assert_eq!(translate(absence("J", "M")), "SMT-2");
        assert_eq!(translate(absence("K", "N")), "SMT-3");
    }

    #[test]
    fn rejects_out_of_range_placeholders() {
        assert_eq!(
            fill_placeholders(&SExpr::atom("#2"), vec![SExpr::atom("one")]),
            Err(TranslationError::PlaceholderOutOfBounds {
                placeholder: 2,
                arguments: 1,
            })
        );
    }

    /// The selection as a least fixed point computed by rounds: every round adds each remaining
    /// expression that mentions a constant of the selection so far, until a round adds none.
    #[cfg(feature = "z3")]
    fn closure_by_rounds(
        interesting: &BTreeSet<&str>,
        expressions: Vec<SExpr>,
    ) -> (Vec<SExpr>, Exactness) {
        let mut constants = interesting
            .iter()
            .map(|&name| name.to_owned())
            .collect::<BTreeSet<_>>();
        let mut remaining = expressions.into_iter().collect::<BTreeSet<_>>();
        let mut selected = BTreeSet::new();
        loop {
            let added = remaining
                .iter()
                .filter(|expression| {
                    smt_variables(expression)
                        .iter()
                        .any(|&name| constants.contains(name))
                })
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
                constants.extend(
                    smt_variables(&expression)
                        .iter()
                        .map(|&name| name.to_owned()),
                );
                selected.insert(expression);
            }
        }
    }

    /// Expressions over a few SMT constants and other atoms, nested a few levels.
    #[cfg(feature = "z3")]
    fn constant_expression() -> impl proptest::strategy::Strategy<Value = SExpr> {
        use proptest::{collection::vec, prelude::*};
        let atom = prop_oneof![
            (0..6_u8).prop_map(|index| SExpr::atom(format!("SMT-{index}"))),
            prop_oneof![Just("="), Just("and"), Just("x"), Just("0")].prop_map(SExpr::atom),
        ];
        atom.prop_recursive(3, 12, 3, |inner| vec(inner, 0..4).prop_map(SExpr::List))
    }

    #[cfg(feature = "z3")]
    proptest::proptest! {
        /// The breadth-first selection is the least set closed under sharing a constant with
        /// the check or with a selected expression, which the rounds compute directly.
        #[test]
        fn breadth_first_selection_is_the_closure_by_rounds(
            expressions in proptest::collection::vec(constant_expression(), 0..8),
            interesting in proptest::collection::btree_set(0..6_u8, 0..3),
        ) {
            let interesting = interesting
                .into_iter()
                .map(|index| format!("SMT-{index}"))
                .collect::<Vec<_>>();
            let interesting = interesting.iter().map(String::as_str).collect::<BTreeSet<_>>();
            proptest::prop_assert_eq!(
                closure_over(&interesting, expressions.clone()),
                closure_by_rounds(&interesting, expressions)
            );
        }
    }
}
