//! Portable SMT-LIB translation shared by native Z3 and solver-free builds.

use std::{collections::BTreeMap, fmt};

use crate::{
    rule::Predicate,
    term::{Sort, Term, TermKind},
};

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
