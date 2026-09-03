use crate::kore::ast::{Associativity, Pattern, Sort, Symbol, Variable, VariableKind};
use crate::kore::lexer::TokenKind;
use crate::kore::string;

use super::{ParseError, Parser};

impl Parser<'_> {
    pub(super) fn sort(&mut self) -> Result<Sort, ParseError> {
        struct Frame {
            name: String,
            arguments: Vec<Sort>,
        }

        let mut stack: Vec<Frame> = Vec::new();
        let mut value = None;
        loop {
            if value.is_none() {
                let name = self.expect(TokenKind::Id)?.text.to_owned();
                if self.consume(TokenKind::LBrace).is_none() {
                    value = Some(Sort::Variable(name));
                } else if self.consume(TokenKind::RBrace).is_some() {
                    value = Some(Sort::Application {
                        name,
                        arguments: Vec::new(),
                    });
                } else {
                    stack.push(Frame {
                        name,
                        arguments: Vec::new(),
                    });
                    continue;
                }
            }

            let sort = value.take().expect("a sort was parsed or reduced");
            let Some(frame) = stack.last_mut() else {
                return Ok(sort);
            };
            frame.arguments.push(sort);
            if self.consume(TokenKind::Comma).is_some() {
                continue;
            }
            self.expect(TokenKind::RBrace)?;
            let frame = stack.pop().expect("the current sort frame is present");
            value = Some(Sort::Application {
                name: frame.name,
                arguments: frame.arguments,
            });
        }
    }

    pub(super) fn sort_variables(&mut self) -> Result<Vec<String>, ParseError> {
        self.delimited(TokenKind::LBrace, TokenKind::RBrace, |parser| {
            Ok(parser.expect(TokenKind::Id)?.text.to_owned())
        })
    }

    pub(super) fn symbol(&mut self) -> Result<Symbol, ParseError> {
        let name = self.symbol_name()?;
        let sort_parameters = self.delimited(TokenKind::LBrace, TokenKind::RBrace, Self::sort)?;
        Ok(Symbol {
            name,
            sort_parameters,
        })
    }

    pub(super) fn pattern(&mut self) -> Result<Pattern, ParseError> {
        let mut stack = Vec::new();
        let mut value = None;
        loop {
            if value.is_none() {
                match self.start_pattern()? {
                    Started::Value(pattern) => value = Some(pattern),
                    Started::Frame(frame) => {
                        stack.push(frame);
                        continue;
                    }
                }
            }

            let pattern = value.take().expect("a pattern was parsed or reduced");
            let Some(frame) = stack.last_mut() else {
                return Ok(pattern);
            };
            frame.arguments.push(pattern);

            let complete = match frame.arity {
                Arity::Variadic => self.consume(TokenKind::Comma).is_none(),
                Arity::Exact(arity) if frame.arguments.len() < arity => {
                    self.expect(TokenKind::Comma)?;
                    false
                }
                Arity::Exact(_) => true,
            };
            if !complete {
                continue;
            }

            self.expect(TokenKind::RParen)?;
            let frame = stack.pop().expect("the current pattern frame is present");
            if frame.outer_close {
                self.expect(TokenKind::RParen)?;
            }
            let offset = self.peek().map_or(self.input_len, |token| token.offset);
            value = Some(frame.head.finish(frame.arguments, offset)?);
        }
    }

    fn start_pattern(&mut self) -> Result<Started, ParseError> {
        let Some(token) = self.peek() else {
            return Err(self.expected(TokenKind::Id));
        };
        match token.kind {
            TokenKind::String => self.string_pattern().map(Started::Value),
            TokenKind::Id if self.variable_follows() => self
                .variable(VariableKind::Element)
                .map(Pattern::Variable)
                .map(Started::Value),
            TokenKind::Id => {
                let symbol = self.symbol()?;
                self.variadic(Head::Application(symbol), false)
            }
            TokenKind::SetVarId => self
                .variable(VariableKind::Set)
                .map(Pattern::Variable)
                .map(Started::Value),
            TokenKind::MlTop | TokenKind::MlBottom => {
                self.expect(token.kind)?;
                let sort = self.one_sort()?;
                self.expect(TokenKind::LParen)?;
                self.expect(TokenKind::RParen)?;
                Ok(Started::Value(if token.kind == TokenKind::MlTop {
                    Pattern::Top { sort }
                } else {
                    Pattern::Bottom { sort }
                }))
            }
            TokenKind::MlAnd | TokenKind::MlOr => {
                self.expect(token.kind)?;
                let sort = self.one_sort()?;
                self.variadic(
                    if token.kind == TokenKind::MlAnd {
                        Head::And(sort)
                    } else {
                        Head::Or(sort)
                    },
                    false,
                )
            }
            TokenKind::MlNot | TokenKind::MlNext => {
                self.expect(token.kind)?;
                let sort = self.one_sort()?;
                self.fixed(Head::Unary(token.kind, sort), 1)
            }
            TokenKind::MlImplies | TokenKind::MlIff | TokenKind::MlRewrites => {
                self.expect(token.kind)?;
                let sort = self.one_sort()?;
                self.fixed(Head::Binary(token.kind, sort), 2)
            }
            TokenKind::MlExists | TokenKind::MlForall => {
                self.expect(token.kind)?;
                let sort = self.one_sort()?;
                self.expect(TokenKind::LParen)?;
                let variable = self.variable(VariableKind::Element)?;
                self.expect(TokenKind::Comma)?;
                Ok(Started::Frame(Frame::exact(
                    Head::Quantifier(token.kind, sort, variable),
                    1,
                )))
            }
            TokenKind::MlMu | TokenKind::MlNu => {
                self.expect(token.kind)?;
                self.expect(TokenKind::LBrace)?;
                self.expect(TokenKind::RBrace)?;
                self.expect(TokenKind::LParen)?;
                let variable = self.variable(VariableKind::Set)?;
                self.expect(TokenKind::Comma)?;
                Ok(Started::Frame(Frame::exact(
                    Head::Fixpoint(token.kind, variable),
                    1,
                )))
            }
            TokenKind::MlCeil | TokenKind::MlFloor => {
                self.expect(token.kind)?;
                let (operand_sort, result_sort) = self.two_sorts()?;
                self.fixed(
                    Head::RoundPredicate(token.kind, operand_sort, result_sort),
                    1,
                )
            }
            TokenKind::MlEquals | TokenKind::MlIn => {
                self.expect(token.kind)?;
                let (operand_sort, result_sort) = self.two_sorts()?;
                self.fixed(
                    Head::BinaryPredicate(token.kind, operand_sort, result_sort),
                    2,
                )
            }
            TokenKind::MlDv => self.domain_value().map(Started::Value),
            TokenKind::MlLeftAssoc | TokenKind::MlRightAssoc => {
                self.associative(if token.kind == TokenKind::MlLeftAssoc {
                    Associativity::Left
                } else {
                    Associativity::Right
                })
            }
            actual => Err(ParseError {
                offset: token.offset,
                message: format!("expected pattern, found {actual:?}"),
            }),
        }
    }

    fn fixed(&mut self, head: Head, arity: usize) -> Result<Started, ParseError> {
        self.expect(TokenKind::LParen)?;
        Ok(Started::Frame(Frame::exact(head, arity)))
    }

    fn variadic(&mut self, head: Head, outer_close: bool) -> Result<Started, ParseError> {
        self.expect(TokenKind::LParen)?;
        if self.consume(TokenKind::RParen).is_some() {
            if outer_close {
                self.expect(TokenKind::RParen)?;
            }
            let offset = self.peek().map_or(self.input_len, |token| token.offset);
            return head.finish(Vec::new(), offset).map(Started::Value);
        }
        Ok(Started::Frame(Frame {
            head,
            arguments: Vec::new(),
            arity: Arity::Variadic,
            outer_close,
        }))
    }

    fn string_pattern(&mut self) -> Result<Pattern, ParseError> {
        let token = self.expect(TokenKind::String)?;
        let value = string::unquote(token.text).map_err(|error| ParseError {
            offset: token.offset + error.offset,
            message: error.message.into(),
        })?;
        Ok(Pattern::String(value))
    }

    fn string_value(&mut self) -> Result<String, ParseError> {
        let token = self.expect(TokenKind::String)?;
        string::unquote(token.text).map_err(|error| ParseError {
            offset: token.offset + error.offset,
            message: error.message.into(),
        })
    }

    fn variable_follows(&self) -> bool {
        self.tokens
            .get(self.cursor + 1)
            .is_some_and(|token| token.kind == TokenKind::Colon)
    }

    pub(super) fn variable(&mut self, kind: VariableKind) -> Result<Variable, ParseError> {
        let token_kind = match kind {
            VariableKind::Element => TokenKind::Id,
            VariableKind::Set => TokenKind::SetVarId,
        };
        let name = self.expect(token_kind)?.text.to_owned();
        self.expect(TokenKind::Colon)?;
        let sort = self.sort()?;
        Ok(Variable { kind, name, sort })
    }

    fn symbol_name(&mut self) -> Result<String, ParseError> {
        Ok(self.expect(TokenKind::Id)?.text.to_owned())
    }

    fn one_sort(&mut self) -> Result<Sort, ParseError> {
        self.expect(TokenKind::LBrace)?;
        let sort = self.sort()?;
        self.expect(TokenKind::RBrace)?;
        Ok(sort)
    }

    fn two_sorts(&mut self) -> Result<(Sort, Sort), ParseError> {
        self.expect(TokenKind::LBrace)?;
        let operand_sort = self.sort()?;
        self.expect(TokenKind::Comma)?;
        let result_sort = self.sort()?;
        self.expect(TokenKind::RBrace)?;
        Ok((operand_sort, result_sort))
    }

    fn domain_value(&mut self) -> Result<Pattern, ParseError> {
        self.expect(TokenKind::MlDv)?;
        let sort = self.one_sort()?;
        self.expect(TokenKind::LParen)?;
        let value = self.string_value()?;
        self.expect(TokenKind::RParen)?;
        Ok(Pattern::DomainValue { sort, value })
    }

    fn associative(&mut self, associativity: Associativity) -> Result<Started, ParseError> {
        self.expect(if associativity == Associativity::Left {
            TokenKind::MlLeftAssoc
        } else {
            TokenKind::MlRightAssoc
        })?;
        self.expect(TokenKind::LBrace)?;
        self.expect(TokenKind::RBrace)?;
        self.expect(TokenKind::LParen)?;

        if let Some(or) = self.consume(TokenKind::MlOr) {
            let mut sorts = self.delimited(TokenKind::LBrace, TokenKind::RBrace, Self::sort)?;
            if sorts.len() != 1 {
                return Err(ParseError {
                    offset: or.offset,
                    message: "\\or under associative syntax requires exactly one sort parameter"
                        .into(),
                });
            }
            return self.variadic(
                Head::AssociativeOr(
                    associativity,
                    sorts.pop().expect("one sort was checked above"),
                ),
                true,
            );
        }

        let symbol = self.symbol()?;
        self.variadic(Head::AssociativeApplication(associativity, symbol), true)
    }
}

enum Started {
    Value(Pattern),
    Frame(Frame),
}

enum Arity {
    Variadic,
    Exact(usize),
}

struct Frame {
    head: Head,
    arguments: Vec<Pattern>,
    arity: Arity,
    outer_close: bool,
}

impl Frame {
    fn exact(head: Head, arity: usize) -> Self {
        Self {
            head,
            arguments: Vec::with_capacity(arity),
            arity: Arity::Exact(arity),
            outer_close: false,
        }
    }
}

enum Head {
    Application(Symbol),
    And(Sort),
    Or(Sort),
    Unary(TokenKind, Sort),
    Binary(TokenKind, Sort),
    Quantifier(TokenKind, Sort, Variable),
    Fixpoint(TokenKind, Variable),
    RoundPredicate(TokenKind, Sort, Sort),
    BinaryPredicate(TokenKind, Sort, Sort),
    AssociativeApplication(Associativity, Symbol),
    AssociativeOr(Associativity, Sort),
}

impl Head {
    fn finish(self, arguments: Vec<Pattern>, offset: usize) -> Result<Pattern, ParseError> {
        let mut arguments = arguments.into_iter();
        let mut boxed = || {
            Box::new(
                arguments
                    .next()
                    .expect("the parser enforces fixed pattern arity"),
            )
        };
        Ok(match self {
            Self::Application(symbol) => Pattern::Application {
                symbol,
                arguments: arguments.collect(),
            },
            Self::And(sort) => Pattern::And {
                sort,
                arguments: arguments.collect(),
            },
            Self::Or(sort) => Pattern::Or {
                sort,
                arguments: arguments.collect(),
            },
            Self::Unary(TokenKind::MlNot, sort) => Pattern::Not {
                sort,
                argument: boxed(),
            },
            Self::Unary(TokenKind::MlNext, sort) => Pattern::Next {
                sort,
                argument: boxed(),
            },
            Self::Binary(kind, sort) => {
                let (left, right) = (boxed(), boxed());
                match kind {
                    TokenKind::MlImplies => Pattern::Implies { sort, left, right },
                    TokenKind::MlIff => Pattern::Iff { sort, left, right },
                    TokenKind::MlRewrites => Pattern::Rewrites { sort, left, right },
                    _ => unreachable!("binary head has a binary token"),
                }
            }
            Self::Quantifier(kind, sort, variable) => {
                let body = boxed();
                match kind {
                    TokenKind::MlExists => Pattern::Exists {
                        sort,
                        variable,
                        body,
                    },
                    TokenKind::MlForall => Pattern::Forall {
                        sort,
                        variable,
                        body,
                    },
                    _ => unreachable!("quantifier head has a quantifier token"),
                }
            }
            Self::Fixpoint(kind, variable) => {
                let body = boxed();
                match kind {
                    TokenKind::MlMu => Pattern::Mu { variable, body },
                    TokenKind::MlNu => Pattern::Nu { variable, body },
                    _ => unreachable!("fixpoint head has a fixpoint token"),
                }
            }
            Self::RoundPredicate(kind, operand_sort, result_sort) => {
                let argument = boxed();
                match kind {
                    TokenKind::MlCeil => Pattern::Ceil {
                        operand_sort,
                        result_sort,
                        argument,
                    },
                    TokenKind::MlFloor => Pattern::Floor {
                        operand_sort,
                        result_sort,
                        argument,
                    },
                    _ => unreachable!("round-predicate head has a round-predicate token"),
                }
            }
            Self::BinaryPredicate(kind, operand_sort, result_sort) => {
                let (left, right) = (boxed(), boxed());
                match kind {
                    TokenKind::MlEquals => Pattern::Equals {
                        operand_sort,
                        result_sort,
                        left,
                        right,
                    },
                    TokenKind::MlIn => Pattern::In {
                        operand_sort,
                        result_sort,
                        left,
                        right,
                    },
                    _ => unreachable!("binary-predicate head has a binary-predicate token"),
                }
            }
            Self::AssociativeApplication(associativity, symbol) => {
                let arguments: Vec<_> = arguments.collect();
                if arguments.is_empty() {
                    return Err(ParseError {
                        offset,
                        message: "associative application requires at least one argument".into(),
                    });
                }
                Pattern::AssociativeApplication {
                    associativity,
                    symbol,
                    arguments,
                }
            }
            Self::AssociativeOr(associativity, sort) => {
                let arguments: Vec<_> = arguments.collect();
                if arguments.is_empty() {
                    return Err(ParseError {
                        offset,
                        message: "associative application requires at least one argument".into(),
                    });
                }
                fold_associative_or(associativity, sort, arguments)
            }
            Self::Unary(_, _) => unreachable!("unary head has a unary token"),
        })
    }
}

fn fold_associative_or(
    associativity: Associativity,
    sort: Sort,
    arguments: Vec<Pattern>,
) -> Pattern {
    let binary = |left, right| Pattern::Or {
        sort: sort.clone(),
        arguments: vec![left, right],
    };
    match associativity {
        Associativity::Left => {
            let mut arguments = arguments.into_iter();
            let first = arguments
                .next()
                .expect("associative arguments are non-empty");
            arguments.fold(first, binary)
        }
        Associativity::Right => {
            let mut arguments = arguments.into_iter().rev();
            let last = arguments
                .next()
                .expect("associative arguments are non-empty");
            arguments.fold(last, |right, left| binary(left, right))
        }
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    macro_rules! assert_pattern_snapshot {
        ($code:expr) => {{
            let source = indoc! { $code };
            let pattern =
                $crate::kore::parser::parse_pattern(source).expect("pattern should parse");

            insta::with_settings!({
                description => format!("KORE pattern:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(pattern);
            });
        }};
    }

    #[test]
    fn variables_and_application() {
        assert_pattern_snapshot!(
            r#"
            foo{S, List{T}}(X:S, @Set:SortSet{}, "value")
            "#
        );
    }

    #[test]
    fn multiary_connectives() {
        assert_pattern_snapshot!(
            r#"
            \and{SortBool{}}(
                \top{SortBool{}}(),
                \or{SortBool{}}(a{}(), b{}(), c{}())
            )
            "#
        );
    }

    #[test]
    fn preserves_multiary_connective_arity() {
        let top = crate::kore::parser::parse_pattern(r"\and{S}()").unwrap();
        let bottom = crate::kore::parser::parse_pattern(r"\or{S}()").unwrap();
        let unary_and = crate::kore::parser::parse_pattern(r"\and{S}(a{}())").unwrap();
        let unary_or = crate::kore::parser::parse_pattern(r"\or{S}(a{}())").unwrap();

        assert!(
            matches!(&top, crate::kore::ast::Pattern::And { arguments, .. } if arguments.is_empty())
        );
        assert!(
            matches!(&bottom, crate::kore::ast::Pattern::Or { arguments, .. } if arguments.is_empty())
        );
        assert!(
            matches!(&unary_and, crate::kore::ast::Pattern::And { arguments, .. } if arguments.len() == 1)
        );
        assert!(
            matches!(&unary_or, crate::kore::ast::Pattern::Or { arguments, .. } if arguments.len() == 1)
        );
    }

    #[test]
    fn quantifiers_and_predicates() {
        assert_pattern_snapshot!(
            r#"
            \forall{SortBool{}}(
                X:SortInt{},
                \equals{SortInt{}, SortBool{}}(X:SortInt{}, \dv{SortInt{}}("42"))
            )
            "#
        );
    }

    #[test]
    fn fixpoint_and_next() {
        assert_pattern_snapshot!(
            r#"
            \mu{}(@X:SortSet{}, \next{SortSet{}}(@X:SortSet{}))
            "#
        );
    }

    #[test]
    fn unary_and_binary_connectives() {
        assert_pattern_snapshot!(
            r#"
            \iff{S}(
                \not{S}(a{}()),
                \implies{S}(b{}(), \rewrites{S}(c{}(), d{}()))
            )
            "#
        );
    }

    #[test]
    fn quantifier_and_round_predicates() {
        assert_pattern_snapshot!(
            r#"
            \exists{SortBool{}}(
                X:SortInt{},
                \in{SortInt{}, SortBool{}}(
                    X:SortInt{},
                    \ceil{SortInt{}, SortBool{}}(value{}())
                )
            )
            "#
        );
    }

    #[test]
    fn bottom_floor_and_nu() {
        assert_pattern_snapshot!(
            r#"
            \nu{}(
                @X:SortSet{},
                \floor{SortSet{}, SortBool{}}(\bottom{SortSet{}}())
            )
            "#
        );
    }

    #[test]
    fn associative_application() {
        assert_pattern_snapshot!(
            r#"
            \left-assoc{}(Lbl'Unds'Map'Unds{}(a{}(), b{}(), c{}()))
            "#
        );
    }

    #[test]
    fn right_associative_application() {
        assert_pattern_snapshot!(
            r#"
            \right-assoc{}(append{S}(a{}(), b{}(), c{}()))
            "#
        );
    }

    #[test]
    fn parses_reference_accepted_backslash_identifiers() {
        let element = crate::kore::parser::parse_pattern(r"\foo:\S{}").unwrap();
        let set = crate::kore::parser::parse_pattern(r"\@X:\S{}").unwrap();
        let application = crate::kore::parser::parse_pattern(r"\foo{}()").unwrap();

        assert!(matches!(
            &element,
            crate::kore::ast::Pattern::Variable(crate::kore::ast::Variable {
                kind: crate::kore::ast::VariableKind::Element,
                name,
                ..
            }) if name == "\\foo"
        ));
        assert!(matches!(
            &set,
            crate::kore::ast::Pattern::Variable(crate::kore::ast::Variable {
                kind: crate::kore::ast::VariableKind::Set,
                name,
                ..
            }) if name == "\\@X"
        ));
        assert!(matches!(
            &application,
            crate::kore::ast::Pattern::Application { symbol, arguments }
                if symbol.name == "\\foo" && arguments.is_empty()
        ));
    }

    #[test]
    fn expands_legacy_associative_or_like_the_reference() {
        let left =
            crate::kore::parser::parse_pattern(r"\left-assoc{}(\or{S{}}(a{}(), b{}(), c{}()))")
                .unwrap();
        let right =
            crate::kore::parser::parse_pattern(r"\right-assoc{}(\or{S{}}(a{}(), b{}(), c{}()))")
                .unwrap();

        assert_eq!(
            left,
            crate::kore::parser::parse_pattern(r"\or{S{}}(\or{S{}}(a{}(), b{}()), c{}())").unwrap()
        );
        assert_eq!(
            right,
            crate::kore::parser::parse_pattern(r"\or{S{}}(a{}(), \or{S{}}(b{}(), c{}()))").unwrap()
        );
        assert_eq!(
            crate::kore::parser::parse_pattern(r"\left-assoc{}(\or{S{}}(a{}()))").unwrap(),
            crate::kore::parser::parse_pattern(r"a{}()").unwrap()
        );
    }

    #[test]
    fn rejects_undefined_associative_ml_heads_without_panicking() {
        let error =
            crate::kore::parser::parse_pattern(r"\left-assoc{}(\or{S{}, T{}}(a{}(), b{}()))")
                .unwrap_err();
        assert_eq!(
            error.message,
            "\\or under associative syntax requires exactly one sort parameter"
        );
        assert!(
            crate::kore::parser::parse_pattern(r"\right-assoc{}(\and{S{}}(a{}(), b{}()))").is_err()
        );
    }
}
