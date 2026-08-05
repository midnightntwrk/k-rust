use crate::kore::ast::{Associativity, Pattern, Sort, Symbol, Variable, VariableKind};
use crate::kore::lexer::TokenKind;
use crate::kore::string;

use super::{ParseError, Parser};

impl Parser<'_> {
    pub(super) fn sort(&mut self) -> Result<Sort, ParseError> {
        let name = self.expect(TokenKind::Id)?.text.to_owned();
        if self.at(TokenKind::LBrace) {
            let arguments = self.delimited(TokenKind::LBrace, TokenKind::RBrace, Self::sort)?;
            Ok(Sort::Application { name, arguments })
        } else {
            Ok(Sort::Variable(name))
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
        let Some(token) = self.peek() else {
            return Err(self.expected(TokenKind::Id));
        };
        match token.kind {
            TokenKind::String => self.string_pattern(),
            TokenKind::Id if self.variable_follows() => {
                self.variable(VariableKind::Element).map(Pattern::Variable)
            }
            TokenKind::Id | TokenKind::SymbolId => self.application(),
            TokenKind::SetVarId => self.variable(VariableKind::Set).map(Pattern::Variable),
            TokenKind::MlTop => self.nullary(true),
            TokenKind::MlBottom => self.nullary(false),
            TokenKind::MlAnd => self.multiary(true),
            TokenKind::MlOr => self.multiary(false),
            TokenKind::MlNot => self.unary(TokenKind::MlNot),
            TokenKind::MlNext => self.unary(TokenKind::MlNext),
            TokenKind::MlImplies => self.binary(TokenKind::MlImplies),
            TokenKind::MlIff => self.binary(TokenKind::MlIff),
            TokenKind::MlRewrites => self.binary(TokenKind::MlRewrites),
            TokenKind::MlExists => self.quantifier(TokenKind::MlExists),
            TokenKind::MlForall => self.quantifier(TokenKind::MlForall),
            TokenKind::MlMu => self.fixpoint(TokenKind::MlMu),
            TokenKind::MlNu => self.fixpoint(TokenKind::MlNu),
            TokenKind::MlCeil => self.round_predicate(TokenKind::MlCeil),
            TokenKind::MlFloor => self.round_predicate(TokenKind::MlFloor),
            TokenKind::MlEquals => self.binary_predicate(TokenKind::MlEquals),
            TokenKind::MlIn => self.binary_predicate(TokenKind::MlIn),
            TokenKind::MlDv => self.domain_value(),
            TokenKind::MlLeftAssoc => self.associative(Associativity::Left),
            TokenKind::MlRightAssoc => self.associative(Associativity::Right),
            actual => Err(ParseError {
                offset: token.offset,
                message: format!("expected pattern, found {actual:?}"),
            }),
        }
    }

    pub(super) fn application(&mut self) -> Result<Pattern, ParseError> {
        let symbol = self.symbol()?;
        let arguments = self.delimited(TokenKind::LParen, TokenKind::RParen, Self::pattern)?;
        Ok(Pattern::Application { symbol, arguments })
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
        match self.string_pattern()? {
            Pattern::String(value) => Ok(value),
            _ => unreachable!("string_pattern always returns Pattern::String"),
        }
    }

    fn variable_follows(&self) -> bool {
        self.tokens
            .get(self.cursor + 1)
            .is_some_and(|token| token.kind == TokenKind::Colon)
    }

    fn variable(&mut self, kind: VariableKind) -> Result<Variable, ParseError> {
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
        if let Some(token) = self.consume(TokenKind::Id) {
            Ok(token.text.to_owned())
        } else {
            Ok(self.expect(TokenKind::SymbolId)?.text.to_owned())
        }
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

    fn one_pattern(&mut self) -> Result<Pattern, ParseError> {
        self.expect(TokenKind::LParen)?;
        let pattern = self.pattern()?;
        self.expect(TokenKind::RParen)?;
        Ok(pattern)
    }

    fn two_patterns(&mut self) -> Result<(Pattern, Pattern), ParseError> {
        self.expect(TokenKind::LParen)?;
        let left = self.pattern()?;
        self.expect(TokenKind::Comma)?;
        let right = self.pattern()?;
        self.expect(TokenKind::RParen)?;
        Ok((left, right))
    }

    fn nullary(&mut self, top: bool) -> Result<Pattern, ParseError> {
        self.expect(if top {
            TokenKind::MlTop
        } else {
            TokenKind::MlBottom
        })?;
        let sort = self.one_sort()?;
        self.expect(TokenKind::LParen)?;
        self.expect(TokenKind::RParen)?;
        Ok(if top {
            Pattern::Top { sort }
        } else {
            Pattern::Bottom { sort }
        })
    }

    fn multiary(&mut self, and: bool) -> Result<Pattern, ParseError> {
        self.expect(if and {
            TokenKind::MlAnd
        } else {
            TokenKind::MlOr
        })?;
        let sort = self.one_sort()?;
        let arguments = self.delimited(TokenKind::LParen, TokenKind::RParen, Self::pattern)?;
        Ok(if and {
            Pattern::And { sort, arguments }
        } else {
            Pattern::Or { sort, arguments }
        })
    }

    fn unary(&mut self, kind: TokenKind) -> Result<Pattern, ParseError> {
        self.expect(kind)?;
        let sort = self.one_sort()?;
        let argument = Box::new(self.one_pattern()?);
        Ok(match kind {
            TokenKind::MlNot => Pattern::Not { sort, argument },
            TokenKind::MlNext => Pattern::Next { sort, argument },
            _ => unreachable!("unary called with a non-unary token"),
        })
    }

    fn binary(&mut self, kind: TokenKind) -> Result<Pattern, ParseError> {
        self.expect(kind)?;
        let sort = self.one_sort()?;
        let (left, right) = self.two_patterns()?;
        let (left, right) = (Box::new(left), Box::new(right));
        Ok(match kind {
            TokenKind::MlImplies => Pattern::Implies { sort, left, right },
            TokenKind::MlIff => Pattern::Iff { sort, left, right },
            TokenKind::MlRewrites => Pattern::Rewrites { sort, left, right },
            _ => unreachable!("binary called with a non-binary token"),
        })
    }

    fn quantifier(&mut self, kind: TokenKind) -> Result<Pattern, ParseError> {
        self.expect(kind)?;
        let sort = self.one_sort()?;
        self.expect(TokenKind::LParen)?;
        let variable = self.variable(VariableKind::Element)?;
        self.expect(TokenKind::Comma)?;
        let body = Box::new(self.pattern()?);
        self.expect(TokenKind::RParen)?;
        Ok(match kind {
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
            _ => unreachable!("quantifier called with a non-quantifier token"),
        })
    }

    fn fixpoint(&mut self, kind: TokenKind) -> Result<Pattern, ParseError> {
        self.expect(kind)?;
        self.expect(TokenKind::LBrace)?;
        self.expect(TokenKind::RBrace)?;
        self.expect(TokenKind::LParen)?;
        let variable = self.variable(VariableKind::Set)?;
        self.expect(TokenKind::Comma)?;
        let body = Box::new(self.pattern()?);
        self.expect(TokenKind::RParen)?;
        Ok(match kind {
            TokenKind::MlMu => Pattern::Mu { variable, body },
            TokenKind::MlNu => Pattern::Nu { variable, body },
            _ => unreachable!("fixpoint called with a non-fixpoint token"),
        })
    }

    fn round_predicate(&mut self, kind: TokenKind) -> Result<Pattern, ParseError> {
        self.expect(kind)?;
        let (operand_sort, result_sort) = self.two_sorts()?;
        let argument = Box::new(self.one_pattern()?);
        Ok(match kind {
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
            _ => unreachable!("round_predicate called with a different token"),
        })
    }

    fn binary_predicate(&mut self, kind: TokenKind) -> Result<Pattern, ParseError> {
        self.expect(kind)?;
        let (operand_sort, result_sort) = self.two_sorts()?;
        let (left, right) = self.two_patterns()?;
        let (left, right) = (Box::new(left), Box::new(right));
        Ok(match kind {
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
            _ => unreachable!("binary_predicate called with a different token"),
        })
    }

    fn domain_value(&mut self) -> Result<Pattern, ParseError> {
        self.expect(TokenKind::MlDv)?;
        let sort = self.one_sort()?;
        self.expect(TokenKind::LParen)?;
        let value = self.string_value()?;
        self.expect(TokenKind::RParen)?;
        Ok(Pattern::DomainValue { sort, value })
    }

    fn associative(&mut self, associativity: Associativity) -> Result<Pattern, ParseError> {
        self.expect(match associativity {
            Associativity::Left => TokenKind::MlLeftAssoc,
            Associativity::Right => TokenKind::MlRightAssoc,
        })?;
        self.expect(TokenKind::LBrace)?;
        self.expect(TokenKind::RBrace)?;
        self.expect(TokenKind::LParen)?;
        let Pattern::Application { symbol, arguments } = self.application()? else {
            unreachable!("application always returns Pattern::Application");
        };
        self.expect(TokenKind::RParen)?;
        Ok(Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        })
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
}
