use crate::kore::ast::{Attributes, Pattern, Sentence, VariableKind};
use crate::kore::lexer::TokenKind;

use super::{ParseError, Parser};

impl Parser<'_> {
    pub(super) fn sentence(&mut self) -> Result<Sentence, ParseError> {
        let Some(token) = self.peek() else {
            return Err(self.expected(TokenKind::Import));
        };
        match token.kind {
            TokenKind::Import => self.import(),
            TokenKind::Sort => self.sort_declaration(false),
            TokenKind::HookedSort => self.sort_declaration(true),
            TokenKind::Symbol => self.symbol_declaration(false),
            TokenKind::HookedSymbol => self.symbol_declaration(true),
            TokenKind::Alias => self.alias_declaration(),
            TokenKind::Axiom => self.axiom(false),
            TokenKind::Claim => self.axiom(true),
            actual => Err(ParseError {
                offset: token.offset,
                message: format!("expected sentence, found {actual:?}"),
            }),
        }
    }

    pub(super) fn attributes(&mut self) -> Result<Attributes, ParseError> {
        let patterns = self.delimited(TokenKind::LBracket, TokenKind::RBracket, |parser| {
            parser.pattern()
        })?;
        Ok(Attributes(patterns))
    }

    fn import(&mut self) -> Result<Sentence, ParseError> {
        self.expect(TokenKind::Import)?;
        let module = self.expect(TokenKind::Id)?.text.to_owned();
        let attributes = self.attributes()?;
        Ok(Sentence::Import { module, attributes })
    }

    fn sort_declaration(&mut self, hooked: bool) -> Result<Sentence, ParseError> {
        self.expect(if hooked {
            TokenKind::HookedSort
        } else {
            TokenKind::Sort
        })?;
        let name = self.expect(TokenKind::Id)?.text.to_owned();
        let parameters = self.sort_variables()?;
        let attributes = self.attributes()?;
        Ok(Sentence::SortDeclaration {
            hooked,
            name,
            parameters,
            attributes,
        })
    }

    fn symbol_declaration(&mut self, hooked: bool) -> Result<Sentence, ParseError> {
        self.expect(if hooked {
            TokenKind::HookedSymbol
        } else {
            TokenKind::Symbol
        })?;
        let symbol = self.symbol()?;
        let argument_sorts = self.delimited(TokenKind::LParen, TokenKind::RParen, Self::sort)?;
        self.expect(TokenKind::Colon)?;
        let result_sort = self.sort()?;
        let attributes = self.attributes()?;
        Ok(Sentence::SymbolDeclaration {
            hooked,
            symbol,
            argument_sorts,
            result_sort,
            attributes,
        })
    }

    fn alias_declaration(&mut self) -> Result<Sentence, ParseError> {
        self.expect(TokenKind::Alias)?;
        let alias = self.symbol()?;
        let argument_sorts = self.delimited(TokenKind::LParen, TokenKind::RParen, Self::sort)?;
        self.expect(TokenKind::Colon)?;
        let result_sort = self.sort()?;
        self.expect(TokenKind::Where)?;
        let symbol = self.symbol()?;
        let arguments = self.delimited(
            TokenKind::LParen,
            TokenKind::RParen,
            Self::alias_left_variable,
        )?;
        let left = Pattern::Application { symbol, arguments };
        self.expect(TokenKind::Walrus)?;
        let right = self.pattern()?;
        let attributes = self.attributes()?;
        Ok(Sentence::AliasDeclaration {
            alias,
            argument_sorts,
            result_sort,
            left: Box::new(left),
            right: Box::new(right),
            attributes,
        })
    }

    fn alias_left_variable(&mut self) -> Result<Pattern, ParseError> {
        let Some(token) = self.peek() else {
            return Err(ParseError {
                offset: self.input_len,
                message: "expected variable in alias left-hand side, found end of input".into(),
            });
        };
        let kind = match token.kind {
            TokenKind::Id => VariableKind::Element,
            TokenKind::SetVarId => VariableKind::Set,
            actual => {
                return Err(ParseError {
                    offset: token.offset,
                    message: format!("expected variable in alias left-hand side, found {actual:?}"),
                });
            }
        };
        if !self
            .tokens
            .get(self.cursor + 1)
            .is_some_and(|next| next.kind == TokenKind::Colon)
        {
            let offending = self.tokens.get(self.cursor + 1).copied().unwrap_or(token);
            return Err(ParseError {
                offset: offending.offset,
                message: format!(
                    "expected variable in alias left-hand side, found {:?}",
                    offending.kind
                ),
            });
        }
        self.variable(kind).map(Pattern::Variable)
    }

    fn axiom(&mut self, claim: bool) -> Result<Sentence, ParseError> {
        self.expect(if claim {
            TokenKind::Claim
        } else {
            TokenKind::Axiom
        })?;
        let parameters = self.sort_variables()?;
        let pattern = self.pattern()?;
        let attributes = self.attributes()?;
        Ok(if claim {
            Sentence::Claim {
                parameters,
                pattern: Box::new(pattern),
                attributes,
            }
        } else {
            Sentence::Axiom {
                parameters,
                pattern: Box::new(pattern),
                attributes,
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    macro_rules! assert_sentence_snapshot {
        ($code:expr) => {{
            let source = indoc! { $code };
            let sentence =
                $crate::kore::parser::parse_sentence(source).expect("sentence should parse");

            insta::with_settings!({
                description => format!("KORE sentence:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(sentence);
            });
        }};
    }

    #[test]
    fn sort_declarations() {
        assert_sentence_snapshot!(
            r#"
            hooked-sort SortMap{K, V} [hook{}("MAP.Map")]
            "#
        );
    }

    #[test]
    fn symbol_declaration() {
        assert_sentence_snapshot!(
            r#"
            symbol concat{S}(List{S}, List{S}) : List{S} [assoc{}(), unit{}("nil")]
            "#
        );
    }

    #[test]
    fn hooked_symbol_declaration() {
        assert_sentence_snapshot!(
            r#"
            hooked-symbol plus{}(SortInt{}, SortInt{}) : SortInt{} [hook{}("INT.add")]
            "#
        );
    }

    #[test]
    fn alias_declaration() {
        assert_sentence_snapshot!(
            r#"
            alias id{S}(S) : S where id{S}(X:S) := X:S []
            "#
        );
    }

    #[test]
    fn axiom_declaration() {
        assert_sentence_snapshot!(
            r#"
            axiom{S} \equals{S, SortBool{}}(id{S}(X:S), X:S) [simplification{}()]
            "#
        );
    }

    #[test]
    fn accepts_any_pattern_in_attributes() {
        let sentence = crate::kore::parser::parse_sentence(
            r#"axiom{} \top{S{}}() [a{}(), "literal", X:S{}, \dv{S{}}("1"), \and{S{}}(), @Y:S{}]"#,
        )
        .unwrap();
        let crate::kore::ast::Sentence::Axiom { attributes, .. } = sentence else {
            panic!("expected an axiom")
        };
        assert_eq!(attributes.0.len(), 6);
    }

    #[test]
    fn alias_left_hand_side_accepts_only_variables() {
        crate::kore::parser::parse_sentence(
            "alias h{}(S{}) : S{} where h{}(X:S{}, @Y:S{}) := X:S{} []",
        )
        .unwrap();

        let error = crate::kore::parser::parse_sentence(
            "alias h{}(S{}) : S{} where h{}(g{}(X:S{})) := X:S{} []",
        )
        .unwrap_err();
        assert_eq!(
            error.message,
            "expected variable in alias left-hand side, found LBrace"
        );
    }
}
