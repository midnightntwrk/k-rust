use crate::ast::{Attributes, Sentence};
use crate::lexer::TokenKind;

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
            parser.application()
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
        let left = self.application()?;
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
            let sentence = $crate::parser::parse_sentence(source).expect("sentence should parse");

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
}
