use crate::ast::{Definition, Module};
use crate::lexer::TokenKind;

use super::{ParseError, Parser};

impl Parser<'_> {
    pub(super) fn module(&mut self) -> Result<Module, ParseError> {
        self.expect(TokenKind::Module)?;
        let name = self.expect(TokenKind::Id)?.text.to_owned();
        let mut sentences = Vec::new();
        while !self.at(TokenKind::EndModule) {
            if self.peek().is_none() {
                return Err(self.expected(TokenKind::EndModule));
            }
            sentences.push(self.sentence()?);
        }
        self.expect(TokenKind::EndModule)?;
        let attributes = self.attributes()?;
        Ok(Module {
            name,
            sentences,
            attributes,
        })
    }

    pub(super) fn definition(&mut self) -> Result<Definition, ParseError> {
        let attributes = self.attributes()?;
        let mut modules = Vec::new();
        while self.peek().is_some() {
            modules.push(self.module()?);
        }
        Ok(Definition {
            attributes,
            modules,
        })
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    macro_rules! assert_module_snapshot {
        ($code:expr) => {{
            let source = indoc! { $code };
            let module = $crate::parser::parse_module(source).expect("module should parse");

            insta::with_settings!({
                description => format!("KORE module:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(module);
            });
        }};
    }

    macro_rules! assert_definition_snapshot {
        ($code:expr) => {{
            let source = indoc! { $code };
            let definition =
                $crate::parser::parse_definition(source).expect("definition should parse");

            insta::with_settings!({
                description => format!("KORE definition:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(definition);
            });
        }};
    }

    #[test]
    fn module_with_sentences() {
        assert_module_snapshot!(
            r#"
            module NAT
                import BOOL []
                sort SortNat{} [hook{}("NAT.Nat")]
                symbol zero{}() : SortNat{} [constructor{}()]
                symbol succ{}(SortNat{}) : SortNat{} [constructor{}()]
                axiom{}
                    \equals{SortNat{}, SortBool{}}(succ{}(zero{}()), succ{}(zero{}()))
                    []
            endmodule [main{}()]
            "#
        );
    }

    #[test]
    fn definition_with_multiple_modules() {
        assert_definition_snapshot!(
            r#"
            [source{}("snapshot-test")]

            module BOOL
                sort SortBool{} []
            endmodule []

            module MAIN
                import BOOL []
                claim{}
                    \implies{SortBool{}}(\top{SortBool{}}(), \top{SortBool{}}())
                    [trusted{}()]
            endmodule []
            "#
        );
    }
}
