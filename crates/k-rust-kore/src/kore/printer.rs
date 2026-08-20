//! Compact and width-aware textual KORE printing.

mod document;

use std::fmt::{self, Display, Formatter};

use document::{Doc, RenderMode, render};

use super::ast::{
    Associativity, Attributes, Definition, Module, Pattern, Sentence, Sort, Symbol, Variable,
};
use super::string;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrintStyle {
    Compact,
    Pretty,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrintOptions {
    pub style: PrintStyle,
    pub width: usize,
    pub indent: usize,
}

impl PrintOptions {
    pub const fn compact() -> Self {
        Self {
            style: PrintStyle::Compact,
            width: usize::MAX,
            indent: 2,
        }
    }

    pub const fn pretty(width: usize) -> Self {
        Self {
            style: PrintStyle::Pretty,
            width,
            indent: 2,
        }
    }
}

impl Default for PrintOptions {
    fn default() -> Self {
        Self::pretty(100)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Printer {
    options: PrintOptions,
}

impl Printer {
    pub const fn new(options: PrintOptions) -> Self {
        Self { options }
    }

    pub const fn compact() -> Self {
        Self::new(PrintOptions::compact())
    }

    pub const fn pretty(width: usize) -> Self {
        Self::new(PrintOptions::pretty(width))
    }

    pub fn print_definition(self, definition: &Definition) -> String {
        self.render(definition_doc(definition, self.options.indent))
    }

    pub fn print_module(self, module: &Module) -> String {
        self.render(module_doc(module, self.options.indent))
    }

    pub fn print_sentence(self, sentence: &Sentence) -> String {
        self.render(sentence_doc(sentence, self.options.indent))
    }

    pub fn print_pattern(self, pattern: &Pattern) -> String {
        self.render(pattern_doc(pattern, self.options.indent))
    }

    fn render(self, document: Doc) -> String {
        let mode = match self.options.style {
            PrintStyle::Compact => RenderMode::Compact,
            PrintStyle::Pretty => RenderMode::Pretty,
        };
        render(&document, mode, self.options.width)
    }
}

macro_rules! impl_compact_display {
    ($type:ty, $method:ident) => {
        impl Display for $type {
            fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
                formatter.write_str(&Printer::compact().$method(self))
            }
        }
    };
}

impl_compact_display!(Definition, print_definition);
impl_compact_display!(Module, print_module);
impl_compact_display!(Sentence, print_sentence);
impl_compact_display!(Pattern, print_pattern);

impl Display for Attributes {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&render(
            &attributes_doc(self, PrintOptions::compact().indent),
            RenderMode::Compact,
            usize::MAX,
        ))
    }
}

impl Display for Sort {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&render(
            &sort_doc(self, PrintOptions::compact().indent),
            RenderMode::Compact,
            usize::MAX,
        ))
    }
}

impl Display for Symbol {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&render(
            &symbol_doc(self, PrintOptions::compact().indent),
            RenderMode::Compact,
            usize::MAX,
        ))
    }
}

impl Display for Variable {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&render(
            &variable_doc(self, PrintOptions::compact().indent),
            RenderMode::Compact,
            usize::MAX,
        ))
    }
}

fn definition_doc(definition: &Definition, indent: usize) -> Doc {
    let mut documents = vec![attributes_doc(&definition.attributes, indent)];
    for module in &definition.modules {
        documents.push(Doc::hard_line());
        documents.push(module_doc(module, indent));
    }
    Doc::concat(documents)
}

fn module_doc(module: &Module, indent: usize) -> Doc {
    let mut body = Vec::new();
    for (index, sentence) in module.sentences.iter().enumerate() {
        if index > 0 {
            body.push(Doc::hard_line());
        }
        body.push(sentence_doc(sentence, indent));
    }

    let mut documents = vec![Doc::text(format!("module {}", module.name))];
    if !body.is_empty() {
        documents.push(Doc::concat(std::iter::once(Doc::hard_line()).chain(body)).nest(indent));
    }
    documents.push(Doc::hard_line());
    documents.push(Doc::text("endmodule "));
    documents.push(attributes_doc(&module.attributes, indent));
    Doc::concat(documents)
}

fn sentence_doc(sentence: &Sentence, indent: usize) -> Doc {
    match sentence {
        Sentence::Import { module, attributes } => Doc::concat([
            Doc::text(format!("import {module}")),
            Doc::line(),
            attributes_doc(attributes, indent),
        ])
        .group(),
        Sentence::SortDeclaration {
            hooked,
            name,
            parameters,
            attributes,
        } => Doc::concat([
            Doc::text(format!(
                "{}sort {name}",
                if *hooked { "hooked-" } else { "" }
            )),
            delimited(
                "{",
                "}",
                parameters
                    .iter()
                    .map(|parameter| Doc::text(parameter.clone())),
                indent,
            ),
            Doc::line(),
            attributes_doc(attributes, indent),
        ])
        .group(),
        Sentence::SymbolDeclaration {
            hooked,
            symbol,
            argument_sorts,
            result_sort,
            attributes,
        } => Doc::concat([
            Doc::text(if *hooked { "hooked-symbol " } else { "symbol " }),
            symbol_doc(symbol, indent),
            delimited(
                "(",
                ")",
                argument_sorts.iter().map(|sort| sort_doc(sort, indent)),
                indent,
            ),
            Doc::text(" : "),
            sort_doc(result_sort, indent),
            Doc::line(),
            attributes_doc(attributes, indent),
        ])
        .group(),
        Sentence::AliasDeclaration {
            alias,
            argument_sorts,
            result_sort,
            left,
            right,
            attributes,
        } => Doc::concat([
            Doc::text("alias "),
            symbol_doc(alias, indent),
            delimited(
                "(",
                ")",
                argument_sorts.iter().map(|sort| sort_doc(sort, indent)),
                indent,
            ),
            Doc::text(" : "),
            sort_doc(result_sort, indent),
            Doc::text(" where"),
            Doc::concat([
                Doc::line(),
                pattern_doc(left, indent),
                Doc::text(" :="),
                Doc::line(),
                pattern_doc(right, indent),
                Doc::line(),
                attributes_doc(attributes, indent),
            ])
            .nest(indent),
        ])
        .group(),
        Sentence::Axiom {
            parameters,
            pattern,
            attributes,
        } => declaration_pattern_doc("axiom", parameters, pattern, attributes, indent),
        Sentence::Claim {
            parameters,
            pattern,
            attributes,
        } => declaration_pattern_doc("claim", parameters, pattern, attributes, indent),
    }
}

fn declaration_pattern_doc(
    keyword: &str,
    parameters: &[String],
    pattern: &Pattern,
    attributes: &Attributes,
    indent: usize,
) -> Doc {
    Doc::concat([
        Doc::text(keyword),
        delimited(
            "{",
            "}",
            parameters
                .iter()
                .map(|parameter| Doc::text(parameter.clone())),
            indent,
        ),
        Doc::concat([
            Doc::line(),
            pattern_doc(pattern, indent),
            Doc::line(),
            attributes_doc(attributes, indent),
        ])
        .nest(indent),
    ])
    .group()
}

fn attributes_doc(attributes: &Attributes, indent: usize) -> Doc {
    delimited(
        "[",
        "]",
        attributes
            .0
            .iter()
            .map(|pattern| pattern_doc(pattern, indent)),
        indent,
    )
}

fn sort_doc(sort: &Sort, indent: usize) -> Doc {
    match sort {
        Sort::Variable(name) => Doc::text(name.clone()),
        Sort::Application { name, arguments } => Doc::concat([
            Doc::text(name.clone()),
            delimited(
                "{",
                "}",
                arguments.iter().map(|sort| sort_doc(sort, indent)),
                indent,
            ),
        ]),
    }
}

fn symbol_doc(symbol: &Symbol, indent: usize) -> Doc {
    Doc::concat([
        Doc::text(symbol.name.clone()),
        delimited(
            "{",
            "}",
            symbol
                .sort_parameters
                .iter()
                .map(|sort| sort_doc(sort, indent)),
            indent,
        ),
    ])
}

fn variable_doc(variable: &Variable, indent: usize) -> Doc {
    Doc::concat([
        Doc::text(format!("{}:", variable.name)),
        sort_doc(&variable.sort, indent),
    ])
}

fn pattern_doc(pattern: &Pattern, indent: usize) -> Doc {
    match pattern {
        Pattern::String(value) => Doc::text(string::quote(value)),
        Pattern::Variable(variable) => variable_doc(variable, indent),
        Pattern::Application { symbol, arguments } => application_doc(symbol, arguments, indent),
        Pattern::Top { sort } => nullary_doc("top", sort, indent),
        Pattern::Bottom { sort } => nullary_doc("bottom", sort, indent),
        Pattern::And { sort, arguments } => multiary_doc("and", sort, arguments, indent),
        Pattern::Or { sort, arguments } => multiary_doc("or", sort, arguments, indent),
        Pattern::Not { sort, argument } => unary_doc("not", sort, argument, indent),
        Pattern::Next { sort, argument } => unary_doc("next", sort, argument, indent),
        Pattern::Implies { sort, left, right } => binary_doc("implies", sort, left, right, indent),
        Pattern::Iff { sort, left, right } => binary_doc("iff", sort, left, right, indent),
        Pattern::Rewrites { sort, left, right } => {
            binary_doc("rewrites", sort, left, right, indent)
        }
        Pattern::Exists {
            sort,
            variable,
            body,
        } => quantifier_doc("exists", sort, variable, body, indent),
        Pattern::Forall {
            sort,
            variable,
            body,
        } => quantifier_doc("forall", sort, variable, body, indent),
        Pattern::Mu { variable, body } => fixpoint_doc("mu", variable, body, indent),
        Pattern::Nu { variable, body } => fixpoint_doc("nu", variable, body, indent),
        Pattern::Ceil {
            operand_sort,
            result_sort,
            argument,
        } => round_predicate_doc("ceil", operand_sort, result_sort, argument, indent),
        Pattern::Floor {
            operand_sort,
            result_sort,
            argument,
        } => round_predicate_doc("floor", operand_sort, result_sort, argument, indent),
        Pattern::Equals {
            operand_sort,
            result_sort,
            left,
            right,
        } => binary_predicate_doc("equals", operand_sort, result_sort, left, right, indent),
        Pattern::In {
            operand_sort,
            result_sort,
            left,
            right,
        } => binary_predicate_doc("in", operand_sort, result_sort, left, right, indent),
        Pattern::DomainValue { sort, value } => Doc::concat([
            Doc::text("\\dv{"),
            sort_doc(sort, indent),
            Doc::text(format!("}}({})", string::quote(value))),
        ]),
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => {
            let name = match associativity {
                Associativity::Left => "left-assoc",
                Associativity::Right => "right-assoc",
            };
            Doc::concat([
                Doc::text(format!("\\{name}{{}}(")),
                application_doc(symbol, arguments, indent),
                Doc::text(")"),
            ])
            .group()
        }
    }
}

fn application_doc(symbol: &Symbol, arguments: &[Pattern], indent: usize) -> Doc {
    Doc::concat([
        symbol_doc(symbol, indent),
        delimited(
            "(",
            ")",
            arguments.iter().map(|pattern| pattern_doc(pattern, indent)),
            indent,
        ),
    ])
}

fn nullary_doc(name: &str, sort: &Sort, indent: usize) -> Doc {
    Doc::concat([
        Doc::text(format!("\\{name}{{")),
        sort_doc(sort, indent),
        Doc::text("}()"),
    ])
}

fn unary_doc(name: &str, sort: &Sort, argument: &Pattern, indent: usize) -> Doc {
    Doc::concat([
        Doc::text(format!("\\{name}{{")),
        sort_doc(sort, indent),
        Doc::text("}"),
        delimited(
            "(",
            ")",
            std::iter::once(pattern_doc(argument, indent)),
            indent,
        ),
    ])
    .group()
}

fn binary_doc(name: &str, sort: &Sort, left: &Pattern, right: &Pattern, indent: usize) -> Doc {
    Doc::concat([
        Doc::text(format!("\\{name}{{")),
        sort_doc(sort, indent),
        Doc::text("}"),
        delimited(
            "(",
            ")",
            [pattern_doc(left, indent), pattern_doc(right, indent)],
            indent,
        ),
    ])
    .group()
}

fn multiary_doc(name: &str, sort: &Sort, arguments: &[Pattern], indent: usize) -> Doc {
    Doc::concat([
        Doc::text(format!("\\{name}{{")),
        sort_doc(sort, indent),
        Doc::text("}"),
        delimited(
            "(",
            ")",
            arguments.iter().map(|pattern| pattern_doc(pattern, indent)),
            indent,
        ),
    ])
    .group()
}

fn quantifier_doc(
    name: &str,
    sort: &Sort,
    variable: &Variable,
    body: &Pattern,
    indent: usize,
) -> Doc {
    Doc::concat([
        Doc::text(format!("\\{name}{{")),
        sort_doc(sort, indent),
        Doc::text("}"),
        delimited(
            "(",
            ")",
            [variable_doc(variable, indent), pattern_doc(body, indent)],
            indent,
        ),
    ])
    .group()
}

fn fixpoint_doc(name: &str, variable: &Variable, body: &Pattern, indent: usize) -> Doc {
    Doc::concat([
        Doc::text(format!("\\{name}{{}}")),
        delimited(
            "(",
            ")",
            [variable_doc(variable, indent), pattern_doc(body, indent)],
            indent,
        ),
    ])
    .group()
}

fn round_predicate_doc(
    name: &str,
    operand_sort: &Sort,
    result_sort: &Sort,
    argument: &Pattern,
    indent: usize,
) -> Doc {
    Doc::concat([
        Doc::text(format!("\\{name}")),
        delimited(
            "{",
            "}",
            [
                sort_doc(operand_sort, indent),
                sort_doc(result_sort, indent),
            ],
            indent,
        ),
        delimited(
            "(",
            ")",
            std::iter::once(pattern_doc(argument, indent)),
            indent,
        ),
    ])
    .group()
}

fn binary_predicate_doc(
    name: &str,
    operand_sort: &Sort,
    result_sort: &Sort,
    left: &Pattern,
    right: &Pattern,
    indent: usize,
) -> Doc {
    Doc::concat([
        Doc::text(format!("\\{name}")),
        delimited(
            "{",
            "}",
            [
                sort_doc(operand_sort, indent),
                sort_doc(result_sort, indent),
            ],
            indent,
        ),
        delimited(
            "(",
            ")",
            [pattern_doc(left, indent), pattern_doc(right, indent)],
            indent,
        ),
    ])
    .group()
}

fn delimited(
    open: &str,
    close: &str,
    documents: impl IntoIterator<Item = Doc>,
    indent: usize,
) -> Doc {
    let documents: Vec<_> = documents.into_iter().collect();
    if documents.is_empty() {
        return Doc::text(format!("{open}{close}"));
    }

    Doc::concat([
        Doc::text(open),
        Doc::concat([
            Doc::line_break(),
            join(documents, Doc::concat([Doc::text(","), Doc::line()])),
        ])
        .nest(indent),
        Doc::line_break(),
        Doc::text(close),
    ])
    .group()
}

fn join(documents: Vec<Doc>, separator: Doc) -> Doc {
    let mut iterator = documents.into_iter();
    let Some(first) = iterator.next() else {
        return Doc::Nil;
    };
    let mut joined = vec![first];
    for document in iterator {
        joined.push(separator.clone());
        joined.push(document);
    }
    Doc::concat(joined)
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    macro_rules! assert_pattern_print_snapshot {
        ($code:expr) => {{
            let source = indoc! { $code };
            let pattern =
                $crate::kore::parser::parse_pattern(source).expect("pattern should parse");
            let printed = $crate::kore::printer::Printer::pretty(60).print_pattern(&pattern);
            let reparsed =
                $crate::kore::parser::parse_pattern(&printed).expect("printed pattern should parse");
            assert_eq!(reparsed, pattern);

            insta::with_settings!({
                description => format!("Input KORE pattern:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_snapshot!(printed);
            });
        }};
    }

    macro_rules! assert_definition_print_snapshot {
        ($code:expr) => {{
            let source = indoc! { $code };
            let definition =
                $crate::kore::parser::parse_definition(source).expect("definition should parse");
            let printed =
                $crate::kore::printer::Printer::pretty(80).print_definition(&definition);
            let reparsed = $crate::kore::parser::parse_definition(&printed)
                .expect("printed definition should parse");
            assert_eq!(reparsed, definition);

            insta::with_settings!({
                description => format!("Input KORE definition:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_snapshot!(printed);
            });
        }};
    }

    #[test]
    fn pretty_pattern() {
        assert_pattern_print_snapshot!(
            r#"
            \forall{SortBool{}}(
                X:SortInt{},
                \implies{SortBool{}}(
                    \equals{SortInt{}, SortBool{}}(X:SortInt{}, \dv{SortInt{}}("42")),
                    \top{SortBool{}}()
                )
            )
            "#
        );
    }

    #[test]
    fn pretty_definition() {
        assert_definition_print_snapshot!(
            r#"
            [source{}("printer-test")]

            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int")]
                hooked-symbol plus{}(SortInt{}, SortInt{}) : SortInt{} [hook{}("INT.add")]
                claim{}
                    \rewrites{SortInt{}}(plus{}(X:SortInt{}, \dv{SortInt{}}("0")), X:SortInt{})
                    [simplification{}()]
            endmodule []
            "#
        );
    }
}
