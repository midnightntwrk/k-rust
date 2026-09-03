//! Compact and width-aware textual KORE printing.

mod document;

use std::fmt::{self, Display, Formatter};

use document::{Doc, Op, RenderMode, render};

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
    syntax_doc(SyntaxTask::Sort(sort), indent)
}

fn symbol_doc(symbol: &Symbol, indent: usize) -> Doc {
    syntax_doc(SyntaxTask::Symbol(symbol), indent)
}

fn variable_doc(variable: &Variable, indent: usize) -> Doc {
    syntax_doc(SyntaxTask::Variable(variable), indent)
}

fn pattern_doc(pattern: &Pattern, indent: usize) -> Doc {
    syntax_doc(SyntaxTask::Pattern(pattern), indent)
}

enum SyntaxTask<'a> {
    Pattern(&'a Pattern),
    Sort(&'a Sort),
    Symbol(&'a Symbol),
    Variable(&'a Variable),
    Text(String),
    Line(&'static str),
    NestStart,
    NestEnd,
    GroupStart,
    GroupEnd,
    Delimited {
        open: &'static str,
        close: &'static str,
        items: Vec<Self>,
    },
}

fn syntax_doc(root: SyntaxTask<'_>, indent: usize) -> Doc {
    fn schedule<'a>(stack: &mut Vec<SyntaxTask<'a>>, tasks: Vec<SyntaxTask<'a>>) {
        stack.extend(tasks.into_iter().rev());
    }

    fn grouped<'a>(mut tasks: Vec<SyntaxTask<'a>>) -> Vec<SyntaxTask<'a>> {
        tasks.insert(0, SyntaxTask::GroupStart);
        tasks.push(SyntaxTask::GroupEnd);
        tasks
    }

    fn delimited<'a>(
        open: &'static str,
        close: &'static str,
        items: impl IntoIterator<Item = SyntaxTask<'a>>,
    ) -> SyntaxTask<'a> {
        SyntaxTask::Delimited {
            open,
            close,
            items: items.into_iter().collect(),
        }
    }

    let mut stack = vec![root];
    let mut ops = Vec::new();
    while let Some(task) = stack.pop() {
        match task {
            SyntaxTask::Text(text) => ops.push(Op::Text(text)),
            SyntaxTask::Line(flat) => ops.push(Op::Line(flat)),
            SyntaxTask::NestStart => ops.push(Op::NestStart(indent)),
            SyntaxTask::NestEnd => ops.push(Op::NestEnd(indent)),
            SyntaxTask::GroupStart => ops.push(Op::GroupStart),
            SyntaxTask::GroupEnd => ops.push(Op::GroupEnd),
            SyntaxTask::Delimited { open, close, items } => {
                if items.is_empty() {
                    ops.push(Op::Text(format!("{open}{close}")));
                    continue;
                }
                let mut tasks = vec![
                    SyntaxTask::GroupStart,
                    SyntaxTask::Text(open.into()),
                    SyntaxTask::NestStart,
                    SyntaxTask::Line(""),
                ];
                for (index, item) in items.into_iter().enumerate() {
                    if index > 0 {
                        tasks.push(SyntaxTask::Text(",".into()));
                        tasks.push(SyntaxTask::Line(" "));
                    }
                    tasks.push(item);
                }
                tasks.extend([
                    SyntaxTask::NestEnd,
                    SyntaxTask::Line(""),
                    SyntaxTask::Text(close.into()),
                    SyntaxTask::GroupEnd,
                ]);
                schedule(&mut stack, tasks);
            }
            SyntaxTask::Sort(sort) => match sort {
                Sort::Variable(name) => ops.push(Op::Text(name.clone())),
                Sort::Application { name, arguments } => schedule(
                    &mut stack,
                    vec![
                        SyntaxTask::Text(name.clone()),
                        delimited("{", "}", arguments.iter().map(SyntaxTask::Sort)),
                    ],
                ),
            },
            SyntaxTask::Symbol(symbol) => schedule(
                &mut stack,
                vec![
                    SyntaxTask::Text(symbol.name.clone()),
                    delimited(
                        "{",
                        "}",
                        symbol.sort_parameters.iter().map(SyntaxTask::Sort),
                    ),
                ],
            ),
            SyntaxTask::Variable(variable) => schedule(
                &mut stack,
                vec![
                    SyntaxTask::Text(format!("{}:", variable.name)),
                    SyntaxTask::Sort(&variable.sort),
                ],
            ),
            SyntaxTask::Pattern(pattern) => {
                let tasks = match pattern {
                    Pattern::String(value) => vec![SyntaxTask::Text(string::quote(value))],
                    Pattern::Variable(variable) => vec![SyntaxTask::Variable(variable)],
                    Pattern::Application { symbol, arguments } => vec![
                        SyntaxTask::Symbol(symbol),
                        delimited("(", ")", arguments.iter().map(SyntaxTask::Pattern)),
                    ],
                    Pattern::Top { sort } => vec![
                        SyntaxTask::Text("\\top{".into()),
                        SyntaxTask::Sort(sort),
                        SyntaxTask::Text("}()".into()),
                    ],
                    Pattern::Bottom { sort } => vec![
                        SyntaxTask::Text("\\bottom{".into()),
                        SyntaxTask::Sort(sort),
                        SyntaxTask::Text("}()".into()),
                    ],
                    Pattern::And { sort, arguments } | Pattern::Or { sort, arguments } => {
                        let name = if matches!(pattern, Pattern::And { .. }) {
                            "and"
                        } else {
                            "or"
                        };
                        grouped(vec![
                            SyntaxTask::Text(format!("\\{name}{{")),
                            SyntaxTask::Sort(sort),
                            SyntaxTask::Text("}".into()),
                            delimited("(", ")", arguments.iter().map(SyntaxTask::Pattern)),
                        ])
                    }
                    Pattern::Not { sort, argument } | Pattern::Next { sort, argument } => {
                        let name = if matches!(pattern, Pattern::Not { .. }) {
                            "not"
                        } else {
                            "next"
                        };
                        grouped(vec![
                            SyntaxTask::Text(format!("\\{name}{{")),
                            SyntaxTask::Sort(sort),
                            SyntaxTask::Text("}".into()),
                            delimited("(", ")", [SyntaxTask::Pattern(argument)]),
                        ])
                    }
                    Pattern::Implies { sort, left, right }
                    | Pattern::Iff { sort, left, right }
                    | Pattern::Rewrites { sort, left, right } => {
                        let name = match pattern {
                            Pattern::Implies { .. } => "implies",
                            Pattern::Iff { .. } => "iff",
                            _ => "rewrites",
                        };
                        grouped(vec![
                            SyntaxTask::Text(format!("\\{name}{{")),
                            SyntaxTask::Sort(sort),
                            SyntaxTask::Text("}".into()),
                            delimited(
                                "(",
                                ")",
                                [SyntaxTask::Pattern(left), SyntaxTask::Pattern(right)],
                            ),
                        ])
                    }
                    Pattern::Exists {
                        sort,
                        variable,
                        body,
                    }
                    | Pattern::Forall {
                        sort,
                        variable,
                        body,
                    } => {
                        let name = if matches!(pattern, Pattern::Exists { .. }) {
                            "exists"
                        } else {
                            "forall"
                        };
                        grouped(vec![
                            SyntaxTask::Text(format!("\\{name}{{")),
                            SyntaxTask::Sort(sort),
                            SyntaxTask::Text("}".into()),
                            delimited(
                                "(",
                                ")",
                                [SyntaxTask::Variable(variable), SyntaxTask::Pattern(body)],
                            ),
                        ])
                    }
                    Pattern::Mu { variable, body } | Pattern::Nu { variable, body } => {
                        let name = if matches!(pattern, Pattern::Mu { .. }) {
                            "mu"
                        } else {
                            "nu"
                        };
                        grouped(vec![
                            SyntaxTask::Text(format!("\\{name}{{}}")),
                            delimited(
                                "(",
                                ")",
                                [SyntaxTask::Variable(variable), SyntaxTask::Pattern(body)],
                            ),
                        ])
                    }
                    Pattern::Ceil {
                        operand_sort,
                        result_sort,
                        argument,
                    }
                    | Pattern::Floor {
                        operand_sort,
                        result_sort,
                        argument,
                    } => {
                        let name = if matches!(pattern, Pattern::Ceil { .. }) {
                            "ceil"
                        } else {
                            "floor"
                        };
                        grouped(vec![
                            SyntaxTask::Text(format!("\\{name}")),
                            delimited(
                                "{",
                                "}",
                                [
                                    SyntaxTask::Sort(operand_sort),
                                    SyntaxTask::Sort(result_sort),
                                ],
                            ),
                            delimited("(", ")", [SyntaxTask::Pattern(argument)]),
                        ])
                    }
                    Pattern::Equals {
                        operand_sort,
                        result_sort,
                        left,
                        right,
                    }
                    | Pattern::In {
                        operand_sort,
                        result_sort,
                        left,
                        right,
                    } => {
                        let name = if matches!(pattern, Pattern::Equals { .. }) {
                            "equals"
                        } else {
                            "in"
                        };
                        grouped(vec![
                            SyntaxTask::Text(format!("\\{name}")),
                            delimited(
                                "{",
                                "}",
                                [
                                    SyntaxTask::Sort(operand_sort),
                                    SyntaxTask::Sort(result_sort),
                                ],
                            ),
                            delimited(
                                "(",
                                ")",
                                [SyntaxTask::Pattern(left), SyntaxTask::Pattern(right)],
                            ),
                        ])
                    }
                    Pattern::DomainValue { sort, value } => vec![
                        SyntaxTask::Text("\\dv{".into()),
                        SyntaxTask::Sort(sort),
                        SyntaxTask::Text(format!("}}({})", string::quote(value))),
                    ],
                    Pattern::AssociativeApplication {
                        associativity,
                        symbol,
                        arguments,
                    } => {
                        let name = match associativity {
                            Associativity::Left => "left-assoc",
                            Associativity::Right => "right-assoc",
                        };
                        grouped(vec![
                            SyntaxTask::Text(format!("\\{name}{{}}(")),
                            SyntaxTask::Symbol(symbol),
                            delimited("(", ")", arguments.iter().map(SyntaxTask::Pattern)),
                            SyntaxTask::Text(")".into()),
                        ])
                    }
                };
                schedule(&mut stack, tasks);
            }
        }
    }
    Doc::from_ops(ops)
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
        return Doc::from_ops(Vec::new());
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
