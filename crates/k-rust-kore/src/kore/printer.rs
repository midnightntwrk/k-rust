//! ```toml algorithm
//! id = "kore.printer.build"
//! name = "construction of KORE pretty-print documents"
//! sites = ["definition_doc", "module_doc", "sentence_doc", "pattern_doc", "syntax_doc", "SyntaxOps::next", "Printer::print_definition", "Printer::print_module", "Printer::print_sentence", "Printer::print_pattern", "Printer::write_pattern", "attributes_doc", "declaration_pattern_doc", "delimited", "join", "expand"]
//! variable = "N = KORE syntax nodes; the Doc::concat, Doc::nest, and Doc::group wrappers around any op are bounded by a constant, because they wrap only the definition, module, sentence, sentence-body nest, and attribute-list delimited levels, while patterns, sorts, symbols, and variables are produced by the SyntaxOps task stack; Printer::write_pattern pulls those ops on demand from inside the render span, so its construction time is measured together with rendering"
//! counters = []
//! no_counter = "KORE document construction has no dedicated counter"
//! span = "per call"
//!
//! [[cost]]
//! mode = "one syntax tree"
//! bound = "O(N)"
//! ```
//!
//! KORE pretty printing produces a sequence of ops and renders it through `document::render`, which writes to an `io::Write` as it goes.
//! Building is O(N) over KORE syntax nodes: `SyntaxOps` emits each op of a pattern, sort, symbol, or variable once from an explicit task stack, scheduling fixed task sequences and delimited groups directly onto that stack, and the `Doc` combinators that copy ops (`concat`) or shift them (`nest`, `group`) wrap each op only in the fixed structural levels of definition, module, sentence, and attribute list, independent of pattern depth.
//! A pattern is printed by feeding `SyntaxOps` straight to the renderer (`Printer::write_pattern`), so neither its op sequence nor its text is held whole; `print_pattern` is the same path into a byte buffer.
//! Static syntax tokens borrow their text while generated names and quoted values own theirs; both yield the same text bytes to the renderer.
//! Definitions, modules, and sentences are built as a `Doc` first and then rendered by the same function.
//! Rendering decides each group's layout with a look-ahead bounded by the line width and writes every op once; no dedicated counter.
//!
//! Compact and width-aware textual KORE printing.

mod document;

use std::{
    borrow::Cow,
    fmt::{self, Display, Formatter},
    io,
};

use document::{Doc, Op, RenderMode, render};

use crate::measure::{self, Algorithm};

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

/// ```toml algorithm-site
/// id = "kore.printer.render"
/// role = "part"
/// sites = ["Printer::render"]
/// ```
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
        let _span = measure::algorithm_span(Algorithm::KorePrinterBuild);
        self.render(definition_doc(definition, self.options.indent))
    }

    pub fn print_module(self, module: &Module) -> String {
        let _span = measure::algorithm_span(Algorithm::KorePrinterBuild);
        self.render(module_doc(module, self.options.indent))
    }

    pub fn print_sentence(self, sentence: &Sentence) -> String {
        let _span = measure::algorithm_span(Algorithm::KorePrinterBuild);
        self.render(sentence_doc(sentence, self.options.indent))
    }

    pub fn print_pattern(self, pattern: &Pattern) -> String {
        let mut output = Vec::new();
        self.write_pattern(pattern, &mut output)
            .expect("writing to a Vec does not fail");
        String::from_utf8(output).expect("rendered ops are UTF-8 strings")
    }

    /// Write the text `print_pattern` returns to `output`, producing and rendering the pattern's
    /// ops one at a time: memory beyond the pattern itself is the syntax task stack, the render
    /// mode stack, and the bounded fits look-ahead, not the document or the text.
    pub fn write_pattern<W: io::Write + ?Sized>(
        self,
        pattern: &Pattern,
        output: &mut W,
    ) -> io::Result<()> {
        let _span = measure::algorithm_span(Algorithm::KorePrinterBuild);
        render(
            SyntaxOps::new(SyntaxTask::Pattern(pattern), self.options.indent),
            self.render_mode(),
            self.options.width,
            output,
        )
    }

    fn render(self, document: Doc) -> String {
        render_to_string(document, self.render_mode(), self.options.width)
    }

    const fn render_mode(self) -> RenderMode {
        match self.options.style {
            PrintStyle::Compact => RenderMode::Compact,
            PrintStyle::Pretty => RenderMode::Pretty,
        }
    }
}

fn render_to_string(document: Doc, mode: RenderMode, width: usize) -> String {
    let mut output = Vec::new();
    render(document.into_ops(), mode, width, &mut output).expect("writing to a Vec does not fail");
    String::from_utf8(output).expect("rendered ops are UTF-8 strings")
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
        formatter.write_str(&render_to_string(
            attributes_doc(self, PrintOptions::compact().indent),
            RenderMode::Compact,
            usize::MAX,
        ))
    }
}

impl Display for Sort {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&render_to_string(
            sort_doc(self, PrintOptions::compact().indent),
            RenderMode::Compact,
            usize::MAX,
        ))
    }
}

impl Display for Symbol {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&render_to_string(
            symbol_doc(self, PrintOptions::compact().indent),
            RenderMode::Compact,
            usize::MAX,
        ))
    }
}

impl Display for Variable {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(&render_to_string(
            variable_doc(self, PrintOptions::compact().indent),
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
    Text(Cow<'static, str>),
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
    Doc::from_ops(SyntaxOps::new(root, indent).collect())
}

/// The ops of one pattern, sort, symbol, or variable, in output order, produced on demand from
/// an explicit task stack.
struct SyntaxOps<'a> {
    stack: Vec<SyntaxTask<'a>>,
    indent: usize,
}

impl<'a> SyntaxOps<'a> {
    fn new(root: SyntaxTask<'a>, indent: usize) -> Self {
        Self {
            stack: vec![root],
            indent,
        }
    }
}

impl Iterator for SyntaxOps<'_> {
    type Item = Op;

    fn next(&mut self) -> Option<Op> {
        let indent = self.indent;
        let stack = &mut self.stack;
        // Invariant: the ops returned so far, followed by the ops of the tasks on `stack` taken
        // from top to bottom, are the root's ops in output order; each pop either returns one op
        // or replaces one syntax node or `Delimited` task by its children, so each node of the
        // root is expanded once.
        while let Some(task) = stack.pop() {
            match task {
                SyntaxTask::Text(text) => return Some(Op::Text(text)),
                SyntaxTask::Line(flat) => return Some(Op::Line(flat)),
                SyntaxTask::NestStart => return Some(Op::NestStart(indent)),
                SyntaxTask::NestEnd => return Some(Op::NestEnd(indent)),
                SyntaxTask::GroupStart => return Some(Op::GroupStart),
                SyntaxTask::GroupEnd => return Some(Op::GroupEnd),
                task => expand(stack, task),
            }
        }
        None
    }
}

/// Replace a syntax node or `Delimited` task by its children on `stack`, in reverse output order.
fn expand<'a>(stack: &mut Vec<SyntaxTask<'a>>, task: SyntaxTask<'a>) {
    fn push_grouped<'a, const N: usize>(
        stack: &mut Vec<SyntaxTask<'a>>,
        tasks: [SyntaxTask<'a>; N],
    ) {
        stack.push(SyntaxTask::GroupEnd);
        for task in tasks.into_iter().rev() {
            stack.push(task);
        }
        stack.push(SyntaxTask::GroupStart);
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

    match task {
        SyntaxTask::Text(_)
        | SyntaxTask::Line(_)
        | SyntaxTask::NestStart
        | SyntaxTask::NestEnd
        | SyntaxTask::GroupStart
        | SyntaxTask::GroupEnd => unreachable!("SyntaxOps::next returns leaf tasks as ops"),
        SyntaxTask::Delimited { open, close, items } => {
            if items.is_empty() {
                let text = match (open, close) {
                    ("{", "}") => Cow::Borrowed("{}"),
                    ("(", ")") => Cow::Borrowed("()"),
                    _ => Cow::Owned(format!("{open}{close}")),
                };
                stack.push(SyntaxTask::Text(text));
                return;
            }
            stack.push(SyntaxTask::GroupEnd);
            stack.push(SyntaxTask::Text(close.into()));
            stack.push(SyntaxTask::Line(""));
            stack.push(SyntaxTask::NestEnd);
            for (index, item) in items.into_iter().enumerate().rev() {
                stack.push(item);
                if index > 0 {
                    stack.push(SyntaxTask::Line(" "));
                    stack.push(SyntaxTask::Text(",".into()));
                }
            }
            stack.push(SyntaxTask::Line(""));
            stack.push(SyntaxTask::NestStart);
            stack.push(SyntaxTask::Text(open.into()));
            stack.push(SyntaxTask::GroupStart);
        }
        SyntaxTask::Sort(sort) => match sort {
            Sort::Variable(name) => stack.push(SyntaxTask::Text(name.clone().into())),
            Sort::Application { name, arguments } => {
                stack.push(delimited("{", "}", arguments.iter().map(SyntaxTask::Sort)));
                stack.push(SyntaxTask::Text(name.clone().into()));
            }
        },
        SyntaxTask::Symbol(symbol) => {
            stack.push(delimited(
                "{",
                "}",
                symbol.sort_parameters.iter().map(SyntaxTask::Sort),
            ));
            stack.push(SyntaxTask::Text(symbol.name.clone().into()));
        }
        SyntaxTask::Variable(variable) => {
            stack.push(SyntaxTask::Sort(&variable.sort));
            stack.push(SyntaxTask::Text(format!("{}:", variable.name).into()));
        }
        SyntaxTask::Pattern(pattern) => match pattern {
            Pattern::String(value) => stack.push(SyntaxTask::Text(string::quote(value).into())),
            Pattern::Variable(variable) => stack.push(SyntaxTask::Variable(variable)),
            Pattern::Application { symbol, arguments } => {
                stack.push(delimited(
                    "(",
                    ")",
                    arguments.iter().map(SyntaxTask::Pattern),
                ));
                stack.push(SyntaxTask::Symbol(symbol));
            }
            Pattern::Top { sort } => {
                stack.push(SyntaxTask::Text("}()".into()));
                stack.push(SyntaxTask::Sort(sort));
                stack.push(SyntaxTask::Text("\\top{".into()));
            }
            Pattern::Bottom { sort } => {
                stack.push(SyntaxTask::Text("}()".into()));
                stack.push(SyntaxTask::Sort(sort));
                stack.push(SyntaxTask::Text("\\bottom{".into()));
            }
            Pattern::And { sort, arguments } | Pattern::Or { sort, arguments } => {
                let name = if matches!(pattern, Pattern::And { .. }) {
                    "and"
                } else {
                    "or"
                };
                push_grouped(
                    stack,
                    [
                        SyntaxTask::Text(format!("\\{name}{{").into()),
                        SyntaxTask::Sort(sort),
                        SyntaxTask::Text("}".into()),
                        delimited("(", ")", arguments.iter().map(SyntaxTask::Pattern)),
                    ],
                );
            }
            Pattern::Not { sort, argument } | Pattern::Next { sort, argument } => {
                let name = if matches!(pattern, Pattern::Not { .. }) {
                    "not"
                } else {
                    "next"
                };
                push_grouped(
                    stack,
                    [
                        SyntaxTask::Text(format!("\\{name}{{").into()),
                        SyntaxTask::Sort(sort),
                        SyntaxTask::Text("}".into()),
                        delimited("(", ")", [SyntaxTask::Pattern(argument)]),
                    ],
                );
            }
            Pattern::Implies { sort, left, right }
            | Pattern::Iff { sort, left, right }
            | Pattern::Rewrites { sort, left, right } => {
                let name = match pattern {
                    Pattern::Implies { .. } => "implies",
                    Pattern::Iff { .. } => "iff",
                    _ => "rewrites",
                };
                push_grouped(
                    stack,
                    [
                        SyntaxTask::Text(format!("\\{name}{{").into()),
                        SyntaxTask::Sort(sort),
                        SyntaxTask::Text("}".into()),
                        delimited(
                            "(",
                            ")",
                            [SyntaxTask::Pattern(left), SyntaxTask::Pattern(right)],
                        ),
                    ],
                );
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
                push_grouped(
                    stack,
                    [
                        SyntaxTask::Text(format!("\\{name}{{").into()),
                        SyntaxTask::Sort(sort),
                        SyntaxTask::Text("}".into()),
                        delimited(
                            "(",
                            ")",
                            [SyntaxTask::Variable(variable), SyntaxTask::Pattern(body)],
                        ),
                    ],
                );
            }
            Pattern::Mu { variable, body } | Pattern::Nu { variable, body } => {
                let name = if matches!(pattern, Pattern::Mu { .. }) {
                    "mu"
                } else {
                    "nu"
                };
                push_grouped(
                    stack,
                    [
                        SyntaxTask::Text(format!("\\{name}{{}}").into()),
                        delimited(
                            "(",
                            ")",
                            [SyntaxTask::Variable(variable), SyntaxTask::Pattern(body)],
                        ),
                    ],
                );
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
                push_grouped(
                    stack,
                    [
                        SyntaxTask::Text(format!("\\{name}").into()),
                        delimited(
                            "{",
                            "}",
                            [
                                SyntaxTask::Sort(operand_sort),
                                SyntaxTask::Sort(result_sort),
                            ],
                        ),
                        delimited("(", ")", [SyntaxTask::Pattern(argument)]),
                    ],
                );
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
                push_grouped(
                    stack,
                    [
                        SyntaxTask::Text(format!("\\{name}").into()),
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
                    ],
                );
            }
            Pattern::DomainValue { sort, value } => {
                stack.push(SyntaxTask::Text(
                    format!("}}({})", string::quote(value)).into(),
                ));
                stack.push(SyntaxTask::Sort(sort));
                stack.push(SyntaxTask::Text("\\dv{".into()));
            }
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => {
                let name = match associativity {
                    Associativity::Left => "left-assoc",
                    Associativity::Right => "right-assoc",
                };
                push_grouped(
                    stack,
                    [
                        SyntaxTask::Text(format!("\\{name}{{}}(").into()),
                        SyntaxTask::Symbol(symbol),
                        delimited("(", ")", arguments.iter().map(SyntaxTask::Pattern)),
                        SyntaxTask::Text(")".into()),
                    ],
                );
            }
        },
    }
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
    use std::fmt::Write as _;

    use indoc::indoc;

    use super::{SyntaxOps, SyntaxTask};
    use crate::kore::ast::{Associativity, Pattern, Sort, Symbol, Variable, VariableKind};

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

    #[test]
    fn syntax_ops_preserve_each_constructors_op_order() {
        fn kind(pattern: &Pattern) -> &'static str {
            match pattern {
                Pattern::String(_) => "String",
                Pattern::Variable(_) => "Variable",
                Pattern::Application { .. } => "Application",
                Pattern::Top { .. } => "Top",
                Pattern::Bottom { .. } => "Bottom",
                Pattern::And { .. } => "And",
                Pattern::Or { .. } => "Or",
                Pattern::Not { .. } => "Not",
                Pattern::Next { .. } => "Next",
                Pattern::Implies { .. } => "Implies",
                Pattern::Iff { .. } => "Iff",
                Pattern::Rewrites { .. } => "Rewrites",
                Pattern::Exists { .. } => "Exists",
                Pattern::Forall { .. } => "Forall",
                Pattern::Mu { .. } => "Mu",
                Pattern::Nu { .. } => "Nu",
                Pattern::Ceil { .. } => "Ceil",
                Pattern::Floor { .. } => "Floor",
                Pattern::Equals { .. } => "Equals",
                Pattern::In { .. } => "In",
                Pattern::DomainValue { .. } => "DomainValue",
                Pattern::AssociativeApplication { .. } => "AssociativeApplication",
            }
        }

        let sort = || Sort::Application {
            name: "SortS".into(),
            arguments: vec![Sort::Variable("T".into())],
        };
        let element = || Variable {
            kind: VariableKind::Element,
            name: "X".into(),
            sort: sort(),
        };
        let set = || Variable {
            kind: VariableKind::Set,
            name: "@X".into(),
            sort: sort(),
        };
        let symbol = || Symbol {
            name: "f".into(),
            sort_parameters: vec![sort()],
        };
        let atom = || Pattern::String("a".into());
        let patterns = vec![
            Pattern::String("a".into()),
            Pattern::Variable(element()),
            Pattern::Application {
                symbol: symbol(),
                arguments: vec![atom(), atom()],
            },
            Pattern::Top { sort: sort() },
            Pattern::Bottom { sort: sort() },
            Pattern::And {
                sort: sort(),
                arguments: vec![atom(), atom()],
            },
            Pattern::Or {
                sort: sort(),
                arguments: vec![atom(), atom()],
            },
            Pattern::Not {
                sort: sort(),
                argument: Box::new(atom()),
            },
            Pattern::Next {
                sort: sort(),
                argument: Box::new(atom()),
            },
            Pattern::Implies {
                sort: sort(),
                left: Box::new(atom()),
                right: Box::new(atom()),
            },
            Pattern::Iff {
                sort: sort(),
                left: Box::new(atom()),
                right: Box::new(atom()),
            },
            Pattern::Rewrites {
                sort: sort(),
                left: Box::new(atom()),
                right: Box::new(atom()),
            },
            Pattern::Exists {
                sort: sort(),
                variable: element(),
                body: Box::new(atom()),
            },
            Pattern::Forall {
                sort: sort(),
                variable: element(),
                body: Box::new(atom()),
            },
            Pattern::Mu {
                variable: set(),
                body: Box::new(atom()),
            },
            Pattern::Nu {
                variable: set(),
                body: Box::new(atom()),
            },
            Pattern::Ceil {
                operand_sort: sort(),
                result_sort: sort(),
                argument: Box::new(atom()),
            },
            Pattern::Floor {
                operand_sort: sort(),
                result_sort: sort(),
                argument: Box::new(atom()),
            },
            Pattern::Equals {
                operand_sort: sort(),
                result_sort: sort(),
                left: Box::new(atom()),
                right: Box::new(atom()),
            },
            Pattern::In {
                operand_sort: sort(),
                result_sort: sort(),
                left: Box::new(atom()),
                right: Box::new(atom()),
            },
            Pattern::DomainValue {
                sort: sort(),
                value: "a".into(),
            },
            Pattern::AssociativeApplication {
                associativity: Associativity::Left,
                symbol: symbol(),
                arguments: vec![atom(), atom()],
            },
            Pattern::AssociativeApplication {
                associativity: Associativity::Right,
                symbol: symbol(),
                arguments: vec![atom(), atom()],
            },
        ];
        assert_eq!(patterns.len(), 23);

        let mut output = String::new();
        for pattern in &patterns {
            writeln!(
                output,
                "{}: {:?}",
                kind(pattern),
                SyntaxOps::new(SyntaxTask::Pattern(pattern), 2).collect::<Vec<_>>()
            )
            .unwrap();
        }
        let variable = element();
        let sort_variable = Sort::Variable("T".into());
        let sort_application = sort();
        let symbol = symbol();
        for (name, task) in [
            ("SortVariable", SyntaxTask::Sort(&sort_variable)),
            ("SortApplication", SyntaxTask::Sort(&sort_application)),
            ("Symbol", SyntaxTask::Symbol(&symbol)),
            ("VariableRoot", SyntaxTask::Variable(&variable)),
        ] {
            writeln!(
                output,
                "{name}: {:?}",
                SyntaxOps::new(task, 2).collect::<Vec<_>>()
            )
            .unwrap();
        }
        insta::assert_snapshot!(output);
    }

    mod streaming {
        use proptest::prelude::*;

        use super::super::{
            PrintOptions, Printer, document::RenderMode, document::whole_document_render,
            pattern_doc,
        };
        use crate::kore::ast::{Associativity, Pattern, Sort, Symbol, Variable, VariableKind};

        /// The printed text of `pattern` by the two-pass whole-document renderer, the oracle
        /// for the streaming path.
        fn whole_document(pattern: &Pattern, width: usize) -> String {
            whole_document_render(
                &pattern_doc(pattern, PrintOptions::pretty(width).indent),
                RenderMode::Pretty,
                width,
            )
        }

        fn streamed(pattern: &Pattern, width: usize) -> String {
            let mut output = Vec::new();
            Printer::pretty(width)
                .write_pattern(pattern, &mut output)
                .unwrap();
            String::from_utf8(output).unwrap()
        }

        // Short names make narrow patterns; long ones make single texts wider than the line.
        fn name() -> impl Strategy<Value = String> {
            prop_oneof![4 => "[A-C][a-c0-9']{0,3}", 1 => "[A-C][a-z]{30,110}"]
        }

        fn sort() -> impl Strategy<Value = Sort> {
            let leaf = prop_oneof![
                name().prop_map(Sort::Variable),
                name().prop_map(|name| Sort::Application {
                    name,
                    arguments: Vec::new(),
                }),
            ];
            leaf.prop_recursive(2, 6, 2, |inner| {
                (name(), prop::collection::vec(inner, 1..3))
                    .prop_map(|(name, arguments)| Sort::Application { name, arguments })
            })
        }

        fn symbol() -> impl Strategy<Value = Symbol> {
            (name(), prop::collection::vec(sort(), 0..3)).prop_map(|(name, sort_parameters)| {
                Symbol {
                    name,
                    sort_parameters,
                }
            })
        }

        fn variable(kind: VariableKind) -> impl Strategy<Value = Variable> {
            let prefix = match kind {
                VariableKind::Element => "",
                VariableKind::Set => "@",
            };
            (name(), sort()).prop_map(move |(name, sort)| Variable {
                kind,
                name: format!("{prefix}{name}"),
                sort,
            })
        }

        fn text() -> impl Strategy<Value = String> {
            prop_oneof![
                3 => "[a-b0-9 ]{0,8}",
                1 => prop::collection::vec(any::<char>(), 0..6).prop_map(String::from_iter),
                1 => "[a-z\\n\"]{80,160}",
            ]
        }

        /// Every pattern constructor, nested up to 24 levels.
        fn pattern() -> impl Strategy<Value = Pattern> {
            let leaf = prop_oneof![
                text().prop_map(|value| Pattern::String(value.into())),
                variable(VariableKind::Element).prop_map(Pattern::Variable),
                sort().prop_map(|sort| Pattern::Top { sort }),
                sort().prop_map(|sort| Pattern::Bottom { sort }),
                (sort(), text()).prop_map(|(sort, value)| Pattern::DomainValue {
                    sort,
                    value: value.into(),
                }),
            ];
            leaf.prop_recursive(24, 384, 4, |inner| {
                let boxed = || inner.clone().prop_map(Box::new);
                let list = |range| prop::collection::vec(inner.clone(), range);
                prop_oneof![
                    4 => (symbol(), list(0..4))
                        .prop_map(|(symbol, arguments)| Pattern::Application { symbol, arguments }),
                    1 => (sort(), list(0..3)).prop_map(|(sort, arguments)| Pattern::And { sort, arguments }),
                    1 => (sort(), list(0..3)).prop_map(|(sort, arguments)| Pattern::Or { sort, arguments }),
                    1 => (sort(), boxed()).prop_map(|(sort, argument)| Pattern::Not { sort, argument }),
                    1 => (sort(), boxed()).prop_map(|(sort, argument)| Pattern::Next { sort, argument }),
                    1 => (sort(), boxed(), boxed())
                        .prop_map(|(sort, left, right)| Pattern::Implies { sort, left, right }),
                    1 => (sort(), boxed(), boxed())
                        .prop_map(|(sort, left, right)| Pattern::Iff { sort, left, right }),
                    1 => (sort(), boxed(), boxed())
                        .prop_map(|(sort, left, right)| Pattern::Rewrites { sort, left, right }),
                    1 => (sort(), variable(VariableKind::Element), boxed()).prop_map(
                        |(sort, variable, body)| Pattern::Exists { sort, variable, body }
                    ),
                    1 => (sort(), variable(VariableKind::Element), boxed()).prop_map(
                        |(sort, variable, body)| Pattern::Forall { sort, variable, body }
                    ),
                    1 => (variable(VariableKind::Set), boxed())
                        .prop_map(|(variable, body)| Pattern::Mu { variable, body }),
                    1 => (variable(VariableKind::Set), boxed())
                        .prop_map(|(variable, body)| Pattern::Nu { variable, body }),
                    1 => (sort(), sort(), boxed()).prop_map(|(operand_sort, result_sort, argument)| {
                        Pattern::Ceil { operand_sort, result_sort, argument }
                    }),
                    1 => (sort(), sort(), boxed()).prop_map(|(operand_sort, result_sort, argument)| {
                        Pattern::Floor { operand_sort, result_sort, argument }
                    }),
                    1 => (sort(), sort(), boxed(), boxed()).prop_map(
                        |(operand_sort, result_sort, left, right)| Pattern::Equals {
                            operand_sort, result_sort, left, right,
                        }
                    ),
                    1 => (sort(), sort(), boxed(), boxed()).prop_map(
                        |(operand_sort, result_sort, left, right)| Pattern::In {
                            operand_sort, result_sort, left, right,
                        }
                    ),
                    1 => (
                        prop_oneof![Just(Associativity::Left), Just(Associativity::Right)],
                        symbol(),
                        list(1..3)
                    )
                        .prop_map(|(associativity, symbol, arguments)| {
                            Pattern::AssociativeApplication { associativity, symbol, arguments }
                        }),
                ]
            })
        }

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(512))]

            #[test]
            fn write_pattern_matches_whole_document_render(
                pattern in pattern(),
                width in prop_oneof![0usize..20, 20usize..130, Just(100usize)],
            ) {
                prop_assert_eq!(streamed(&pattern, width), whole_document(&pattern, width));
            }
        }

        /// A chain of applications nested far deeper than the line width allows to stay flat,
        /// with a wide sibling at every level, as in a large configuration.
        #[test]
        fn deeply_nested_pattern_matches_whole_document_render() {
            let sort = Sort::Application {
                name: "SortK".into(),
                arguments: Vec::new(),
            };
            let mut pattern = Pattern::DomainValue {
                sort: sort.clone(),
                value: "0".into(),
            };
            for level in 0..2_000 {
                let sibling = Pattern::DomainValue {
                    sort: sort.clone(),
                    value: "x".repeat(level % 150).into(),
                };
                pattern = Pattern::Application {
                    symbol: Symbol {
                        name: format!("Lbl{level}"),
                        sort_parameters: vec![sort.clone()],
                    },
                    arguments: if level % 2 == 0 {
                        vec![pattern, sibling]
                    } else {
                        vec![sibling, pattern]
                    },
                };
            }
            for width in [0, 40, 100, 100_000] {
                assert_eq!(streamed(&pattern, width), whole_document(&pattern, width));
            }
            assert_eq!(
                Printer::pretty(100).print_pattern(&pattern),
                whole_document(&pattern, 100)
            );
        }
    }
}
