//! Canonical textual KAST printing.

use std::fmt::{self, Display, Formatter};

use super::ast::{Label, Sort, Term};
use super::names::InternalLabel;
use super::string;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Printer;

/// Why a term has no textual KAST that reads back as the same term.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unprintable {
    /// The textual format has no spelling for a variable's sort, so printing the variable would
    /// read back as the unsorted variable, which matches a different set of terms.
    SortedVariable { name: String, sort: Sort },
    /// The reader reads a variable only as `[_A-Z][A-Za-z0-9'_]*`, so any other name (a set
    /// variable's `@X`, for instance) would not read back.
    UnreadableVariableName { name: String },
    /// An application of the empty label would print as ` ``( `, which the reader takes as the
    /// opening of a group.
    EmptyApplicationLabel,
}

impl Display for Unprintable {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::SortedVariable { name, sort } => write!(
                formatter,
                "variable {name} has sort {}, which textual KAST cannot spell",
                print_sort(sort)
            ),
            Self::UnreadableVariableName { name } => write!(
                formatter,
                "variable name {name:?} is not readable as textual KAST, which spells a variable \
                 [_A-Z][A-Za-z0-9'_]*"
            ),
            Self::EmptyApplicationLabel => formatter
                .write_str("an application of the empty label is not readable as textual KAST"),
        }
    }
}

impl std::error::Error for Unprintable {}

impl Printer {
    pub const fn new() -> Self {
        Self
    }

    /// Print `term` as textual KAST for display.
    ///
    /// Rewrites, aliases and sequences are grouped so that the text reads back
    /// ([`crate::kast::parser::parse_term`]) as `term` up to sequence flattening and the
    /// identification of a one-item sequence with its item.
    /// The text is lossy for what the format cannot spell, which [`Printer::try_print_term`]
    /// refuses instead: a variable's sort is not written, and a variable name or an application
    /// label the reader cannot read is written as is.
    pub fn print_term(self, term: &Term) -> String {
        let mut output = String::new();
        print_term(&mut output, term, Layout::Readable, Position::TERM, false);
        output
    }

    /// Print `term` as the text a sentence identifier (`UNIQUE_ID`) is the digest of.
    ///
    /// An identifier names a sentence to whatever reads it later (another compilation of the same
    /// definition, a tool that refers to rules by identifier), so the text it digests is a fixed
    /// format of its own and does not follow [`Printer::print_term`]'s layout, which is free to
    /// change for readability. The identifier layout groups a rewrite or an alias only as an item
    /// of a sequence of two or more items, and never groups a sequence; the text is not read back.
    pub fn print_identifier_term(self, term: &Term) -> String {
        let mut output = String::new();
        print_term(&mut output, term, Layout::Identifier, Position::TERM, false);
        output
    }

    /// Print `term` as textual KAST that reads back as `term`, up to sequence flattening and the
    /// identification of a one-item sequence with its item, or say why no such text exists.
    pub fn try_print_term(self, term: &Term) -> Result<String, Unprintable> {
        if let Some(unprintable) = first_unprintable(term) {
            return Err(unprintable);
        }
        Ok(self.print_term(term))
    }

    pub fn print_sort(self, sort: &Sort) -> String {
        print_sort(sort)
    }

    pub fn print_label(self, label: &Label) -> String {
        print_label(label, false)
    }
}

fn first_unprintable(term: &Term) -> Option<Unprintable> {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        match term.unannotated() {
            Term::Variable { name, sort } => {
                if !is_readable_variable_name(name) {
                    return Some(Unprintable::UnreadableVariableName { name: name.clone() });
                }
                if let Some(sort) = sort {
                    return Some(Unprintable::SortedVariable {
                        name: name.clone(),
                        sort: sort.clone(),
                    });
                }
            }
            Term::Apply { label, .. } if label.name.is_empty() => {
                return Some(Unprintable::EmptyApplicationLabel);
            }
            _ => {}
        }
        pending.extend(term.children().into_iter().rev());
    }
    None
}

/// Whether the reader reads `name` back as one variable: `[_A-Z][A-Za-z0-9'_]*`.
fn is_readable_variable_name(name: &str) -> bool {
    name.as_bytes().split_first().is_some_and(|(first, rest)| {
        (*first == b'_' || first.is_ascii_uppercase())
            && rest
                .iter()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'\'' | b'_'))
    })
}

/// Which text a term is printed as.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Layout {
    /// Text that reads back as the term ([`Printer::print_term`]).
    Readable,
    /// The fixed text sentence identifiers digest ([`Printer::print_identifier_term`]): an
    /// operand of `=>` or `#as` is printed as at the top, a one-item sequence as its item at a
    /// sequence item's position, and a sequence is never grouped.
    Identifier,
}

impl Layout {
    /// The position of an operand of `=>` or `#as` that the readable layout prints at `readable`.
    const fn operand(self, readable: Position) -> Position {
        match self {
            Self::Readable => readable,
            Self::Identifier => Position::TERM,
        }
    }

    /// The position of the item of a one-item sequence printed at `position`.
    const fn sole_item(self, position: Position) -> Position {
        match self {
            Self::Readable => position.with_sequence_item(),
            Self::Identifier => Position::SEQUENCE_ITEM,
        }
    }

    /// Whether a sequence of two or more items printed at `position` is grouped.
    const fn groups_sequence(self, position: Position) -> bool {
        match self {
            Self::Readable => position.groups_sequence,
            Self::Identifier => false,
        }
    }
}

/// The reader nonterminal that reads the text printed at a position, as the shapes it cannot
/// derive without a ` `` ` group.
///
/// The reader's grammar is
///
/// ```text
/// term          ::= rewrite_or_as ('~>' rewrite_or_as)*
/// rewrite_or_as ::= atom (('=>' | '#as') rewrite_or_as)?
/// atom          ::= '``' term '``' | '.K' | '#token(...)' | '#klabel(...)' | variable | label '(' args ')'
/// ```
///
/// A sequence of two or more items is a `term` and not a `rewrite_or_as`, and a rewrite or alias
/// is a `rewrite_or_as` and not an `atom`; printed bare where the reader expects the narrower
/// nonterminal, the text would read back with its operands regrouped
/// (`(a ~> b) => c` as `a ~> (b => c)`, `(a => b) => c` as `a => (b => c)`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Position {
    /// A sequence of two or more items is grouped here.
    groups_sequence: bool,
    /// A rewrite or an alias is grouped here.
    groups_rewrite_or_as: bool,
}

impl Position {
    /// `term`: the whole text, an argument, the inside of a group.
    const TERM: Self = Self {
        groups_sequence: false,
        groups_rewrite_or_as: false,
    };
    /// An item of a sequence of two or more items, read as `rewrite_or_as`.
    /// A rewrite or alias item is grouped although the reader would derive it bare: K writes
    /// `~>` tighter than `=>`, so a bare `a=>b~>c` would mislead a reader of the text into
    /// `a => (b ~> c)`, which the grouping rules out.
    const SEQUENCE_ITEM: Self = Self {
        groups_sequence: false,
        groups_rewrite_or_as: true,
    };
    /// The right operand of `=>` or `#as`, read as `rewrite_or_as`; rewrites and aliases nest to
    /// the right bare.
    const OPERATOR_RIGHT: Self = Self {
        groups_sequence: true,
        groups_rewrite_or_as: false,
    };
    /// The left operand of `=>` or `#as`, read as `atom`.
    const OPERATOR_LEFT: Self = Self {
        groups_sequence: true,
        groups_rewrite_or_as: true,
    };

    /// The position of the item of a one-item sequence printed here: the text must read back as
    /// the item at this position, and it is printed as a sequence item would be.
    const fn with_sequence_item(self) -> Self {
        Self {
            groups_sequence: self.groups_sequence || Self::SEQUENCE_ITEM.groups_sequence,
            groups_rewrite_or_as: self.groups_rewrite_or_as
                || Self::SEQUENCE_ITEM.groups_rewrite_or_as,
        }
    }
}

// stack-accepted(kast-printer): one level per term level; about 85,000 levels print on 8 MiB in a release build, deeper than any term worth reading as KAST text. See docs/backend-port.md#stack-bounds.
fn print_term(
    output: &mut String,
    term: &Term,
    layout: Layout,
    position: Position,
    first_in_group: bool,
) {
    match term.unannotated() {
        Term::Token { token, sort } => {
            output.push_str("#token(");
            output.push_str(&string::quote(token));
            output.push(',');
            output.push_str(&string::quote(&print_sort(sort)));
            output.push(')');
        }
        Term::InjectedLabel(label) => {
            output.push_str("#klabel(");
            output.push_str(&print_label(label, false));
            output.push(')');
        }
        Term::Variable { name, .. } => output.push_str(name),
        Term::Apply { label, arguments } => {
            output.push_str(&print_label(label, first_in_group));
            output.push('(');
            if arguments.is_empty() {
                output.push_str(".KList");
            } else {
                for (index, argument) in arguments.iter().enumerate() {
                    if index != 0 {
                        output.push(',');
                    }
                    print_term(output, argument, layout, Position::TERM, false);
                }
            }
            output.push(')');
        }
        Term::Sequence(items) if items.is_empty() => output.push_str(".K"),
        Term::Sequence(items) if items.len() == 1 => {
            print_term(
                output,
                &items[0],
                layout,
                layout.sole_item(position),
                first_in_group,
            );
        }
        Term::Sequence(items) => {
            let grouped = layout.groups_sequence(position);
            if grouped {
                output.push_str("``");
            }
            for (index, item) in items.iter().enumerate() {
                if index != 0 {
                    output.push_str("~>");
                }
                print_term(
                    output,
                    item,
                    layout,
                    Position::SEQUENCE_ITEM,
                    index == 0 && (grouped || first_in_group),
                );
            }
            if grouped {
                output.push_str("``");
            }
        }
        Term::Rewrite { left, right } => {
            print_operator(output, left, "=>", right, layout, position, first_in_group);
        }
        Term::As { pattern, alias } => {
            print_operator(
                output,
                pattern,
                " #as ",
                alias,
                layout,
                position,
                first_in_group,
            );
        }
        Term::Annotated { .. } => unreachable!(),
    }
}

fn print_operator(
    output: &mut String,
    left: &Term,
    operator: &str,
    right: &Term,
    layout: Layout,
    position: Position,
    first_in_group: bool,
) {
    let grouped = position.groups_rewrite_or_as;
    if grouped {
        output.push_str("``");
    }
    print_term(
        output,
        left,
        layout,
        layout.operand(Position::OPERATOR_LEFT),
        grouped || first_in_group,
    );
    output.push_str(operator);
    print_term(
        output,
        right,
        layout,
        layout.operand(Position::OPERATOR_RIGHT),
        false,
    );
    if grouped {
        output.push_str("``");
    }
}

fn print_sort(sort: &Sort) -> String {
    let mut output = sort.name.clone();
    if !sort.parameters.is_empty() {
        output.push('{');
        for (index, parameter) in sort.parameters.iter().enumerate() {
            if index != 0 {
                output.push(',');
            }
            output.push_str(&print_sort(parameter));
        }
        output.push('}');
    }
    output
}

fn print_label(label: &Label, first_in_group: bool) -> String {
    let simple = label
        .name
        .as_bytes()
        .split_first()
        .is_some_and(|(first, rest)| {
            (*first == b'#' || first.is_ascii_lowercase())
                && rest.iter().all(u8::is_ascii_alphanumeric)
        })
        && !label.is(InternalLabel::Token)
        && !label.is(InternalLabel::KLabel);
    let mut output = if simple {
        label.name.clone()
    } else {
        let quoted = string::quote_label(&label.name);
        if first_in_group {
            format!(" {quoted}")
        } else {
            quoted
        }
    };
    if !label.parameters.is_empty() {
        output.push('{');
        for (index, parameter) in label.parameters.iter().enumerate() {
            if index != 0 {
                output.push(',');
            }
            output.push_str(&print_sort(parameter));
        }
        output.push('}');
    }
    output
}

#[cfg(test)]
mod tests {
    use super::{Printer, Unprintable};
    use crate::kast::ast::{Label, Sort, Term};
    use crate::kast::parser::parse_term;

    fn rewrite(left: Term, right: Term) -> Term {
        Term::Rewrite {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn alias(pattern: Term, alias: Term) -> Term {
        Term::As {
            pattern: Box::new(pattern),
            alias: Box::new(alias),
        }
    }

    fn seq<const N: usize>(items: [Term; N]) -> Term {
        Term::Sequence(items.into())
    }

    fn var(name: &str) -> Term {
        Term::variable(name)
    }

    /// Each term prints as the given text, and the text reads back as the term.
    #[track_caller]
    fn assert_prints_and_reads_back(cases: &[(Term, &str)]) {
        for (term, text) in cases {
            let printed = Printer::new().print_term(term);
            assert_eq!(printed, *text, "{term:?}");
            assert_eq!(parse_term(&printed).as_ref(), Ok(term), "{printed}");
        }
    }

    // Each pair below is two terms the reader tells apart (a rewrite or alias nested on the left
    // against the same nesting on the right, a sequence as an operand against an operator as a
    // sequence item); the pair must print as two texts, each reading back as its own term.
    #[test]
    fn groups_a_sequence_operand_of_a_rewrite_or_alias() {
        assert_prints_and_reads_back(&[
            (rewrite(seq([var("A"), var("B")]), var("C")), "``A~>B``=>C"),
            (seq([var("A"), rewrite(var("B"), var("C"))]), "A~>``B=>C``"),
            (rewrite(var("A"), seq([var("B"), var("C")])), "A=>``B~>C``"),
            (seq([rewrite(var("A"), var("B")), var("C")]), "``A=>B``~>C"),
            (alias(var("A"), seq([var("B"), var("C")])), "A #as ``B~>C``"),
            (seq([alias(var("A"), var("B")), var("C")]), "``A #as B``~>C"),
            (
                rewrite(seq([var("X"), var("K")]), seq([var("Y"), var("K")])),
                "``X~>K``=>``Y~>K``",
            ),
        ]);
    }

    #[test]
    fn groups_a_rewrite_or_alias_on_the_left_of_a_rewrite_or_alias() {
        assert_prints_and_reads_back(&[
            (
                rewrite(rewrite(var("A"), var("B")), var("C")),
                "``A=>B``=>C",
            ),
            (rewrite(var("A"), rewrite(var("B"), var("C"))), "A=>B=>C"),
            (
                rewrite(alias(var("A"), var("B")), var("C")),
                "``A #as B``=>C",
            ),
            (alias(var("A"), rewrite(var("B"), var("C"))), "A #as B=>C"),
            (
                alias(rewrite(var("A"), var("B")), var("C")),
                "``A=>B`` #as C",
            ),
            (rewrite(var("A"), alias(var("B"), var("C"))), "A=>B #as C"),
            (
                alias(alias(var("A"), var("B")), var("C")),
                "``A #as B`` #as C",
            ),
            (alias(var("A"), alias(var("B"), var("C"))), "A #as B #as C"),
        ]);
    }

    #[test]
    fn prints_a_one_item_sequence_as_its_item_where_the_item_stands() {
        let inner = seq([var("A"), var("B")]);
        assert_eq!(
            Printer::new().print_term(&rewrite(seq([inner.clone()]), var("C"))),
            "``A~>B``=>C"
        );
        assert_eq!(
            Printer::new().print_term(&rewrite(var("C"), seq([inner]))),
            "C=>``A~>B``"
        );
        assert_eq!(
            Printer::new().print_term(&seq([rewrite(var("A"), var("B"))])),
            "``A=>B``"
        );
    }

    /// The identifier text is a fixed format: a rewrite or alias is grouped only as an item of a
    /// sequence, and a sequence or an operator operand is never grouped, so the identifiers of
    /// rules whose rewrites have sequence sides do not move with the readable layout.
    #[test]
    fn prints_the_identifier_text_in_its_own_layout() {
        let plus = Term::apply("_+_", Vec::new());
        let cases = [
            (
                rewrite(seq([var("X"), var("K")]), seq([var("Y"), var("K")])),
                "X~>K=>Y~>K",
            ),
            (seq([rewrite(var("A"), var("B")), var("C")]), "``A=>B``~>C"),
            (seq([var("A"), rewrite(var("B"), var("C"))]), "A~>``B=>C``"),
            (seq([rewrite(var("A"), var("B"))]), "``A=>B``"),
            (
                rewrite(seq([seq([var("A"), var("B")])]), var("C")),
                "A~>B=>C",
            ),
            (rewrite(alias(var("P"), var("V")), var("R")), "P #as V=>R"),
            (alias(var("A"), seq([var("B"), var("C")])), "A #as B~>C"),
            (rewrite(rewrite(var("A"), var("B")), var("C")), "A=>B=>C"),
            (
                seq([alias(plus.clone(), var("B")), var("C")]),
                "`` `_+_`(.KList) #as B``~>C",
            ),
            (
                Term::apply("f", vec![rewrite(seq([plus, var("B")]), var("C"))]),
                "f(`_+_`(.KList)~>B=>C)",
            ),
        ];
        for (term, text) in cases {
            assert_eq!(
                Printer::new().print_identifier_term(&term),
                text,
                "{term:?}"
            );
        }
    }

    #[test]
    fn separates_a_quoted_label_from_the_group_it_opens() {
        let plus = Term::apply("_+_", Vec::new());
        assert_prints_and_reads_back(&[
            (
                rewrite(seq([plus.clone(), var("B")]), var("C")),
                "`` `_+_`(.KList)~>B``=>C",
            ),
            (
                rewrite(rewrite(plus.clone(), var("B")), var("C")),
                "`` `_+_`(.KList)=>B``=>C",
            ),
            (
                seq([alias(plus, var("B")), var("C")]),
                "`` `_+_`(.KList) #as B``~>C",
            ),
        ]);
    }

    #[test]
    fn refuses_what_textual_kast_cannot_spell() {
        let sorted = Term::Variable {
            name: "X".into(),
            sort: Some(Sort::new("Int")),
        };
        assert_eq!(
            Printer::new().try_print_term(&Term::apply("f", vec![sorted])),
            Err(Unprintable::SortedVariable {
                name: "X".into(),
                sort: Sort::new("Int"),
            })
        );
        for name in ["@X", "?X", "!X", "X:Int", "x", ""] {
            assert_eq!(
                Printer::new().try_print_term(&rewrite(var("Y"), var(name))),
                Err(Unprintable::UnreadableVariableName { name: name.into() }),
                "{name}"
            );
        }
        assert_eq!(
            Printer::new().try_print_term(&Term::apply("", Vec::new())),
            Err(Unprintable::EmptyApplicationLabel)
        );
        assert_eq!(
            Printer::new().try_print_term(&Term::InjectedLabel(Label::new(""))),
            Ok("#klabel(``)".into())
        );
        assert_eq!(
            Printer::new().try_print_term(&rewrite(seq([var("_X'1"), var("_")]), var("Y"))),
            Ok("``_X'1~>_``=>Y".into())
        );
    }

    #[test]
    fn prints_labels_that_begin_with_a_keyword_bare_and_reads_them_back() {
        assert_prints_and_reads_back(&[
            (Term::apply("#tokenize", vec![var("X")]), "#tokenize(X)"),
            (Term::apply("#klabelOf", Vec::new()), "#klabelOf(.KList)"),
        ]);
    }

    #[test]
    fn prints_backquoted_labels_and_sorted_tokens() {
        let term = Term::Apply {
            label: Label::new("_+Int_"),
            arguments: vec![
                Term::variable("X"),
                Term::Token {
                    token: "1".into(),
                    sort: Sort::new("Int"),
                },
            ],
        };
        assert_eq!(
            Printer::new().print_term(&term),
            r#"`_+Int_`(X,#token("1","Int"))"#
        );
    }
}
