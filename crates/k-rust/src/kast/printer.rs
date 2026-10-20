//! Canonical textual KAST printing.

use super::ast::{Label, Sort, Term};
use super::names::InternalLabel;
use super::string;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Printer;

impl Printer {
    pub const fn new() -> Self {
        Self
    }

    /// Print `term` as textual KAST for display.
    ///
    /// Rewrites, aliases and sequences are grouped so that the text reads back
    /// ([`crate::kast::parser::parse_term`]) as `term` up to sequence flattening and the
    /// identification of a one-item sequence with its item.
    /// The text is lossy for what the format cannot spell: a variable's sort is not written, and
    /// a variable name or an application label the reader cannot read is written as is.
    pub fn print_term(self, term: &Term) -> String {
        let mut output = String::new();
        print_term(&mut output, term, Position::TERM, false);
        output
    }

    pub fn print_sort(self, sort: &Sort) -> String {
        print_sort(sort)
    }

    pub fn print_label(self, label: &Label) -> String {
        print_label(label, false)
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
fn print_term(output: &mut String, term: &Term, position: Position, first_in_group: bool) {
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
                    print_term(output, argument, Position::TERM, false);
                }
            }
            output.push(')');
        }
        Term::Sequence(items) if items.is_empty() => output.push_str(".K"),
        Term::Sequence(items) if items.len() == 1 => {
            print_term(
                output,
                &items[0],
                position.with_sequence_item(),
                first_in_group,
            );
        }
        Term::Sequence(items) => {
            let grouped = position.groups_sequence;
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
                    Position::SEQUENCE_ITEM,
                    index == 0 && (grouped || first_in_group),
                );
            }
            if grouped {
                output.push_str("``");
            }
        }
        Term::Rewrite { left, right } => {
            print_operator(output, left, "=>", right, position, first_in_group);
        }
        Term::As { pattern, alias } => {
            print_operator(output, pattern, " #as ", alias, position, first_in_group);
        }
        Term::Annotated { .. } => unreachable!(),
    }
}

fn print_operator(
    output: &mut String,
    left: &Term,
    operator: &str,
    right: &Term,
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
        Position::OPERATOR_LEFT,
        grouped || first_in_group,
    );
    output.push_str(operator);
    print_term(output, right, Position::OPERATOR_RIGHT, false);
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
    use super::Printer;
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
