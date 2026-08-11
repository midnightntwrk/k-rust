//! Canonical textual KAST printing.

use super::ast::{Label, Sort, Term};
use super::string;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Printer;

impl Printer {
    pub const fn new() -> Self {
        Self
    }

    pub fn print_term(self, term: &Term) -> String {
        let mut output = String::new();
        print_term(&mut output, term, 0, false);
        output
    }

    pub fn print_sort(self, sort: &Sort) -> String {
        print_sort(sort)
    }

    pub fn print_label(self, label: &Label) -> String {
        print_label(label, false)
    }
}

fn print_term(output: &mut String, term: &Term, precedence: u8, first_in_group: bool) {
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
                    print_term(output, argument, 0, false);
                }
            }
            output.push(')');
        }
        Term::Sequence(items) if items.is_empty() => output.push_str(".K"),
        Term::Sequence(items) => {
            for (index, item) in items.iter().enumerate() {
                if index != 0 {
                    output.push_str("~>");
                }
                print_term(output, item, 2, index == 0 && first_in_group);
            }
        }
        Term::Rewrite { left, right } => {
            let grouped = precedence > 1;
            if grouped {
                output.push_str("``");
            }
            print_term(output, left, 1, grouped || first_in_group);
            output.push_str("=>");
            print_term(output, right, 1, false);
            if grouped {
                output.push_str("``");
            }
        }
        Term::As { pattern, alias } => {
            let grouped = precedence > 1;
            if grouped {
                output.push_str("``");
            }
            print_term(output, pattern, 1, grouped || first_in_group);
            output.push_str(" #as ");
            print_term(output, alias, 1, false);
            if grouped {
                output.push_str("``");
            }
        }
        Term::Annotated { .. } => unreachable!(),
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
        && label.name != "#token"
        && label.name != "#klabel";
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

    #[test]
    fn matches_reference_spelling() {
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
