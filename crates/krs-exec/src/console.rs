//! Console I/O for `run` (KF-035): the stdin stream's initial buffer, the stdout stream's final buffer, and the exit cell.
//!
//! `run` uses k-rust's buffered console semantics, as `krun --io off` does: standard input is the
//! initial `#buffer` of the `stream = "stdin"` cell, and console output is what the
//! `stream = "stdout"` cell's `#buffer` holds when the run ends. The request API performs no host
//! I/O (k-rust `docs/compatibility.md`), so nothing is written while the rules run.

use k_rust::kore::ast::{Pattern, Sort, Symbol};
use krs_ir::{CellAttribute, CellStream, FixedCell, FixedCellContent};
use krs_ir_levels::{DefinitionIr, DefinitionSentence};

/// The console cells a definition declares.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct ConsoleCells {
    /// A `stream = "stdin"` cell.
    pub(crate) stdin: bool,
    /// A `stream = "stdout"` cell.
    pub(crate) stdout: bool,
    /// An `exit` cell.
    pub(crate) exit: bool,
}

impl ConsoleCells {
    pub(crate) fn of(definition: &DefinitionIr) -> Self {
        let mut cells = Self::default();
        for module in definition.modules() {
            for sentence in module.sentences() {
                if let DefinitionSentence::Configuration(configuration) = sentence {
                    cells.visit(configuration.cells());
                }
            }
        }
        cells
    }

    fn visit<S, C>(&mut self, cells: &[FixedCell<S, C>]) {
        for cell in cells {
            for attribute in cell.attributes() {
                match attribute {
                    CellAttribute::Stream {
                        value: CellStream::Stdin,
                        ..
                    } => self.stdin = true,
                    CellAttribute::Stream {
                        value: CellStream::Stdout,
                        ..
                    } => self.stdout = true,
                    CellAttribute::Exit { .. } => self.exit = true,
                    CellAttribute::Color { .. }
                    | CellAttribute::Multiplicity { .. }
                    | CellAttribute::CollectionType { .. } => {}
                }
            }
            if let FixedCellContent::Children { children } = cell.content() {
                self.visit(children);
            }
        }
    }
}

/// The text krun buffers into `$STDIN` under `--io off`: every trailing newline is replaced by
/// exactly one, also for empty input, and every other byte is kept.
pub(crate) fn buffered_input(input: &[u8]) -> Vec<u8> {
    let kept = input
        .iter()
        .rposition(|byte| *byte != b'\n')
        .map_or(0, |index| index + 1);
    let mut buffered = input[..kept].to_vec();
    buffered.push(b'\n');
    buffered
}

/// The bytes the stdout stream cell's `#buffer` holds in `state`, as k-rust's captured output
/// reads them: a cell whose content is `ListItem(#ostream(1)) ListItem("off") ListItem(#buffer(S))`.
///
/// `None` when no cell has that shape, and also when more than one does.
pub(crate) fn stdout_buffer(state: &Pattern) -> Option<Vec<u8>> {
    let mut found = Vec::new();
    collect_stdout_buffers(state, &mut found);
    let mut buffers = found.into_iter();
    let buffer = buffers.next()?;
    buffers.next().is_none().then_some(buffer)
}

fn collect_stdout_buffers(pattern: &Pattern, found: &mut Vec<Vec<u8>>) {
    let arguments: &[Pattern] = match pattern {
        Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            if let Some(buffer) = stream_cell_buffer(&symbol.name, arguments) {
                found.push(buffer);
                return;
            }
            arguments
        }
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => arguments,
        _ => return,
    };
    for argument in arguments {
        collect_stdout_buffers(argument, found);
    }
}

fn stream_cell_buffer(symbol: &str, arguments: &[Pattern]) -> Option<Vec<u8>> {
    let [content] = arguments else {
        return None;
    };
    if !symbol.starts_with("Lbl'-LT-'") || !symbol.contains("'-GT-'") {
        return None;
    }
    let mut items = Vec::new();
    list_items(content, &mut items)?;
    let [descriptor, mode, buffer] = items.as_slice() else {
        return None;
    };
    let (name, [fd]) = application(descriptor)? else {
        return None;
    };
    if !name.starts_with("Lbl'Hash'ostream") || domain_value(fd, "SortInt")? != b"1" {
        return None;
    }
    if domain_value(mode, "SortString")? != b"off" {
        return None;
    }
    let (name, [sequence]) = application(buffer)? else {
        return None;
    };
    if !name.starts_with("Lbl'Hash'buffer") {
        return None;
    }
    let ("kseq", [item, end]) = application(sequence)? else {
        return None;
    };
    let ("dotk", []) = application(end)? else {
        return None;
    };
    domain_value(item, "SortString").map(<[u8]>::to_vec)
}

/// The items of a concatenation of `ListItem`s, or `None` for any other List term.
fn list_items<'a>(pattern: &'a Pattern, items: &mut Vec<&'a Pattern>) -> Option<()> {
    match uninjected(pattern) {
        Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        } if symbol.name == "Lbl'Unds'List'Unds'" => {
            for argument in arguments {
                list_items(argument, items)?;
            }
            Some(())
        }
        Pattern::Application { symbol, arguments } if symbol.name == "LblListItem" => {
            let [item] = arguments.as_slice() else {
                return None;
            };
            items.push(item);
            Some(())
        }
        _ => None,
    }
}

fn uninjected(mut pattern: &Pattern) -> &Pattern {
    while let Pattern::Application { symbol, arguments } = pattern
        && symbol.name == "inj"
        && let [inner] = arguments.as_slice()
    {
        pattern = inner;
    }
    pattern
}

fn application(pattern: &Pattern) -> Option<(&str, &[Pattern])> {
    match uninjected(pattern) {
        Pattern::Application { symbol, arguments } => {
            Some((symbol.name.as_str(), arguments.as_slice()))
        }
        _ => None,
    }
}

fn domain_value<'a>(pattern: &'a Pattern, sort_name: &str) -> Option<&'a [u8]> {
    match uninjected(pattern) {
        Pattern::DomainValue {
            sort: Sort::Application { name, arguments },
            value,
        } if name == sort_name && arguments.is_empty() => Some(value.as_bytes()),
        _ => None,
    }
}

/// `getExitCode(<generatedTop> .. </generatedTop>)`, the function k-rust generates for an exit
/// cell, applied to the configuration term of `state`.
pub(crate) fn exit_code_request(state: &Pattern) -> Option<Pattern> {
    let configuration = match state {
        Pattern::And { arguments, .. } => arguments.iter().find(|argument| {
            matches!(argument, Pattern::Application { symbol, .. } if symbol.name.starts_with("Lbl'-LT-'"))
        })?,
        Pattern::Application { .. } => state,
        _ => return None,
    };
    Some(Pattern::Application {
        symbol: Symbol {
            name: "LblgetExitCode".to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments: vec![configuration.clone()],
    })
}

/// The Int value of a simplified `getExitCode` application: the value itself when it fits an
/// `i64`, and otherwise its residue modulo 256 (the part the OS keeps).
pub(crate) fn exit_value(pattern: &Pattern) -> Option<i64> {
    let digits = match pattern {
        Pattern::And { arguments, .. } => arguments
            .iter()
            .find_map(|argument| domain_value(argument, "SortInt"))?,
        _ => domain_value(pattern, "SortInt")?,
    };
    let text = std::str::from_utf8(digits).ok()?;
    if let Ok(value) = text.parse::<i64>() {
        return Some(value);
    }
    let (negative, magnitude) = text
        .strip_prefix('-')
        .map_or((false, text), |rest| (true, rest));
    let mut residue = 0_i64;
    for digit in magnitude.bytes() {
        if !digit.is_ascii_digit() {
            return None;
        }
        residue = (residue * 10 + i64::from(digit - b'0')) % 256;
    }
    Some(if negative {
        (256 - residue) % 256
    } else {
        residue
    })
}

#[cfg(test)]
mod tests {
    use super::{buffered_input, exit_value, stdout_buffer};
    use k_rust::kore::parser::parse_pattern;

    #[test]
    fn buffered_input_keeps_exactly_one_trailing_newline() {
        assert_eq!(buffered_input(b"3\n4\n\n\n"), b"3\n4\n");
        assert_eq!(buffered_input(b"3\n4"), b"3\n4\n");
        assert_eq!(buffered_input(b""), b"\n");
    }

    #[test]
    fn stdout_buffer_reads_the_off_mode_stream_cell() {
        let cell = |fd: &str, mode: &str| {
            format!(
                r#"Lbl'-LT-'output'-GT-'{{}}(Lbl'Unds'List'Unds'{{}}(Lbl'Unds'List'Unds'{{}}(LblListItem{{}}(inj{{SortStream{{}}, SortKItem{{}}}}(Lbl'Hash'ostream'LParUndsRParUnds'K-IO'Unds'Stream'Unds'Int{{}}(\dv{{SortInt{{}}}}("{fd}")))), LblListItem{{}}(inj{{SortString{{}}, SortKItem{{}}}}(\dv{{SortString{{}}}}("{mode}")))), LblListItem{{}}(inj{{SortStream{{}}, SortKItem{{}}}}(Lbl'Hash'buffer'LParUndsRParUnds'K-IO'Unds'Stream'Unds'K{{}}(kseq{{}}(inj{{SortString{{}}, SortKItem{{}}}}(\dv{{SortString{{}}}}("7")), dotk{{}}()))))))"#
            )
        };
        let state = parse_pattern(&format!(
            "Lbl'-LT-'generatedTop'-GT-'{{}}({}, Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))",
            cell("1", "off")
        ))
        .unwrap();
        assert_eq!(stdout_buffer(&state).as_deref(), Some(&b"7"[..]));
        let interactive = parse_pattern(&cell("1", "on")).unwrap();
        assert_eq!(stdout_buffer(&interactive), None);
        let stderr = parse_pattern(&cell("2", "off")).unwrap();
        assert_eq!(stdout_buffer(&stderr), None);
    }

    #[test]
    fn exit_values_beyond_i64_keep_their_residue_modulo_256() {
        let value = |text: &str| {
            exit_value(&parse_pattern(&format!("\\dv{{SortInt{{}}}}(\"{text}\")")).unwrap())
        };
        assert_eq!(value("7"), Some(7));
        assert_eq!(value("-1"), Some(-1));
        assert_eq!(value("18446744073709551623"), Some(7));
        assert_eq!(value("-18446744073709551617"), Some(255));
        assert_eq!(
            exit_value(&parse_pattern("\\dv{SortString{}}(\"7\")").unwrap()),
            None
        );
    }
}
