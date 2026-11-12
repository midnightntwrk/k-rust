//! Console I/O for `run` (KF-035): the stdin stream's initial buffer, the stdout stream's final buffer, and the exit cell.
//!
//! `run` uses k-rust's buffered console semantics, as `krun --io off` does: standard input is the
//! initial `#buffer` of the `stream = "stdin"` cell, and console output is what the
//! `stream = "stdout"` cell's `#buffer` holds when the run ends. The request API performs no host
//! I/O (k-rust `docs/compatibility.md`), so nothing is written while the rules run.

use k_rust::backend::HeldState;
use k_rust::kore::ast::{Pattern, Sort, Symbol};
use k_rust::kore::node::{PatternNode, PatternSource, materialize};
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
                    | CellAttribute::CollectionType { .. }
                    | CellAttribute::Initial { .. }
                    | CellAttribute::Unobservable { .. } => {}
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

/// [`stdout_buffer`] of the pattern of `state`, read from the backend's state without building
/// the pattern.
///
/// The pattern's nodes are read in the order [`stdout_buffer`] reads them, and descended into
/// where it descends. A cell is built, alone, where its content may be a list of three items
/// ([`may_hold_three_items`]), which the stream cell's shape requires; the shape is then read on
/// the built cell as it is on the whole pattern, so every other cell, however long its list, is
/// read and not built.
pub(crate) fn stdout_buffer_held(state: &HeldState) -> Option<Vec<u8>> {
    let mut found = Vec::new();
    let mut pending = vec![state.source()];
    while let Some(source) = pending.pop() {
        let arguments = match source.node() {
            PatternNode::Application { symbol, arguments } => {
                if let [content] = arguments.as_slice()
                    && symbol.name.starts_with("Lbl'-LT-'")
                    && may_hold_three_items(*content)
                    && let Some(buffer) = match &materialize(source) {
                        Pattern::Application { symbol, arguments } => {
                            stream_cell_buffer(&symbol.name, arguments)
                        }
                        _ => None,
                    }
                {
                    found.push(buffer);
                    continue;
                }
                arguments
            }
            PatternNode::And { arguments, .. } | PatternNode::Or { arguments, .. } => arguments,
            _ => continue,
        };
        pending.extend(arguments.into_iter().rev());
    }
    let mut buffers = found.into_iter();
    let buffer = buffers.next()?;
    buffers.next().is_none().then_some(buffer)
}

/// Whether [`list_items`] of the pattern of `content` may give exactly three items: false only
/// where it gives another number or none. The items are counted as [`list_items`] finds them,
/// and the count stops past three, so a long list is not read to its end.
fn may_hold_three_items<'a, S: PatternSource<'a>>(content: S) -> bool {
    let mut items = 0_usize;
    let mut pending = vec![content];
    while let Some(mut source) = pending.pop() {
        // The pattern below its injections ([`uninjected`]).
        let node = loop {
            match source.node() {
                PatternNode::Application { symbol, arguments }
                    if symbol.name == "inj" && arguments.len() == 1 =>
                {
                    source = arguments.into_iter().next().expect("one argument");
                }
                node => break node,
            }
        };
        match node {
            PatternNode::Application { symbol, arguments }
                if symbol.name == "Lbl'Unds'List'Unds'" =>
            {
                pending.extend(arguments.into_iter().rev());
            }
            PatternNode::Application { symbol, arguments }
                if symbol.name == "LblListItem" && arguments.len() == 1 =>
            {
                items += 1;
                if items > 3 {
                    return false;
                }
            }
            _ => return false,
        }
    }
    items == 3
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

/// The function k-rust generates for an exit cell: the cell's value in a configuration.
pub(crate) const EXIT_CODE: &str = "LblgetExitCode";

/// Whether [`exit_code_request`] of the pattern of `state` applies [`EXIT_CODE`] to that whole
/// pattern: the pattern is an application, which the root node says without building it. A
/// state held by the backend has no constraints, so its pattern is its configuration.
pub(crate) fn exit_code_of_whole(state: &HeldState) -> bool {
    matches!(state.source().node(), PatternNode::Application { .. })
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
            name: EXIT_CODE.to_owned(),
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

    /// The count that decides whether a cell is built to read its stream shape is true of
    /// every list of three items, the stream cell's among them, and false of a list of another
    /// length, however long, and of what is no list of items.
    #[test]
    fn a_cell_is_built_only_where_its_content_may_be_three_items() {
        use super::may_hold_three_items;

        let item = |text: &str| {
            format!(
                r#"LblListItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{text}")))"#
            )
        };
        let list = |length: usize| {
            let mut items = (0..length).map(|index| item(&index.to_string()));
            let last = items
                .next_back()
                .unwrap_or_else(|| "Lbl'Stop'List{}()".to_owned());
            items.rfold(last, |rest, item| {
                format!("Lbl'Unds'List'Unds'{{}}({item}, {rest})")
            })
        };
        for (length, may) in [
            (0, false),
            (1, false),
            (2, false),
            (3, true),
            (4, false),
            (50, false),
        ] {
            let content = parse_pattern(&list(length)).unwrap();
            assert_eq!(may_hold_three_items(&content), may, "{length}");
        }
        let left_nested = parse_pattern(&format!(
            "Lbl'Unds'List'Unds'{{}}(Lbl'Unds'List'Unds'{{}}({}, {}), {})",
            item("0"),
            item("1"),
            item("2")
        ))
        .unwrap();
        assert!(may_hold_three_items(&left_nested));
        let injected =
            parse_pattern(&format!("inj{{SortList{{}}, SortKItem{{}}}}({})", list(3))).unwrap();
        assert!(may_hold_three_items(&injected));
        let no_list = parse_pattern(r#"\dv{SortInt{}}("3")"#).unwrap();
        assert!(!may_hold_three_items(&no_list));
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
