//! KORE of collection and data-sort values, and values read back from KORE (ARCHITECTURE 2.3,
//! 2.6, 3). Owner: FZ-09 and FZ-G6.
//!
//! The KORE of a value is the pattern the configuration assembler builds when it reads the
//! value's K text ([`super::text::TextSyntax::parse`]):
//!
//! - an element of a collection is injected to the element symbol's argument sort
//!   (`ListItem(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")))`);
//! - a collection of several elements is the concatenation of its elements nested to the left,
//!   as the frontend parses the juxtaposition of the printed elements (`_List_` is
//!   left-associative), and the empty collection is the unit;
//! - a constructor's data argument is injected from the argument value's own sort (the result
//!   sort of its constructor, or the sort of a builtin subsort) to the argument's declared sort;
//! - a data hole's value is at its own sort: the injection above it is its position's (the
//!   assembler injects a value directly to the sort its position needs).

use k_rust::{
    kast::parser::parse_sort,
    kompile::encode_kore_sort,
    kore::ast::{Pattern as KorePattern, Sort as KoreSort, Symbol as KoreSymbol},
    names::{BuiltinSort, MINT_SORT},
};
use num_bigint::BigInt;

use super::{
    ArgumentSort, CollectionKind, CollectionSymbols, DataAlternative, DataSorts, MAX_VALUE_DEPTH,
    Value, ValueSort, check_data,
    print::{PrintError, parse_int, parse_mint, to_kore},
};

/// The KORE sort without arguments named `name`.
pub(super) fn simple_sort(name: &str) -> KoreSort {
    KoreSort::Application {
        name: name.to_owned(),
        arguments: Vec::new(),
    }
}

fn application(symbol: &str, arguments: Vec<KorePattern>) -> KorePattern {
    KorePattern::Application {
        symbol: KoreSymbol {
            name: symbol.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments,
    }
}

/// `pattern`, of sort `from`, at sort `to`: itself when the sorts are equal, its injection
/// otherwise.
pub(crate) fn inject(pattern: KorePattern, from: &KoreSort, to: &KoreSort) -> KorePattern {
    if from == to {
        return pattern;
    }
    KorePattern::Application {
        symbol: KoreSymbol {
            name: "inj".to_owned(),
            sort_parameters: vec![from.clone(), to.clone()],
        },
        arguments: vec![pattern],
    }
}

/// `pattern` without the injections around it.
fn uninject(mut pattern: &KorePattern) -> &KorePattern {
    while let KorePattern::Application { symbol, arguments } = pattern
        && symbol.name == "inj"
        && arguments.len() == 1
    {
        pattern = &arguments[0];
    }
    pattern
}

/// The KORE of `value` at `sort`, and the KORE sort of that pattern (the value's own sort; for a
/// data value, the result sort of its constructor or the sort of its subsort).
pub(super) fn kore_of(
    value: &Value,
    sort: &ValueSort,
) -> Result<(KorePattern, KoreSort), PrintError> {
    match sort {
        ValueSort::List { symbols, .. }
        | ValueSort::Set { symbols, .. }
        | ValueSort::Map { symbols, .. } => {
            Ok((collection(value, sort)?, simple_sort(&symbols.kore_sort)))
        }
        ValueSort::Data { table, .. } => data(value, table, 0),
        _ => {
            let pattern = to_kore(value, sort)?;
            let KorePattern::DomainValue { sort, .. } = &pattern else {
                unreachable!("a builtin value is a domain value");
            };
            let sort = sort.clone();
            Ok((pattern, sort))
        }
    }
}

/// The KORE of a collection value.
fn collection(value: &Value, sort: &ValueSort) -> Result<KorePattern, PrintError> {
    let element =
        |item: &Value, item_sort: &ValueSort, argument: usize, symbols: &CollectionSymbols| {
            let (pattern, own) = kore_of(item, item_sort)?;
            let declared = symbols
                .element_arguments
                .get(argument)
                .ok_or(PrintError::SortMismatch)?;
            Ok::<_, PrintError>(inject(pattern, &own, &simple_sort(declared)))
        };
    let (symbols, items) = match (value, sort) {
        (
            Value::List(items),
            ValueSort::List {
                symbols,
                element: item_sort,
                ..
            },
        )
        | (
            Value::Set(items),
            ValueSort::Set {
                symbols,
                element: item_sort,
                ..
            },
        ) => (
            symbols,
            items
                .iter()
                .map(|item| {
                    Ok(application(
                        &symbols.element,
                        vec![element(item, item_sort, 0, symbols)?],
                    ))
                })
                .collect::<Result<Vec<_>, PrintError>>()?,
        ),
        (
            Value::Map(entries),
            ValueSort::Map {
                symbols,
                key,
                value: value_sort,
                ..
            },
        ) => (
            symbols,
            entries
                .iter()
                .map(|(entry_key, entry_value)| {
                    Ok(application(
                        &symbols.element,
                        vec![
                            element(entry_key, key, 0, symbols)?,
                            element(entry_value, value_sort, 1, symbols)?,
                        ],
                    ))
                })
                .collect::<Result<Vec<_>, PrintError>>()?,
        ),
        _ => return Err(PrintError::SortMismatch),
    };
    Ok(concatenation(symbols, items))
}

/// The unit for no items, the item itself for one, and the left-nested concatenation otherwise.
fn concatenation(symbols: &CollectionSymbols, items: Vec<KorePattern>) -> KorePattern {
    items
        .into_iter()
        .reduce(|left, right| application(&symbols.concat, vec![left, right]))
        .unwrap_or_else(|| application(&symbols.unit, Vec::new()))
}

/// The KORE of a value of entry `index` of `table`, and its own sort.
fn data(
    value: &Value,
    table: &DataSorts,
    index: usize,
) -> Result<(KorePattern, KoreSort), PrintError> {
    match check_data(value, table, index).map_err(|_| PrintError::SortMismatch)? {
        DataAlternative::Constructor(constructor) => {
            let Value::Apply { arguments, .. } = value else {
                unreachable!("a constructor alternative is an application");
            };
            let arguments = constructor
                .arguments
                .iter()
                .zip(arguments)
                .map(|(sort, argument)| argument_kore(argument, sort, table, true))
                .collect::<Result<Vec<_>, _>>()?;
            Ok((
                application(&constructor.symbol, arguments),
                simple_sort(&constructor.result_kore_sort),
            ))
        }
        DataAlternative::Subsort(subsort) => {
            let pattern = argument_kore(value, subsort, table, false)?;
            let own = match subsort {
                ArgumentSort::Value(sort) => kore_of(value, sort)?.1,
                ArgumentSort::Empty(empty) => simple_sort(&empty.symbols.kore_sort),
                ArgumentSort::Data(_) => unreachable!("a subsort alternative is not data"),
            };
            Ok((pattern, own))
        }
    }
}

/// The KORE of `value` as a value of the argument sort `sort`; a data argument is injected to
/// its entry's sort when `inject_data` holds.
fn argument_kore(
    value: &Value,
    sort: &ArgumentSort,
    table: &DataSorts,
    inject_data: bool,
) -> Result<KorePattern, PrintError> {
    match sort {
        ArgumentSort::Value(sort) => Ok(kore_of(value, sort)?.0),
        ArgumentSort::Empty(empty) => Ok(application(&empty.symbols.unit, Vec::new())),
        ArgumentSort::Data(index) => {
            let (pattern, own) = data(value, table, *index)?;
            Ok(if inject_data {
                inject(pattern, &own, &simple_sort(&table.sorts[*index].kore_sort))
            } else {
                pattern
            })
        }
    }
}

/// The value of `sort` whose KORE is `pattern` (injections around it are ignored): the inverse
/// of [`kore_of`], which reads collections of any nesting.
///
/// # Errors
///
/// A message when `pattern` is no value of `sort`, or is nested deeper than
/// [`MAX_VALUE_DEPTH`] values, which this recursion refuses before the stack runs out.
pub(super) fn value_of(pattern: &KorePattern, sort: &ValueSort) -> Result<Value, String> {
    value_at(pattern, sort, 0)
}

/// [`value_of`] for a value at `level` levels below the value read.
fn value_at(pattern: &KorePattern, sort: &ValueSort, level: usize) -> Result<Value, String> {
    let below = deeper(level)?;
    let pattern = uninject(pattern);
    match sort.generated() {
        ValueSort::List {
            symbols, element, ..
        } => {
            let items = items(pattern, symbols)?
                .into_iter()
                .map(|item| single(item, symbols).and_then(|item| value_at(item, element, below)))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Value::List(items))
        }
        ValueSort::Set {
            symbols, element, ..
        } => {
            let mut items = items(pattern, symbols)?
                .into_iter()
                .map(|item| single(item, symbols).and_then(|item| value_at(item, element, below)))
                .collect::<Result<Vec<_>, _>>()?;
            items.sort();
            items.dedup();
            Ok(Value::Set(items))
        }
        ValueSort::Map {
            symbols,
            key,
            value,
            ..
        } => {
            let mut entries = items(pattern, symbols)?
                .into_iter()
                .map(|item| match item {
                    KorePattern::Application { symbol, arguments }
                        if symbol.name == symbols.element && arguments.len() == 2 =>
                    {
                        Ok((
                            value_at(&arguments[0], key, below)?,
                            value_at(&arguments[1], value, below)?,
                        ))
                    }
                    _ => Err(format!(
                        "a {} entry is not `{}`",
                        symbols.kore_sort, symbols.element
                    )),
                })
                .collect::<Result<Vec<_>, String>>()?;
            entries.sort_by(|left, right| left.0.cmp(&right.0));
            if entries.windows(2).any(|pair| pair[0].0 == pair[1].0) {
                return Err("a map with a repeated key".to_owned());
            }
            Ok(Value::Map(entries))
        }
        ValueSort::Data { table, .. } => data_value(pattern, table, 0, level),
        builtin => domain_value(pattern, builtin, &builtin_kore_sort(sort)?),
    }
}

impl ValueSort {
    /// The sort's own KORE sort: the sort a hole declared with this sort holds (`SortInt`,
    /// `SortMInt{Sort64{}}`, `SortList`, `SortTx`), as opposed to the own sort of one value,
    /// which for a data value may be a subsort.
    ///
    /// # Errors
    ///
    /// A message when a token sort's name does not parse, or a data sort has no table entry.
    pub(crate) fn kore_sort(&self) -> Result<KoreSort, String> {
        match self {
            Self::List { symbols, .. } | Self::Set { symbols, .. } | Self::Map { symbols, .. } => {
                Ok(simple_sort(&symbols.kore_sort))
            }
            Self::Data { table, sort, .. } => table
                .sorts
                .first()
                .map(|entry| simple_sort(&entry.kore_sort))
                .ok_or_else(|| format!("the data sort {sort} has no table entry")),
            builtin => builtin_kore_sort(builtin),
        }
    }
}

/// The KORE sort of the domain values of the builtin or renamed sort `sort`.
fn builtin_kore_sort(sort: &ValueSort) -> Result<KoreSort, String> {
    Ok(match sort {
        ValueSort::Renamed { kore_sort, .. } => simple_sort(kore_sort),
        ValueSort::Int => simple_sort(BuiltinSort::Int.kore_name()),
        ValueSort::Bool => simple_sort(BuiltinSort::Bool.kore_name()),
        ValueSort::String => simple_sort(BuiltinSort::String.kore_name()),
        ValueSort::Bytes => simple_sort(BuiltinSort::Bytes.kore_name()),
        ValueSort::MInt { width } => KoreSort::Application {
            name: MINT_SORT.to_owned(),
            arguments: vec![simple_sort(&format!("Sort{width}"))],
        },
        ValueSort::Token { sort } => {
            encode_kore_sort(&parse_sort(sort).map_err(|error| error.to_string())?)
        }
        _ => return Err("not a builtin sort".to_owned()),
    })
}

/// The items of a collection pattern: the leaves of its concatenations, without units.
fn items<'p>(
    pattern: &'p KorePattern,
    symbols: &CollectionSymbols,
) -> Result<Vec<&'p KorePattern>, String> {
    let mut found = Vec::new();
    let mut pending = vec![pattern];
    while let Some(pattern) = pending.pop() {
        match pattern {
            KorePattern::Application { symbol, arguments } if symbol.name == symbols.concat => {
                pending.extend(arguments.iter().rev());
            }
            KorePattern::Application { symbol, arguments }
                if symbol.name == symbols.unit && arguments.is_empty() => {}
            KorePattern::Application { symbol, .. } if symbol.name == symbols.element => {
                found.push(pattern);
            }
            _ => {
                return Err(format!(
                    "the pattern is not a {} built from its symbols",
                    symbols.kore_sort
                ));
            }
        }
    }
    Ok(found)
}

/// The argument of a one-argument element application.
fn single<'p>(
    item: &'p KorePattern,
    symbols: &CollectionSymbols,
) -> Result<&'p KorePattern, String> {
    match item {
        KorePattern::Application { arguments, .. } if arguments.len() == 1 => Ok(&arguments[0]),
        _ => Err(format!("a {} element has one argument", symbols.kore_sort)),
    }
}

/// The level below `level`, or a message when a value at `level` would be deeper than
/// [`MAX_VALUE_DEPTH`].
fn deeper(level: usize) -> Result<usize, String> {
    if level >= MAX_VALUE_DEPTH {
        Err(format!(
            "the value is nested deeper than {MAX_VALUE_DEPTH} levels, the most a value read back \
             may have"
        ))
    } else {
        Ok(level + 1)
    }
}

/// The value of entry `index` of `table` whose KORE is `pattern`, at `level` levels below the
/// value read ([`value_at`]).
fn data_value(
    pattern: &KorePattern,
    table: &DataSorts,
    index: usize,
    level: usize,
) -> Result<Value, String> {
    let below = deeper(level)?;
    let pattern = uninject(pattern);
    let entry = &table.sorts[index];
    if let KorePattern::Application { symbol, arguments } = pattern
        && let Some(constructor) = entry
            .constructors
            .iter()
            .find(|constructor| constructor.symbol == symbol.name)
    {
        if constructor.arguments.len() != arguments.len() {
            return Err(format!("{} has the wrong number of arguments", symbol.name));
        }
        let arguments = constructor
            .arguments
            .iter()
            .zip(arguments)
            .map(|(sort, argument)| argument_value(argument, sort, table, below))
            .collect::<Result<Vec<_>, _>>()?;
        return Ok(Value::Apply {
            symbol: symbol.name.clone(),
            arguments,
        });
    }
    entry
        .subsorts
        .iter()
        .find_map(|subsort| argument_value(pattern, subsort, table, level).ok())
        .ok_or_else(|| {
            format!(
                "the pattern is no value of {}: its head is not one of the sort's constructors \
                 and it is no value of a subsort",
                entry.kore_sort
            )
        })
}

fn argument_value(
    pattern: &KorePattern,
    sort: &ArgumentSort,
    table: &DataSorts,
    level: usize,
) -> Result<Value, String> {
    match sort {
        ArgumentSort::Value(sort) => value_at(pattern, sort, level),
        ArgumentSort::Data(index) => data_value(pattern, table, *index, level),
        ArgumentSort::Empty(empty) => match uninject(pattern) {
            KorePattern::Application { symbol, arguments }
                if symbol.name == empty.symbols.unit && arguments.is_empty() =>
            {
                Ok(match empty.kind {
                    CollectionKind::List => Value::List(Vec::new()),
                    CollectionKind::Set => Value::Set(Vec::new()),
                    CollectionKind::Map => Value::Map(Vec::new()),
                })
            }
            _ => Err(format!(
                "only the empty {} is generated here",
                empty.symbols.kore_sort
            )),
        },
    }
}

/// The builtin value whose KORE is the domain value `pattern`, of the KORE sort `expected`.
fn domain_value(
    pattern: &KorePattern,
    sort: &ValueSort,
    expected: &KoreSort,
) -> Result<Value, String> {
    let KorePattern::DomainValue {
        sort: found, value, ..
    } = pattern
    else {
        return Err("the pattern is not a domain value".to_owned());
    };
    if found != expected {
        return Err(format!("a domain value of {found:?}, not of {expected:?}"));
    }
    let text = || {
        value
            .as_utf8()
            .map(str::to_owned)
            .map_err(|_| "the domain value is not UTF-8".to_owned())
    };
    match sort {
        ValueSort::Int => parse_int(&text()?).map(Value::Int),
        ValueSort::Bool => match text()?.as_str() {
            "true" => Ok(Value::Bool(true)),
            "false" => Ok(Value::Bool(false)),
            other => Err(format!("{other:?} is not a Bool")),
        },
        ValueSort::String => text().map(Value::String),
        ValueSort::Bytes => Ok(Value::Bytes(value.as_bytes().to_vec())),
        ValueSort::MInt { width } => parse_mint(&text()?, *width),
        ValueSort::Token { sort } => Ok(Value::Token {
            sort: sort.clone(),
            text: text()?,
        }),
        _ => Err("not a builtin sort".to_owned()),
    }
}

/// A value of `sort` different from `value`, for locating a hole's position by differential
/// parsing (ARCHITECTURE 2.3): for a builtin, the length-preserving change FZ-02 makes; for a
/// collection, the value without its last item (or, for an empty one, with the least item);
/// for a data value, the first argument that has another value changed, or else another
/// alternative of the sort at its least height. `None` when the sort has no second value.
pub(crate) fn second_value(value: &Value, sort: &ValueSort) -> Option<Value> {
    match (value, sort.generated()) {
        (Value::List(items), ValueSort::List { element, .. }) => {
            Some(Value::List(shorter_or_longer(items, || {
                least_value(element)
            })?))
        }
        (Value::Set(items), ValueSort::Set { element, .. }) => {
            Some(Value::Set(shorter_or_longer(items, || {
                least_value(element)
            })?))
        }
        (Value::Map(entries), ValueSort::Map { key, value, .. }) => {
            Some(Value::Map(shorter_or_longer(entries, || {
                Some((least_value(key)?, least_value(value)?))
            })?))
        }
        (_, ValueSort::Data { table, .. }) => second_data(value, table, 0),
        (value, _) => second_builtin(value),
    }
}

fn shorter_or_longer<T: Clone>(items: &[T], least: impl FnOnce() -> Option<T>) -> Option<Vec<T>> {
    match items.split_last() {
        Some((_, rest)) => Some(rest.to_vec()),
        None => Some(vec![least()?]),
    }
}

fn second_data(value: &Value, table: &DataSorts, index: usize) -> Option<Value> {
    if let Ok(DataAlternative::Constructor(constructor)) = check_data(value, table, index)
        && let Value::Apply { symbol, arguments } = value
    {
        for (position, (sort, argument)) in constructor.arguments.iter().zip(arguments).enumerate()
        {
            let changed = match sort {
                ArgumentSort::Value(sort) => second_value(argument, sort),
                ArgumentSort::Data(child) => second_data(argument, table, *child),
                ArgumentSort::Empty(_) => None,
            };
            if let Some(changed) = changed {
                let mut arguments = arguments.clone();
                arguments[position] = changed;
                return Some(Value::Apply {
                    symbol: symbol.clone(),
                    arguments,
                });
            }
        }
    } else if let Ok(DataAlternative::Subsort(ArgumentSort::Value(sort))) =
        check_data(value, table, index)
        && let Some(changed) = second_value(value, sort)
    {
        return Some(changed);
    }
    least_alternatives(table, index)
        .into_iter()
        .find(|candidate| candidate != value)
}

/// One least value of each alternative of entry `index` that has height at most the entry's.
fn least_alternatives(table: &DataSorts, index: usize) -> Vec<Value> {
    let entry = &table.sorts[index];
    let mut found = entry
        .subsorts
        .iter()
        .filter_map(|subsort| least_argument(subsort, table))
        .collect::<Vec<_>>();
    for constructor in &entry.constructors {
        let arguments = constructor
            .arguments
            .iter()
            .map(|sort| least_argument(sort, table))
            .collect::<Option<Vec<_>>>();
        if let Some(arguments) = arguments {
            found.push(Value::Apply {
                symbol: constructor.symbol.clone(),
                arguments,
            });
        }
    }
    found
}

fn least_argument(sort: &ArgumentSort, table: &DataSorts) -> Option<Value> {
    match sort {
        ArgumentSort::Value(sort) => least_value(sort),
        ArgumentSort::Empty(empty) => Some(match empty.kind {
            CollectionKind::List => Value::List(Vec::new()),
            CollectionKind::Set => Value::Set(Vec::new()),
            CollectionKind::Map => Value::Map(Vec::new()),
        }),
        ArgumentSort::Data(index) => least_data(table, *index),
    }
}

/// A value of entry `index` of least height: a subsort's least value, or the first lowest
/// constructor applied to least arguments (constructors are ordered lowest first).
fn least_data(table: &DataSorts, index: usize) -> Option<Value> {
    let entry = &table.sorts[index];
    let height = entry.height?;
    if let Some(value) = entry
        .subsorts
        .iter()
        .find_map(|subsort| least_argument(subsort, table))
    {
        return Some(value);
    }
    let constructor = entry
        .constructors
        .iter()
        .find(|constructor| constructor.height == Some(height))?;
    let arguments = constructor
        .arguments
        .iter()
        .map(|sort| least_argument(sort, table))
        .collect::<Option<Vec<_>>>()?;
    Some(Value::Apply {
        symbol: constructor.symbol.clone(),
        arguments,
    })
}

/// The least value of `sort`: zero, false, the empty string or byte string, the empty
/// collection, or a data value of least height. `None` for a token sort.
pub(crate) fn least_value(sort: &ValueSort) -> Option<Value> {
    Some(match sort.generated() {
        ValueSort::Int => Value::Int(BigInt::default()),
        ValueSort::Bool => Value::Bool(false),
        ValueSort::String => Value::String(String::new()),
        ValueSort::Bytes => Value::Bytes(Vec::new()),
        ValueSort::MInt { width } => Value::MInt {
            width: *width,
            value: num_bigint::BigUint::default(),
        },
        ValueSort::List { .. } => Value::List(Vec::new()),
        ValueSort::Set { .. } => Value::Set(Vec::new()),
        ValueSort::Map { .. } => Value::Map(Vec::new()),
        ValueSort::Data { table, .. } => least_data(table, 0)?,
        ValueSort::Token { .. } | ValueSort::Renamed { .. } => return None,
    })
}

/// FZ-02's length-preserving second value of a builtin (`holes/position.rs`, `alternative`).
fn second_builtin(value: &Value) -> Option<Value> {
    use num_bigint::BigUint;
    use num_traits::{One as _, Zero as _};
    let ten = || BigUint::from(10_u8);
    let nine = || BigUint::from(9_u8);
    let other_last = |text: &str| {
        let mut text = text.to_owned();
        let last = text.pop();
        text.push(if last == Some('a') { 'b' } else { 'a' });
        text
    };
    Some(match value {
        Value::Int(value) => {
            let last_is_nine = value.magnitude() % ten() == nine();
            let step = if last_is_nine == (value.sign() == num_bigint::Sign::Minus) {
                1
            } else {
                -1
            };
            Value::Int(value + step)
        }
        Value::Bool(value) => Value::Bool(!value),
        Value::String(text) => Value::String(other_last(text)),
        Value::Token { sort, text } => Value::Token {
            sort: sort.clone(),
            text: other_last(text),
        },
        Value::Bytes(bytes) => {
            let mut bytes = bytes.clone();
            let last = bytes.pop();
            bytes.push(if last == Some(b'a') { b'b' } else { b'a' });
            Value::Bytes(bytes)
        }
        Value::MInt { width, value } => {
            if *width == 0 {
                return None;
            }
            let bound = BigUint::one() << *width;
            let up = value + BigUint::one();
            let value = if value % ten() != nine() && up < bound {
                up
            } else if value.is_zero() {
                return None;
            } else {
                value - BigUint::one()
            };
            Value::MInt {
                width: *width,
                value,
            }
        }
        Value::List(_) | Value::Set(_) | Value::Map(_) | Value::Apply { .. } => return None,
    })
}
