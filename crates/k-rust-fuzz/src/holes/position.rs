//! Hole positions in the assembled configuration, located by differential parsing, and the
//! per-case round-trip check (ARCHITECTURE 2.3).

use k_rust::kore::{
    ast::{Pattern as KorePattern, Sort as KoreSort},
    node::PatternSource,
    printer::Printer,
    walk,
};
use num_bigint::BigUint;
use num_traits::{One, Zero};

use super::{
    PrintedValue, ResolvedHole, ResolvedHoles, RoundTripCheck, RoundTripFailure, instantiate,
};
use crate::{
    assemble::ProgramAssembly,
    error::CampaignError,
    spec::{CompiledDefinition, ProgramInput},
    values::{
        Value, ValueSort,
        print::{print_k_text, to_kore},
        term::second_value,
    },
};

/// The longest KORE text a [`RoundTripFailure`] quotes.
const QUOTED_KORE_LIMIT: usize = 200;

/// [`RoundTripCheck::new`].
pub(super) fn locate_all(
    assembly: &ProgramAssembly,
    definition: &CompiledDefinition,
    program: &ProgramInput,
    holes: &ResolvedHoles,
) -> Result<RoundTripCheck, CampaignError> {
    if let ProgramInput::KoreTemplate(template) = program {
        return Ok(RoundTripCheck {
            anchor_configuration: template.clone(),
            names: names(holes),
            positions: vec![None; holes.holes.len()],
        });
    }
    let anchors = holes
        .holes
        .iter()
        .map(anchor_printed)
        .collect::<Result<Vec<_>, _>>()?;
    let mut assembler = assembly.assembler(definition);
    let anchor_configuration = assembler
        .assemble(&instantiate(program, holes, &anchors))
        .map_err(|error| CampaignError::Program {
            message: format!(
                "the program does not assemble with its anchor values: {}",
                error.message
            ),
        })?;
    let mut positions = Vec::with_capacity(holes.holes.len());
    for (index, hole) in holes.holes.iter().enumerate() {
        let unlocatable = |message: String| CampaignError::AnchorDoesNotParse {
            hole: hole.decl.name.clone(),
            message,
        };
        let anchor = hole
            .anchor
            .as_ref()
            .expect("a source hole has an anchor (anchor_printed)");
        let second = alternative(anchor, &hole.sort).ok_or_else(|| {
            unlocatable(format!(
                "sort {} has no second value to locate the hole's position with",
                hole.decl.sort
            ))
        })?;
        let printed = printed(&second, hole).map_err(unlocatable)?;
        let mut values = anchors.clone();
        values[index] = printed;
        let second_configuration = assembler
            .assemble(&instantiate(program, holes, &values))
            .map_err(|error| {
                unlocatable(format!(
                    "the hole's position cannot be located: the program with `{}` at the hole \
                     does not assemble: {}",
                    values[index].k_text, error.message
                ))
            })?;
        let path = locate(
            &anchor_configuration,
            &second_configuration,
            &anchors[index].kore,
            &values[index].kore,
        )
        .map_err(unlocatable)?;
        positions.push(Some(path));
    }
    Ok(RoundTripCheck {
        anchor_configuration,
        names: names(holes),
        positions,
    })
}

fn names(holes: &ResolvedHoles) -> Vec<String> {
    holes
        .holes
        .iter()
        .map(|hole| hole.decl.name.clone())
        .collect()
}

/// A source hole's anchor as a [`PrintedValue`]: its text exactly as the program has it, so the
/// anchor configuration is the unmodified program's, and its KORE.
fn anchor_printed(hole: &ResolvedHole) -> Result<PrintedValue, CampaignError> {
    let (Some(text), Some(anchor)) = (&hole.anchor_text, &hole.anchor) else {
        unreachable!("resolve gives every source hole an anchor");
    };
    let refuse = |message: String| CampaignError::AnchorDoesNotParse {
        hole: hole.decl.name.clone(),
        message,
    };
    // A collection or data anchor is read as the assembler reads it, so a set or map written in
    // another order than the value's sorted one is found as written (D19); a builtin anchor's
    // KORE is its domain value.
    let kore = match &hole.sort {
        ValueSort::List {
            text: Some(syntax), ..
        }
        | ValueSort::Set {
            text: Some(syntax), ..
        }
        | ValueSort::Map {
            text: Some(syntax), ..
        }
        | ValueSort::Data {
            text: Some(syntax), ..
        } => syntax
            .parse(text, &hole.decl.sort)
            .map_err(|message| refuse(format!("the anchor does not read back: {message}")))?,
        _ => to_kore(anchor, &hole.sort)
            .map_err(|error| refuse(format!("the anchor has no KORE form: {error:?}")))?,
    };
    Ok(PrintedValue {
        k_text: text.clone(),
        kore,
    })
}

fn printed(value: &Value, hole: &ResolvedHole) -> Result<PrintedValue, String> {
    let k_text = print_k_text(value, &hole.sort).map_err(|error| format!("{error:?}"))?;
    let kore = to_kore(value, &hole.sort).map_err(|error| format!("{error:?}"))?;
    Ok(PrintedValue { k_text, kore })
}

/// A second value of the anchor's sort for differential parsing, printed with the anchor's
/// length where the sort allows, so that text positions after the hole (and the locations of a
/// definition that records them) do not move: an integer changes its last digit, a string or a
/// token its last character. `None` when the sort has one value or no second value is known
/// (`MInt{0}`).
///
/// The length is not kept for a `Bool` (`true` and `false`), an empty string or byte string,
/// and a string or byte string whose anchor is written with escapes (the second value is
/// printed afresh). On a definition that records locations the later columns then differ too,
/// no single subterm holds every difference, and the hole is refused: a false refusal, never a
/// false acceptance.
fn alternative(anchor: &Value, sort: &ValueSort) -> Option<Value> {
    let ten = || BigUint::from(10_u8);
    let nine = || BigUint::from(9_u8);
    let other_last = |text: &str| {
        let mut text = text.to_owned();
        let last = text.pop();
        text.push(if last == Some('a') { 'b' } else { 'a' });
        text
    };
    Some(match anchor {
        Value::Int(value) => {
            // Away from the last digit 9, so the length and the sign are kept.
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
        // A collection loses its last item (or gains its least one), a data value changes its
        // first changeable argument or takes another alternative (FZ-G6/FZ-09).
        Value::List(_) | Value::Set(_) | Value::Map(_) | Value::Apply { .. } => {
            return second_value(anchor, sort);
        }
    })
}

/// The path to the one subterm that holds `anchor` in `first` and `second` in `other`, inside
/// which every difference between the two configurations lies.
fn locate(
    first: &KorePattern,
    other: &KorePattern,
    anchor: &KorePattern,
    second: &KorePattern,
) -> Result<Vec<usize>, String> {
    let differences = differences(first, other);
    let Some((head, rest)) = differences.split_first() else {
        return Err("the hole's value does not reach the configuration".to_owned());
    };
    let mut common = head.clone();
    for path in rest {
        let shared = common
            .iter()
            .zip(path)
            .take_while(|(left, right)| left == right)
            .count();
        common.truncate(shared);
    }
    for length in (0..=common.len()).rev() {
        let path = &common[..length];
        let (Some(left), Some(right)) = (at(first, path), at(other, path)) else {
            continue;
        };
        if left == anchor && right == second {
            return Ok(path.to_vec());
        }
        // A second data value of another own sort comes with its own injection to the
        // position's sort (D19): the position is the injections' argument.
        if let (Some((left_target, left_child)), Some((right_target, right_child))) =
            (injection(left), injection(right))
            && left_target == right_target
            && left_child == anchor
            && right_child == second
        {
            let mut path = path.to_vec();
            path.push(0);
            return Ok(path);
        }
    }
    let found = at(first, &common);
    if let (
        [_],
        Some(KorePattern::DomainValue {
            sort: found_sort,
            value: found_value,
        }),
        KorePattern::DomainValue { sort, value },
    ) = (differences.as_slice(), found, anchor)
        && found_sort == sort
        && same_integer(found_value.as_bytes(), value.as_bytes())
    {
        return Err(format!(
            "the anchor is written `{}`, which the configuration keeps as written, while the \
             hole's values are compared in their canonical spelling `{}`; write the literal \
             canonically",
            String::from_utf8_lossy(found_value.as_bytes()),
            String::from_utf8_lossy(value.as_bytes()),
        ));
    }
    let found = found.map_or_else(|| "nothing".to_owned(), quote);
    Err(format!(
        "the anchor does not parse back to its value at the hole's position: the configuration \
         differs from the one with another value at {} place(s), and the innermost subterm \
         holding every difference is {found}, not {}",
        differences.len(),
        quote(anchor)
    ))
}

/// Whether two domain-value texts are integers of one value (`07`, `+7` and `7`).
fn same_integer(left: &[u8], right: &[u8]) -> bool {
    let parse = |text: &[u8]| {
        std::str::from_utf8(text)
            .ok()
            .and_then(|text| text.parse::<num_bigint::BigInt>().ok())
    };
    matches!((parse(left), parse(right)), (Some(left), Some(right)) if left == right)
}

/// The paths of the outermost subterms at which `left` and `right` differ in their root node,
/// in pre-order.
fn differences(left: &KorePattern, right: &KorePattern) -> Vec<Vec<usize>> {
    // Each visited pair records its parent's entry and its argument index, so a path is built
    // only for a difference.
    let mut trail: Vec<(usize, usize)> = Vec::new();
    let mut work = vec![(left, right, usize::MAX, 0)];
    let mut found = Vec::new();
    while let Some((left, right, parent, index)) = work.pop() {
        let entry = trail.len();
        trail.push((parent, index));
        if !same_node(left, right) {
            let mut path = Vec::new();
            let mut cursor = entry;
            while trail[cursor].0 != usize::MAX {
                path.push(trail[cursor].1);
                cursor = trail[cursor].0;
            }
            path.reverse();
            found.push(path);
            continue;
        }
        let pairs = walk::children(left)
            .into_iter()
            .zip(walk::children(right))
            .enumerate()
            .collect::<Vec<_>>();
        for (index, (left, right)) in pairs.into_iter().rev() {
            work.push((left, right, entry, index));
        }
    }
    found
}

/// Whether two patterns have the same root node: variant, scalar fields and arity.
fn same_node(left: &KorePattern, right: &KorePattern) -> bool {
    let (left, left_children) = left.node().split();
    let (right, right_children) = right.node().split();
    left.discriminant() == right.discriminant()
        && left.compare_scalars(&right).is_eq()
        && left_children.len() == right_children.len()
}

/// The target sort and the argument of an injection `inj{From, To}(argument)`.
fn injection(pattern: &KorePattern) -> Option<(&KoreSort, &KorePattern)> {
    match pattern {
        KorePattern::Application { symbol, arguments }
            if symbol.name == "inj" && symbol.sort_parameters.len() == 2 =>
        {
            match arguments.as_slice() {
                [argument] => Some((&symbol.sort_parameters[1], argument)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Whether `node` is `value`, or `value` injected to another sort.
fn value_at(node: &KorePattern, value: &KorePattern) -> bool {
    node == value || injection(node).is_some_and(|(_, argument)| argument == value)
}

fn at<'p>(pattern: &'p KorePattern, path: &[usize]) -> Option<&'p KorePattern> {
    path.iter().try_fold(pattern, |pattern, index| {
        walk::children(pattern).get(*index).copied()
    })
}

fn quote(pattern: &KorePattern) -> String {
    let mut text = Printer::compact().print_pattern(pattern);
    if text.len() > QUOTED_KORE_LIMIT {
        let mut cut = QUOTED_KORE_LIMIT;
        while !text.is_char_boundary(cut) {
            cut -= 1;
        }
        text.truncate(cut);
        text.push('…');
    }
    text
}

/// [`RoundTripCheck::check`].
pub(super) fn check(
    check: &RoundTripCheck,
    assembled: &KorePattern,
    values: &[PrintedValue],
) -> Result<(), RoundTripFailure> {
    for ((position, value), name) in check.positions.iter().zip(values).zip(&check.names) {
        let Some(path) = position else {
            continue;
        };
        let failure = |found: String| RoundTripFailure {
            hole: name.clone(),
            found,
        };
        let Some((last, upper)) = path.split_last() else {
            // The position is the whole configuration.
            if value_at(assembled, &value.kore) {
                continue;
            }
            return Err(failure(quote(assembled)));
        };
        let mut expected = &check.anchor_configuration;
        let mut actual = assembled;
        for (depth, step) in upper.iter().enumerate() {
            if !same_node(expected, actual) {
                return Err(failure(format!(
                    "{} at depth {depth} of the hole's position, where the configuration with \
                     the anchors has {}",
                    quote(actual),
                    quote(expected)
                )));
            }
            let (Some(next_expected), Some(next_actual)) = (
                walk::children(expected).get(*step).copied(),
                walk::children(actual).get(*step).copied(),
            ) else {
                return Err(failure(format!("no subterm at {path:?}")));
            };
            expected = next_expected;
            actual = next_actual;
        }
        // `expected` and `actual` are the nodes above the position. A data value is injected to
        // its position's sort from its own sort (D19), so a case value of another own sort than
        // the anchor's comes with another injection, and one of the position's own sort with
        // none; the value itself must be at the position either way.
        let holds = if let Some((target, _)) = injection(expected) {
            match injection(actual) {
                Some((actual_target, child)) => actual_target == target && *child == value.kore,
                None => *actual == value.kore,
            }
        } else {
            same_node(expected, actual)
                && walk::children(actual)
                    .get(*last)
                    .is_some_and(|child| value_at(child, &value.kore))
        };
        if !holds {
            let found = walk::children(actual)
                .get(*last)
                .map_or_else(|| quote(actual), |child| quote(child));
            return Err(failure(found));
        }
    }
    Ok(())
}
