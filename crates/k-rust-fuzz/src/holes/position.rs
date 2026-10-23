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
        print::{parse_mint, print_k_text, to_kore, to_kore_with_sort},
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
                    values[index].k_text.as_deref().unwrap_or_default(),
                    error.message
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
    // The per-case check compares everything outside the holes' check points and checks each
    // point's value, so one point inside another's subterm would go unchecked. Holes replace
    // disjoint text, and a located position holds only its hole's value, so this does not
    // happen; it is refused rather than assumed.
    let points = check_points(&anchor_configuration, &positions);
    for pair in points.windows(2) {
        if pair[1].path.starts_with(pair[0].path) {
            let hole = &holes.holes[pair[1].hole];
            return Err(CampaignError::AnchorDoesNotParse {
                hole: hole.decl.name.clone(),
                message: format!(
                    "its position lies inside the position of hole `{}`",
                    holes.holes[pair[0].hole].decl.name
                ),
            });
        }
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
pub(super) fn anchor_printed(hole: &ResolvedHole) -> Result<PrintedValue, CampaignError> {
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
    // The anchor value's own sort, which the parsed anchor KORE has too.
    let (_, sort) = to_kore_with_sort(anchor, &hole.sort)
        .map_err(|error| refuse(format!("the anchor has no KORE form: {error:?}")))?;
    Ok(PrintedValue {
        k_text: Some(text.clone()),
        kore,
        sort,
    })
}

pub(super) fn printed(value: &Value, hole: &ResolvedHole) -> Result<PrintedValue, String> {
    let k_text = print_k_text(value, &hole.sort).map_err(|error| format!("{error:?}"))?;
    let (kore, sort) =
        to_kore_with_sort(value, &hole.sort).map_err(|error| format!("{error:?}"))?;
    Ok(PrintedValue {
        k_text: Some(k_text),
        kore,
        sort,
    })
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
        && same_literal_value(found_value.as_bytes(), value.as_bytes())
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

/// Whether two domain-value texts are literals of one value: integers (`07`, `+7` and `7`), or
/// machine integers of one width (`-56p8` and `200p8`, both the residue 200 modulo `2^8`).
fn same_literal_value(left: &[u8], right: &[u8]) -> bool {
    let integer = |text: &[u8]| {
        std::str::from_utf8(text)
            .ok()
            .and_then(|text| text.parse::<num_bigint::BigInt>().ok())
    };
    let machine_integer = |text: &[u8]| {
        let text = std::str::from_utf8(text).ok()?;
        let (_, width) = text.rsplit_once(['p', 'P'])?;
        parse_mint(text, width.parse().ok()?).ok()
    };
    matches!((integer(left), integer(right)), (Some(left), Some(right)) if left == right)
        || matches!(
            (machine_integer(left), machine_integer(right)),
            (Some(left), Some(right)) if left == right
        )
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

/// [`same_node`], without building the nodes for the variants a configuration is made of.
fn same_root(left: &KorePattern, right: &KorePattern) -> bool {
    match (left, right) {
        (
            KorePattern::Application {
                symbol: left_symbol,
                arguments: left_arguments,
            },
            KorePattern::Application {
                symbol: right_symbol,
                arguments: right_arguments,
            },
        ) => left_symbol == right_symbol && left_arguments.len() == right_arguments.len(),
        (KorePattern::DomainValue { .. }, KorePattern::DomainValue { .. }) => left == right,
        _ => same_node(left, right),
    }
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

/// Replace the subterm of `pattern` at `path` (`kore::walk::children` indices, as
/// [`RoundTripCheck::positions`] gives them) with `replacement`; `false`, leaving `pattern`
/// unchanged, when no subterm is there.
#[cfg_attr(
    not(feature = "z3"),
    expect(
        dead_code,
        reason = "only the solve proposer (`z3` feature) replaces subterms"
    )
)]
pub(crate) fn replace_at(
    pattern: &mut KorePattern,
    path: &[usize],
    replacement: KorePattern,
) -> bool {
    let mut cursor = pattern;
    for &index in path {
        let child = match cursor {
            KorePattern::Application { arguments, .. }
            | KorePattern::And { arguments, .. }
            | KorePattern::Or { arguments, .. }
            | KorePattern::AssociativeApplication { arguments, .. } => arguments.get_mut(index),
            KorePattern::Not { argument, .. }
            | KorePattern::Next { argument, .. }
            | KorePattern::Ceil { argument, .. }
            | KorePattern::Floor { argument, .. } => (index == 0).then_some(argument.as_mut()),
            KorePattern::Implies { left, right, .. }
            | KorePattern::Iff { left, right, .. }
            | KorePattern::Rewrites { left, right, .. }
            | KorePattern::Equals { left, right, .. }
            | KorePattern::In { left, right, .. } => match index {
                0 => Some(left.as_mut()),
                1 => Some(right.as_mut()),
                _ => None,
            },
            KorePattern::Exists { body, .. }
            | KorePattern::Forall { body, .. }
            | KorePattern::Mu { body, .. }
            | KorePattern::Nu { body, .. } => (index == 0).then_some(body.as_mut()),
            KorePattern::String(_)
            | KorePattern::Variable(_)
            | KorePattern::Top { .. }
            | KorePattern::Bottom { .. }
            | KorePattern::DomainValue { .. } => None,
        };
        let Some(child) = child else {
            return false;
        };
        cursor = child;
    }
    *cursor = replacement;
    true
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

/// The KORE symbol of `#location` (module `K-LOCATIONS`): `#location{S}(term, file, line,
/// column, line, column)` wraps each term of a sort that declares `[locations]`.
const LOCATION_SYMBOL: &str = "Lbl'Hash'location";

/// Whether `pattern` is a location wrapper `#location{S}(term, file, l1, c1, l2, c2)`.
fn is_location(pattern: &KorePattern) -> bool {
    matches!(
        pattern,
        KorePattern::Application { symbol, arguments }
            if symbol.name == LOCATION_SYMBOL && arguments.len() == 6
    )
}

/// Whether the case configuration may differ from the anchor configuration in the child at
/// `index` of `node` although the program is the same: the lines and columns of a location
/// wrapper, which move when a value printed with another length than its anchor comes before
/// them on their line, or inside the term they locate.
fn may_move(node: &KorePattern, index: usize) -> bool {
    index >= 2 && is_location(node)
}

/// How a hole's value is checked at its check point.
#[derive(Clone, Copy)]
enum Point {
    /// The check point is the position: it holds the value, or the value injected to another
    /// sort.
    Value,
    /// The check point is the injection above the position in the anchor configuration: a data
    /// value of another own sort than the anchor's comes with its own injection to the same
    /// target, and one of the position's own sort with none (D19).
    Injection,
}

/// One hole's check point: the path to it, the hole's index and how it is checked.
struct CheckPoint<'p> {
    path: &'p [usize],
    hole: usize,
    point: Point,
}

/// The check point of every hole that has a position, ordered by path: its position, or the
/// injection above it in `anchor` (see [`Point`]).
fn check_points<'p>(
    anchor: &KorePattern,
    positions: &'p [Option<Vec<usize>>],
) -> Vec<CheckPoint<'p>> {
    let mut points = positions
        .iter()
        .enumerate()
        .filter_map(|(hole, position)| {
            let path = position.as_deref()?;
            let parent = path.split_last().and_then(|(_, upper)| at(anchor, upper));
            Some(match parent {
                Some(parent) if injection(parent).is_some() => CheckPoint {
                    path: &path[..path.len() - 1],
                    hole,
                    point: Point::Injection,
                },
                _ => CheckPoint {
                    path,
                    hole,
                    point: Point::Value,
                },
            })
        })
        .collect::<Vec<_>>();
    points.sort_by(|left, right| left.path.cmp(right.path));
    points
}

/// [`RoundTripCheck::check`].
///
/// The case configuration must equal the anchor configuration everywhere outside the holes'
/// positions (review R1), up to the lines and columns of location wrappers ([`may_move`]), and
/// hold each hole's intended value at its position. A printed value that the grammar reads
/// differently, at its position (`-5` read as the negation of `5`) or by re-parsing a
/// neighbouring part of the program, therefore makes the case `rejected`. So does a macro whose
/// expansion outside the hole's position depends on the value: a false rejection, never a false
/// acceptance.
///
/// The walk descends from the root along the paths to the check points, comparing nodes, and
/// compares every subterm off those paths whole ([`same_outside_locations`]), so a case costs
/// one pass over the configuration.
pub(super) fn check(
    check: &RoundTripCheck,
    assembled: &KorePattern,
    values: &[PrintedValue],
) -> Result<(), RoundTripFailure> {
    let anchor = &check.anchor_configuration;
    let points = check_points(anchor, &check.positions);
    if points.is_empty() {
        // KORE-template holes: substitution places their values exactly.
        return Ok(());
    }
    let failure = |hole: usize, found: String| RoundTripFailure {
        hole: check.names[hole].clone(),
        found,
        held: None,
    };
    // Each entry is a pair of nodes at one path and the check points below it: a contiguous
    // range of `points`, all of whose paths extend that path, of length `depth`.
    let mut work = vec![(anchor, assembled, 0, 0..points.len())];
    // One work list serves every comparison off the paths.
    let mut scratch = Vec::new();
    while let Some((expected, actual, depth, range)) = work.pop() {
        if let Some(here) = points[range.clone()]
            .iter()
            .find(|point| point.path.len() == depth)
        {
            // Holes do not nest (`locate_all`), so no other check point lies below this one.
            let value = &values[here.hole].kore;
            let holds = match here.point {
                Point::Value => value_at(actual, value),
                Point::Injection => match (injection(expected), injection(actual)) {
                    (Some((target, _)), Some((actual_target, child))) => {
                        actual_target == target && child == value
                    }
                    (_, None) => actual == value,
                    (None, Some(_)) => false,
                },
            };
            if !holds {
                let found = match (here.point, injection(actual)) {
                    (Point::Injection, Some((_, child))) => child,
                    _ => actual,
                };
                return Err(RoundTripFailure {
                    held: Some(Box::new(found.clone())),
                    ..failure(here.hole, quote(found))
                });
            }
            continue;
        }
        let nearest = points[range.start].hole;
        if !same_root(expected, actual) {
            return Err(failure(
                nearest,
                format!(
                    "{} at depth {depth} of the hole's position, where the configuration with \
                     the anchors has {}",
                    quote(actual),
                    quote(expected)
                ),
            ));
        }
        let mut cursor = range.start;
        for (index, (expected_child, actual_child)) in walk::children(expected)
            .into_iter()
            .zip(walk::children(actual))
            .enumerate()
        {
            let start = cursor;
            while cursor < range.end && points[cursor].path[depth] == index {
                cursor += 1;
            }
            if start < cursor {
                work.push((expected_child, actual_child, depth + 1, start..cursor));
            } else if !may_move(expected, index)
                && let Err((expected_differs, actual_differs)) =
                    same_outside_locations(expected_child, actual_child, &mut scratch)
            {
                return Err(failure(
                    nearest,
                    format!(
                        "{} outside every hole's position, where the configuration with the \
                         anchors has {}",
                        quote(actual_differs),
                        quote(expected_differs)
                    ),
                ));
            }
        }
    }
    Ok(())
}

/// Whether `expected` and `actual` are equal up to the lines and columns of location wrappers
/// ([`may_move`]); otherwise the outermost pair of differing subterms. Applications and domain
/// values, which configurations are made of, are compared field by field; any other subterm
/// whole. `work` is a work list to reuse; its contents are discarded.
fn same_outside_locations<'p>(
    expected: &'p KorePattern,
    actual: &'p KorePattern,
    work: &mut Vec<(&'p KorePattern, &'p KorePattern)>,
) -> Result<(), (&'p KorePattern, &'p KorePattern)> {
    work.clear();
    work.push((expected, actual));
    while let Some((expected, actual)) = work.pop() {
        let same = match (expected, actual) {
            (
                KorePattern::Application {
                    symbol: expected_symbol,
                    arguments: expected_arguments,
                },
                KorePattern::Application {
                    symbol: actual_symbol,
                    arguments: actual_arguments,
                },
            ) => {
                let same = expected_symbol == actual_symbol
                    && expected_arguments.len() == actual_arguments.len();
                if same {
                    let compared = if is_location(expected) {
                        2
                    } else {
                        expected_arguments.len()
                    };
                    work.extend(
                        expected_arguments[..compared]
                            .iter()
                            .zip(&actual_arguments[..compared]),
                    );
                }
                same
            }
            (
                KorePattern::DomainValue {
                    sort: expected_sort,
                    value: expected_value,
                },
                KorePattern::DomainValue {
                    sort: actual_sort,
                    value: actual_value,
                },
            ) => expected_sort == actual_sort && expected_value == actual_value,
            _ => expected == actual,
        };
        if !same {
            return Err((expected, actual));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use k_rust::kore::{ast::Sort as KoreSort, parser::parse_pattern};

    use super::{PrintedValue, RoundTripCheck, locate};

    fn pattern(text: &str) -> k_rust::kore::ast::Pattern {
        parse_pattern(text).expect("the pattern parses")
    }

    #[test]
    fn a_machine_integer_anchor_written_other_than_canonically_is_named() {
        // The frontend keeps a literal as written (`-56p8`), while a hole's values are compared
        // in their canonical spelling (`200p8`): the refusal says so, as for an `Int`.
        let at = |literal: &str| {
            pattern(&format!(
                r#"Lblw8{{}}(\dv{{SortMInt{{Sort8{{}}}}}}("{literal}"))"#
            ))
        };
        let dv = |literal: &str| pattern(&format!(r#"\dv{{SortMInt{{Sort8{{}}}}}}("{literal}")"#));
        for written in ["-56p8", "+200p8", "0200P8"] {
            let message = locate(&at(written), &at("201p8"), &dv("200p8"), &dv("201p8"))
                .expect_err("a spelling other than the canonical one is refused");
            assert!(
                message.contains(&format!("written `{written}`"))
                    && message.contains("canonically"),
                "{written}: {message}"
            );
        }
        // Another value is not a spelling of the anchor.
        let message = locate(&at("57p8"), &at("201p8"), &dv("200p8"), &dv("201p8"))
            .expect_err("another value is refused");
        assert!(!message.contains("canonically"), "{message}");
        // The canonical spelling is located.
        assert_eq!(
            locate(&at("200p8"), &at("201p8"), &dv("200p8"), &dv("201p8")),
            Ok(vec![0])
        );
    }

    /// An `Int` value as the round-trip check compares it.
    fn int_value(value: &str) -> PrintedValue {
        PrintedValue {
            k_text: Some(value.to_owned()),
            kore: pattern(&format!(r#"\dv{{SortInt{{}}}}("{value}")"#)),
            sort: KoreSort::Application {
                name: "SortInt".to_owned(),
                arguments: Vec::new(),
            },
        }
    }

    fn one_hole(anchor_configuration: &str, position: Vec<usize>) -> RoundTripCheck {
        RoundTripCheck {
            anchor_configuration: pattern(anchor_configuration),
            names: vec!["H".to_owned()],
            positions: vec![Some(position)],
        }
    }

    #[test]
    fn a_case_that_differs_outside_its_holes_is_rejected() {
        // The hole is the `1` under `g`; its value is intended at that position and nowhere
        // else changes the configuration (review R1). A value whose text re-parses into a
        // neighbouring position keeps the path and the value but changes a neighbour.
        let check = one_hole(
            r#"Lblf{}(Lblg{}(\dv{SortInt{}}("1")), \dv{SortInt{}}("2"))"#,
            vec![0, 0],
        );
        let case = |text: &str| check.check(&pattern(text), &[int_value("7")]);
        assert_eq!(
            case(r#"Lblf{}(Lblg{}(\dv{SortInt{}}("7")), \dv{SortInt{}}("2"))"#),
            Ok(())
        );
        let failure = case(r#"Lblf{}(Lblg{}(\dv{SortInt{}}("7")), \dv{SortInt{}}("3"))"#)
            .expect_err("a changed neighbour is rejected");
        assert_eq!(failure.hole, "H");
        assert!(failure.found.contains(r#"("3")"#), "{failure:?}");
        // A difference deep inside a neighbour, and an extra argument, are rejected too.
        let check = one_hole(
            r#"Lblf{}(\dv{SortInt{}}("1"), Lblh{}(Lblg{}(\dv{SortInt{}}("2"))))"#,
            vec![0],
        );
        let case = |text: &str| check.check(&pattern(text), &[int_value("7")]);
        assert!(
            case(r#"Lblf{}(\dv{SortInt{}}("7"), Lblh{}(Lblg{}(\dv{SortInt{}}("4"))))"#).is_err()
        );
        assert!(
            case(r#"Lblf{}(\dv{SortInt{}}("7"), Lblh{}(Lblg{}(\dv{SortInt{}}("2"), \dv{SortInt{}}("2"))))"#)
                .is_err()
        );
    }

    #[test]
    fn only_the_lines_and_columns_of_locations_may_move() {
        // `1 + 2` located, with the hole at `1`: a longer value moves the columns of the
        // hole's location, of the sum's and of the `2` after it, and nothing else.
        let located = |term: &str, columns: [u32; 2]| {
            format!(
                r#"Lbl'Hash'location{{SortExp{{}}}}({term}, \dv{{SortString{{}}}}("p"), \dv{{SortInt{{}}}}("1"), \dv{{SortInt{{}}}}("{}"), \dv{{SortInt{{}}}}("1"), \dv{{SortInt{{}}}}("{}"))"#,
                columns[0], columns[1]
            )
        };
        let int = |value: &str| {
            format!(r#"inj{{SortInt{{}}, SortExp{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#)
        };
        let sum = |left: &str, right: &str, columns: [[u32; 2]; 3]| {
            located(
                &format!(
                    "Lblplus{{}}({}, {})",
                    located(&int(left), columns[0]),
                    located(&int(right), columns[1])
                ),
                columns[2],
            )
        };
        let check = one_hole(&sum("1", "2", [[1, 2], [5, 6], [1, 6]]), vec![0, 0, 0, 0]);
        assert_eq!(
            check.check(
                &pattern(&sum("123", "2", [[1, 4], [7, 8], [1, 8]])),
                &[int_value("123")]
            ),
            Ok(())
        );
        // The located terms themselves must still agree.
        assert!(
            check
                .check(
                    &pattern(&sum("123", "3", [[1, 4], [7, 8], [1, 8]])),
                    &[int_value("123")]
                )
                .is_err()
        );
    }
}
