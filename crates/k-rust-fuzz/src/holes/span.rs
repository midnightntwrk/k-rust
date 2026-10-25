//! Where each hole sits: span addressing, configuration variables, template variables, and the
//! overlap rule (ARCHITECTURE 2.2, T-9).

use std::collections::BTreeMap;

use k_rust::{
    kast::parser::parse_sort,
    kompile::encode_kore_sort,
    kore::{
        ast::{Pattern as KorePattern, VariableKind},
        node::PatternSource,
        walk,
    },
};

use super::{HoleDecl, HoleLocation, HoleSite, SpanAddress, SpanText};
use crate::{
    error::{CampaignError, SortRefusal, SpanProblem},
    spec::{CompiledDefinition, ProgramInput},
};

/// The site of `decl` in `program` and its anchor text (`None` for a template variable).
pub(super) fn locate(
    decl: &HoleDecl,
    program: &ProgramInput,
    definition: &CompiledDefinition,
) -> Result<(HoleSite, Option<String>), CampaignError> {
    let refuse = |problem| CampaignError::HoleSpan {
        hole: decl.name.clone(),
        problem,
    };
    match &decl.location {
        HoleLocation::Span(address) => {
            let (text, content) = addressed_text(address, program)
                .ok_or_else(|| refuse(SpanProblem::UnknownProgram))?;
            let (start, end) = literal_span(address, content).map_err(refuse)?;
            Ok((
                HoleSite::Span { text, start, end },
                Some(address.literal.clone()),
            ))
        }
        HoleLocation::ConfigVar { name } => {
            let name = name.strip_prefix('$').unwrap_or(name);
            let ProgramInput::Source(source) = program else {
                return Err(refuse(SpanProblem::UnknownConfigVar));
            };
            // The anchor is the text the program binds; a variable the program leaves to its
            // default (or that the definition does not declare) has no binding to replace.
            let bound = source
                .config_vars
                .iter()
                .find(|(bound, _)| bound.strip_prefix('$').unwrap_or(bound) == name)
                .filter(|_| definition.configuration_variables.contains_key(name))
                .ok_or_else(|| refuse(SpanProblem::UnknownConfigVar))?;
            // Whitespace around the value (a trailing newline of a file it was read from) is
            // not part of the value; replacing the whole binding drops it too.
            Ok((
                HoleSite::ConfigVar(name.to_owned()),
                Some(bound.1.trim().to_owned()),
            ))
        }
        HoleLocation::KoreVariable { name } => {
            let ProgramInput::KoreTemplate(template) = program else {
                return Err(refuse(SpanProblem::KoreVariable));
            };
            let variable = template
                .free_variables()
                .into_iter()
                .find(|variable| variable.kind == VariableKind::Element && variable.name == *name)
                .ok_or_else(|| refuse(SpanProblem::KoreVariable))?;
            // A variable also bound somewhere in the template would need a substitution that
            // avoids the bound occurrences; templates are configurations, so refuse it.
            if binds(template, name) {
                return Err(refuse(SpanProblem::KoreVariable));
            }
            // The hole's values are values of its declared sort, substituted for the variable
            // as they are, so the two sorts must be one (D17).
            let sort = parse_sort(&decl.sort).map_err(|_| CampaignError::RefusedHoleSort {
                hole: decl.name.clone(),
                sort: decl.sort.clone(),
                reason: SortRefusal::Unknown,
            })?;
            if encode_kore_sort(&sort) != variable.sort {
                return Err(refuse(SpanProblem::KoreVariable));
            }
            Ok((HoleSite::KoreVariable(variable), None))
        }
    }
}

/// The text `address` names: the program text, or the text bound to `$NAME`.
fn addressed_text<'p>(
    address: &SpanAddress,
    program: &'p ProgramInput,
) -> Option<(SpanText, &'p str)> {
    let ProgramInput::Source(source) = program else {
        return None;
    };
    if let Some(name) = address.program.strip_prefix('$') {
        source
            .config_vars
            .iter()
            .find(|(bound, _)| bound.strip_prefix('$').unwrap_or(bound) == name)
            .map(|(_, text)| (SpanText::Binding(name.to_owned()), text.as_str()))
    } else {
        source
            .program
            .as_ref()
            .filter(|text| text.name == address.program)
            .map(|text| (SpanText::Program, text.text.as_str()))
    }
}

/// The byte range of `address.literal` in `content`: the literal at `line` and `column` when a
/// column is given; otherwise `find` occurs exactly once in the addressed line (or all of
/// `content`), and `literal` exactly once in `find`. Occurrences are counted overlapping, since
/// each is a different place the text could mean.
fn literal_span(address: &SpanAddress, content: &str) -> Result<(usize, usize), SpanProblem> {
    if let Some(column) = address.column {
        if address.line.is_none() {
            return Err(SpanProblem::ColumnWithoutLine);
        }
        if !address.find.is_empty() && address.find != address.literal {
            return Err(SpanProblem::FindWithColumn);
        }
        let (offset, region) = addressed_line(address, content)?;
        let at = usize::try_from(column)
            .ok()
            .and_then(|column| column.checked_sub(1))
            .and_then(|index| match region.char_indices().nth(index) {
                Some((at, _)) => Some(at),
                None if index == region.chars().count() => Some(region.len()),
                None => None,
            })
            .ok_or(SpanProblem::LiteralNotAtColumn)?;
        if address.literal.is_empty() || !region[at..].starts_with(&address.literal) {
            return Err(SpanProblem::LiteralNotAtColumn);
        }
        let start = offset + at;
        return Ok((start, start + address.literal.len()));
    }
    let (offset, region) = addressed_line(address, content)?;
    let finds = occurrences(region, &address.find);
    let [find] = finds.as_slice() else {
        return Err(SpanProblem::FindCount(finds.len()));
    };
    let literals = occurrences(&address.find, &address.literal);
    let [literal] = literals.as_slice() else {
        return Err(SpanProblem::LiteralCount(literals.len()));
    };
    let start = offset + find + literal;
    Ok((start, start + address.literal.len()))
}

/// The byte offset in `content` and the text of the line `address` names, or all of `content`
/// without a line.
fn addressed_line<'c>(
    address: &SpanAddress,
    content: &'c str,
) -> Result<(usize, &'c str), SpanProblem> {
    Ok(match address.line {
        None => (0, content),
        Some(line) => {
            let index = usize::try_from(line)
                .ok()
                .and_then(|line| line.checked_sub(1))
                .ok_or(SpanProblem::LineOutOfRange)?;
            let mut offset = 0;
            let mut found = None;
            for (number, text) in content.split('\n').enumerate() {
                if number == index {
                    found = Some((offset, text));
                    break;
                }
                offset += text.len() + 1;
            }
            found.ok_or(SpanProblem::LineOutOfRange)?
        }
    })
}

/// The byte offsets of every occurrence of `needle` in `haystack`, overlapping ones included;
/// none for an empty needle, which addresses no text.
fn occurrences(haystack: &str, needle: &str) -> Vec<usize> {
    if needle.is_empty() {
        return Vec::new();
    }
    let mut found = Vec::new();
    let mut from = 0;
    while let Some(at) = haystack[from..].find(needle) {
        let at = from + at;
        found.push(at);
        // Resume one character later, so overlapping occurrences are found too.
        from = at + haystack[at..].chars().next().map_or(1, char::len_utf8);
    }
    found
}

/// Whether a binder of `template` binds a variable named `name`.
fn binds(template: &KorePattern, name: &str) -> bool {
    let mut bound = false;
    walk::for_each_post_order(template, |pattern| match pattern {
        KorePattern::Exists { variable, .. }
        | KorePattern::Forall { variable, .. }
        | KorePattern::Mu { variable, .. }
        | KorePattern::Nu { variable, .. } => bound |= variable.name == name,
        _ => {}
    });
    bound
}

/// Every free variable of `template` is addressed by a hole (ARCHITECTURE 2.2): a template with
/// a free variable left over is not a configuration.
pub(super) fn check_template_is_covered(
    template: &KorePattern,
    located: &[(HoleSite, Option<String>)],
) -> Result<(), CampaignError> {
    for variable in template.free_variables() {
        let addressed = located.iter().any(
            |(site, _)| matches!(site, HoleSite::KoreVariable(addressed) if *addressed == variable),
        );
        if !addressed {
            return Err(CampaignError::HoleSpan {
                hole: variable.name.clone(),
                problem: SpanProblem::KoreVariable,
            });
        }
    }
    Ok(())
}

/// No two holes replace overlapping text: two spans of one text that share a byte, a span
/// inside a binding and a hole on the whole binding, or two holes on one variable.
pub(super) fn check_overlaps(
    decls: &[HoleDecl],
    located: &[(HoleSite, Option<String>)],
) -> Result<(), CampaignError> {
    for (second, (second_site, _)) in located.iter().enumerate() {
        for (first, (first_site, _)) in located[..second].iter().enumerate() {
            if overlap(first_site, second_site) {
                return Err(CampaignError::OverlappingHoles {
                    first: decls[first].name.clone(),
                    second: decls[second].name.clone(),
                });
            }
        }
    }
    Ok(())
}

fn overlap(left: &HoleSite, right: &HoleSite) -> bool {
    match (left, right) {
        (
            HoleSite::Span {
                text: left_text,
                start: left_start,
                end: left_end,
            },
            HoleSite::Span {
                text: right_text,
                start: right_start,
                end: right_end,
            },
        ) => left_text == right_text && left_start < right_end && right_start < left_end,
        (HoleSite::ConfigVar(whole), HoleSite::Span { text, .. })
        | (HoleSite::Span { text, .. }, HoleSite::ConfigVar(whole)) => {
            *text == SpanText::Binding(whole.clone())
        }
        (HoleSite::ConfigVar(left), HoleSite::ConfigVar(right)) => left == right,
        (HoleSite::KoreVariable(left), HoleSite::KoreVariable(right)) => left.name == right.name,
        _ => false,
    }
}

/// `template` with each free element variable named in `substitution` replaced by its value.
/// [`locate`] refused variables that a binder of the template also binds, so every occurrence
/// of such a name is free.
pub(super) fn substitute(
    template: &KorePattern,
    substitution: &BTreeMap<&str, KorePattern>,
) -> KorePattern {
    walk::rebuild(template, |pattern, children: Vec<KorePattern>| {
        if let KorePattern::Variable(variable) = pattern
            && variable.kind == VariableKind::Element
            && let Some(value) = substitution.get(variable.name.as_str())
        {
            return value.clone();
        }
        pattern.node().split().0.fill(children).into_pattern()
    })
}
