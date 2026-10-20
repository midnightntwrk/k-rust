//! Holes: an overlay of typed spans on an unmodified program (ARCHITECTURE 2). Owner: FZ-02.
//!
//! Neither the specification nor the program is edited or copied. A hole addresses a literal of
//! the program text by `find` and `literal` (the same addressing as kink's mutation edits), a
//! configuration variable by name, or a free variable of a KORE template. A case replaces each
//! span in memory with a value printed as K text, assembles the configuration exactly as krun
//! does ([`crate::assemble`]), and checks that every value parsed back to the value intended.
//!
//! ARCHITECTURE 2.2 writes a span hole of the unchanged program `transfer.imp` as follows (the
//! fields map to [`HoleDecl`] and [`SpanAddress`]):
//!
//! ```toml
//! [[hole]]
//! name = "AMOUNT"
//! sort = "Int"
//! program = "transfer.imp"   # or "$TX" for a literal inside the binding of $TX
//! line = 4                   # optional
//! find = "amount = 250;"     # occurs exactly once in the line (or the text)
//! literal = "250"            # occurs exactly once in `find`; the anchor value
//! range = { min = 0, max = 1000000 }
//! ```
//!
//! The span is replaced by each case's value printed as K text, and the anchor is the first
//! value tried. A configuration-variable hole replaces a whole binding (`name`, without `$`),
//! and a template hole a free variable of a KORE initial pattern.
//!
//! The hole's sort must be data ([`check_hole_sort`]). Builtin sorts with a generator are
//! admitted although programs contain their literals; `K`, `KItem`, cell sorts, the sorts
//! programs are written in and token sorts such as `Id` are refused, the last three unless the
//! declaration sets `allow-refused-sort`, which the report records.

mod position;
mod sorts;
mod span;

use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    k_rust_backend::definition::BackendDefinition,
    kore::ast::{Pattern as KorePattern, Variable as KoreVariable},
};
use serde::{Deserialize, Serialize};

use crate::{
    assemble::ProgramAssembly,
    error::{CampaignError, SortRefusal},
    spec::{CompiledDefinition, ProgramInput, ProgramText},
    values::{Constraints, Value, ValueSort, print::parse_k_text, resolve_value_sort},
};

/// One hole declaration (ARCHITECTURE 2.2).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct HoleDecl {
    /// The hole's name, unique in the campaign.
    pub name: String,
    /// The hole's sort, as the definition names it (`Int`, `List`, `MInt{64}`, a user sort).
    pub sort: String,
    /// What the hole replaces.
    pub location: HoleLocation,
    /// Optional constraints (ARCHITECTURE 2.5).
    pub constraints: Constraints,
    /// Admit a sort the hole-sort rule refuses (ARCHITECTURE 2.4); recorded in the report.
    pub allow_refused_sort: bool,
}

/// What a hole replaces (ARCHITECTURE 2.2).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum HoleLocation {
    /// A literal of the program text.
    Span(SpanAddress),
    /// The value of a configuration variable (`$NAME`, given without `$`); its anchor is the
    /// value the program's bindings give it.
    ConfigVar {
        /// The variable's name, without `$`.
        name: String,
    },
    /// A free element variable of a [`ProgramInput::KoreTemplate`], by its KORE name.
    KoreVariable {
        /// The variable's KORE name.
        name: String,
    },
}

/// The address of one literal in the program text or in a configuration variable's binding
/// (ARCHITECTURE 2.2, T-9).
///
/// `program` names the text: the program's name ([`crate::spec::ProgramText::name`]), or
/// `$NAME` for the text bound to the configuration variable `NAME`
/// ([`crate::spec::ProgramSource::config_vars`]), so that a literal inside a binding such as
/// `$TX = transfer(30, 1)` can be a hole. `find` must occur exactly once in the addressed line
/// (or the whole text without `line`), and `literal`, the hole's text, exactly once inside
/// `find`; occurrences are counted overlapping. `find` may equal `literal` when the literal is
/// unique, and otherwise carries enough context to make the span unique (`find = "x = 7;"`,
/// `literal = "7"`).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct SpanAddress {
    /// The program's name ([`crate::spec::ProgramText::name`]), or `$NAME` for the binding of
    /// the configuration variable `NAME`.
    pub program: String,
    /// The one-based line of the addressed text the span is on.
    pub line: Option<u32>,
    /// A text occurring exactly once in the line or program, containing the literal.
    pub find: String,
    /// The hole's literal, occurring exactly once in `find`; the hole's anchor value.
    pub literal: String,
}

/// Where a resolved hole sits.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum HoleSite {
    /// The byte range of the literal in the program text or in a binding's text.
    Span {
        /// The text the literal is in.
        text: SpanText,
        /// First byte of the literal.
        start: usize,
        /// One past the last byte of the literal.
        end: usize,
    },
    /// A configuration variable, without `$`.
    ConfigVar(String),
    /// A free variable of the KORE template.
    KoreVariable(KoreVariable),
}

/// The text a span hole addresses.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SpanText {
    /// The program text bound to `$PGM`.
    Program,
    /// The text bound to a configuration variable (name without `$`).
    Binding(String),
}

/// A hole after [`resolve`]: its site, the sort of its values and its anchor.
#[derive(Clone, Debug)]
pub(crate) struct ResolvedHole {
    /// The declaration as given.
    pub(crate) decl: HoleDecl,
    /// Where it sits in the unmodified program.
    pub(crate) site: HoleSite,
    /// The sort of the values it takes.
    pub(crate) sort: ValueSort,
    /// The text at the span (or the configuration variable's bound text); `None` for a KORE
    /// template variable, which has no value in the template.
    pub(crate) anchor_text: Option<String>,
    /// The anchor as a value, the first value the explicit proposer tries (ARCHITECTURE 2.2,
    /// 8.1); `None` for a KORE template variable.
    pub(crate) anchor: Option<Value>,
    /// The refusal an override admitted, recorded in the report (ARCHITECTURE 2.4).
    pub(crate) overridden: Option<SortRefusal>,
}

/// Every hole of a campaign, in declaration order; values are passed in this order.
#[derive(Clone, Debug)]
pub(crate) struct ResolvedHoles {
    pub(crate) holes: Vec<ResolvedHole>,
}

/// A value of one hole, printed: its K text (for span and configuration-variable holes) and its
/// KORE (for template holes, the round-trip check and the witness).
#[derive(Clone, Debug)]
pub(crate) struct PrintedValue {
    /// [`crate::values::print::print_k_text`] of the value.
    pub(crate) k_text: String,
    /// [`crate::values::print::to_kore`] of the value.
    pub(crate) kore: KorePattern,
}

/// The program of one case, with every hole replaced (ARCHITECTURE 2.3). It lives in memory
/// only.
#[derive(Clone, Debug)]
pub(crate) enum InstantiatedProgram {
    /// A program text and configuration-variable bindings for [`ProgramAssembly::assemble`].
    Source {
        /// The program's name and start sort with the instantiated text; `None` when the
        /// definition runs without `$PGM`.
        program: Option<crate::spec::ProgramText>,
        /// `NAME=VALUE` bindings in krun's order, with configuration-variable holes replaced.
        config_vars: Vec<(String, String)>,
    },
    /// The KORE template with every hole variable substituted.
    Kore(KorePattern),
}

/// Why an instantiated value did not parse back to the value intended (ARCHITECTURE 2.3); the
/// case is `rejected`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RoundTripFailure {
    /// The hole's name.
    pub(crate) hole: String,
    /// What the configuration holds at the hole's position instead, as KORE text, or why the
    /// position could not be read.
    pub(crate) found: String,
}

/// Resolve `decls` against the unmodified `program` and the baseline definition
/// (ARCHITECTURE 2.2, 2.4, 9.2).
///
/// Checks, in order: names are unique; each span's `find` occurs exactly once in its line or
/// text and `literal` exactly once in `find`; configuration-variable and template holes name
/// a declared and bound variable or a free template variable, and every free template variable
/// is a hole; spans do not overlap; each sort passes [`check_hole_sort`] (or is overridden) and
/// resolves to a [`ValueSort`] ([`crate::values::resolve_value_sort`]); each anchor text parses
/// as a value of that sort. `backend` is the baseline's internalized definition. Whether an
/// anchor parses back *in the program* is checked by [`RoundTripCheck::new`].
///
/// # Errors
///
/// [`CampaignError::DuplicateHole`], [`CampaignError::HoleSpan`],
/// [`CampaignError::OverlappingHoles`], [`CampaignError::RefusedHoleSort`],
/// [`CampaignError::AnchorDoesNotParse`], [`CampaignError::Definition`] when the definition's
/// grammar does not resolve.
pub(crate) fn resolve(
    decls: &[HoleDecl],
    program: &ProgramInput,
    definition: &CompiledDefinition,
    backend: &BackendDefinition,
) -> Result<ResolvedHoles, CampaignError> {
    let mut names = BTreeSet::new();
    for decl in decls {
        if !names.insert(decl.name.as_str()) {
            return Err(CampaignError::DuplicateHole {
                hole: decl.name.clone(),
            });
        }
    }
    let located = decls
        .iter()
        .map(|decl| span::locate(decl, program, definition))
        .collect::<Result<Vec<_>, _>>()?;
    if let ProgramInput::KoreTemplate(template) = program {
        span::check_template_is_covered(template, &located)?;
    }
    span::check_overlaps(decls, &located)?;

    let rule = sorts::SortRule::new(program, definition)?;
    let mut holes = Vec::with_capacity(decls.len());
    for (decl, (site, anchor_text)) in decls.iter().zip(located) {
        let overridden = rule.check(decl)?;
        let sort = if overridden == Some(SortRefusal::Token) {
            // A token sort has no generator of its own: an overridden hole takes tokens.
            ValueSort::Token {
                sort: decl.sort.clone(),
            }
        } else {
            resolve_value_sort(&decl.sort, &decl.constraints, backend).map_err(|reason| {
                CampaignError::RefusedHoleSort {
                    hole: decl.name.clone(),
                    sort: decl.sort.clone(),
                    reason,
                }
            })?
        };
        let anchor = anchor_text
            .as_deref()
            .map(|text| {
                parse_k_text(text, &sort).map_err(|message| CampaignError::AnchorDoesNotParse {
                    hole: decl.name.clone(),
                    message: format!("`{text}` is not a value of sort {}: {message}", decl.sort),
                })
            })
            .transpose()?;
        holes.push(ResolvedHole {
            decl: decl.clone(),
            site,
            sort,
            anchor_text,
            anchor,
            overridden,
        });
    }
    Ok(ResolvedHoles { holes })
}

/// The hole-sort rule (ARCHITECTURE 2.4, R-11, T-9): refuse `K`, `KItem`, cell sorts, user
/// sorts in the closure of the program start sort's productions, and user token sorts such as
/// `Id`; builtin and hooked sorts that have a generator (`Int`, `Bool`, `String`, `Bytes`,
/// `MInt`) are exempt from the closure rule even though programs contain their literals.
/// Returns `Ok(None)` for an admitted sort and `Ok(Some(refusal))` for a refused sort that
/// `decl.allow_refused_sort` admits (recorded in the report). A sort the definition does not
/// declare is refused whatever the override. Whether a hooked sort has a generator is
/// [`crate::values::resolve_value_sort`]'s part of the rule.
///
/// The closure is taken over the productions of the syntax module, the grammar programs are
/// written in, from the program's start sort (krun's `--sort`), or from the declared sort of
/// `$PGM` when the program has no text.
///
/// # Errors
///
/// [`CampaignError::RefusedHoleSort`] for a refused sort without an override;
/// [`CampaignError::Definition`] when the definition's grammar does not resolve.
pub(crate) fn check_hole_sort(
    decl: &HoleDecl,
    program: &ProgramInput,
    definition: &CompiledDefinition,
) -> Result<Option<SortRefusal>, CampaignError> {
    sorts::SortRule::new(program, definition)?.check(decl)
}

/// Replace every hole of `program` with its printed value, in memory (ARCHITECTURE 2.3).
/// `values` is in the order of `holes`. The program text and binding texts outside the spans
/// are copied byte for byte; `program` itself is never modified.
///
/// # Panics
///
/// When `values` and `holes` differ in length, or `holes` was not resolved against `program`.
pub(crate) fn instantiate(
    program: &ProgramInput,
    holes: &ResolvedHoles,
    values: &[PrintedValue],
) -> InstantiatedProgram {
    assert_eq!(
        holes.holes.len(),
        values.len(),
        "one value per hole, in the order of the holes"
    );
    match program {
        ProgramInput::Source(source) => {
            let mut program_edits = Vec::new();
            let mut binding_edits = BTreeMap::<&str, Vec<(usize, usize, &str)>>::new();
            let mut whole_bindings = BTreeMap::<&str, &str>::new();
            for (hole, value) in holes.holes.iter().zip(values) {
                match &hole.site {
                    HoleSite::Span {
                        text: SpanText::Program,
                        start,
                        end,
                    } => program_edits.push((*start, *end, value.k_text.as_str())),
                    HoleSite::Span {
                        text: SpanText::Binding(name),
                        start,
                        end,
                    } => binding_edits.entry(name.as_str()).or_default().push((
                        *start,
                        *end,
                        value.k_text.as_str(),
                    )),
                    HoleSite::ConfigVar(name) => {
                        whole_bindings.insert(name.as_str(), value.k_text.as_str());
                    }
                    HoleSite::KoreVariable(_) => {
                        panic!("a template hole in a source program")
                    }
                }
            }
            let program_text = source.program.as_ref().map(|text| ProgramText {
                text: replace_spans(&text.text, program_edits),
                ..text.clone()
            });
            let config_vars = source
                .config_vars
                .iter()
                .map(|(name, text)| {
                    let key = name.strip_prefix('$').unwrap_or(name);
                    let text = if let Some(whole) = whole_bindings.get(key) {
                        (*whole).to_owned()
                    } else {
                        replace_spans(text, binding_edits.remove(key).unwrap_or_default())
                    };
                    (name.clone(), text)
                })
                .collect();
            InstantiatedProgram::Source {
                program: program_text,
                config_vars,
            }
        }
        ProgramInput::KoreTemplate(template) => {
            let substitution = holes
                .holes
                .iter()
                .zip(values)
                .map(|(hole, value)| match &hole.site {
                    HoleSite::KoreVariable(variable) => (variable.name.as_str(), &value.kore),
                    HoleSite::Span { .. } | HoleSite::ConfigVar(_) => {
                        panic!("a source hole in a KORE template")
                    }
                })
                .collect::<BTreeMap<_, _>>();
            InstantiatedProgram::Kore(span::substitute(template, &substitution))
        }
    }
}

/// `text` with each `(start, end, replacement)` span replaced; the spans do not overlap.
fn replace_spans(text: &str, mut edits: Vec<(usize, usize, &str)>) -> String {
    edits.sort_unstable_by_key(|(start, ..)| *start);
    let mut output = String::with_capacity(text.len());
    let mut copied = 0;
    for (start, end, replacement) in edits {
        output.push_str(&text[copied..start]);
        output.push_str(replacement);
        copied = end;
    }
    output.push_str(&text[copied..]);
    output
}

/// The per-case round-trip check (ARCHITECTURE 2.3): the configuration assembled from an
/// instantiated program holds, at each hole's position, exactly the value intended.
///
/// A hole's position is located once per campaign and definition by differential parsing: the
/// program is assembled with every anchor, then with one hole's anchor replaced by a second
/// value of its sort. Every difference between the two configurations must lie inside one
/// subterm, which holds the anchor's KORE in the first and the second value's KORE in the
/// second; the path to that subterm is the hole's position. Per case, the configuration must
/// have the anchor configuration's constructors along each hole's path, and the intended value
/// at its end. A value that the grammar reads differently (`-5` read as the negation of `5`)
/// changes the constructors on the path or the value at its end, and the case is `rejected`.
///
/// A KORE-template hole needs no check: substitution places its KORE exactly.
pub(crate) struct RoundTripCheck {
    /// The configuration assembled with every anchor.
    anchor_configuration: KorePattern,
    /// The holes' names, in order.
    names: Vec<String>,
    /// Each hole's position in it, in the order of the holes; `None` for a template hole.
    positions: Vec<Option<Vec<usize>>>,
}

impl RoundTripCheck {
    /// Locate each hole's position in configurations `assembly` builds from `program` over
    /// `definition`, the definition `assembly` was built from.
    ///
    /// # Errors
    ///
    /// [`CampaignError::AnchorDoesNotParse`] when an anchor does not parse back at its hole's
    /// position, or the position cannot be located; [`CampaignError::Program`] when the program
    /// does not assemble with its anchors.
    pub(crate) fn new(
        assembly: &ProgramAssembly,
        definition: &CompiledDefinition,
        program: &ProgramInput,
        holes: &ResolvedHoles,
    ) -> Result<Self, CampaignError> {
        position::locate_all(assembly, definition, program, holes)
    }

    /// Check `assembled` against the intended `values` (in the order of the holes).
    ///
    /// # Errors
    ///
    /// The first hole whose position does not hold its value; the case is `rejected`.
    pub(crate) fn check(
        &self,
        assembled: &KorePattern,
        values: &[PrintedValue],
    ) -> Result<(), RoundTripFailure> {
        position::check(self, assembled, values)
    }
}

#[cfg(test)]
mod tests;
