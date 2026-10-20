//! Holes: an overlay of typed spans on an unmodified program (ARCHITECTURE 2). Owner: FZ-02.
//!
//! Neither the specification nor the program is edited or copied. A hole addresses a literal of
//! the program text by `find` and `literal` (the same addressing as kink's mutation edits), a
//! configuration variable by name, or a free variable of a KORE template. A case replaces each
//! span in memory with a value printed as K text, assembles the configuration exactly as krun
//! does ([`crate::assemble`]), and checks that every value parsed back to the value intended.

use k_rust::{
    k_rust_backend::definition::BackendDefinition,
    kore::ast::{Pattern as KorePattern, Variable as KoreVariable},
};
use serde::{Deserialize, Serialize};

use crate::{
    assemble::ProgramAssembly,
    error::{CampaignError, SortRefusal},
    spec::{CompiledDefinition, ProgramInput},
    values::{Constraints, Value, ValueSort},
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

/// The address of one literal in the program text (ARCHITECTURE 2.2, T-9).
///
/// `find` must occur exactly once in the addressed line (or the whole program without `line`),
/// and `literal`, the hole's text, exactly once inside `find`. `find` may equal `literal` when
/// the literal is unique, and otherwise carries enough context to make the span unique
/// (`find = "x = 7;"`, `literal = "7"`).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct SpanAddress {
    /// The program's name ([`crate::spec::ProgramText::name`]).
    pub program: String,
    /// The one-based line the span is on.
    pub line: Option<u32>,
    /// A text occurring exactly once in the line or program, containing the literal.
    pub find: String,
    /// The hole's literal, occurring exactly once in `find`; the hole's anchor value.
    pub literal: String,
}

/// Where a resolved hole sits.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum HoleSite {
    /// The byte range of the literal in the program text.
    Span {
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
/// program and `literal` exactly once in `find`; configuration-variable and template holes name
/// a declared variable or a free template variable, and every free template variable is a
/// hole; spans do not overlap; each sort passes [`check_hole_sort`] (or is overridden) and
/// resolves to a [`ValueSort`] ([`crate::values::resolve_value_sort`]); each anchor text parses
/// as a value of that sort. `backend` is the baseline's internalized definition. Whether an
/// anchor parses back *in the program* is checked by [`RoundTripCheck::new`].
///
/// # Errors
///
/// [`CampaignError::DuplicateHole`], [`CampaignError::HoleSpan`],
/// [`CampaignError::OverlappingHoles`], [`CampaignError::RefusedHoleSort`],
/// [`CampaignError::AnchorDoesNotParse`], [`CampaignError::InvalidConstraints`].
pub(crate) fn resolve(
    decls: &[HoleDecl],
    program: &ProgramInput,
    definition: &CompiledDefinition,
    backend: &BackendDefinition,
) -> Result<ResolvedHoles, CampaignError> {
    unimplemented!("FZ-02")
}

/// The hole-sort rule (ARCHITECTURE 2.4, R-11, T-9): refuse `K`, `KItem`, cell sorts, user
/// sorts in the closure of the program start sort's productions, and user token sorts such as
/// `Id`; builtin and hooked sorts that have a generator (`Int`, `Bool`, `String`, `Bytes`,
/// `MInt`) are exempt from the closure rule even though programs contain their literals.
/// Returns `Ok(None)` for an admitted sort and `Ok(Some(refusal))` for a refused sort that
/// `decl.allow_refused_sort` admits (recorded in the report).
///
/// # Errors
///
/// [`CampaignError::RefusedHoleSort`] for a refused sort without an override.
pub(crate) fn check_hole_sort(
    decl: &HoleDecl,
    program: &ProgramInput,
    definition: &CompiledDefinition,
) -> Result<Option<SortRefusal>, CampaignError> {
    unimplemented!("FZ-02")
}

/// Replace every hole of `program` with its printed value, in memory (ARCHITECTURE 2.3).
/// `values` is in the order of `holes`. The program text outside the spans is copied byte for
/// byte; `program` itself is never modified.
pub(crate) fn instantiate(
    program: &ProgramInput,
    holes: &ResolvedHoles,
    values: &[PrintedValue],
) -> InstantiatedProgram {
    unimplemented!("FZ-02")
}

/// The per-case round-trip check (ARCHITECTURE 2.3): the configuration assembled from an
/// instantiated program holds, at each hole's position, exactly the value intended.
///
/// The positions are located once per campaign and definition (differential parsing is one
/// way: assemble with two distinct values and require exactly one differing position).
pub(crate) struct RoundTripCheck {
    _positions: (),
}

impl RoundTripCheck {
    /// Locate each hole's position in configurations `assembly` builds from `program`.
    ///
    /// # Errors
    ///
    /// [`CampaignError::AnchorDoesNotParse`] when an anchor does not parse back at its hole's
    /// position; [`CampaignError::Program`] when the program does not assemble with its anchors.
    pub(crate) fn new(
        assembly: &mut ProgramAssembly,
        program: &ProgramInput,
        holes: &ResolvedHoles,
    ) -> Result<Self, CampaignError> {
        unimplemented!("FZ-02")
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
        unimplemented!("FZ-02")
    }
}
