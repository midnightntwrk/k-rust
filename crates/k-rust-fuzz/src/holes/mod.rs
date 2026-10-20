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
//! The hole's sort, and every sort its values may contain, must be data ([`check_hole_sort`]).
//! Builtin sorts with a generator are admitted although programs contain their literals; `K`,
//! `KItem`, `KResult`, cell sorts, the sorts programs are written in and token sorts such as
//! `Id` are refused. An override (`allow-refused-sort`) admits all but an undeclared sort, and
//! the report records it. A template hole's sort must be its variable's sort.

mod position;
mod sorts;
mod span;

use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    k_rust_backend::definition::BackendDefinition,
    kore::ast::{Pattern as KorePattern, Sort as KoreSort, Variable as KoreVariable},
};
use serde::{Deserialize, Serialize};

use crate::{
    assemble::ProgramAssembly,
    error::{CampaignError, SortRefusal},
    report::SortOverride,
    spec::{CompiledDefinition, ProgramInput, ProgramText},
    values::{Constraints, TextSyntax, Value, ValueSort, print::parse_k_text, resolve_value_sort},
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
    /// Optional constraints (ARCHITECTURE 2.5); none when omitted.
    #[serde(default)]
    pub constraints: Constraints,
    /// Admit a sort the hole-sort rule refuses (ARCHITECTURE 2.4); recorded in the report.
    /// `false` when omitted.
    #[serde(default)]
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
    /// Every refusal the override admitted: the refused sort and why, the hole's own sort first,
    /// then the contained sorts by name. Empty when nothing was refused.
    pub(crate) refusals: Vec<(String, SortRefusal)>,
}

impl ResolvedHole {
    /// The KORE sort of the hole's declared sort ([`ValueSort::kore_sort`]): the sort of every
    /// value the hole takes, whatever its own subsort.
    ///
    /// # Errors
    ///
    /// As [`ValueSort::kore_sort`].
    pub(crate) fn kore_sort(&self) -> Result<k_rust::kore::ast::Sort, String> {
        self.sort.kore_sort()
    }

    /// The report's record of what this hole's override admitted (ARCHITECTURE 2.4): one
    /// [`SortOverride`] per entry of [`Self::refusals`], in order, naming the refused sort, so
    /// that a hole whose values may contain two refused sorts (`both(Id, Stmt)`) reports both.
    /// Empty when nothing was refused.
    pub(crate) fn sort_overrides(&self) -> Vec<SortOverride> {
        self.refusals
            .iter()
            .map(|(sort, refusal)| SortOverride {
                hole: self.decl.name.clone(),
                sort: sort.clone(),
                refusal: format!("{refusal:?}"),
            })
            .collect()
    }
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
    /// [`crate::values::print::print_k_text`] of the value. Always present for a span or
    /// configuration-variable hole, whose text it replaces; for a KORE-template hole, which
    /// needs only the KORE, it is the witness's K text when the value prints, and `None` when
    /// it does not (a definition without K-text syntax, say).
    pub(crate) k_text: Option<String>,
    /// [`crate::values::print::to_kore`] of the value: at its own sort, not injected.
    pub(crate) kore: KorePattern,
    /// The KORE sort of [`Self::kore`], the value's own sort
    /// ([`crate::values::print::to_kore_with_sort`]).
    pub(crate) sort: KoreSort,
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
    // Collection and data values print and read back as K text only through the definition's
    // syntax (ARCHITECTURE 3, D19). A definition built without the compiler's syntax outputs
    // (both empty) resolves without it: its collection and data anchors do not read back.
    let text = (!definition.syntax_definition_kore.is_empty()
        || !definition.macros_kore.is_empty())
    .then(|| {
        TextSyntax::new(
            &definition.frontend_definition,
            &definition.main_module,
            &definition.syntax_definition_kore,
            &definition.macros_kore,
            rule.excluded(),
        )
        .map_err(|message| CampaignError::Definition {
            message: format!("the definition's K-text syntax: {message}"),
        })
    })
    .transpose()?;
    let mut holes = Vec::with_capacity(decls.len());
    for (decl, (site, anchor_text)) in decls.iter().zip(located) {
        let refuse = |reason| CampaignError::RefusedHoleSort {
            hole: decl.name.clone(),
            sort: decl.sort.clone(),
            reason,
        };
        let verdict = rule.verdict(decl)?;
        let mut refusals = verdict.all(&decl.sort);
        if let Some((_, reason)) = refusals.first()
            && !decl.allow_refused_sort
        {
            return Err(refuse(reason.clone()));
        }
        // Only the hole's own token sort makes it a token hole; an override of a token sort its
        // values contain (`Map<Id, Int>`, `rec(Id, Int)`) leaves the hole a value of its sort.
        let own_token = verdict.own == Some(SortRefusal::Token);
        let sort = if own_token {
            ValueSort::Token {
                sort: decl.sort.clone(),
            }
        } else {
            match &text {
                Some(text) => text.resolve(&decl.sort, &decl.constraints, backend),
                None => resolve_value_sort(&decl.sort, &decl.constraints, backend),
            }
            .map_err(refuse)?
        };
        // The backend may see a token sort the frontend's token declarations do not name; a
        // token hole is admitted only with a recorded override, whichever side saw it.
        if matches!(sort, ValueSort::Token { .. }) && !own_token {
            if !decl.allow_refused_sort {
                return Err(refuse(SortRefusal::Token));
            }
            refusals.insert(0, (decl.sort.clone(), SortRefusal::Token));
        }
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
            refusals,
        });
    }
    Ok(ResolvedHoles { holes })
}

/// The hole-sort rule (ARCHITECTURE 2.4 as amended by D17, R-11, T-9). Refused: `K`, `KItem`,
/// `KResult` and K's other internal sorts, cell sorts, user sorts programs are written in, and
/// user token sorts such as `Id`. Builtin and hooked sorts that have a generator (`Int`,
/// `Bool`, `String`, `Bytes`, `MInt`) are admitted even though programs contain their literals.
/// The rule also applies to every sort a value of the hole's sort may contain: a collection's
/// declared element sorts, and transitively the argument sorts of the main module's productions
/// of a data sort, so `List<Stmt>`, `List<K>` and a record holding an `AExp` are refused. A
/// collection reached inside a data sort declares no element sorts, so it holds `KItem`s and is
/// refused as a computation.
///
/// Returns `Ok(None)` for an admitted sort and `Ok(Some(refusal))` for a refused sort that
/// `decl.allow_refused_sort` admits (recorded in the report). A sort the definition does not
/// declare is refused whatever the override. Whether a hooked sort has a generator is
/// [`crate::values::resolve_value_sort`]'s part of the rule.
///
/// The sorts programs are written in are those reachable from the program's start sort (krun's
/// `--sort`, or the declared sort of `$PGM` when the program has no text) through the
/// productions of the syntax module. Every sort is a `KItem`, so when that start sort is `K` or
/// `KItem` (or the closure reaches one of them) they are every non-hooked sort the syntax
/// module declares.
///
/// # Errors
///
/// [`CampaignError::RefusedHoleSort`] for a refused sort without an override;
/// [`CampaignError::Definition`] when the definition's grammar does not resolve.
#[cfg(test)]
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
                let text = || {
                    value
                        .k_text
                        .as_deref()
                        .expect("a source hole's value is printed as K text")
                };
                match &hole.site {
                    HoleSite::Span {
                        text: SpanText::Program,
                        start,
                        end,
                    } => program_edits.push((*start, *end, text())),
                    HoleSite::Span {
                        text: SpanText::Binding(name),
                        start,
                        end,
                    } => {
                        binding_edits.entry(name.as_str()).or_default().push((
                            *start,
                            *end,
                            text(),
                        ));
                    }
                    HoleSite::ConfigVar(name) => {
                        whole_bindings.insert(name.as_str(), text());
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
            // The variable has the hole's declared sort (D17), and a value is at its own sort,
            // a subsort of it for a data value of a constructor of a subsort: the substituted
            // term is the value injected to the variable's sort, so that the configuration is
            // as well sorted as the template.
            let substitution = holes
                .holes
                .iter()
                .zip(values)
                .map(|(hole, value)| match &hole.site {
                    HoleSite::KoreVariable(variable) => (
                        variable.name.as_str(),
                        crate::values::term::inject(
                            value.kore.clone(),
                            &value.sort,
                            &variable.sort,
                        ),
                    ),
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

    /// The configuration assembled with every anchor.
    pub(crate) fn anchor_configuration(&self) -> &KorePattern {
        &self.anchor_configuration
    }

    /// Each hole's position in [`Self::anchor_configuration`], in the order of the holes: the
    /// path of `kore::walk::children` indices to the subterm that holds the hole's value
    /// (ARCHITECTURE 2.3). `None` for a KORE-template hole, which has no anchor.
    pub(crate) fn positions(&self) -> &[Option<Vec<usize>>] {
        &self.positions
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
