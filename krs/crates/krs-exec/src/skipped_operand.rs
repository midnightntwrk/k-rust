//! The places of a loaded definition where a value or a condition depends on an operand that
//! `&&`, `||`, `bool::and`, `bool::or`, `bool::implies` or `kequal::ite` skips
//! ([`Semantics::skipped_operands`]).
//!
//! The analysis is k-rust's ([`k_rust::k_rust_backend::short_circuit`]): one analysis of the
//! definition the run commands load, so `krs check` and any other reader of it cannot disagree
//! about which sentences depend on the reading. This module projects it onto the KRS-authored
//! sentences: it reports each originating witness at the sentence that holds it, and a sentence
//! whose dependence originates in a sentence no KRS author wrote (the prelude, a pass k-rust
//! runs) at the nearest KRS-authored sentence of its chain.
//!
//! An equation of a local function k-rust generates from a KRS sentence (a `#lambda` function,
//! what k-rust compiles K's `#let`, `#fun` and `:=K` into) carries that sentence as its author,
//! but the author wrote it as an expression of the sentence, not as a sentence: the sentence
//! alone applies the function, at the place the expression stands. Its witnesses are therefore
//! reported through the sentence, as the witnesses of a sentence no KRS author wrote are: where
//! the sentence's own reading depends on them, and in the part of the sentence that applies the
//! function. So a `let` block that stands as a top-level conjunct of a condition and whose value
//! is itself a top-level conjunction is not reported, as the same conjunction written without
//! the block is not.

use std::collections::BTreeSet;

use k_rust::k_rust_backend::short_circuit::{
    CausePart, SentenceRef, ShortCircuitAnalysis, Witness, equation_parts, is_owise, rewrite_sides,
};
use k_rust::kore::ast::{Attributes, Definition, Pattern, Sentence};
use k_rust::names::KoreAttribute;
use krs_ir::NodeOrigin;
use krs_k_rust::{Author, InputSentenceKind, SentenceProvenance};

use crate::{ExecError, Semantics};

/// The KRS sentence a [`SkippedOperand`] is reported at.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Anchor {
    /// The emitted module of the Definition IR sentence.
    pub module: String,
    /// Its module-local index in the Definition IR.
    pub index: u32,
    /// Its KRS origin.
    pub origin: NodeOrigin,
    /// Its kind before compilation.
    pub kind: InputSentenceKind,
}

/// The part of the sentence that holds the operator.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Part {
    /// A leaf of its condition (a rule's `requires` or left-hand side, an equation's antecedent).
    Condition,
    /// Its result: a rule's or an equation's right-hand side.
    Result,
}

/// Where the operator of a [`SkippedOperand`] is, when it is not in the anchor sentence itself.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Through {
    /// In a sentence the native frontend generated from the anchor (`pass`, k-rust's name of the
    /// generating pass), such as a `let` lifted into a function of its own.
    Generated {
        /// The generating pass's name.
        pass: String,
    },
    /// In a local function k-rust generated from the anchor (`function`, its KORE symbol): what
    /// it compiles a `let` block or a `k::matches!` test of the anchor into, which the anchor
    /// alone applies.
    Local {
        /// The generated function's KORE symbol.
        function: String,
    },
    /// In the prelude's function `function` (its K label), whose equation module `module` of
    /// the prelude writes, which the anchor applies.
    Builtin {
        /// The prelude module.
        module: String,
        /// The function's K label.
        function: String,
    },
}

/// One place where a value or a condition depends on an operand a short-circuiting reading
/// skips, and which may have no value.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SkippedOperand {
    /// The KRS sentence to report it at; `None` for a prelude rule whose whole chain no KRS
    /// author wrote.
    pub anchor: Option<Anchor>,
    /// The part of the sentence holding the operator.
    pub part: Part,
    /// The operator's hook (`BOOL.andThen`, `KEQUAL.ite`, ..).
    pub operator_hook: String,
    /// The argument position of the skipped operand.
    pub position: usize,
    /// The skipped operand, printed through the definition's grammar.
    pub operand: String,
    /// The application in the operand that may have no value, printed likewise.
    pub term: String,
    /// The KORE symbol of [`Self::term`]'s head.
    pub term_symbol: String,
    /// The hook of [`Self::term`]'s head, if it has one.
    pub term_hook: Option<String>,
    /// The KORE head symbol of each argument of [`Self::term`] that is an application (below
    /// sort injections), the value of each that is a domain value (marked `\dv:`), `None` for
    /// any other argument: what tells two applications of one symbol apart where the operator is
    /// written.
    pub term_arguments: Vec<Option<String>>,
    /// Among the operator witnesses of the anchor's emitted sentence with this finding's
    /// operator, position, term symbol and term arguments, in the order the analysis enumerates
    /// them (its conditions, its left-hand side, then its right-hand side, each in post-order),
    /// the index of this one: what tells apart two places the analysis gives equal witnesses, or
    /// witnesses of one term, where the operator is written. `0` for a finding reported through
    /// another sentence.
    pub occurrence: usize,
    /// Whether [`Self::term`]'s head is declared `total` (then it depends on the reading
    /// through a sentence of [`Self::through`]).
    pub term_total: bool,
    /// Where the operator is, when not in the anchor itself.
    pub through: Option<Through>,
    /// The KORE name of the sentence holding the operator, for a finding with no anchor.
    pub sentence: Option<String>,
}

impl Semantics {
    /// Every place of the loaded definition where a value or a condition depends on an operand
    /// that a short-circuit operator skips, at the KRS sentence to report it at (module
    /// documentation), in a fixed order. Span `exec.skipped_operand` is the caller's.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Backend`] when the loaded KORE does not parse or its definition
    /// cannot be selected, which a definition the backend loaded does not do.
    pub fn skipped_operands(&mut self) -> Result<Vec<SkippedOperand>, ExecError> {
        let kore = k_rust::kore::parser::parse_definition(&self.definition_kore)
            .map_err(|error| ExecError::Backend(error.to_string()))?;
        let definition = self
            .backend
            .select_definition(None)
            .map_err(|error| ExecError::Backend(error.to_string()))?;
        let mut analysis = ShortCircuitAnalysis::of(&definition);
        analysis.close_over(&kore);
        let finder = Finder {
            kore: &kore,
            analysis: &analysis,
            provenance: &self.provenance,
            definition: &definition,
            print: &|pattern: &Pattern| {
                self.unparser
                    .print_kore(
                        pattern,
                        &krs_unparse::Options::new(krs_unparse::Mode::Pretty),
                    )
                    .text
            },
        };
        Ok(finder.findings())
    }
}

/// The inputs of [`Semantics::skipped_operands`].
struct Finder<'a> {
    kore: &'a Definition,
    analysis: &'a ShortCircuitAnalysis<'a>,
    provenance: &'a SentenceProvenance,
    definition: &'a k_rust::k_rust_backend::definition::BackendDefinition,
    print: &'a dyn Fn(&Pattern) -> String,
}

/// Who wrote a sentence of the loaded KORE.
enum Writer {
    /// A KRS sentence, reported at this anchor.
    Krs(Anchor),
    /// Another sentence: what wrote it.
    Other(Through),
}

impl Finder<'_> {
    fn findings(&self) -> Vec<SkippedOperand> {
        let mut findings = BTreeSet::new();
        let mut anchored = BTreeSet::new();
        self.own_findings(&mut findings, &mut anchored);
        self.chain_findings(&mut findings, &anchored);
        findings.into_iter().collect()
    }

    /// Step 1: every originating witness of a KRS-authored sentence, at that sentence, into
    /// `findings`, with each sentence that holds one into `anchored`.
    fn own_findings(
        &self,
        findings: &mut BTreeSet<SkippedOperand>,
        anchored: &mut BTreeSet<SentenceRef>,
    ) {
        for (module_index, module) in self.kore.modules.iter().enumerate() {
            for (sentence_index, sentence) in module.sentences.iter().enumerate() {
                let Sentence::Axiom {
                    pattern,
                    attributes,
                    ..
                } = sentence
                else {
                    continue;
                };
                let at = SentenceRef {
                    module: module_index,
                    sentence: sentence_index,
                };
                let Some(Writer::Krs(anchor)) = self.writer(at) else {
                    continue;
                };
                let Some(witnesses) = self.witnesses(pattern, attributes) else {
                    continue;
                };
                // Each witness's index among the earlier ones of the sentence that a reader of
                // the written sentence cannot tell from it ([`SkippedOperand::occurrence`]).
                let mut seen = Vec::new();
                for (part, witness) in witnesses {
                    let Some(site) = site(&witness) else {
                        continue;
                    };
                    let occurrence = seen.iter().filter(|earlier| **earlier == site).count();
                    seen.push(site);
                    if self.analysis.originates(&witness)
                        && let Some(mut finding) =
                            self.finding(Some(anchor.clone()), part, &witness, None, None)
                    {
                        finding.occurrence = occurrence;
                        anchored.insert(at);
                        findings.insert(finding);
                    }
                }
            }
        }
    }

    /// Steps 2 and 3: each sentence not in `anchored` whose dependence originates where no KRS
    /// author wrote, into `findings`.
    fn chain_findings(
        &self,
        findings: &mut BTreeSet<SkippedOperand>,
        anchored: &BTreeSet<SentenceRef>,
    ) {
        let starts = self
            .analysis
            .rule_readings(self.kore)
            .into_iter()
            .map(|reading| {
                let first = reading
                    .applicability
                    .map(|(part, witness)| (part_of(&part), witness))
                    .or_else(|| reading.result.map(|witness| (Part::Result, witness)));
                (reading.rule, true, first)
            })
            .chain(
                self.analysis
                    .equation_readings(self.kore)
                    .into_iter()
                    .map(|reading| {
                        let first = reading
                            .result
                            .map(|witness| (Part::Result, witness))
                            .or_else(|| {
                                reading
                                    .valued
                                    .map(|(part, witness)| (part_of(&part), witness))
                            });
                        (reading.equation, false, first)
                    }),
            );
        // The part is the one of the sentence the reading starts at: where its own value or
        // applicability depends on the operator, which is where its author sees the dependence.
        for (at, rule, first) in starts {
            let Some((part, witness)) = first else {
                continue;
            };
            if anchored.contains(&at) {
                continue;
            }
            let Some((origin_at, origin_part, origin, krs_between)) =
                self.origin(at, part, witness)
            else {
                continue;
            };
            match (self.writer(at), self.writer(origin_at)) {
                // A KRS sentence holds the origin: step 1 reports it there, or at the
                // competitor of an `owise` equation whose guard holds it.
                (_, Some(Writer::Krs(_))) => {}
                // A KRS sentence between them is a reading of its own, reported by its own
                // chain, so a sentence that applies it is not warned again.
                _ if krs_between => {}
                // A local function's own reading is its sentence's: the sentence reports it
                // where its own reading depends on it.
                (Some(Writer::Other(Through::Local { .. })), _) => {}
                (Some(Writer::Krs(anchor)), other) => {
                    let through = match other {
                        Some(Writer::Other(through)) => Some(through),
                        _ => None,
                    };
                    if let Some(finding) = self.finding(Some(anchor), part, &origin, through, None)
                    {
                        findings.insert(finding);
                    }
                }
                // A function of the prelude depends on the reading only where a sentence applies
                // it, and is reported there; a rewrite rule whose chain no KRS author wrote any
                // sentence of is reported unanchored, as kink judges its runs.
                _ if !rule => {}
                _ => {
                    let name = self.sentence_name(origin_at);
                    if let Some(finding) =
                        self.finding(None, origin_part, &origin, None, Some(name))
                    {
                        findings.insert(finding);
                    }
                }
            }
        }
    }

    /// Every operator witness of the axiom `pattern` with `attributes`, with the part that holds
    /// it: a rewrite rule's conditions and left-hand side, then its right-hand side; an equation's
    /// antecedent (without an `owise` equation's guard), then its right-hand side. `None` for an
    /// axiom of another shape.
    fn witnesses(
        &self,
        pattern: &Pattern,
        attributes: &Attributes,
    ) -> Option<Vec<(Part, Witness)>> {
        let mut witnesses = Vec::new();
        if let Some((conditions, left, right)) = rewrite_sides(pattern) {
            for side in conditions.into_iter().chain([left]) {
                witnesses.extend(
                    self.analysis
                        .condition_operator_witnesses(side, false)
                        .into_iter()
                        .map(|(_, witness)| (Part::Condition, witness)),
                );
            }
            witnesses.extend(
                self.analysis
                    .operator_witnesses(right)
                    .into_iter()
                    .map(|witness| (Part::Result, witness)),
            );
        } else if let Some((_, condition, right)) = equation_parts(pattern) {
            if let Some(condition) = condition {
                witnesses.extend(
                    self.analysis
                        .condition_operator_witnesses(condition, is_owise(attributes))
                        .into_iter()
                        .map(|(_, witness)| (Part::Condition, witness)),
                );
            }
            witnesses.extend(
                self.analysis
                    .operator_witnesses(right)
                    .into_iter()
                    .map(|witness| (Part::Result, witness)),
            );
        } else {
            return None;
        }
        Some(witnesses)
    }

    /// The first originating witness of the chain from `witness` at `part` of the sentence `at`,
    /// with the sentence and part that hold it ([`ShortCircuitAnalysis::next_reason`]), and
    /// whether a sentence strictly between `at` and that one has a KRS author.
    fn origin(
        &self,
        mut at: SentenceRef,
        mut part: Part,
        mut witness: Witness,
    ) -> Option<(SentenceRef, Part, Witness, bool)> {
        let start = at;
        let mut krs_between = false;
        let mut followed = BTreeSet::new();
        loop {
            if self.analysis.originates(&witness) {
                return Some((at, part, witness, krs_between));
            }
            let (key, reason) = self.analysis.next_reason(&witness)?;
            if !followed.insert(key.clone()) {
                return None;
            }
            if at != start && matches!(self.writer(at), Some(Writer::Krs(_))) {
                krs_between = true;
            }
            at = reason.equation;
            part = part_of(&reason.part);
            witness = reason.witness.clone();
        }
    }

    /// Who wrote the sentence `at`: its `UNIQUE_ID`'s first author, or the pass that generated
    /// it, or, for an equation of a local function k-rust generated from a KRS sentence (module
    /// documentation), that function; `None` for a sentence with no id the provenance knows.
    fn writer(&self, at: SentenceRef) -> Option<Writer> {
        let (_, sentence) = at.resolve(self.kore)?;
        let Sentence::Axiom {
            pattern,
            attributes,
            ..
        } = sentence
        else {
            return None;
        };
        let id = string_attribute(attributes, KoreAttribute::UniqueId)?;
        let provenance = self.provenance.get(id)?;
        if let Some(pass) = provenance.generated_by() {
            return Some(Writer::Other(Through::Generated {
                pass: pass.as_str().to_owned(),
            }));
        }
        match provenance.authors().first()? {
            Author::Krs { .. }
                if let Some((head, _, _)) = equation_parts(pattern)
                    && is_local_function(head) =>
            {
                Some(Writer::Other(Through::Local {
                    function: head.to_owned(),
                }))
            }
            Author::Krs {
                module,
                index,
                kind,
                origin,
            } => Some(Writer::Krs(Anchor {
                module: module.clone(),
                index: *index,
                origin: origin.clone(),
                kind: *kind,
            })),
            Author::Builtin { module, .. } => Some(Writer::Other(Through::Builtin {
                module: module.clone(),
                function: equation_parts(pattern)
                    .map(|(head, _, _)| k_rust::kast::identifier::label_or_name(head))
                    .unwrap_or_default(),
            })),
        }
    }

    /// The name of the sentence `at`: its label, else its `UNIQUE_ID`.
    fn sentence_name(&self, at: SentenceRef) -> String {
        let Some((module, Sentence::Axiom { attributes, .. })) = at.resolve(self.kore) else {
            return String::new();
        };
        let name = string_attribute(attributes, KoreAttribute::Label)
            .or_else(|| string_attribute(attributes, KoreAttribute::UniqueId))
            .unwrap_or("an unnamed axiom");
        format!("{} in {}", name, module.name)
    }

    /// The finding of the operator witness `witness`; `None` for a function witness.
    fn finding(
        &self,
        anchor: Option<Anchor>,
        part: Part,
        witness: &Witness,
        through: Option<Through>,
        sentence: Option<String>,
    ) -> Option<SkippedOperand> {
        let Witness::Operator {
            operator,
            position,
            operand,
            term,
            ..
        } = witness
        else {
            return None;
        };
        let hook = |name: &str| {
            self.definition
                .symbols()
                .get(name)
                .and_then(|symbol| symbol.attributes.hook.as_deref())
                .map(str::to_owned)
        };
        let (term_symbol, term_arguments) = match term {
            Pattern::Application { symbol, arguments } => (
                symbol.name.clone(),
                arguments.iter().map(application_head).collect(),
            ),
            _ => (String::new(), Vec::new()),
        };
        Some(SkippedOperand {
            anchor,
            part,
            operator_hook: hook(operator).unwrap_or_default(),
            position: *position,
            operand: (self.print)(operand),
            term: (self.print)(term),
            term_hook: hook(&term_symbol),
            term_arguments,
            occurrence: 0,
            term_total: !self.analysis.partial().contains(&term_symbol),
            term_symbol,
            through,
            sentence,
        })
    }
}

/// What a reader of the written sentence tells an operator witness by: its operator, position,
/// term symbol and term arguments ([`SkippedOperand::occurrence`]); `None` for a function
/// witness.
fn site(witness: &Witness) -> Option<(String, usize, String, Vec<Option<String>>)> {
    let Witness::Operator {
        operator,
        position,
        term,
        ..
    } = witness
    else {
        return None;
    };
    Some(match term {
        Pattern::Application { symbol, arguments } => (
            operator.clone(),
            *position,
            symbol.name.clone(),
            arguments.iter().map(application_head).collect(),
        ),
        _ => (operator.clone(), *position, String::new(), Vec::new()),
    })
}

/// The head symbol of `pattern` when it is an application, below sort injections, or its value,
/// marked `\dv:`, when it is a domain value.
fn application_head(pattern: &Pattern) -> Option<String> {
    match pattern {
        Pattern::Application { symbol, arguments } if symbol.name == "inj" => {
            arguments.first().and_then(application_head)
        }
        Pattern::Application { symbol, .. } => Some(symbol.name.clone()),
        Pattern::DomainValue { value, .. } => Some(format!(
            "\\dv:{}",
            String::from_utf8_lossy(value.as_bytes())
        )),
        _ => None,
    }
}

/// Whether the KORE symbol `symbol` is a local function k-rust generated (a `#lambda` label):
/// every such label is unused elsewhere in the definition, so the sentence it was generated from
/// is its only user.
fn is_local_function(symbol: &str) -> bool {
    k_rust::kast::identifier::decode_label(symbol).is_ok_and(|label| {
        matches!(
            k_rust::kast::GeneratedLabel::of_name(&label),
            Some(k_rust::kast::GeneratedLabel::Lambda { .. })
        )
    })
}

const fn part_of(part: &CausePart) -> Part {
    match part {
        CausePart::Condition { .. } => Part::Condition,
        CausePart::RightSide => Part::Result,
    }
}

fn string_attribute(attributes: &Attributes, attribute: KoreAttribute) -> Option<&str> {
    attributes.string(attribute).ok().flatten()
}
