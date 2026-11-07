//! The places of a loaded definition where a value or a condition depends on an operand that
//! `&&`, `||`, `bool::and`, `bool::or`, `bool::implies` or `kequal::ite` skips
//! ([`Semantics::skipped_operands`]).
//!
//! The analysis is k-rust's ([`k_rust::k_rust_backend::short_circuit`]): one analysis of the
//! definition the run commands load, so `krs check` and any other reader of it cannot disagree
//! about which sentences depend on the reading. This module projects it onto the KRS-authored
//! sentences: it reports each originating witness at the sentence that holds it, and a
//! dependence that originates in a sentence no KRS author wrote (the prelude, a pass k-rust
//! runs) at the place of the KRS sentence that applies it.
//!
//! A reader fixes origins one at a time, at the places they are written, so every originating
//! witness a KRS sentence depends on is reported, each at its own place, and how the author
//! wrote an expression must not change which are: an expression written in a `let` block is
//! reported as the same expression written in place.
//!
//! An equation of a local function k-rust generates from a KRS sentence (a `#lambda` function,
//! what k-rust compiles K's `#let`, `#fun` and `:=K` into) carries that sentence as its author,
//! but the author wrote it as an expression of the sentence, not as a sentence: the sentence
//! alone applies the function, at the place the expression stands. Its equations are therefore
//! read in place of the application ([`ShortCircuitAnalysis::axiom_visits`]), as the expression
//! written there would be, and their witnesses are reported at the sentence, in the part of the
//! sentence that applies the function. So a `let` block that stands as a top-level conjunct of a
//! condition and whose value is itself a top-level conjunction is not reported, as the same
//! conjunction written without the block is not, and each origin inside a block is reported as
//! it is outside one.
//!
//! A function of the prelude (or of a sentence a pass generated) that depends on the reading is
//! no place the author writes: each application of one by a KRS sentence, where the sentence's
//! reading depends on it, is reported once, at the application, with the first origin its chain
//! of reasons reaches. A user function is reported at its own equations, never at its users.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::k_rust_backend::short_circuit::{
    CausePart, Inlined, SentenceRef, ShortCircuitAnalysis, Visit, Witness, equation_parts, is_owise,
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
    /// the prelude writes, which the anchor applies (`applied`, its K label, is `function` or a
    /// function whose value depends on `function`'s).
    Builtin {
        /// The prelude module.
        module: String,
        /// The K label of the function whose equation holds the operator.
        function: String,
        /// The K label of the prelude function the anchor applies.
        applied: String,
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
    /// The index of the operator's application among the applications of its symbol in the
    /// anchor's emitted sentence, in the order the analysis walks them
    /// ([`Visit::Operator`]'s `occurrence`: its conditions, its left-hand side, then its
    /// right-hand side, each in post-order, a local function's equations read where the sentence
    /// applies it, and no conjunction at the top of a condition counted): what tells apart two
    /// places that give equal witnesses, or witnesses whose terms a reader of the written
    /// sentence cannot tell apart, where the operator is written. It counts every application
    /// of the operator, whatever its operand, since no term the analysis picks for one decides
    /// which written operator it is. For a finding through the prelude, the index of the
    /// application among the sentence's applications of the same prelude function, in that
    /// order ([`Visit::Applied`]'s `occurrence`), a conjunctive call at the top of a condition
    /// counted though it has no finding, so that the count is of every application a reader of
    /// the written sentence sees; `0` for a finding with no anchor.
    pub occurrence: usize,
    /// Whether [`Self::term`]'s head is a local function k-rust generates from the anchor (a
    /// `let` block's, a `k::matches!` test's), which the author wrote as that expression.
    pub term_local: bool,
    /// For a [`Self::term_local`] term, an application in the local function's value that may
    /// have no value (through the local functions it applies), as the expression the author
    /// wrote in the block: its KORE symbol, hook and argument heads, as [`Self::term_symbol`],
    /// [`Self::term_hook`] and [`Self::term_arguments`] give the term's.
    pub value_term: Option<TermHead>,
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

/// An application's KORE head symbol, its hook, and the head of each of its arguments
/// ([`SkippedOperand::term_arguments`]).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TermHead {
    /// The KORE symbol.
    pub symbol: String,
    /// The symbol's hook, if it has one.
    pub hook: Option<String>,
    /// Each argument's head, as [`SkippedOperand::term_arguments`] gives a term's.
    pub arguments: Vec<Option<String>>,
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
        self.sentence_findings(&mut findings);
        self.unanchored_findings(&mut findings);
        findings.into_iter().collect()
    }

    /// Every finding of each KRS-authored sentence, at that sentence: each originating operator
    /// witness of the sentence, its local functions read in place
    /// ([`ShortCircuitAnalysis::axiom_visits`]), and each application of a function no KRS author
    /// wrote that depends on the reading, with the origin its chain reaches.
    fn sentence_findings(&self, findings: &mut BTreeSet<SkippedOperand>) {
        let inline = self.local_functions();
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
                let Some(visits) = self.analysis.axiom_visits(pattern, attributes, &inline) else {
                    continue;
                };
                for visit in visits {
                    match visit {
                        Visit::Operator {
                            condition,
                            witness,
                            within,
                            occurrence,
                        } => {
                            if !self.analysis.originates(&witness) {
                                continue;
                            }
                            let through = within.last().map(|function| Through::Local {
                                function: function.clone(),
                            });
                            if let Some(mut finding) = self.finding(
                                Some(anchor.clone()),
                                part(condition),
                                &witness,
                                through,
                                None,
                            ) {
                                finding.occurrence = occurrence;
                                findings.insert(finding);
                            }
                        }
                        Visit::Applied {
                            condition,
                            symbol,
                            dependence,
                            occurrence,
                            ..
                        } => {
                            let start = Witness::Function {
                                symbol: symbol.clone(),
                                dependence,
                            };
                            if let Some(mut finding) =
                                self.applied_finding(at, &anchor, part(condition), &symbol, start)
                            {
                                finding.occurrence = occurrence;
                                findings.insert(finding);
                            }
                        }
                    }
                }
            }
        }
    }

    /// The finding of the KRS sentence `at`'s application of the reading-dependent function
    /// `symbol`, through `start`: the first originating witness its chain of reasons reaches,
    /// when no KRS author wrote the sentence that holds it nor any sentence between (a user
    /// function is reported at its own equations, and a KRS sentence between is a reading of its
    /// own).
    fn applied_finding(
        &self,
        at: SentenceRef,
        anchor: &Anchor,
        part: Part,
        symbol: &str,
        start: Witness,
    ) -> Option<SkippedOperand> {
        let (_, first) = self.analysis.next_reason(&start)?;
        if self.authored(first.equation) {
            return None;
        }
        let (origin_at, _, origin, krs_between) = self.origin(at, part, start)?;
        if krs_between || self.authored(origin_at) {
            return None;
        }
        let through = match self.writer(origin_at) {
            Some(Writer::Other(Through::Builtin {
                module, function, ..
            })) => Some(Through::Builtin {
                module,
                function,
                applied: k_rust::kast::identifier::label_or_name(symbol),
            }),
            Some(Writer::Other(through)) => Some(through),
            Some(Writer::Krs(_)) | None => None,
        };
        self.finding(Some(anchor.clone()), part, &origin, through, None)
    }

    /// Each rewrite rule no KRS author wrote whose dependence originates where no KRS author
    /// wrote either (a prelude rule reaching a prelude origin): reported with no anchor, as kink
    /// judges its runs. A function of the prelude depends on the reading only where a sentence
    /// applies it, and is reported there.
    fn unanchored_findings(&self, findings: &mut BTreeSet<SkippedOperand>) {
        for reading in self.analysis.rule_readings(self.kore) {
            if matches!(
                self.writer(reading.rule),
                Some(Writer::Krs(_) | Writer::Other(Through::Local { .. }))
            ) {
                continue;
            }
            let first = reading
                .applicability
                .map(|(part, witness)| (part_of(&part), witness))
                .or_else(|| reading.result.map(|witness| (Part::Result, witness)));
            let Some((part, witness)) = first else {
                continue;
            };
            let Some((origin_at, origin_part, origin, krs_between)) =
                self.origin(reading.rule, part, witness)
            else {
                continue;
            };
            if krs_between || self.authored(origin_at) {
                continue;
            }
            let name = self.sentence_name(origin_at);
            if let Some(finding) = self.finding(None, origin_part, &origin, None, Some(name)) {
                findings.insert(finding);
            }
        }
    }

    /// The equations of every local function k-rust generated ([`is_local_function`]), which a
    /// sentence's walk reads in place of their applications.
    fn local_functions(&self) -> BTreeMap<String, Vec<Inlined<'_>>> {
        let mut functions: BTreeMap<String, Vec<Inlined<'_>>> = BTreeMap::new();
        for module in &self.kore.modules {
            for sentence in &module.sentences {
                let Sentence::Axiom {
                    pattern,
                    attributes,
                    ..
                } = sentence
                else {
                    continue;
                };
                if let Some((head, condition, right)) = equation_parts(pattern)
                    && is_local_function(head)
                {
                    functions.entry(head.to_owned()).or_default().push(Inlined {
                        condition,
                        right,
                        owise: is_owise(attributes),
                    });
                }
            }
        }
        functions
    }

    /// The first originating witness of the chain from `witness` at `part` of the sentence `at`,
    /// with the sentence and part that hold it ([`ShortCircuitAnalysis::next_reason`]), and
    /// whether a KRS author wrote a sentence strictly between `at` and that one ([`Self::authored`]).
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
            if at != start && self.authored(at) {
                krs_between = true;
            }
            at = reason.equation;
            part = part_of(&reason.part);
            witness = reason.witness.clone();
        }
    }

    /// Whether a KRS author wrote the sentence `at`, as a sentence or as an expression of one (a
    /// local function's equation, [`Through::Local`]).
    fn authored(&self, at: SentenceRef) -> bool {
        matches!(
            self.writer(at),
            Some(Writer::Krs(_) | Writer::Other(Through::Local { .. }))
        )
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
            Author::Builtin { module, .. } => {
                let function = equation_parts(pattern)
                    .map(|(head, _, _)| k_rust::kast::identifier::label_or_name(head))
                    .unwrap_or_default();
                Some(Writer::Other(Through::Builtin {
                    module: module.clone(),
                    applied: function.clone(),
                    function,
                }))
            }
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

    /// An application that may have no value in the value of the local function `function`
    /// (in its equations' right-hand sides, the first of their `May` that is no local function's
    /// application, else one in a local function they apply), as its symbol and argument heads;
    /// `None` when there is none, or `function` is in `visited`.
    fn value_term(
        &self,
        function: &str,
        visited: &mut BTreeSet<String>,
    ) -> Option<(String, Vec<Option<String>>)> {
        if !visited.insert(function.to_owned()) {
            return None;
        }
        let rights = self
            .kore
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
            .filter_map(|sentence| match sentence {
                Sentence::Axiom { pattern, .. } => equation_parts(pattern),
                _ => None,
            })
            .filter(|(head, _, _)| *head == function)
            .map(|(_, _, right)| right);
        let mut local = Vec::new();
        for right in rights {
            for term in self.analysis.may(right) {
                let Pattern::Application { symbol, arguments } = &term else {
                    continue;
                };
                if is_local_function(&symbol.name) {
                    local.push(symbol.name.clone());
                } else {
                    return Some((
                        symbol.name.clone(),
                        arguments.iter().map(application_head).collect(),
                    ));
                }
            }
        }
        local
            .iter()
            .find_map(|inner| self.value_term(inner, visited))
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
        let term_local = is_local_function(&term_symbol);
        let value_term = term_local
            .then(|| self.value_term(&term_symbol, &mut BTreeSet::new()))
            .flatten()
            .map(|(symbol, arguments)| TermHead {
                hook: hook(&symbol),
                symbol,
                arguments,
            });
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
            term_local,
            value_term,
            term_total: !self.analysis.partial().contains(&term_symbol),
            term_symbol,
            through,
            sentence,
        })
    }
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

/// The part a visit's `condition` flag names.
const fn part(condition: bool) -> Part {
    if condition {
        Part::Condition
    } else {
        Part::Result
    }
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
