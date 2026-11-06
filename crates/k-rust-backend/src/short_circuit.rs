//! Which sentences of a loaded definition depend on the short-circuit reading of its Boolean
//! connectives and conditional.
//!
//! k-rust's meaning of `andBool`, `orBool`, `impliesBool`, `#if`, `andThenBool` and `orElseBool`
//! is strict: in matching logic an application to an undefined argument is undefined, so an
//! application of any of these symbols is undefined wherever an operand is ([`crate::deferred`]).
//! K's text also admits a short-circuiting reading, which evaluates the deciding left operand
//! and, once that operand decides the value, skips the operand after it (the right operand of
//! the Boolean operators, the branch a decided `#if` does not select). Where such a skipped
//! operand is undefined, a step through the application is undefined in the strict reading and
//! has a value in the short-circuiting one. The left operand is never skipped: a
//! `[simplification]` such as `_ andBool false => false` binds an element variable, which
//! matches only a defined value, so it licenses no skip of an undefined left operand
//! ([`SHORT_CIRCUIT_HOOKS`]).
//!
//! [`ShortCircuitAnalysis`] judges, over a loaded [`BackendDefinition`] and the KORE it was
//! loaded from, which functions, equations and rewrite rules can differ between the two
//! readings. It reads only the definition: symbol declarations (`total`, hooks), axioms, and the
//! ceil theory the backend loaded; never a run.
//!
//! - `May(p)` ([`ShortCircuitAnalysis::may`]): the applications in `p` that may be undefined, of
//!   a function that can be undefined in the strict reading where the other gives a value, or of
//!   a partial function unless the application owes nothing beyond its arguments under the
//!   definition's ceil theory ([`ShortCircuitAnalysis::owes_nothing`]).
//! - `Must(p)` ([`ShortCircuitAnalysis::must`]): the applications of partial functions that do
//!   not depend on the reading which every evaluation of `p` evaluates, under every order a
//!   short-circuit operator may take.
//! - An operator application depends on the reading at a skippable position `i` when some term
//!   of `May(arg_i)` is outside the union of `Must(arg_j)` over the other positions `j`
//!   ([`ShortCircuitAnalysis::direct`]): the readings differ at an operator only on an instance
//!   where a skipped operand is undefined while the operands evaluated are defined, and a term
//!   that another evaluated operand also evaluates is undefined in both readings together. No
//!   guard's truth is read.
//! - A condition's matching-logic connectives are walked into down to their `\equals(C, true)`
//!   leaves; a leaf whose `C` is a tree of `andThenBool` and `andBool` over reading-independent
//!   atoms has the same truth value in both readings, as has every connective over such leaves
//!   (the predicate-truth argument at [`ShortCircuitAnalysis::condition_side`], with its scope).
//! - The functions whose value depends on the reading are the least fixed point of
//!   [`ShortCircuitAnalysis::close_over`] over every equation of the definition.
//!
//! # Originating witnesses
//!
//! A dependence propagates: a function whose equation applies
//! `D =/=Int 0 andThenBool N /Int D >Int 1` makes every sentence that applies it depend on the reading too, and it can be removed
//! only at the operator. An operator witness ([`Witness::Operator`]) **originates**
//! ([`ShortCircuitAnalysis::originates`]) when its possibly undefined term `t` is undefined
//! independently of any reading-dependent function: `t`'s head depends on no reading
//! (`through` is `None`), or `t`'s head is not declared `total` (then `t` may be undefined on
//! every reading, so the skip is ambiguous at this site whatever is fixed elsewhere). A witness
//! through a `total` function that depends on the reading is inherited: removing the function's
//! own origin removes it. Every chain of reasons from a sentence that depends on the reading
//! ends at an originating witness, since the least fixed point starts only from operator
//! witnesses over terms that depend on no function's reading.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use k_rust_kore::kore::ast::{Attributes, Definition, Pattern, Sentence};
use k_rust_kore::kore::walk;
use k_rust_kore::names::KoreAttribute;

use crate::definition::BackendDefinition;
use crate::term::{FunctionType, SymbolType};

/// An operator whose operands a backend may or may not skip ([`SHORT_CIRCUIT_HOOKS`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ShortCircuitOperator {
    /// The operator's hook.
    pub hook: &'static str,
    /// The argument positions a short-circuiting reading may skip: the operands after the
    /// deciding operand, which is position 0 and which every reading evaluates.
    pub skippable: &'static [usize],
    /// Whether some value of the deciding operand decides the application alone, so that a
    /// short-circuiting reading may skip every skippable operand at once: the Boolean operators
    /// (`false andBool _`, `true orBool _`, `false impliesBool _`), not `#if`, which evaluates the
    /// branch its condition selects.
    pub decides_alone: bool,
}

/// The operators whose operands a backend may or may not skip (domains.md 1115-1117: `andBool`
/// and `orBool` "may be short-circuited in concrete backends", and `impliesBool` is `notBool P
/// orBool Q`, 1110-1111; 2314-2317: `#if` "does not short-circuit on symbolic backends"; 1115
/// calls `andThenBool` and `orElseBool` short-circuiting, but k-rust reads their skipped
/// operand's definedness too, so a step through one over an undefined operand is undefined in
/// k-rust where the text gives a value). Each with the argument positions a backend may skip:
/// the right operand of a Boolean operator and the branches of `#if`, the operands after the
/// deciding left one. The left operand of a Boolean operator is not skippable: a
/// short-circuiting reading evaluates the deciding operand and may skip what follows it once that
/// operand decides, and a `[simplification]` such as `_ andBool false => false` binds an element
/// variable, which matches only a defined value, so it licenses no skip of an undefined left
/// operand (k-rust lists only these readings, `shortCircuitReadings`). The analysis needs every
/// operator here to evaluate every position that is not skippable, and, unless the deciding
/// operand can decide alone, at least one skippable position (kink-native's test
/// `every_short_circuit_operator_evaluates_a_skippable_operand_and_every_other_one` checks it
/// from each operator's meaning and fails on an operator it has none for).
pub const SHORT_CIRCUIT_HOOKS: &[ShortCircuitOperator] = &[
    ShortCircuitOperator {
        hook: "BOOL.and",
        skippable: &[1],
        decides_alone: true,
    },
    ShortCircuitOperator {
        hook: "BOOL.or",
        skippable: &[1],
        decides_alone: true,
    },
    ShortCircuitOperator {
        hook: "BOOL.implies",
        skippable: &[1],
        decides_alone: true,
    },
    ShortCircuitOperator {
        hook: "BOOL.andThen",
        skippable: &[1],
        decides_alone: true,
    },
    ShortCircuitOperator {
        hook: "BOOL.orElse",
        skippable: &[1],
        decides_alone: true,
    },
    ShortCircuitOperator {
        hook: "KEQUAL.ite",
        skippable: &[1, 2],
        decides_alone: false,
    },
];

/// The conjunctions whose operands, at the top of the Bool term `C` of a condition's leaf
/// `\equals(C, true)`, may be undefined without making the leaf's truth value depend on the
/// reading: a skipped operand makes `C` `false` where k-rust's reading makes it undefined, and
/// the leaf is `\bottom` in both. The leaf may sit under any matching-logic connective of the
/// condition (`\and`, `\or`, `\not`, `\implies`, `\iff`, `\exists`, `\forall`), whose truth
/// value is a function of its operands' (the predicate-truth argument at
/// [`ShortCircuitAnalysis::condition_side`]).
const CONJUNCTION_HOOKS: [&str; 2] = ["BOOL.and", "BOOL.andThen"];

/// How a rewrite rule depends on the short-circuit reading.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ShortCircuitEffect {
    /// Whether the rule applies can differ between the readings: its condition depends on the
    /// reading, or its right-hand side applies a function whose own condition does
    /// ([`RuleReading::applicability`]).
    Applicability,
    /// The rule's result can be undefined in k-rust's reading where a short-circuiting backend
    /// gives a value ([`RuleReading::result`]).
    Result,
}

/// How a function depends on the short-circuit reading.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ReadingDependence {
    /// An application can be undefined in k-rust's reading where a short-circuiting backend gives
    /// a value: an equation's right-hand side can be.
    Undefined,
    /// An application's value can differ between the readings with no undefined step: an
    /// equation's condition depends on the reading, so k-rust may apply another equation (or
    /// its right-hand side applies a function for which this holds).
    Valued,
}

/// The part of a sentence at which a witness of a dependence on the reading sits.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum CausePart {
    /// A leaf of the sentence's condition (a rewrite rule's `requires` and left-hand side, an
    /// equation's antecedent, an `owise` equation's guard included): the Bool term `C` of a leaf
    /// `\equals(C, true)`, or a part the analysis reads as a whole (a configuration, `\in`,
    /// `\ceil`, an `\equals` of two terms).
    Condition {
        /// The leaf's Bool term, or the part read as a whole.
        leaf: Pattern,
    },
    /// The sentence's right-hand side.
    RightSide,
}

/// The ceil-theory judgements of the analysis on one loaded definition
/// ([`ShortCircuitAnalysis::owes_nothing`] of each application judged so far), kept across
/// analyses of that definition ([`ShortCircuitAnalysis::with_memo`],
/// [`ShortCircuitAnalysis::into_memo`]). A judgement depends only on the application and the
/// definition, so a memo is valid for exactly the definition it was filled on.
#[derive(Debug, Default)]
pub struct CeilMemo {
    /// Whether each application judged owes nothing beyond its arguments.
    owes_nothing: BTreeMap<Pattern, bool>,
}

/// A sentence of a KORE definition, by position: an index into `Definition::modules` and one
/// into that module's `sentences`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SentenceRef {
    /// The module's index in `Definition::modules`.
    pub module: usize,
    /// The sentence's index in that module's `sentences`.
    pub sentence: usize,
}

impl SentenceRef {
    /// The module and the sentence `self` names in `kore`, if `kore` has them.
    #[must_use]
    pub fn resolve(
        self,
        kore: &Definition,
    ) -> Option<(&k_rust_kore::kore::ast::Module, &Sentence)> {
        let module = kore.modules.get(self.module)?;
        Some((module, module.sentences.get(self.sentence)?))
    }
}

/// Where a pattern depends on the short-circuit reading, as [`ShortCircuitAnalysis`]'s
/// predicates find it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Witness {
    /// A short-circuit operator whose argument at `position`, `operand`, a backend may skip and
    /// holds `term`, a possibly undefined application ([`ShortCircuitAnalysis::may`]) no operand
    /// evaluated whenever it is skipped evaluates. `through` is how `term`'s head depends on the
    /// reading when the witness was found, if it does.
    Operator {
        /// The operator's symbol.
        operator: String,
        /// The argument position of the skipped operand.
        position: usize,
        /// The operand a backend may skip.
        operand: Pattern,
        /// The possibly undefined application in the operand.
        term: Pattern,
        /// How `term`'s head depends on the reading, if it does.
        through: Option<ReadingDependence>,
    },
    /// An application of a function that depends on the reading as `dependence` says.
    Function {
        /// The function's symbol.
        symbol: String,
        /// How it depends on the reading.
        dependence: ReadingDependence,
    },
}

/// Why a function depends on the reading ([`ShortCircuitAnalysis::reasons`]): the equation, the
/// part of it, and the witness found there when the function was inserted.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reason {
    /// The equation.
    pub equation: SentenceRef,
    /// Where in the equation the witness sits.
    pub part: CausePart,
    /// The witness.
    pub witness: Witness,
}

/// How one rewrite rule depends on the reading ([`ShortCircuitAnalysis::rule_readings`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleReading {
    /// The rewrite axiom.
    pub rule: SentenceRef,
    /// Whether the rule applies can differ: the first leaf of its conditions and left-hand side
    /// that depends on the reading, else an application in its right-hand side of a function
    /// whose value does.
    pub applicability: Option<(CausePart, Witness)>,
    /// Its right-hand side can be undefined in k-rust's reading where the other gives a value.
    pub result: Option<Witness>,
}

/// How one equation depends on the reading ([`ShortCircuitAnalysis::equation_readings`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EquationReading {
    /// The equation axiom.
    pub equation: SentenceRef,
    /// Its head symbol.
    pub head: String,
    /// Its right-hand side can be undefined in k-rust's reading where the other gives a value.
    pub result: Option<Witness>,
    /// Its head's value can differ with no undefined step: the first leaf of its antecedent that
    /// depends on the reading, else an application in its right-hand side of a function whose
    /// value does.
    pub valued: Option<(CausePart, Witness)>,
}

/// The short-circuit reading of one loaded definition: its operators, its partial functions,
/// and, once closed over the definition's equations, the functions whose value depends on the
/// reading.
pub struct ShortCircuitAnalysis<'d> {
    /// The loaded definition, whose ceil theory says which partial applications owe nothing
    /// beyond their arguments ([`Self::owes_nothing`]).
    definition: &'d BackendDefinition,
    /// [`Self::owes_nothing`] of each application asked so far.
    owes_nothing: RefCell<BTreeMap<Pattern, bool>>,
    /// Each short-circuit operator symbol with its operator ([`SHORT_CIRCUIT_HOOKS`]).
    operators: BTreeMap<String, &'static ShortCircuitOperator>,
    /// The conjunction operator symbols ([`CONJUNCTION_HOOKS`]).
    conjunctions: BTreeSet<String>,
    /// The function symbols not declared `total`: an application of one may be undefined.
    partial: BTreeSet<String>,
    /// Functions that can be undefined in k-rust's reading where a short-circuiting backend gives
    /// a value: an equation's right-hand side skips an operand that may be undefined.
    undefined: BTreeSet<String>,
    /// Functions whose value can differ between the readings with no undefined step: an
    /// equation's condition depends on the reading, so k-rust may apply another equation.
    valued: BTreeSet<String>,
    /// The functions of [`Self::undefined`], not of [`Self::valued`], every equation of which is
    /// a conjunction (`andBool`, `andThenBool`) of terms that do not depend on the reading and of
    /// calls of such functions: where k-rust's reading makes a call undefined, the other makes
    /// it `false` (a skipped conjunct makes its conjunction `false`), and nowhere else do the
    /// readings differ. At the top of a condition such a call, like a conjunct, makes the rule
    /// inapplicable in both readings (a guard such as `lengthBytes(B) ==Int 1 andBool B[0] ==Int
    /// 128`).
    conjunctive: BTreeSet<String>,
    /// Why each function of [`Self::undefined`] and of [`Self::valued`] is there, recorded by
    /// [`Self::close_over`] when it inserts the function: the equation, its part and the witness
    /// found there. A witness names only functions inserted before, so following the reasons
    /// from any witness ends.
    reasons: BTreeMap<(String, ReadingDependence), Reason>,
}

impl<'d> ShortCircuitAnalysis<'d> {
    /// The analysis of `definition` before any equation is read: its operators, conjunctions
    /// and partial functions.
    #[must_use]
    pub fn of(definition: &'d BackendDefinition) -> Self {
        let mut operators = BTreeMap::new();
        let mut conjunctions = BTreeSet::new();
        let mut partial = BTreeSet::new();
        for symbol in definition.symbols().values() {
            let name = symbol.name.to_string();
            if let Some(hook) = symbol.attributes.hook.as_deref() {
                if let Some(operator) = SHORT_CIRCUIT_HOOKS
                    .iter()
                    .find(|operator| operator.hook == hook)
                {
                    operators.insert(name.clone(), operator);
                }
                if CONJUNCTION_HOOKS.contains(&hook) {
                    conjunctions.insert(name.clone());
                }
            }
            if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial) {
                partial.insert(name);
            }
        }
        Self {
            definition,
            owes_nothing: RefCell::default(),
            operators,
            conjunctions,
            partial,
            undefined: BTreeSet::new(),
            valued: BTreeSet::new(),
            conjunctive: BTreeSet::new(),
            reasons: BTreeMap::new(),
        }
    }

    /// `self` with the ceil-theory judgements of `memo`, which must have been filled on the same
    /// definition.
    #[must_use]
    pub fn with_memo(mut self, memo: CeilMemo) -> Self {
        self.owes_nothing = RefCell::new(memo.owes_nothing);
        self
    }

    /// The ceil-theory judgements made so far, to reuse on the same definition.
    #[must_use]
    pub fn into_memo(self) -> CeilMemo {
        CeilMemo {
            owes_nothing: self.owes_nothing.into_inner(),
        }
    }

    /// Take `symbols` as the functions that can be undefined in k-rust's reading where the
    /// other gives a value ([`Self::undefined`]), as found by an earlier closure over the same
    /// definition.
    pub fn assume_undefined(&mut self, symbols: BTreeSet<String>) {
        self.undefined = symbols;
    }

    /// Why each reading-dependent function is one, by function and dependence.
    #[must_use]
    pub const fn reasons(&self) -> &BTreeMap<(String, ReadingDependence), Reason> {
        &self.reasons
    }

    /// The functions that can be undefined in k-rust's reading where the other gives a value.
    #[must_use]
    pub const fn undefined(&self) -> &BTreeSet<String> {
        &self.undefined
    }

    /// The functions whose value can differ between the readings with no undefined step.
    #[must_use]
    pub const fn valued(&self) -> &BTreeSet<String> {
        &self.valued
    }

    /// The function symbols not declared `total`.
    #[must_use]
    pub const fn partial(&self) -> &BTreeSet<String> {
        &self.partial
    }

    /// Close [`Self::undefined`] and [`Self::valued`] over every equation of `kore`, whatever its
    /// source (a prelude function can depend on the reading too), recording why each function is
    /// inserted ([`Self::reasons`]).
    pub fn close_over(&mut self, kore: &Definition) {
        let equations = equations(kore);
        loop {
            let mut changed = false;
            for (at, head, condition, right) in &equations {
                if !self.undefined.contains(*head)
                    && let Some(witness) = self.result(right)
                {
                    self.undefined.insert((*head).to_owned());
                    self.reasons.insert(
                        ((*head).to_owned(), ReadingDependence::Undefined),
                        Reason {
                            equation: *at,
                            part: CausePart::RightSide,
                            witness,
                        },
                    );
                    changed = true;
                }
                if !self.valued.contains(*head)
                    && let Some((part, witness)) = self.valued_witness(*condition, right)
                {
                    self.valued.insert((*head).to_owned());
                    self.reasons.insert(
                        ((*head).to_owned(), ReadingDependence::Valued),
                        Reason {
                            equation: *at,
                            part,
                            witness,
                        },
                    );
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // The greatest set of conjunctive functions: start from every function that can be
        // undefined and does not depend on the reading otherwise, and drop each one an equation
        // of which is not a conjunction of reading-independent terms and conjunctive calls.
        self.conjunctive = self.undefined.difference(&self.valued).cloned().collect();
        loop {
            let dropped = self
                .conjunctive
                .iter()
                .filter(|function| {
                    equations
                        .iter()
                        .any(|(_, head, _, right)| head == function && self.condition(right))
                })
                .cloned()
                .collect::<Vec<_>>();
            if dropped.is_empty() {
                break;
            }
            for function in dropped {
                self.conjunctive.remove(&function);
            }
        }
    }

    /// The witness by which an equation with antecedent `condition` and right-hand side `right`
    /// makes its head's value depend on the reading: [`Self::condition_side`] of the antecedent,
    /// else an application in `right` of a function of [`Self::valued`].
    fn valued_witness(
        &self,
        condition: Option<&Pattern>,
        right: &Pattern,
    ) -> Option<(CausePart, Witness)> {
        condition
            .and_then(|condition| self.condition_side(condition))
            .map(|(leaf, witness)| (CausePart::Condition { leaf }, witness))
            .or_else(|| {
                self.applies_dependent(right, ReadingDependence::Valued)
                    .map(|witness| (CausePart::RightSide, witness))
            })
    }

    /// How each rewrite axiom of `kore` that depends on the reading does, in sentence order: its
    /// applicability (the first leaf of its conditions and left-hand side that depends on the
    /// reading, else an application in its right-hand side of a function of [`Self::valued`]) and
    /// its result ([`Self::result`] of its right-hand side). Read after [`Self::close_over`].
    #[must_use]
    pub fn rule_readings(&self, kore: &Definition) -> Vec<RuleReading> {
        let mut readings = Vec::new();
        for (module_index, module) in kore.modules.iter().enumerate() {
            for (sentence_index, sentence) in module.sentences.iter().enumerate() {
                let Sentence::Axiom { pattern, .. } = sentence else {
                    continue;
                };
                let Some((conditions, left, right)) = rewrite_sides(pattern) else {
                    continue;
                };
                let applicability = conditions
                    .iter()
                    .chain([&left])
                    .find_map(|side| self.condition_side(side))
                    .map(|(leaf, witness)| (CausePart::Condition { leaf }, witness))
                    .or_else(|| {
                        self.applies_dependent(right, ReadingDependence::Valued)
                            .map(|witness| (CausePart::RightSide, witness))
                    });
                let result = self.result(right);
                if applicability.is_some() || result.is_some() {
                    readings.push(RuleReading {
                        rule: SentenceRef {
                            module: module_index,
                            sentence: sentence_index,
                        },
                        applicability,
                        result,
                    });
                }
            }
        }
        readings
    }

    /// How each equation of `kore` that depends on the reading does, in sentence order, by the
    /// two predicates [`Self::close_over`] applies: its result ([`Self::result`] of its
    /// right-hand side) and its head's value ([`Self::condition_side`] of its antecedent, else an
    /// application in its right-hand side of a function of [`Self::valued`]). Read after
    /// [`Self::close_over`].
    #[must_use]
    pub fn equation_readings(&self, kore: &Definition) -> Vec<EquationReading> {
        equations(kore)
            .into_iter()
            .filter_map(|(at, head, condition, right)| {
                let result = self.result(right);
                let valued = self.valued_witness(condition, right);
                (result.is_some() || valued.is_some()).then(|| EquationReading {
                    equation: at,
                    head: head.to_owned(),
                    result,
                    valued,
                })
            })
            .collect()
    }

    /// Whether `pattern` applies a symbol of `symbols`.
    #[must_use]
    pub fn applies(&self, pattern: &Pattern, symbols: &BTreeSet<String>) -> bool {
        applied(pattern, symbols).is_some()
    }

    /// The first application in `pattern` (in post-order) of a function that depends on the
    /// reading as `dependence` says ([`Self::undefined`], [`Self::valued`]).
    #[must_use]
    pub fn applies_dependent(
        &self,
        pattern: &Pattern,
        dependence: ReadingDependence,
    ) -> Option<Witness> {
        let functions = match dependence {
            ReadingDependence::Undefined => &self.undefined,
            ReadingDependence::Valued => &self.valued,
        };
        applied(pattern, functions).map(|symbol| Witness::Function { symbol, dependence })
    }

    /// How `term`'s head depends on the reading now, if it does: [`Self::undefined`] before
    /// [`Self::valued`].
    #[must_use]
    pub fn dependence(&self, term: &Pattern) -> Option<ReadingDependence> {
        let Pattern::Application { symbol, .. } = term else {
            return None;
        };
        let name = symbol.name.as_str();
        if self.undefined.contains(name) {
            Some(ReadingDependence::Undefined)
        } else if self.valued.contains(name) {
            Some(ReadingDependence::Valued)
        } else {
            None
        }
    }

    /// Whether `symbol` depends on the reading ([`Self::undefined`], [`Self::valued`]).
    #[must_use]
    pub fn reading_dependent(&self, symbol: &str) -> bool {
        self.undefined.contains(symbol) || self.valued.contains(symbol)
    }

    /// `May(pattern)`: the applications anywhere in `pattern` that may be undefined, of a
    /// function that can be undefined in k-rust's reading ([`Self::undefined`]), or of a partial
    /// function unless the application owes nothing beyond its arguments under the definition's
    /// ceil theory ([`Self::owes_nothing`]). Where `pattern` is undefined on an instance, one of
    /// them is. Every symbol is strict, so on that instance some application is undefined while
    /// all its arguments are defined (an innermost undefined one); its symbol is not total, a
    /// constructor or a domain value, and it is no application that owes nothing beyond its
    /// arguments, since that one is defined wherever its arguments are. (An application of a
    /// total function of [`Self::valued`] is flagged by every caller wherever it occurs.)
    #[must_use]
    pub fn may(&self, pattern: &Pattern) -> BTreeSet<Pattern> {
        let mut out = BTreeSet::new();
        walk::for_each_post_order(pattern, |node| {
            if let Pattern::Application { symbol, .. } = node {
                let name = symbol.name.as_str();
                if self.undefined.contains(name)
                    || (self.partial.contains(name)
                        && (self.reading_dependent(name) || !self.owes_nothing(node)))
                {
                    out.insert(node.clone());
                }
            }
        });
        out
    }

    /// Whether the application `node`, of a partial function that does not depend on the reading,
    /// owes nothing beyond the definedness of its arguments under the loaded definition's ceil
    /// theory: [`crate::definedness::application_owes_nothing`] of `node` internalized as a
    /// term, which holds when `apply_ceil_equation` discharges the node's own obligation, such as
    /// an unconditional ceil equation whose condition, instantiated at the node, simplifies to
    /// `\top`. The judgement is made once, over the node's variables, so it holds on every
    /// instance: `bitRangeInt(X, 4, 4)` owes nothing (domains.md `INT-SYMBOLIC-KORE-AMENDMENTS`,
    /// AM-10: `4 >=Int 0 andBool 4 >=Int 0`), `X /Int 16` owes nothing (`INT-SYMBOLIC-KORE`:
    /// `16 =/=Int 0`), and `X /Int Y` owes `Y =/=Int 0`. It reads the ceil theory of the
    /// definition loaded, so it covers every hook with a ceil equation and a definition's own
    /// `#Ceil` lemmas, and it trusts the ceil equations that definition keeps as the analysis
    /// trusts its `total` declarations. A node that does not internalize on the definition (one
    /// under a sort variable, or holding a literal the definition leaves open) owes its `\ceil`.
    #[must_use]
    pub fn owes_nothing(&self, node: &Pattern) -> bool {
        if let Some(known) = self.owes_nothing.borrow().get(node) {
            return *known;
        }
        let owes_nothing = self
            .definition
            .admit_unverified(node, &[])
            .internalize_term()
            .is_ok_and(|term| crate::definedness::application_owes_nothing(self.definition, &term));
        self.owes_nothing
            .borrow_mut()
            .insert(node.clone(), owes_nothing);
        owes_nothing
    }

    /// `Must(pattern)`: applications of partial functions that do not depend on the reading
    /// which every evaluation of `pattern` evaluates, under every order a short-circuit operator
    /// may take. A short-circuit operator contributes its other operands' `Must` (it evaluates
    /// every operand that is not skippable) and, unless its deciding operand can decide alone
    /// ([`ShortCircuitOperator::decides_alone`], the Boolean operators, which may skip their one
    /// skippable operand), the intersection of its skippable operands' (`#if` evaluates the
    /// branch its condition selects): [`SHORT_CIRCUIT_HOOKS`]. Any other application contributes
    /// its arguments' `Must` and, for such a partial function, itself. An application of a
    /// reading-dependent function is left out, so each term of `Must` is undefined in one reading
    /// exactly where it is in the other (for its arguments, see [`Self::direct`]). It is an
    /// under-approximation: a pattern that is no application contributes nothing.
    #[must_use]
    pub fn must(&self, pattern: &Pattern) -> BTreeSet<Pattern> {
        let Pattern::Application { symbol, arguments } = pattern else {
            return BTreeSet::new();
        };
        let mut out = BTreeSet::new();
        if let Some(operator) = self.operators.get(symbol.name.as_str()) {
            let mut skippable: Option<BTreeSet<Pattern>> = None;
            for (index, argument) in arguments.iter().enumerate() {
                let evaluated = self.must(argument);
                if operator.skippable.contains(&index) {
                    skippable = Some(match skippable {
                        None => evaluated,
                        Some(common) => common.intersection(&evaluated).cloned().collect(),
                    });
                } else {
                    out.extend(evaluated);
                }
            }
            if !operator.decides_alone {
                out.extend(skippable.unwrap_or_default());
            }
            return out;
        }
        for argument in arguments {
            out.extend(self.must(argument));
        }
        let name = symbol.name.as_str();
        if self.partial.contains(name) && !self.reading_dependent(name) {
            out.insert(pattern.clone());
        }
        out
    }

    /// Whether `pattern` applies a short-circuit operator with an operand a backend may skip
    /// whose value can differ between the readings: for some skippable position `i`,
    /// `May(arg_i)` is not contained in the union of `Must(arg_j)` over the other positions `j`.
    /// The readings differ at an operator only on an instance where a skipped operand `arg_i` is
    /// undefined while the operands evaluated are defined. There some `t` of `May(arg_i)` is
    /// undefined; if `t` is in `Must(arg_j)`, the same pattern over the same variables, hence the
    /// same value, is evaluated by an operand evaluated whenever `arg_i` is skipped, so both
    /// readings are undefined there. No guard's truth is read, only the definedness of terms both
    /// readings evaluate (`#if A >=Int 0 #then A #else pd(A) #fi` stays flagged where `pd(A)`
    /// occurs in no other operand). The callers flag an application of a reading-dependent
    /// function wherever it occurs, and the walk visits every operator node, so below a node they
    /// do not flag every subterm has the same value and definedness in both readings.
    ///
    /// The reading-dependent functions are the least fixed point of [`Self::close_over`], so a
    /// recursive function is read as independent while its own equations are checked (the
    /// greatest fixed point of independence: `findChar`'s skipped recursive calls each occur in
    /// `Must` of the condition or of the other branch). That is sound by induction on the depth
    /// of evaluation, which needs evaluation to terminate (premise A1, k-rust `data_term`).
    #[must_use]
    pub fn direct(&self, pattern: &Pattern) -> bool {
        self.direct_witness(pattern).is_some()
    }

    /// [`Self::direct`]'s witness: the first such operator node in post-order, at its first such
    /// position, with the first term of `May(arg_i)` outside the other positions' `Must`.
    #[must_use]
    pub fn direct_witness(&self, pattern: &Pattern) -> Option<Witness> {
        let mut found = None;
        walk::for_each_post_order(pattern, |node| {
            if found.is_none()
                && let Pattern::Application { symbol, arguments } = node
                && let Some(operator) = self.operators.get(symbol.name.as_str())
            {
                found = operator
                    .skippable
                    .iter()
                    .find_map(|position| self.position_witness(&symbol.name, arguments, *position));
            }
        });
        found
    }

    /// The witness of the operator application `operator(arguments)` at the skippable `position`:
    /// the first term of `May(arguments[position])` outside the other positions' `Must`.
    fn position_witness(
        &self,
        operator: &str,
        arguments: &[Pattern],
        position: usize,
    ) -> Option<Witness> {
        let skipped = arguments.get(position)?;
        let mut evaluated = BTreeSet::new();
        for (index, other) in arguments.iter().enumerate() {
            if index != position {
                evaluated.extend(self.must(other));
            }
        }
        let term = self
            .may(skipped)
            .into_iter()
            .find(|term| !evaluated.contains(term))?;
        Some(Witness::Operator {
            operator: operator.to_owned(),
            position,
            operand: skipped.clone(),
            through: self.dependence(&term),
            term,
        })
    }

    /// Every operator witness of `pattern`: each operator node in post-order and, per node, each
    /// skippable position whose `May` has a term outside the other positions' `Must`, with the
    /// first such term. [`Self::direct_witness`] of `pattern` is its first element.
    #[must_use]
    pub fn operator_witnesses(&self, pattern: &Pattern) -> Vec<Witness> {
        let mut found = Vec::new();
        walk::for_each_post_order(pattern, |node| {
            if let Pattern::Application { symbol, arguments } = node
                && let Some(operator) = self.operators.get(symbol.name.as_str())
            {
                found.extend(operator.skippable.iter().filter_map(|position| {
                    self.position_witness(&symbol.name, arguments, *position)
                }));
            }
        });
        found
    }

    /// Where a rule's or an equation's right-hand side `right` can be undefined in k-rust's
    /// reading where a short-circuiting backend gives a value, if it can.
    #[must_use]
    pub fn result(&self, right: &Pattern) -> Option<Witness> {
        self.direct_witness(right)
            .or_else(|| self.applies_dependent(right, ReadingDependence::Undefined))
    }

    /// Whether a condition term (a `requires` clause, `Bool`) can be true in one reading and
    /// not in the other: below its top-level conjunctions, it applies a short-circuit operator
    /// over an operand that may be undefined, or a function that depends on the reading, other
    /// than as a conjunctive call ([`Self::conjunctive`]). A top-level conjunct or conjunctive
    /// call that is undefined in k-rust's reading is `false` or undefined in the other, and the
    /// rule applies in neither.
    #[must_use]
    pub fn condition(&self, condition: &Pattern) -> bool {
        self.condition_witness(condition).is_some()
    }

    /// [`Self::condition`]'s witness: that of the first conjunct, or of the first argument of a
    /// conjunctive call, that has one; at any other term, a short-circuit operator
    /// ([`Self::direct_witness`]), else an application of a function of [`Self::undefined`],
    /// else of [`Self::valued`].
    #[must_use]
    pub fn condition_witness(&self, condition: &Pattern) -> Option<Witness> {
        let term = |term: &Pattern| {
            self.direct_witness(term)
                .or_else(|| self.applies_dependent(term, ReadingDependence::Undefined))
                .or_else(|| self.applies_dependent(term, ReadingDependence::Valued))
        };
        match condition {
            // An equation's right-hand side `\and(term, ensures)`.
            Pattern::And { arguments, .. } => arguments
                .iter()
                .find_map(|argument| self.condition_witness(argument)),
            Pattern::Application { symbol, arguments }
                if self.conjunctions.contains(symbol.name.as_str()) =>
            {
                arguments
                    .iter()
                    .find_map(|argument| self.condition_witness(argument))
            }
            // A conjunctive call is `false` where k-rust's reading makes it undefined, as a
            // conjunct is, so only its arguments can make the condition depend on the reading.
            Pattern::Application { symbol, arguments }
                if self.conjunctive.contains(symbol.name.as_str()) =>
            {
                arguments.iter().find_map(term)
            }
            _ => term(condition),
        }
    }

    /// Every operator witness of the condition term `condition` that [`Self::condition_witness`]'s
    /// structure reaches: conjunctions and conjunctive calls are recursed into as there, and
    /// every other term contributes [`Self::operator_witnesses`]. Where
    /// [`Self::condition_witness`] returns an operator witness, it is the first element.
    fn condition_term_operator_witnesses(&self, condition: &Pattern, out: &mut Vec<Witness>) {
        match condition {
            Pattern::And { arguments, .. } => {
                for argument in arguments {
                    self.condition_term_operator_witnesses(argument, out);
                }
            }
            Pattern::Application { symbol, arguments }
                if self.conjunctions.contains(symbol.name.as_str()) =>
            {
                for argument in arguments {
                    self.condition_term_operator_witnesses(argument, out);
                }
            }
            Pattern::Application { symbol, arguments }
                if self.conjunctive.contains(symbol.name.as_str()) =>
            {
                for argument in arguments {
                    out.extend(self.operator_witnesses(argument));
                }
            }
            _ => out.extend(self.operator_witnesses(condition)),
        }
    }

    /// [`Self::condition`] of the side of an axiom that holds its condition: a rewrite rule's
    /// left-hand side (its configuration and `\equals(requires, true)`), or an equation's
    /// antecedent (`\equals(requires, true)` and its argument constraints, or, for an `owise`
    /// equation, also k-rust's guard `\not(\or(\exists.(\equals(C_i, true) /\ match_i), ...,
    /// \bottom))` over the conditions `C_i` of its competitors, kompile `equations.rs`). The
    /// matching-logic connectives (`\and`, `\or`, `\not`, `\implies`, `\iff`, `\exists`,
    /// `\forall`) are walked into, a leaf `\equals(C, true)` is read by [`Self::condition`] of
    /// its Bool term `C`, and any other part (a configuration, `\in`, `\ceil`, an `\equals` of
    /// two terms) counts as a whole.
    ///
    /// The predicate-truth argument, which holds exactly for such a leaf whose `C`
    /// [`Self::condition`] passes: a tree of `andThenBool` and `andBool` over atoms that do not
    /// depend on the reading (conjunctive calls included). The two readings are the
    /// short-circuiting one and k-rust's strict one, in which every application is strict. In
    /// both, such a `C` is `true` exactly where every atom is `true`: a skipped conjunct makes
    /// its conjunction `false` in the short-circuiting reading and `\bottom` in k-rust's where
    /// it is undefined, and a conjunction whose conjuncts are all evaluated is the same in both.
    /// So the readings differ there only as `false` versus `\bottom`, and `\equals(false, true)`
    /// and `\equals(\bottom, true)` are both `\bottom`: the leaf has the same truth value in
    /// both readings on every instance, and so has every connective over such leaves, since a
    /// connective over predicates is a function of its operands' truth values. The argument
    /// does not cover a leaf whose `C` has a skippable operand under `orElseBool`, `notBool`,
    /// `impliesBool` or `#if` (or under any operator other than the conjunctions at its top):
    /// there the readings can differ as `true` versus `\bottom` (`true orElseBool u`, `notBool
    /// (false andThenBool u)`), so `\equals(C, true)` itself differs. Such a leaf keeps the
    /// operand-definedness analysis ([`Self::direct`] in [`Self::condition`]): it counts unless
    /// every skippable operand's possibly undefined applications are evaluated by an operand
    /// that runs whenever it is skipped, or owe nothing under the ceil theory ([`Self::may`]).
    ///
    /// It returns the first leaf that depends on the reading, in the order the connectives hold
    /// their operands, with [`Self::condition_witness`] of it: the leaf is the Bool term `C` of a
    /// leaf `\equals(C, true)`, or the part read as a whole.
    #[must_use]
    pub fn condition_side(&self, side: &Pattern) -> Option<(Pattern, Witness)> {
        match side {
            Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => arguments
                .iter()
                .find_map(|argument| self.condition_side(argument)),
            Pattern::Not { argument, .. } => self.condition_side(argument),
            Pattern::Implies { left, right, .. } | Pattern::Iff { left, right, .. } => self
                .condition_side(left)
                .or_else(|| self.condition_side(right)),
            Pattern::Exists { body, .. } | Pattern::Forall { body, .. } => {
                self.condition_side(body)
            }
            Pattern::Equals { left, right, .. } if is_true(right) => self
                .condition_witness(left)
                .map(|witness| ((**left).clone(), witness)),
            Pattern::Top { .. } | Pattern::Bottom { .. } => None,
            other => self
                .condition_witness(other)
                .map(|witness| (other.clone(), witness)),
        }
    }

    /// Every operator witness of the condition side `side`, with its leaf: [`Self::condition_side`]'s
    /// walk to every leaf instead of the first, collecting at each leaf the operator witnesses
    /// [`Self::condition_witness`]'s structure reaches (conjunctions and conjunctive calls
    /// recursed into as there, [`Self::operator_witnesses`] at every other term). With `owise`,
    /// `side` is an `owise` equation's antecedent and the first argument of its top `\and`, when
    /// it is a `\not`, is k-rust's guard over the competitors' conditions and is not walked: each
    /// of its leaves is, up to renaming, a leaf of a competitor's own condition.
    #[must_use]
    pub fn condition_operator_witnesses(
        &self,
        side: &Pattern,
        owise: bool,
    ) -> Vec<(Pattern, Witness)> {
        let mut out = Vec::new();
        match side {
            Pattern::And { arguments, .. }
                if owise && matches!(arguments.first(), Some(Pattern::Not { .. })) =>
            {
                for argument in &arguments[1..] {
                    self.condition_leaves(argument, &mut out);
                }
            }
            _ => self.condition_leaves(side, &mut out),
        }
        out
    }

    /// [`Self::condition_operator_witnesses`]'s walk below its top.
    fn condition_leaves(&self, side: &Pattern, out: &mut Vec<(Pattern, Witness)>) {
        let leaf = |leaf: &Pattern, out: &mut Vec<(Pattern, Witness)>| {
            let mut witnesses = Vec::new();
            self.condition_term_operator_witnesses(leaf, &mut witnesses);
            out.extend(witnesses.into_iter().map(|witness| (leaf.clone(), witness)));
        };
        match side {
            Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
                for argument in arguments {
                    self.condition_leaves(argument, out);
                }
            }
            Pattern::Not { argument, .. } => self.condition_leaves(argument, out),
            Pattern::Implies { left, right, .. } | Pattern::Iff { left, right, .. } => {
                self.condition_leaves(left, out);
                self.condition_leaves(right, out);
            }
            Pattern::Exists { body, .. } | Pattern::Forall { body, .. } => {
                self.condition_leaves(body, out);
            }
            Pattern::Equals { left, right, .. } if is_true(right) => leaf(left, out),
            Pattern::Top { .. } | Pattern::Bottom { .. } => {}
            other => leaf(other, out),
        }
    }

    /// Whether `witness` originates (the module documentation, "Originating witnesses"): an
    /// operator witness whose term's head depends on no reading, or is not declared `total`.
    /// A function witness never originates.
    #[must_use]
    pub fn originates(&self, witness: &Witness) -> bool {
        match witness {
            Witness::Operator { through, term, .. } => {
                through.is_none()
                    || matches!(term, Pattern::Application { symbol, .. }
                        if self.partial.contains(symbol.name.as_str()))
            }
            Witness::Function { .. } => false,
        }
    }

    /// The reason the witness `witness` leads to, if it leads to one: an operator witness through
    /// a dependence leads to the reason of its term's head under that dependence, a function
    /// witness to its function's.
    #[must_use]
    pub fn next_reason(
        &self,
        witness: &Witness,
    ) -> Option<(&(String, ReadingDependence), &Reason)> {
        let key = match witness {
            Witness::Operator { term, through, .. } => {
                let head = match term {
                    Pattern::Application { symbol, .. } => symbol.name.clone(),
                    _ => String::new(),
                };
                (head, (*through)?)
            }
            Witness::Function { symbol, dependence } => (symbol.clone(), *dependence),
        };
        self.reasons.get_key_value(&key)
    }
}

/// Every equation axiom of `kore` ([`equation_parts`]), in sentence order, with its position.
fn equations(kore: &Definition) -> Vec<(SentenceRef, &str, Option<&Pattern>, &Pattern)> {
    let mut equations = Vec::new();
    for (module_index, module) in kore.modules.iter().enumerate() {
        for (sentence_index, sentence) in module.sentences.iter().enumerate() {
            if let Sentence::Axiom { pattern, .. } = sentence
                && let Some((head, condition, right)) = equation_parts(pattern)
            {
                equations.push((
                    SentenceRef {
                        module: module_index,
                        sentence: sentence_index,
                    },
                    head,
                    condition,
                    right,
                ));
            }
        }
    }
    equations
}

/// The first application in `pattern` (in post-order) of a symbol of `symbols`.
fn applied(pattern: &Pattern, symbols: &BTreeSet<String>) -> Option<String> {
    let mut found = None;
    walk::for_each_post_order(pattern, |node| {
        if found.is_none()
            && let Pattern::Application { symbol, .. } = node
            && symbols.contains(symbol.name.as_str())
        {
            found = Some(symbol.name.clone());
        }
    });
    found
}

/// Whether `pattern` is the Bool domain value `true`.
fn is_true(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::DomainValue { value, .. } if value.as_bytes() == b"true")
}

/// A rewrite axiom's conditions (the antecedents of any `\implies` around it), left-hand side
/// and right-hand side, under its binders; `None` for every other axiom.
#[must_use]
pub fn rewrite_sides(pattern: &Pattern) -> Option<(Vec<&Pattern>, &Pattern, &Pattern)> {
    match pattern {
        Pattern::Forall { body, .. } | Pattern::Exists { body, .. } => rewrite_sides(body),
        Pattern::Implies { left, right, .. } => {
            let (mut conditions, lhs, rhs) = rewrite_sides(right)?;
            conditions.push(left);
            Some((conditions, lhs, rhs))
        }
        Pattern::Rewrites { left, right, .. } => Some((Vec::new(), left, right)),
        _ => None,
    }
}

/// An equation axiom's head symbol, antecedent (its `requires` and argument constraints) and
/// right-hand side, under its binders: `\implies(antecedent, \equals(head(..), right))` or
/// `\equals(head(..), right)`; `None` for every other axiom.
#[must_use]
pub fn equation_parts(pattern: &Pattern) -> Option<(&str, Option<&Pattern>, &Pattern)> {
    match pattern {
        Pattern::Forall { body, .. } | Pattern::Exists { body, .. } => equation_parts(body),
        Pattern::Implies { left, right, .. } => match &**right {
            Pattern::Equals {
                left: head, right, ..
            } => Some((term_head(head)?, Some(&**left), &**right)),
            _ => None,
        },
        Pattern::Equals { left, right, .. } => Some((term_head(left)?, None, &**right)),
        _ => None,
    }
}

/// The head symbol of `pattern` when it is an application, or of the first application of an
/// `\and` at its top.
fn term_head(pattern: &Pattern) -> Option<&str> {
    match pattern {
        Pattern::Application { symbol, .. } => Some(symbol.name.as_str()),
        Pattern::And { arguments, .. } => arguments.iter().find_map(|argument| match argument {
            Pattern::Application { symbol, .. } => Some(symbol.name.as_str()),
            _ => None,
        }),
        _ => None,
    }
}

/// Whether a sentence with `attributes` has the `owise` attribute.
#[must_use]
pub fn is_owise(attributes: &Attributes) -> bool {
    attributes.has(KoreAttribute::Owise)
}
