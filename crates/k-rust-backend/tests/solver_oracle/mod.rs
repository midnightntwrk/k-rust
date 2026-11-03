//! The shared part of the property tests over the tiny definition (`solver_translation.rs`,
//! GAP K19, and `simplifier_equivalence.rs`, GAP K33): the definition, the generator's syntax and
//! its rendering to the backend's predicates, the evaluator of K truth over that syntax, the
//! generator, and the runner and Z3 configuration both targets use.
//!
//! K truth is computed here, over the generator's own syntax tree, by an evaluator written from
//! the semantics of each symbol of the tiny definition below (`eval_int`, `eval_pred`): every
//! application is strict, so an undefined argument makes it `\bottom` (`None`), `#if` included;
//! a partial symbol is `\bottom` exactly where the model below leaves it undefined; an equality
//! of two patterns holds iff both are the same element or both are `\bottom`; a Boolean term as
//! a predicate is `b = true`. No function of k-rust computes this truth: the definition's text is
//! the only input the evaluator and the code under test share. Valuations range over a small
//! domain (`X, Y, Z, N ∈ [-2, 2]`, `B` both Booleans, `M` four maps), which is all a refutation
//! needs; `\exists` over `Bool` is exact; `\exists N:Int` is exact where its body has a conjunct
//! `N = t` with `t` free of `N` (the one-point rule, `one_point`), and otherwise true where a
//! witness lies in `[-4, 4]` and unknown elsewhere, since an unbounded domain cannot be refuted by
//! enumeration.
//! Unknown truth refutes nothing.
//!
//! The definition has more than one model, and the evaluator enumerates four of them wherever a
//! case mentions `pf` or `g`: `pf`'s conditional ceil equation leaves `pf(X)` open for `X < 0`
//! (undefined there, or defined), and the values the definition leaves open (`pf`'s, and `g`'s
//! outside its lemma) take one of two choices. Every other symbol's definedness and value are
//! fixed by an equation, a hook or an `smt-hook`. Each is a model of every axiom, so a claim
//! about all models is refuted by any one of them.
//!
//! Each target uses part of it, so unused items are allowed.

#![allow(dead_code)]

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::Arc,
};

use k_rust_backend::{
    definition::BackendDefinition,
    rule::Predicate,
    smt::{Z3Options, Z3Solver},
    substitution::Substitution,
    term::{Term, TermKind, Variable},
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};
use proptest::{
    prelude::*,
    test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
};

/// The tiny definition, and the models the evaluator reads it in (each satisfies every axiom):
/// - `half(X)`: partial, `smt-hook (div #1 2)`, `\ceil(half(X)) = (even(X) = true)`; `even` total
///   with `smt-hook (= (mod #1 2) 0)`. Model: defined iff `X` even, value `X div 2`.
/// - `divInt(I, J)`: `INT.ediv`, `smt-hook div`, `\ceil(divInt(I, J)) = \top requires J =/=Int 0`
///   (a conditional ceil equation); the hook leaves `I divInt 0` undefined. Model: defined iff
///   `J ≠ 0`, the Euclidean quotient.
/// - `pf(X)`: no hook, no `smt-hook` (a value function), `\ceil(pf(X)) = \top requires X >=Int 0`.
///   Models: `X + 1` (or `X + 3`) where `X >= 0`; below 0 undefined, or the same value.
/// - `pow(X, Y)`: `INT.pow`, `smt-hook ^`, AM-12's `\ceil(pow(X, Y)) = (0 <=Int Y orBool X ==Int 1
///   orBool X ==Int -1)`. Model: the integer power where that holds, else undefined.
/// - `ite` (`KEQUAL.ite`), `plus`, `eqInt`, `ltInt`, `notBool`: total, with their `smt-hook`s.
/// - A map sort with `MAP` hooks: `item` (`|->`), `concat` (defined iff the key sets are
///   disjoint), `unit`, `lookup` (defined iff the key is bound), `inKeys` (total).
/// - `g` total, an `smtlib` function, with the `smt-lemma` `g(X) = 0 requires half(X) >Int 0`.
///   Models: `g(X) = 0` where `X` is even and `X div 2 > 0`, else 1 (or 2).
/// - `emod(I, J)`: `INT.emod`, `smt-hook mod`, `\ceil(emod(I, J)) = (J =/=Int 0 = true)` (an
///   unconditional ceil equation). Model: defined iff `J ≠ 0`, the Euclidean remainder. Drawn
///   only through `sel`.
/// - `sel(B, X, Y)`: partial, no hook, two equations `sel(true, X, Y) = emod(X, Y)` and
///   `sel(false, X, Y) = X`, which the solver reads as a summary over `emod` (GAP K29). Model:
///   `emod(X, Y)` where `B` is true, `X` where it is false.
pub const DEFINITION: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-sort SortMap{} [hook{}("MAP.Map"), unit{}(unit{}()), element{}(item{}()), concat{}(concat{}())]
    hooked-symbol unit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol item{}(SortInt{}, SortInt{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol concat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
    hooked-symbol lookup{}(SortMap{}, SortInt{}) : SortInt{} [function{}(), hook{}("MAP.lookup")]
    hooked-symbol inKeys{}(SortInt{}, SortMap{}) : SortBool{} [function{}(), total{}(), hook{}("MAP.in_keys")]
    hooked-symbol plus{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
    hooked-symbol neInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.ne"), smt-hook{}("distinct")]
    hooked-symbol ltInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.lt"), smt-hook{}("<")]
    hooked-symbol leInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.le"), smt-hook{}("<=")]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
    hooked-symbol geInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.ge"), smt-hook{}(">=")]
    hooked-symbol orBool{}(SortBool{}, SortBool{}) : SortBool{} [function{}(), total{}(), hook{}("BOOL.or"), smt-hook{}("or")]
    hooked-symbol notBool{}(SortBool{}) : SortBool{} [function{}(), total{}(), hook{}("BOOL.not"), smt-hook{}("not")]
    hooked-symbol ite{}(SortBool{}, SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}(), hook{}("KEQUAL.ite"), smt-hook{}("ite")]
    hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), hook{}("INT.ediv"), smt-hook{}("div")]
    hooked-symbol pow{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), hook{}("INT.pow"), smt-hook{}("^")]
    symbol even{}(SortInt{}) : SortBool{} [function{}(), total{}(), smt-hook{}("(= (mod #1 2) 0)")]
    symbol half{}(SortInt{}) : SortInt{} [function{}(), smt-hook{}("(div #1 2)")]
    symbol pf{}(SortInt{}) : SortInt{} [function{}()]
    symbol g{}(SortInt{}) : SortInt{} [function{}(), total{}(), smtlib{}("k19g")]
    hooked-symbol emod{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), hook{}("INT.emod"), smt-hook{}("mod")]
    symbol sel{}(SortBool{}, SortInt{}, SortInt{}) : SortInt{} [function{}()]
    axiom{Q} \implies{Q}(\top{Q}(), \equals{Q, Q}(
        \ceil{SortInt{}, Q}(half{}(X:SortInt{})),
        \and{Q}(\equals{SortBool{}, Q}(even{}(X:SortInt{}), \dv{SortBool{}}("true")), \top{Q}())))
        [label{}("half-defined"), simplification{}()]
    axiom{R, Q} \implies{R}(
        \equals{SortBool{}, R}(neInt{}(J:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")),
        \equals{Q, R}(\ceil{SortInt{}, Q}(divInt{}(I:SortInt{}, J:SortInt{})), \and{Q}(\top{Q}(), \top{Q}())))
        [label{}("div-defined"), simplification{}()]
    axiom{R, Q} \implies{R}(
        \equals{SortBool{}, R}(geInt{}(X:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")),
        \equals{Q, R}(\ceil{SortInt{}, Q}(pf{}(X:SortInt{})), \and{Q}(\top{Q}(), \top{Q}())))
        [label{}("pf-defined"), simplification{}()]
    axiom{Q} \implies{Q}(\top{Q}(), \equals{Q, Q}(
        \ceil{SortInt{}, Q}(pow{}(I1:SortInt{}, I2:SortInt{})),
        \and{Q}(\equals{SortBool{}, Q}(
            orBool{}(leInt{}(\dv{SortInt{}}("0"), I2:SortInt{}),
              orBool{}(eqInt{}(I1:SortInt{}, \dv{SortInt{}}("1")),
                eqInt{}(I1:SortInt{}, \dv{SortInt{}}("-1")))),
            \dv{SortBool{}}("true")), \top{Q}())))
        [label{}("pow-defined"), simplification{}()]
    axiom{R} \implies{R}(
        \equals{SortBool{}, R}(gtInt{}(half{}(X:SortInt{}), \dv{SortInt{}}("0")), \dv{SortBool{}}("true")),
        \equals{SortInt{}, R}(g{}(X:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}())))
        [label{}("g-zero"), simplification{}(), smt-lemma{}()]
    axiom{Q} \implies{Q}(\top{Q}(), \equals{Q, Q}(
        \ceil{SortInt{}, Q}(emod{}(I:SortInt{}, J:SortInt{})),
        \and{Q}(\equals{SortBool{}, Q}(neInt{}(J:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \top{Q}())))
        [label{}("emod-defined"), simplification{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortBool{}, R}(KRSInput0:SortBool{}, \dv{SortBool{}}("true")),
            \and{R}(\in{SortInt{}, R}(KRSInput1:SortInt{}, X:SortInt{}),
              \and{R}(\in{SortInt{}, R}(KRSInput2:SortInt{}, Y:SortInt{}), \top{R}())))),
        \equals{SortInt{}, R}(sel{}(KRSInput0:SortBool{}, KRSInput1:SortInt{}, KRSInput2:SortInt{}),
            \and{SortInt{}}(emod{}(X:SortInt{}, Y:SortInt{}), \top{SortInt{}}())))
        [label{}("sel-true")]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortBool{}, R}(KRSInput0:SortBool{}, \dv{SortBool{}}("false")),
            \and{R}(\in{SortInt{}, R}(KRSInput1:SortInt{}, X:SortInt{}),
              \and{R}(\in{SortInt{}, R}(KRSInput2:SortInt{}, Y:SortInt{}), \top{R}())))),
        \equals{SortInt{}, R}(sel{}(KRSInput0:SortBool{}, KRSInput1:SortInt{}, KRSInput2:SortInt{}),
            \and{SortInt{}}(X:SortInt{}, \top{SortInt{}}())))
        [label{}("sel-false")]
endmodule []"#;

pub fn definition() -> BackendDefinition {
    let syntax = parse_definition(DEFINITION).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

pub fn internal_term(definition: &BackendDefinition, source: &str) -> Term {
    let syntax = parse_pattern(source).expect("the term parses");
    definition
        .admit_unverified(&syntax, &[])
        .internalize_term()
        .expect("the term internalizes")
}

// ---------------------------------------------------------------------------------------------
// The generator's syntax: terms of three sorts and predicates over them.

/// The Int variables. `N` is mostly bound by `\exists`; free, it ranges like the others.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum IntVar {
    X,
    Y,
    Z,
    N,
}

pub const INT_VARS: [IntVar; 4] = [IntVar::X, IntVar::Y, IntVar::Z, IntVar::N];

impl IntVar {
    pub const fn index(self) -> usize {
        self as usize
    }

    pub const fn name(self) -> &'static str {
        match self {
            Self::X => "X",
            Self::Y => "Y",
            Self::Z => "Z",
            Self::N => "N",
        }
    }
}

#[derive(Clone, Debug)]
pub enum IntT {
    Var(IntVar),
    /// A literal; the generator draws them from `i8` ranges, the read-back of a simplified
    /// output may hold any.
    Lit(i128),
    Add(Box<IntT>, Box<IntT>),
    Half(Box<IntT>),
    Div(Box<IntT>, Box<IntT>),
    Pf(Box<IntT>),
    Pow(Box<IntT>, Box<IntT>),
    Ite(Box<BoolT>, Box<IntT>, Box<IntT>),
    G(Box<IntT>),
    Lookup(Box<MapT>, Box<IntT>),
    /// `sel(B, X, Y)`, a function the solver reads through its summary.
    Sel(Box<BoolT>, Box<IntT>, Box<IntT>),
    /// A term-level `\and`: the intersection of its operands, their common value where both
    /// are defined and equal, `\bottom` elsewhere (GAP K30).
    And(Box<IntT>, Box<IntT>),
}

#[derive(Clone, Debug)]
pub enum BoolT {
    /// The Bool variable `B`.
    Var,
    Lit(bool),
    Eq(Box<IntT>, Box<IntT>),
    Lt(Box<IntT>, Box<IntT>),
    Not(Box<BoolT>),
    Even(Box<IntT>),
    InKeys(Box<IntT>, Box<MapT>),
    // The definition's other Boolean symbols, which its ceil equations mention: the generator
    // never draws them, the read-back of a simplified output may hold them.
    Ne(Box<IntT>, Box<IntT>),
    Le(Box<IntT>, Box<IntT>),
    Gt(Box<IntT>, Box<IntT>),
    Ge(Box<IntT>, Box<IntT>),
    Or(Box<BoolT>, Box<BoolT>),
    /// A term-level `\and` of two Booleans, read as `IntT::And` is (GAP K30).
    And(Box<BoolT>, Box<BoolT>),
}

#[derive(Clone, Debug)]
pub enum MapT {
    /// The Map variable `M`.
    Var,
    Unit,
    Item(Box<IntT>, Box<IntT>),
    Concat(Box<MapT>, Box<MapT>),
}

#[derive(Clone, Debug)]
pub enum AnyT {
    Int(IntT),
    Bool(BoolT),
    Map(MapT),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Binder {
    Bool,
    Int(IntVar),
}

#[derive(Clone, Debug)]
pub enum Pred {
    Top,
    Bottom,
    Ceil(AnyT),
    /// Two terms of the same sort.
    Eq(AnyT, AnyT),
    /// A Boolean term as a predicate: `b = true`.
    Holds(BoolT),
    Not(Box<Pred>),
    And(Box<Pred>, Box<Pred>),
    Or(Box<Pred>, Box<Pred>),
    Implies(Box<Pred>, Box<Pred>),
    Exists(Binder, Box<Pred>),
}

/// One generated query: `check_predicates(known, binding, [checked])` and
/// `is_sat(known ∧ checked, binding)`.
#[derive(Clone, Debug)]
pub struct Case {
    pub known: Vec<Pred>,
    pub checked: Pred,
    pub binding: Option<(IntVar, IntT)>,
}

// The free variables a case mentions, so that only those are enumerated.
#[derive(Clone, Debug, Default)]
pub struct Free {
    pub ints: BTreeSet<IntVar>,
    pub bool: bool,
    pub map: bool,
    /// The case mentions `pf` or `g`, whose models are not unique.
    pub open: bool,
    /// The case mentions `sel`, which the solver reads through its summary.
    pub summary: bool,
    /// The case holds a term-level `\and` (GAP K30), which the solver reads by its domain plan
    /// (GAP K35).
    pub conjunction: bool,
}

impl IntT {
    pub fn free(&self, free: &mut Free) {
        match self {
            Self::Var(var) => {
                free.ints.insert(*var);
            }
            Self::Lit(_) => {}
            Self::Half(a) => a.free(free),
            Self::Pf(a) | Self::G(a) => {
                free.open = true;
                a.free(free);
            }
            Self::Add(a, b) | Self::Div(a, b) | Self::Pow(a, b) => {
                a.free(free);
                b.free(free);
            }
            Self::And(a, b) => {
                free.conjunction = true;
                a.free(free);
                b.free(free);
            }
            Self::Ite(c, a, b) => {
                c.free(free);
                a.free(free);
                b.free(free);
            }
            Self::Lookup(m, k) => {
                m.free(free);
                k.free(free);
            }
            Self::Sel(c, a, b) => {
                free.summary = true;
                c.free(free);
                a.free(free);
                b.free(free);
            }
        }
    }

    pub fn mentions(&self, var: IntVar) -> bool {
        let mut free = Free::default();
        self.free(&mut free);
        free.ints.contains(&var)
    }
}

impl BoolT {
    pub fn free(&self, free: &mut Free) {
        match self {
            Self::Var => free.bool = true,
            Self::Lit(_) => {}
            Self::Eq(a, b)
            | Self::Lt(a, b)
            | Self::Ne(a, b)
            | Self::Le(a, b)
            | Self::Gt(a, b)
            | Self::Ge(a, b) => {
                a.free(free);
                b.free(free);
            }
            Self::Or(a, b) => {
                a.free(free);
                b.free(free);
            }
            Self::And(a, b) => {
                free.conjunction = true;
                a.free(free);
                b.free(free);
            }
            Self::Not(a) => a.free(free),
            Self::Even(a) => a.free(free),
            Self::InKeys(k, m) => {
                k.free(free);
                m.free(free);
            }
        }
    }
}

impl MapT {
    pub fn free(&self, free: &mut Free) {
        match self {
            Self::Var => free.map = true,
            Self::Unit => {}
            Self::Item(k, v) => {
                k.free(free);
                v.free(free);
            }
            Self::Concat(a, b) => {
                a.free(free);
                b.free(free);
            }
        }
    }
}

impl AnyT {
    pub fn free(&self, free: &mut Free) {
        match self {
            Self::Int(t) => t.free(free),
            Self::Bool(t) => t.free(free),
            Self::Map(t) => t.free(free),
        }
    }
}

impl Pred {
    pub fn free(&self, free: &mut Free) {
        match self {
            Self::Top | Self::Bottom => {}
            Self::Ceil(t) => t.free(free),
            Self::Eq(a, b) => {
                a.free(free);
                b.free(free);
            }
            Self::Holds(b) => b.free(free),
            Self::Not(p) => p.free(free),
            Self::And(p, q) | Self::Or(p, q) | Self::Implies(p, q) => {
                p.free(free);
                q.free(free);
            }
            Self::Exists(binder, body) => {
                let mut inner = Free::default();
                body.free(&mut inner);
                match binder {
                    Binder::Bool => inner.bool = false,
                    Binder::Int(var) => {
                        inner.ints.remove(var);
                    }
                }
                free.ints.extend(inner.ints);
                free.bool |= inner.bool;
                free.map |= inner.map;
                free.open |= inner.open;
                free.summary |= inner.summary;
                free.conjunction |= inner.conjunction;
            }
        }
    }
}

impl Case {
    pub fn free(&self) -> Free {
        let mut free = Free::default();
        for predicate in &self.known {
            predicate.free(&mut free);
        }
        self.checked.free(&mut free);
        if let Some((var, term)) = &self.binding {
            free.ints.insert(*var);
            term.free(&mut free);
        }
        free
    }
}

// ---------------------------------------------------------------------------------------------
// Printing, in K-like syntax, for failure messages.

impl fmt::Display for IntT {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(var) => write!(f, "{}", var.name()),
            Self::Lit(value) => write!(f, "{value}"),
            Self::Add(a, b) => write!(f, "({a} +Int {b})"),
            Self::Half(a) => write!(f, "half({a})"),
            Self::Div(a, b) => write!(f, "divInt({a}, {b})"),
            Self::Pf(a) => write!(f, "pf({a})"),
            Self::Pow(a, b) => write!(f, "({a} ^Int {b})"),
            Self::Ite(c, a, b) => write!(f, "#if {c} #then {a} #else {b} #fi"),
            Self::G(a) => write!(f, "g({a})"),
            Self::Lookup(m, k) => write!(f, "{m}[{k}]"),
            Self::Sel(c, a, b) => write!(f, "sel({c}, {a}, {b})"),
            Self::And(a, b) => write!(f, "({a} /\\ {b})"),
        }
    }
}

impl fmt::Display for BoolT {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var => write!(f, "B"),
            Self::Lit(value) => write!(f, "{value}"),
            Self::Eq(a, b) => write!(f, "({a} ==Int {b})"),
            Self::Lt(a, b) => write!(f, "({a} <Int {b})"),
            Self::Not(a) => write!(f, "notBool {a}"),
            Self::Even(a) => write!(f, "even({a})"),
            Self::InKeys(k, m) => write!(f, "({k} in_keys({m}))"),
            Self::Ne(a, b) => write!(f, "({a} =/=Int {b})"),
            Self::Le(a, b) => write!(f, "({a} <=Int {b})"),
            Self::Gt(a, b) => write!(f, "({a} >Int {b})"),
            Self::Ge(a, b) => write!(f, "({a} >=Int {b})"),
            Self::Or(a, b) => write!(f, "({a} orBool {b})"),
            Self::And(a, b) => write!(f, "({a} /\\ {b})"),
        }
    }
}

impl fmt::Display for MapT {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var => write!(f, "M"),
            Self::Unit => write!(f, ".Map"),
            Self::Item(k, v) => write!(f, "({k} |-> {v})"),
            Self::Concat(a, b) => write!(f, "({a} {b})"),
        }
    }
}

impl fmt::Display for AnyT {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(t) => write!(f, "{t}"),
            Self::Bool(t) => write!(f, "{t}"),
            Self::Map(t) => write!(f, "{t}"),
        }
    }
}

impl fmt::Display for Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Top => write!(f, r"\top"),
            Self::Bottom => write!(f, r"\bottom"),
            Self::Ceil(t) => write!(f, r"\ceil({t})"),
            Self::Eq(a, b) => write!(f, "{a} = {b}"),
            Self::Holds(b) => write!(f, "{b}"),
            Self::Not(p) => write!(f, r"\not({p})"),
            Self::And(p, q) => write!(f, r"({p} \and {q})"),
            Self::Or(p, q) => write!(f, r"({p} \or {q})"),
            Self::Implies(p, q) => write!(f, r"({p} \implies {q})"),
            Self::Exists(Binder::Bool, body) => write!(f, r"\exists B:Bool. {body}"),
            Self::Exists(Binder::Int(var), body) => {
                write!(f, r"\exists {}:Int. {body}", var.name())
            }
        }
    }
}

impl fmt::Display for Case {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "known: [")?;
        for (index, predicate) in self.known.iter().enumerate() {
            if index > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{predicate}")?;
        }
        write!(f, "]; ")?;
        if let Some((var, term)) = &self.binding {
            write!(f, "binding: {} |-> {term}; ", var.name())?;
        }
        write!(f, "checked: {}", self.checked)
    }
}

// ---------------------------------------------------------------------------------------------
// Rendering to KORE text and to the backend's predicates.

impl IntT {
    pub fn kore(&self) -> String {
        match self {
            Self::Var(var) => format!("{}:SortInt{{}}", var.name()),
            Self::Lit(value) => format!(r#"\dv{{SortInt{{}}}}("{value}")"#),
            Self::Add(a, b) => format!("plus{{}}({}, {})", a.kore(), b.kore()),
            Self::Half(a) => format!("half{{}}({})", a.kore()),
            Self::Div(a, b) => format!("divInt{{}}({}, {})", a.kore(), b.kore()),
            Self::Pf(a) => format!("pf{{}}({})", a.kore()),
            Self::Pow(a, b) => format!("pow{{}}({}, {})", a.kore(), b.kore()),
            Self::Ite(c, a, b) => {
                format!("ite{{}}({}, {}, {})", c.kore(), a.kore(), b.kore())
            }
            Self::G(a) => format!("g{{}}({})", a.kore()),
            Self::Lookup(m, k) => format!("lookup{{}}({}, {})", m.kore(), k.kore()),
            Self::Sel(c, a, b) => {
                format!("sel{{}}({}, {}, {})", c.kore(), a.kore(), b.kore())
            }
            Self::And(a, b) => format!("\\and{{SortInt{{}}}}({}, {})", a.kore(), b.kore()),
        }
    }
}

impl BoolT {
    pub fn kore(&self) -> String {
        match self {
            Self::Var => "B:SortBool{}".to_owned(),
            Self::Lit(value) => format!(r#"\dv{{SortBool{{}}}}("{value}")"#),
            Self::Eq(a, b) => format!("eqInt{{}}({}, {})", a.kore(), b.kore()),
            Self::Lt(a, b) => format!("ltInt{{}}({}, {})", a.kore(), b.kore()),
            Self::Not(a) => format!("notBool{{}}({})", a.kore()),
            Self::Even(a) => format!("even{{}}({})", a.kore()),
            Self::InKeys(k, m) => format!("inKeys{{}}({}, {})", k.kore(), m.kore()),
            Self::Ne(a, b) => format!("neInt{{}}({}, {})", a.kore(), b.kore()),
            Self::Le(a, b) => format!("leInt{{}}({}, {})", a.kore(), b.kore()),
            Self::Gt(a, b) => format!("gtInt{{}}({}, {})", a.kore(), b.kore()),
            Self::Ge(a, b) => format!("geInt{{}}({}, {})", a.kore(), b.kore()),
            Self::Or(a, b) => format!("orBool{{}}({}, {})", a.kore(), b.kore()),
            Self::And(a, b) => format!("\\and{{SortBool{{}}}}({}, {})", a.kore(), b.kore()),
        }
    }
}

impl MapT {
    pub fn kore(&self) -> String {
        match self {
            Self::Var => "M:SortMap{}".to_owned(),
            Self::Unit => "unit{}()".to_owned(),
            Self::Item(k, v) => format!("item{{}}({}, {})", k.kore(), v.kore()),
            Self::Concat(a, b) => format!("concat{{}}({}, {})", a.kore(), b.kore()),
        }
    }
}

impl AnyT {
    pub fn kore(&self) -> String {
        match self {
            Self::Int(t) => t.kore(),
            Self::Bool(t) => t.kore(),
            Self::Map(t) => t.kore(),
        }
    }
}

/// The definition and its variables, to build the backend's predicates.
pub struct Backend {
    pub definition: BackendDefinition,
    pub ints: [Variable; 4],
    pub bool: Variable,
}

pub fn variable_of(term: &Term) -> Variable {
    match term.kind() {
        TermKind::Variable(variable) => variable.clone(),
        other => panic!("not a variable: {other:?}"),
    }
}

impl Backend {
    pub fn new() -> Self {
        let definition = definition();
        let ints = INT_VARS.map(|var| {
            variable_of(&internal_term(
                &definition,
                &format!("{}:SortInt{{}}", var.name()),
            ))
        });
        let bool = variable_of(&internal_term(&definition, "B:SortBool{}"));
        Self {
            definition,
            ints,
            bool,
        }
    }

    pub fn term(&self, source: &str) -> Term {
        internal_term(&self.definition, source)
    }

    pub fn predicate(&self, predicate: &Pred) -> Predicate {
        match predicate {
            Pred::Top => Predicate::True,
            Pred::Bottom => Predicate::False,
            Pred::Ceil(t) => Predicate::Ceil(self.term(&t.kore())),
            Pred::Eq(a, b) => Predicate::Equals(self.term(&a.kore()), self.term(&b.kore())),
            Pred::Holds(b) => Predicate::Term(self.term(&b.kore())),
            Pred::Not(p) => Predicate::Not(Arc::new(self.predicate(p))),
            Pred::And(p, q) => Predicate::And(Arc::from([self.predicate(p), self.predicate(q)])),
            Pred::Or(p, q) => Predicate::Or(Arc::from([self.predicate(p), self.predicate(q)])),
            Pred::Implies(p, q) => {
                Predicate::Implies(Arc::new(self.predicate(p)), Arc::new(self.predicate(q)))
            }
            Pred::Exists(binder, body) => {
                let variable = match binder {
                    Binder::Bool => self.bool.clone(),
                    Binder::Int(var) => self.ints[var.index()].clone(),
                };
                Predicate::Exists(variable, Arc::new(self.predicate(body)))
            }
        }
    }

    pub fn substitution(&self, binding: Option<&(IntVar, IntT)>) -> Substitution {
        binding
            .map(|(var, term)| (self.ints[var.index()].clone(), self.term(&term.kore())))
            .into_iter()
            .collect()
    }
}

// ---------------------------------------------------------------------------------------------
// K truth: the evaluator over the generator's syntax.

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Value {
    Int(i128),
    Bool(bool),
    Map(BTreeMap<i128, i128>),
}

/// A value the evaluator cannot compute exactly (an integer beyond `i128`): its truth is
/// unknown, never a refutation.
#[derive(Clone, Copy, Debug)]
pub struct Overflow;

pub type Eval<T> = Result<Option<T>, Overflow>;

/// The four maps `M` ranges over.
pub fn maps() -> [BTreeMap<i128, i128>; 4] {
    [
        BTreeMap::new(),
        BTreeMap::from([(0, 1)]),
        BTreeMap::from([(1, 0)]),
        BTreeMap::from([(0, 1), (1, 1)]),
    ]
}

/// A valuation of the free variables, and which of the definition's models it is read in.
#[derive(Clone, Debug)]
pub struct Env {
    pub ints: [i128; 4],
    pub bool: bool,
    pub map: usize,
    /// Which of the definition's models: `pf` is defined below 0 (`pf_total`) or not, and the
    /// values the definition leaves open are the first choice or the second (`alt_values`).
    pub pf_total: bool,
    pub alt_values: bool,
}

pub const DOMAIN: std::ops::RangeInclusive<i128> = -2..=2;
pub const WITNESSES: std::ops::RangeInclusive<i128> = -4..=4;

impl Env {
    pub fn show(&self, free: &Free) -> String {
        let mut parts = Vec::new();
        for var in &free.ints {
            parts.push(format!("{} = {}", var.name(), self.ints[var.index()]));
        }
        if free.bool {
            parts.push(format!("B = {}", self.bool));
        }
        if free.map {
            let map = &maps()[self.map];
            let entries = map
                .iter()
                .map(|(k, v)| format!("{k} |-> {v}"))
                .collect::<Vec<_>>()
                .join(", ");
            parts.push(format!("M = {{{entries}}}"));
        }
        if free.open {
            parts.push(format!(
                "model: pf(X) {} for X < 0, pf(X) = X + {} where defined, g(X) = {} outside its lemma",
                if self.pf_total { "defined" } else { "undefined" },
                if self.alt_values { 3 } else { 1 },
                if self.alt_values { 2 } else { 1 },
            ));
        }
        if parts.is_empty() {
            "(no free variables)".to_owned()
        } else {
            parts.join(", ")
        }
    }
}

/// Every valuation of `free` over the domain, completing `base` (whose other variables are
/// kept), in both models of `pf` when the case mentions it.
pub fn valuations(free: &Free, base: &Env, fixed_ints: &BTreeSet<IntVar>) -> Vec<Env> {
    let mut envs = vec![base.clone()];
    for var in free.ints.iter().filter(|var| !fixed_ints.contains(var)) {
        envs = envs
            .into_iter()
            .flat_map(|env| {
                DOMAIN.map(move |value| {
                    let mut env = env.clone();
                    env.ints[var.index()] = value;
                    env
                })
            })
            .collect();
    }
    if free.bool {
        envs = envs
            .into_iter()
            .flat_map(|env| {
                [false, true].map(|value| Env {
                    bool: value,
                    ..env.clone()
                })
            })
            .collect();
    }
    if free.map {
        envs = envs
            .into_iter()
            .flat_map(|env| (0..4).map(move |map| Env { map, ..env.clone() }))
            .collect();
    }
    if free.open {
        envs = envs
            .into_iter()
            .flat_map(|env| {
                [(false, false), (false, true), (true, false), (true, true)].map(
                    |(pf_total, alt_values)| Env {
                        pf_total,
                        alt_values,
                        ..env.clone()
                    },
                )
            })
            .collect();
    }
    envs
}

/// Strict application: `None` (`\bottom`) if any argument is.
macro_rules! strict {
    ($($value:ident = $eval:expr),+ => $body:expr) => {{
        $(let Some($value) = $eval? else { return Ok(None) };)+
        $body
    }};
}

pub fn eval_int(term: &IntT, env: &Env) -> Eval<i128> {
    Ok(match term {
        IntT::Var(var) => Some(env.ints[var.index()]),
        IntT::Lit(value) => Some(*value),
        IntT::Add(a, b) => strict!(a = eval_int(a, env), b = eval_int(b, env) =>
            Some(a.checked_add(b).ok_or(Overflow)?)),
        IntT::Half(a) => strict!(a = eval_int(a, env) => (a % 2 == 0).then_some(a / 2)),
        // SMT-LIB's and `INT.ediv`'s Euclidean quotient: `a = b * q + r`, `0 <= r < |b|`.
        IntT::Div(a, b) => strict!(a = eval_int(a, env), b = eval_int(b, env) =>
            if b == 0 { None } else { Some(a.checked_div_euclid(b).ok_or(Overflow)?) }),
        IntT::Pf(a) => {
            strict!(a = eval_int(a, env) => if a >= 0 || env.pf_total {
                Some(a.checked_add(if env.alt_values { 3 } else { 1 }).ok_or(Overflow)?)
            } else {
                None
            })
        }
        IntT::Pow(a, b) => strict!(a = eval_int(a, env), b = eval_int(b, env) => power(a, b)?),
        // `#if` is an application like any other: strict in all three arguments.
        IntT::Ite(c, a, b) => {
            strict!(c = eval_bool(c, env), a = eval_int(a, env), b = eval_int(b, env) =>
                Some(if c { a } else { b }))
        }
        // The lemma fixes 0 where `half(a) >Int 0` holds; elsewhere any value is a model.
        IntT::G(a) => strict!(a = eval_int(a, env) => Some(if a % 2 == 0 && a / 2 > 0 {
            0
        } else if env.alt_values {
            2
        } else {
            1
        })),
        IntT::Lookup(m, k) => {
            strict!(m = eval_map(m, env), k = eval_int(k, env) => m.get(&k).copied())
        }
        // Strict in every argument, as every application is; then its equations, with
        // SMT-LIB's and `INT.emod`'s Euclidean remainder `0 <= r < |b|`.
        IntT::Sel(c, a, b) => {
            strict!(c = eval_bool(c, env), a = eval_int(a, env), b = eval_int(b, env) =>
                if !c { Some(a) } else if b == 0 { None } else { Some(a.rem_euclid(b)) })
        }
        // The intersection of two patterns that each denote at most one element.
        IntT::And(a, b) => {
            strict!(a = eval_int(a, env), b = eval_int(b, env) => (a == b).then_some(a))
        }
    })
}

/// The integer power: defined where the exponent is not negative, or the base is 1 or -1.
pub fn power(base: i128, exponent: i128) -> Result<Option<i128>, Overflow> {
    if base == 1 {
        return Ok(Some(1));
    }
    if base == -1 {
        return Ok(Some(if exponent % 2 == 0 { 1 } else { -1 }));
    }
    if exponent < 0 {
        return Ok(None);
    }
    if base == 0 {
        return Ok(Some(i128::from(exponent == 0)));
    }
    let exponent = u32::try_from(exponent).map_err(|_| Overflow)?;
    base.checked_pow(exponent).map(Some).ok_or(Overflow)
}

pub fn eval_bool(term: &BoolT, env: &Env) -> Eval<bool> {
    Ok(match term {
        BoolT::Var => Some(env.bool),
        BoolT::Lit(value) => Some(*value),
        BoolT::Eq(a, b) => strict!(a = eval_int(a, env), b = eval_int(b, env) => Some(a == b)),
        BoolT::Lt(a, b) => strict!(a = eval_int(a, env), b = eval_int(b, env) => Some(a < b)),
        BoolT::Not(a) => strict!(a = eval_bool(a, env) => Some(!a)),
        BoolT::Even(a) => strict!(a = eval_int(a, env) => Some(a % 2 == 0)),
        BoolT::InKeys(k, m) => {
            strict!(k = eval_int(k, env), m = eval_map(m, env) => Some(m.contains_key(&k)))
        }
        BoolT::Ne(a, b) => strict!(a = eval_int(a, env), b = eval_int(b, env) => Some(a != b)),
        BoolT::Le(a, b) => strict!(a = eval_int(a, env), b = eval_int(b, env) => Some(a <= b)),
        BoolT::Gt(a, b) => strict!(a = eval_int(a, env), b = eval_int(b, env) => Some(a > b)),
        BoolT::Ge(a, b) => strict!(a = eval_int(a, env), b = eval_int(b, env) => Some(a >= b)),
        // An application like any other: strict in both arguments, `\bottom` if either is.
        BoolT::Or(a, b) => strict!(a = eval_bool(a, env), b = eval_bool(b, env) => Some(a || b)),
        BoolT::And(a, b) => {
            strict!(a = eval_bool(a, env), b = eval_bool(b, env) => (a == b).then_some(a))
        }
    })
}

pub fn eval_map(term: &MapT, env: &Env) -> Eval<BTreeMap<i128, i128>> {
    Ok(match term {
        MapT::Var => Some(maps()[env.map].clone()),
        MapT::Unit => Some(BTreeMap::new()),
        MapT::Item(k, v) => {
            strict!(k = eval_int(k, env), v = eval_int(v, env) => Some(BTreeMap::from([(k, v)])))
        }
        // Defined exactly where the two key sets are disjoint.
        MapT::Concat(a, b) => strict!(a = eval_map(a, env), b = eval_map(b, env) => {
            if a.keys().any(|key| b.contains_key(key)) {
                None
            } else {
                let mut union = a;
                union.extend(b);
                Some(union)
            }
        }),
    })
}

pub fn eval_any(term: &AnyT, env: &Env) -> Eval<Value> {
    Ok(match term {
        AnyT::Int(t) => eval_int(t, env)?.map(Value::Int),
        AnyT::Bool(t) => eval_bool(t, env)?.map(Value::Bool),
        AnyT::Map(t) => eval_map(t, env)?.map(Value::Map),
    })
}

/// Kleene truth: `Unknown` only from an `\exists` over Int with no witness in range, or an
/// integer beyond the evaluator's range.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Truth {
    True,
    False,
    Unknown,
}

impl Truth {
    pub const fn of(value: bool) -> Self {
        if value { Self::True } else { Self::False }
    }

    pub const fn not(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Unknown => Self::Unknown,
        }
    }

    pub const fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::True, Self::True) => Self::True,
            _ => Self::Unknown,
        }
    }

    pub const fn or(self, other: Self) -> Self {
        self.not().and(other.not()).not()
    }
}

pub fn eval_pred(predicate: &Pred, env: &Env) -> Truth {
    match predicate {
        Pred::Top => Truth::True,
        Pred::Bottom => Truth::False,
        Pred::Ceil(t) => {
            eval_any(t, env).map_or(Truth::Unknown, |value| Truth::of(value.is_some()))
        }
        // Two patterns of at most one element are equal iff both are the same element or both
        // are empty.
        Pred::Eq(a, b) => match (eval_any(a, env), eval_any(b, env)) {
            (Ok(a), Ok(b)) => Truth::of(a == b),
            _ => Truth::Unknown,
        },
        Pred::Holds(b) => eval_bool(b, env).map_or(Truth::Unknown, |b| Truth::of(b == Some(true))),
        Pred::Not(p) => eval_pred(p, env).not(),
        Pred::And(p, q) => eval_pred(p, env).and(eval_pred(q, env)),
        Pred::Or(p, q) => eval_pred(p, env).or(eval_pred(q, env)),
        Pred::Implies(p, q) => eval_pred(p, env).not().or(eval_pred(q, env)),
        Pred::Exists(Binder::Bool, body) => [false, true]
            .into_iter()
            .map(|value| {
                eval_pred(
                    body,
                    &Env {
                        bool: value,
                        ..env.clone()
                    },
                )
            })
            .fold(Truth::False, Truth::or),
        Pred::Exists(Binder::Int(var), body) => {
            let mut env = env.clone();
            if let Some(t) = one_point(body, *var) {
                match eval_int(t, &env) {
                    // `N = t` holds of no element `N`, so neither does the body.
                    Ok(None) => return Truth::False,
                    // Only `N = v` satisfies the conjunct, so the body there is the answer.
                    Ok(Some(value)) => {
                        env.ints[var.index()] = value;
                        return eval_pred(body, &env);
                    }
                    Err(Overflow) => {}
                }
            }
            let witnessed = WITNESSES.into_iter().any(|value| {
                env.ints[var.index()] = value;
                eval_pred(body, &env) == Truth::True
            });
            if witnessed {
                Truth::True
            } else {
                Truth::Unknown
            }
        }
    }
}

/// The term `t` of a conjunct `N = t` (or `t = N`) of `body`, read through nested `\and`s, with
/// `t` not mentioning `N`: then `\exists N. body` is `\ceil(t) ∧ body[t/N]`, exactly (the
/// one-point rule), since `N = t` holds of the one element `t` denotes and of none where `t` is
/// `\bottom`.
fn one_point(body: &Pred, var: IntVar) -> Option<&IntT> {
    match body {
        Pred::And(p, q) => one_point(p, var).or_else(|| one_point(q, var)),
        Pred::Eq(AnyT::Int(IntT::Var(bound)), AnyT::Int(t))
        | Pred::Eq(AnyT::Int(t), AnyT::Int(IntT::Var(bound)))
            if *bound == var && !t.mentions(var) =>
        {
            Some(t)
        }
        _ => None,
    }
}

/// The truth of the case's known predicates and binding, and of its checked predicate.
pub fn truths(case: &Case, env: &Env) -> (Truth, Truth) {
    let binding =
        case.binding
            .as_ref()
            .map_or(Truth::True, |(var, term)| match eval_int(term, env) {
                Ok(value) => Truth::of(value == Some(env.ints[var.index()])),
                Err(Overflow) => Truth::Unknown,
            });
    let known = case
        .known
        .iter()
        .map(|predicate| eval_pred(predicate, env))
        .fold(binding, Truth::and);
    (known, eval_pred(&case.checked, env))
}

// ---------------------------------------------------------------------------------------------
// Generation.

/// An Int literal of the generator's `i8` draw.
pub fn int_lit(value: i8) -> IntT {
    IntT::Lit(i128::from(value))
}

pub fn int_leaf() -> BoxedStrategy<IntT> {
    prop_oneof![
        3 => prop_oneof![Just(IntVar::X), Just(IntVar::Y), Just(IntVar::Z)].prop_map(IntT::Var),
        1 => Just(IntT::Var(IntVar::N)),
        3 => (-2i8..=2).prop_map(int_lit),
    ]
    .boxed()
}

pub fn bool_leaf() -> BoxedStrategy<BoolT> {
    prop_oneof![2 => Just(BoolT::Var), 1 => any::<bool>().prop_map(BoolT::Lit)].boxed()
}

pub fn map_leaf() -> BoxedStrategy<MapT> {
    prop_oneof![3 => Just(MapT::Var), 1 => Just(MapT::Unit)].boxed()
}

/// A base of `^Int`: a leaf, or one partial application or sum of leaves, so a power's domain
/// still composes with its operands' and never holds another power.
pub fn power_base() -> BoxedStrategy<Box<IntT>> {
    let leaf = || int_leaf().prop_map(Box::new);
    prop_oneof![
        4 => leaf(),
        1 => leaf().prop_map(IntT::Half).prop_map(Box::new),
        1 => (leaf(), (-2i8..=2).prop_map(|value| Box::new(int_lit(value))))
            .prop_map(|(a, c)| Box::new(IntT::Div(a, c))),
        1 => leaf().prop_map(IntT::Pf).prop_map(Box::new),
        1 => (leaf(), leaf()).prop_map(|(a, c)| Box::new(IntT::Add(a, c))),
    ]
    .boxed()
}

/// An exponent of `^Int`: a literal in `[-2, 2]`, or, with `symbolic` (each target's
/// `*_SYMBOLIC_EXPONENTS` variable), also a base-like symbolic term.
///
/// A symbolic exponent covers the translation's reading of a power whose exponent is not a
/// numeral (`guard_powers` in smt.rs), `0 ^Int Y` at `Y = 0` included (GAP K16); the literals keep
/// `^Int`'s domain (negative exponents, the bases 1 and -1, `0 ^Int 0`) in every run. Before GAP
/// K32 that reading was Z3's own power, whose evaluation at model values polls neither timeout nor
/// resource limit (one generated case ran 2 h 20 min, GAP K19 report), so symbolic exponents were
/// opt-in; `solver_translation` now turns them on by default, and its
/// `the_symbolic_power_queries_k19_found_return_under_either_bound` holds the queries that hung.
pub fn power_exponent(symbolic: bool) -> BoxedStrategy<Box<IntT>> {
    let literal = (-2i8..=2).prop_map(|value| Box::new(int_lit(value)));
    if symbolic {
        prop_oneof![1 => literal, 1 => power_base()].boxed()
    } else {
        literal.boxed()
    }
}

/// Terms of each sort of depth at most `depth`, built bottom-up so that sorts nest in each
/// other. Partial applications are weighted up, and a quotient by a literal (a nonzero one
/// mostly) gets its own weight: an argument a conditional ceil equation's condition does not
/// mention is where a domain composes with another.
pub struct Terms {
    pub int: BoxedStrategy<IntT>,
    pub bool: BoxedStrategy<BoolT>,
    pub map: BoxedStrategy<MapT>,
}

pub fn terms(depth: u32, symbolic_exponents: bool) -> Terms {
    terms_with(depth, symbolic_exponents, false)
}

/// [`terms`], and with `conjunctions` also term-level `\and`s of two Int or two Bool terms
/// (GAP K30), a Bool one drawn as often as a negation and an Int one about as often as a sum
/// (K30's weight): the solver reads both by their domain plan (GAP K35, K36). Without
/// `conjunctions` the draw is [`terms`]'s, case for case.
pub fn terms_with(depth: u32, symbolic_exponents: bool, conjunctions: bool) -> Terms {
    let mut level = Terms {
        int: int_leaf(),
        bool: bool_leaf(),
        map: map_leaf(),
    };
    for _ in 0..depth {
        let (int, bool, map) = (level.int.clone(), level.bool.clone(), level.map.clone());
        let b = |strategy: &BoxedStrategy<IntT>| strategy.clone().prop_map(Box::new);
        let literal = prop_oneof![
            3 => prop_oneof![Just(1i8), Just(2), Just(-1), Just(-2)],
            1 => Just(0i8),
        ]
        .prop_map(|value| Box::new(int_lit(value)));
        let next_int = prop_oneof![
            12 => int_leaf(),
            1 => (b(&int), b(&int)).prop_map(|(a, c)| IntT::Add(a, c)),
            3 => b(&int).prop_map(IntT::Half),
            2 => (b(&int), b(&int)).prop_map(|(a, c)| IntT::Div(a, c)),
            3 => (b(&int), literal).prop_map(|(a, c)| IntT::Div(a, c)),
            2 => b(&int).prop_map(IntT::Pf),
            1 => (power_base(), power_exponent(symbolic_exponents)).prop_map(|(a, c)| IntT::Pow(a, c)),
            2 => (bool.clone().prop_map(Box::new), b(&int), b(&int))
                .prop_map(|(c, a, d)| IntT::Ite(c, a, d)),
            1 => b(&int).prop_map(IntT::G),
            2 => (map.clone().prop_map(Box::new), b(&int)).prop_map(|(m, k)| IntT::Lookup(m, k)),
            2 => (bool.clone().prop_map(Box::new), b(&int), b(&int))
                .prop_map(|(c, a, d)| IntT::Sel(c, a, d)),
        ]
        .boxed();
        let next_int = if conjunctions {
            prop_oneof![
                29 => next_int,
                1 => (b(&int), b(&int)).prop_map(|(a, c)| IntT::And(a, c)),
            ]
            .boxed()
        } else {
            next_int
        };
        let next_bool = prop_oneof![
            5 => bool_leaf(),
            2 => (b(&int), b(&int)).prop_map(|(a, c)| BoolT::Eq(a, c)),
            2 => (b(&int), b(&int)).prop_map(|(a, c)| BoolT::Lt(a, c)),
            1 => bool.clone().prop_map(|a| BoolT::Not(Box::new(a))),
            2 => b(&int).prop_map(BoolT::Even),
            1 => (b(&int), map.clone().prop_map(Box::new)).prop_map(|(k, m)| BoolT::InKeys(k, m)),
        ]
        .boxed();
        let next_bool = if conjunctions {
            prop_oneof![
                13 => next_bool,
                1 => (bool.clone().prop_map(Box::new), bool.clone().prop_map(Box::new))
                    .prop_map(|(a, c)| BoolT::And(a, c)),
            ]
            .boxed()
        } else {
            next_bool
        };
        let next_map = prop_oneof![
            3 => map_leaf(),
            2 => (b(&int), b(&int)).prop_map(|(k, v)| MapT::Item(k, v)),
            2 => (map.clone().prop_map(Box::new), map.prop_map(Box::new))
                .prop_map(|(a, c)| MapT::Concat(a, c)),
        ]
        .boxed();
        level = Terms {
            int: next_int,
            bool: next_bool,
            map: next_map,
        };
    }
    level
}

pub fn atom(terms: &Terms) -> BoxedStrategy<Pred> {
    let any = prop_oneof![
        5 => terms.int.clone().prop_map(AnyT::Int),
        1 => terms.bool.clone().prop_map(AnyT::Bool),
        1 => terms.map.clone().prop_map(AnyT::Map),
    ];
    let literal = (-2i8..=2).prop_map(|value| AnyT::Int(int_lit(value)));
    prop_oneof![
        1 => Just(Pred::Top),
        1 => Just(Pred::Bottom),
        5 => any.prop_map(Pred::Ceil),
        4 => (terms.int.clone(), terms.int.clone())
            .prop_map(|(a, b)| Pred::Eq(AnyT::Int(a), AnyT::Int(b))),
        3 => (terms.int.clone(), literal).prop_map(|(a, b)| Pred::Eq(AnyT::Int(a), b)),
        1 => (terms.bool.clone(), terms.bool.clone())
            .prop_map(|(a, b)| Pred::Eq(AnyT::Bool(a), AnyT::Bool(b))),
        1 => (terms.map.clone(), terms.map.clone())
            .prop_map(|(a, b)| Pred::Eq(AnyT::Map(a), AnyT::Map(b))),
        3 => terms.bool.clone().prop_map(Pred::Holds),
    ]
    .boxed()
}

pub fn predicate(terms: &Terms) -> BoxedStrategy<Pred> {
    let binder = prop_oneof![
        1 => Just(Binder::Bool),
        1 => prop_oneof![Just(IntVar::X), Just(IntVar::Y), Just(IntVar::Z)].prop_map(Binder::Int),
        3 => Just(Binder::Int(IntVar::N)),
    ];
    let composed = atom(terms).prop_recursive(3, 4, 2, move |inner| {
        prop_oneof![
            2 => inner.clone().prop_map(|p| Pred::Not(Box::new(p))),
            2 => (inner.clone(), inner.clone())
                .prop_map(|(p, q)| Pred::And(Box::new(p), Box::new(q))),
            2 => (inner.clone(), inner.clone())
                .prop_map(|(p, q)| Pred::Or(Box::new(p), Box::new(q))),
            1 => (inner.clone(), inner.clone())
                .prop_map(|(p, q)| Pred::Implies(Box::new(p), Box::new(q))),
            2 => (binder.clone(), inner).prop_map(|(v, p)| Pred::Exists(v, Box::new(p))),
        ]
    });
    prop_oneof![7 => composed, 1 => reuse(terms)].boxed()
}

/// The same term on both sides of a binder that rebinds one of its variables (GAP K23 review):
/// `t = c ∧ ∃v. ¬(t = c)`, `¬(t = c) ∧ ∃v. t = c` or `¬⌈t⌉ ∧ ∃v. ⌈t⌉`, with `v` a variable `t`
/// mentions, and half the time all of it under `∃v`, so that `v` is bound twice on one path. The
/// two occurrences of `t` are one node of the translation that denotes two values: inside `∃v`
/// it reads the bound `v`. Whenever the inner `∃` has a witness (`WITNESSES`), K truth holds the
/// whole formula true where its first conjunct holds, and a translation that let the inner `t`
/// reuse the outer one's `let` (its value, or its domain) would read the inner `∃` as the first
/// conjunct's negation: Unsat. The generator draws the two sides of other binders
/// independently, so it rarely puts one node on both sides.
pub fn reuse(terms: &Terms) -> BoxedStrategy<Pred> {
    const VARIABLES: [IntVar; 4] = [IntVar::X, IntVar::Y, IntVar::Z, IntVar::N];
    (
        terms.int.clone(),
        any::<prop::sample::Index>(),
        -2i8..=2,
        0u8..3,
        any::<bool>(),
    )
        .prop_filter_map(
            "a term that mentions a variable and is not one",
            |(t, index, c, shape, twice)| {
                if matches!(t, IntT::Var(_)) {
                    return None;
                }
                let mentioned = VARIABLES
                    .into_iter()
                    .filter(|var| t.mentions(*var))
                    .collect::<Vec<_>>();
                if mentioned.is_empty() {
                    return None;
                }
                let var = *index.get(&mentioned);
                let eq = || Pred::Eq(AnyT::Int(t.clone()), AnyT::Int(int_lit(c)));
                let ceil = || Pred::Ceil(AnyT::Int(t.clone()));
                let not = |p: Pred| Pred::Not(Box::new(p));
                let exists = |p: Pred| Pred::Exists(Binder::Int(var), Box::new(p));
                let (outer, inner) = match shape {
                    0 => (eq(), not(eq())),
                    1 => (not(eq()), eq()),
                    _ => (not(ceil()), ceil()),
                };
                let formula = Pred::And(Box::new(outer), Box::new(exists(inner)));
                Some(if twice { exists(formula) } else { formula })
            },
        )
        .boxed()
}

pub fn case(symbolic_exponents: bool) -> impl Strategy<Value = Case> {
    case_with(symbolic_exponents, false)
}

/// [`case`] over [`terms_with`]'s terms, term-level `\and`s included with `conjunctions`.
pub fn case_with(symbolic_exponents: bool, conjunctions: bool) -> impl Strategy<Value = Case> {
    let terms = terms_with(3, symbolic_exponents, conjunctions);
    let binding_terms = terms_with(2, symbolic_exponents, conjunctions).int;
    let predicate = predicate(&terms);
    let binding = (
        prop_oneof![Just(IntVar::X), Just(IntVar::Y), Just(IntVar::Z)],
        binding_terms,
    );
    (
        prop::collection::vec(predicate.clone(), 0..=2),
        predicate,
        prop::option::weighted(0.25, binding),
    )
        .prop_map(|(known, checked, binding)| Case {
            known,
            checked,
            // A binding is an idempotent substitution: its term does not mention its variable.
            binding: binding.filter(|(var, term)| !term.mentions(*var)),
        })
}

pub fn terms_at(depth: u32, symbolic_exponents: bool) -> BoxedStrategy<IntT> {
    terms(depth, symbolic_exponents).int
}

/// Whether `{prefix}_SYMBOLIC_EXPONENTS` is set: a target's opt-in to symbolic `^Int` exponents
/// (`power_exponent`).
pub fn symbolic_exponents(prefix: &str) -> bool {
    std::env::var_os(format!("{prefix}_SYMBOLIC_EXPONENTS")).is_some()
}

/// A runner of `PROPTEST_CASES` cases (default 512), from `{prefix}_SEED` when it is set and
/// proptest's fixed `deterministic_rng` otherwise, with no failure persistence.
pub fn configured_runner(prefix: &str) -> (TestRunner, u32, Option<u64>) {
    let cases = std::env::var("PROPTEST_CASES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(512);
    let seed = std::env::var(format!("{prefix}_SEED"))
        .ok()
        .and_then(|value| value.parse::<u64>().ok());
    let rng = seed.map_or_else(
        || TestRng::deterministic_rng(RngAlgorithm::ChaCha),
        |seed| {
            let mut bytes = [0u8; 32];
            bytes[..8].copy_from_slice(&seed.to_le_bytes());
            TestRng::from_seed(RngAlgorithm::ChaCha, &bytes)
        },
    );
    let runner = TestRunner::new_with_rng(
        Config {
            cases,
            failure_persistence: None,
            max_shrink_iters: 4096,
            ..Config::default()
        },
        rng,
    );
    (runner, cases, seed)
}

/// A short wall-clock bound per Z3 check and no retry (`{prefix}_TIMEOUT_MS`, default 100), and a
/// bound on Z3's own memory (`memory_max_size`, megabytes): both make an answer `Unknown`, which
/// is counted and refutes nothing, so they bound the test's cost without weakening any check.
/// Which cases are decided can then vary with the machine's load; every decided answer is checked
/// whatever it is, so a failure is a wrong answer on any run, and the failure prints its shrunk
/// case for a rerun.
///
/// Not the clock-free mode (`Z3Options::resource_limit`), which `solver_translation`'s
/// `the_symbolic_power_queries_k19_found_return_under_either_bound` covers for the queries that
/// hung there before GAP K32 (one ran 362 s, one did not end in 300 s, a power of a power
/// exhausted 8 GiB: GAP K19 report), when the translation read a power with a symbolic exponent
/// as Z3's own.
pub fn solver(definition: &BackendDefinition, prefix: &str) -> Z3Solver {
    z3::set_global_param("memory_max_size", "256");
    let timeout_ms = std::env::var(format!("{prefix}_TIMEOUT_MS"))
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(100);
    Z3Solver::with_options(
        definition,
        Z3Options {
            timeout_ms,
            retry_limit: 0,
            resource_limit: None,
        },
    )
    .expect("the solver loads the definition, its smt-lemma included")
}
