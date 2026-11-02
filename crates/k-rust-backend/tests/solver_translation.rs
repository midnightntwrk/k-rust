//! GAP K19: a property test of the solver translation's guarantee.
//!
//! The requirement every solver answer is held to (designs/K15.md section 1.1): for every
//! predicate φ and every K valuation ρ of its free element variables, `I_ρ ⊨ T(φ)` iff `ρ ⊨ φ`,
//! where `I_ρ` interprets each symbol by a model of the definition. So an answer that claims
//! something about every valuation, or about none, is refuted by one valuation of one model of
//! the definition where the claim is false: `Valid` by a valuation where the known predicates
//! hold and the checked one does not; `Refuted` and `Unsat` by one where all of them hold;
//! `InconsistentGroundTruth` by one where the known predicates hold. A `Sat` answer claims only
//! that a valuation exists, and is checked only where the solver gives one (`model_of`'s model
//! of an exact query), by evaluating the original predicates at it. `Contingent` and `Unknown`
//! claim nothing and are only counted; so is a `Contingent` answer every domain valuation
//! decides one way, a completeness statistic that never fails.
//!
//! K truth is computed here, over the generator's own syntax tree, by an evaluator written from
//! the semantics of each symbol of the tiny definition below (`eval_int`, `eval_pred`): every
//! application is strict, so an undefined argument makes it `\bottom` (`None`), `#if` included;
//! a partial symbol is `\bottom` exactly where the model below leaves it undefined; an equality
//! of two patterns holds iff both are the same element or both are `\bottom`; a Boolean term as
//! a predicate is `b = true`. No function of k-rust computes this truth: the definition's text is
//! the only input the evaluator and the code under test share. Valuations range over a small
//! domain (`X, Y, Z, N ∈ [-2, 2]`, `B` both Booleans, `M` four maps), which is all a refutation
//! needs; `\exists` over `Bool` is exact, `\exists` over `Int` is true where a witness lies in
//! `[-4, 4]` and unknown otherwise, since an unbounded domain cannot be refuted by enumeration.
//! Unknown truth refutes nothing.
//!
//! The definition has more than one model, and the evaluator enumerates four of them wherever a
//! case mentions `pf` or `g`: `pf`'s conditional ceil equation leaves `pf(X)` open for `X < 0`
//! (undefined there, or defined), and the values the definition leaves open (`pf`'s, and `g`'s
//! outside its lemma) take one of two choices. Every other symbol's definedness and value are
//! fixed by an equation, a hook or an `smt-hook`. Each is a model of every axiom, so an answer
//! about all models is refuted by any one of them.
//!
//! By default 512 cases from a fixed seed. Run deeper with `PROPTEST_CASES=20000`, from another
//! seed with `SOLVER_TRANSLATION_SEED=<u64>`, with a longer Z3 check bound with
//! `SOLVER_TRANSLATION_TIMEOUT_MS` (default 100), with literal `^Int` exponents only with
//! `SOLVER_TRANSLATION_SYMBOLIC_EXPONENTS=0` (see `power_exponent`), and print every case and its
//! time with
//! `SOLVER_TRANSLATION_TRACE=1`. A failure prints the shrunk case, the answer, and the
//! counter-valuation with each predicate's truth there.

#![cfg(feature = "z3")]

use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    fmt,
    num::NonZeroU32,
    sync::Arc,
};

use k_rust_backend::{
    definition::BackendDefinition,
    model::model_of,
    rule::Predicate,
    simplify::{SimplificationOptions, simplify_predicate_with_solver},
    smt::{
        Exactness, ModelResult, NoSolver, Satisfiability, SmtSolver, Validity, Z3Options, Z3Solver,
        translation_exactness,
    },
    substitution::Substitution,
    term::{Term, TermKind, Variable},
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};
use proptest::{
    prelude::*,
    test_runner::{Config, RngAlgorithm, TestCaseError, TestError, TestRng, TestRunner},
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
const DEFINITION: &str = r#"[]
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
endmodule []"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(DEFINITION).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

fn internal_term(definition: &BackendDefinition, source: &str) -> Term {
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
enum IntVar {
    X,
    Y,
    Z,
    N,
}

const INT_VARS: [IntVar; 4] = [IntVar::X, IntVar::Y, IntVar::Z, IntVar::N];

impl IntVar {
    const fn index(self) -> usize {
        self as usize
    }

    const fn name(self) -> &'static str {
        match self {
            Self::X => "X",
            Self::Y => "Y",
            Self::Z => "Z",
            Self::N => "N",
        }
    }
}

#[derive(Clone, Debug)]
enum IntT {
    Var(IntVar),
    Lit(i8),
    Add(Box<IntT>, Box<IntT>),
    Half(Box<IntT>),
    Div(Box<IntT>, Box<IntT>),
    Pf(Box<IntT>),
    Pow(Box<IntT>, Box<IntT>),
    Ite(Box<BoolT>, Box<IntT>, Box<IntT>),
    G(Box<IntT>),
    Lookup(Box<MapT>, Box<IntT>),
}

#[derive(Clone, Debug)]
enum BoolT {
    /// The Bool variable `B`.
    Var,
    Lit(bool),
    Eq(Box<IntT>, Box<IntT>),
    Lt(Box<IntT>, Box<IntT>),
    Not(Box<BoolT>),
    Even(Box<IntT>),
    InKeys(Box<IntT>, Box<MapT>),
}

#[derive(Clone, Debug)]
enum MapT {
    /// The Map variable `M`.
    Var,
    Unit,
    Item(Box<IntT>, Box<IntT>),
    Concat(Box<MapT>, Box<MapT>),
}

#[derive(Clone, Debug)]
enum AnyT {
    Int(IntT),
    Bool(BoolT),
    Map(MapT),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binder {
    Bool,
    Int(IntVar),
}

#[derive(Clone, Debug)]
enum Pred {
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
struct Case {
    known: Vec<Pred>,
    checked: Pred,
    binding: Option<(IntVar, IntT)>,
}

// The free variables a case mentions, so that only those are enumerated.
#[derive(Clone, Debug, Default)]
struct Free {
    ints: BTreeSet<IntVar>,
    bool: bool,
    map: bool,
    /// The case mentions `pf` or `g`, whose models are not unique.
    open: bool,
}

impl IntT {
    fn free(&self, free: &mut Free) {
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
            Self::Ite(c, a, b) => {
                c.free(free);
                a.free(free);
                b.free(free);
            }
            Self::Lookup(m, k) => {
                m.free(free);
                k.free(free);
            }
        }
    }

    fn mentions(&self, var: IntVar) -> bool {
        let mut free = Free::default();
        self.free(&mut free);
        free.ints.contains(&var)
    }
}

impl BoolT {
    fn free(&self, free: &mut Free) {
        match self {
            Self::Var => free.bool = true,
            Self::Lit(_) => {}
            Self::Eq(a, b) | Self::Lt(a, b) => {
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
    fn free(&self, free: &mut Free) {
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
    fn free(&self, free: &mut Free) {
        match self {
            Self::Int(t) => t.free(free),
            Self::Bool(t) => t.free(free),
            Self::Map(t) => t.free(free),
        }
    }
}

impl Pred {
    fn free(&self, free: &mut Free) {
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
            }
        }
    }
}

impl Case {
    fn free(&self) -> Free {
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
    fn kore(&self) -> String {
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
        }
    }
}

impl BoolT {
    fn kore(&self) -> String {
        match self {
            Self::Var => "B:SortBool{}".to_owned(),
            Self::Lit(value) => format!(r#"\dv{{SortBool{{}}}}("{value}")"#),
            Self::Eq(a, b) => format!("eqInt{{}}({}, {})", a.kore(), b.kore()),
            Self::Lt(a, b) => format!("ltInt{{}}({}, {})", a.kore(), b.kore()),
            Self::Not(a) => format!("notBool{{}}({})", a.kore()),
            Self::Even(a) => format!("even{{}}({})", a.kore()),
            Self::InKeys(k, m) => format!("inKeys{{}}({}, {})", k.kore(), m.kore()),
        }
    }
}

impl MapT {
    fn kore(&self) -> String {
        match self {
            Self::Var => "M:SortMap{}".to_owned(),
            Self::Unit => "unit{}()".to_owned(),
            Self::Item(k, v) => format!("item{{}}({}, {})", k.kore(), v.kore()),
            Self::Concat(a, b) => format!("concat{{}}({}, {})", a.kore(), b.kore()),
        }
    }
}

impl AnyT {
    fn kore(&self) -> String {
        match self {
            Self::Int(t) => t.kore(),
            Self::Bool(t) => t.kore(),
            Self::Map(t) => t.kore(),
        }
    }
}

/// The definition and its variables, to build the backend's predicates.
struct Backend {
    definition: BackendDefinition,
    ints: [Variable; 4],
    bool: Variable,
}

fn variable_of(term: &Term) -> Variable {
    match term.kind() {
        TermKind::Variable(variable) => variable.clone(),
        other => panic!("not a variable: {other:?}"),
    }
}

impl Backend {
    fn new() -> Self {
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

    fn term(&self, source: &str) -> Term {
        internal_term(&self.definition, source)
    }

    fn predicate(&self, predicate: &Pred) -> Predicate {
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

    fn substitution(&self, binding: Option<&(IntVar, IntT)>) -> Substitution {
        binding
            .map(|(var, term)| (self.ints[var.index()].clone(), self.term(&term.kore())))
            .into_iter()
            .collect()
    }
}

// ---------------------------------------------------------------------------------------------
// K truth: the evaluator over the generator's syntax.

#[derive(Clone, Debug, Eq, PartialEq)]
enum Value {
    Int(i128),
    Bool(bool),
    Map(BTreeMap<i128, i128>),
}

/// A value the evaluator cannot compute exactly (an integer beyond `i128`): its truth is
/// unknown, never a refutation.
#[derive(Clone, Copy, Debug)]
struct Overflow;

type Eval<T> = Result<Option<T>, Overflow>;

/// The four maps `M` ranges over.
fn maps() -> [BTreeMap<i128, i128>; 4] {
    [
        BTreeMap::new(),
        BTreeMap::from([(0, 1)]),
        BTreeMap::from([(1, 0)]),
        BTreeMap::from([(0, 1), (1, 1)]),
    ]
}

/// A valuation of the free variables, and which of the definition's models it is read in.
#[derive(Clone, Debug)]
struct Env {
    ints: [i128; 4],
    bool: bool,
    map: usize,
    /// Which of the definition's models: `pf` is defined below 0 (`pf_total`) or not, and the
    /// values the definition leaves open are the first choice or the second (`alt_values`).
    pf_total: bool,
    alt_values: bool,
}

const DOMAIN: std::ops::RangeInclusive<i128> = -2..=2;
const WITNESSES: std::ops::RangeInclusive<i128> = -4..=4;

impl Env {
    fn show(&self, free: &Free) -> String {
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
fn valuations(free: &Free, base: &Env, fixed_ints: &BTreeSet<IntVar>) -> Vec<Env> {
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

fn eval_int(term: &IntT, env: &Env) -> Eval<i128> {
    Ok(match term {
        IntT::Var(var) => Some(env.ints[var.index()]),
        IntT::Lit(value) => Some(i128::from(*value)),
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
    })
}

/// The integer power: defined where the exponent is not negative, or the base is 1 or -1.
fn power(base: i128, exponent: i128) -> Result<Option<i128>, Overflow> {
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

fn eval_bool(term: &BoolT, env: &Env) -> Eval<bool> {
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
    })
}

fn eval_map(term: &MapT, env: &Env) -> Eval<BTreeMap<i128, i128>> {
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

fn eval_any(term: &AnyT, env: &Env) -> Eval<Value> {
    Ok(match term {
        AnyT::Int(t) => eval_int(t, env)?.map(Value::Int),
        AnyT::Bool(t) => eval_bool(t, env)?.map(Value::Bool),
        AnyT::Map(t) => eval_map(t, env)?.map(Value::Map),
    })
}

/// Kleene truth: `Unknown` only from an `\exists` over Int with no witness in range, or an
/// integer beyond the evaluator's range.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Truth {
    True,
    False,
    Unknown,
}

impl Truth {
    const fn of(value: bool) -> Self {
        if value { Self::True } else { Self::False }
    }

    const fn not(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Unknown => Self::Unknown,
        }
    }

    const fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::True, Self::True) => Self::True,
            _ => Self::Unknown,
        }
    }

    const fn or(self, other: Self) -> Self {
        self.not().and(other.not()).not()
    }
}

fn eval_pred(predicate: &Pred, env: &Env) -> Truth {
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

/// The truth of the case's known predicates and binding, and of its checked predicate.
fn truths(case: &Case, env: &Env) -> (Truth, Truth) {
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

fn int_leaf() -> BoxedStrategy<IntT> {
    prop_oneof![
        3 => prop_oneof![Just(IntVar::X), Just(IntVar::Y), Just(IntVar::Z)].prop_map(IntT::Var),
        1 => Just(IntT::Var(IntVar::N)),
        3 => (-2i8..=2).prop_map(IntT::Lit),
    ]
    .boxed()
}

fn bool_leaf() -> BoxedStrategy<BoolT> {
    prop_oneof![2 => Just(BoolT::Var), 1 => any::<bool>().prop_map(BoolT::Lit)].boxed()
}

fn map_leaf() -> BoxedStrategy<MapT> {
    prop_oneof![3 => Just(MapT::Var), 1 => Just(MapT::Unit)].boxed()
}

/// A base of `^Int`: a leaf, or one partial application or sum of leaves, so a power's domain
/// still composes with its operands' and never holds another power.
fn power_base() -> BoxedStrategy<Box<IntT>> {
    let leaf = || int_leaf().prop_map(Box::new);
    prop_oneof![
        4 => leaf(),
        1 => leaf().prop_map(IntT::Half).prop_map(Box::new),
        1 => (leaf(), (-2i8..=2).prop_map(|value| Box::new(IntT::Lit(value))))
            .prop_map(|(a, c)| Box::new(IntT::Div(a, c))),
        1 => leaf().prop_map(IntT::Pf).prop_map(Box::new),
        1 => (leaf(), leaf()).prop_map(|(a, c)| Box::new(IntT::Add(a, c))),
    ]
    .boxed()
}

/// An exponent of `^Int`: a literal in `[-2, 2]`, or a base-like symbolic term, unless
/// `SOLVER_TRANSLATION_SYMBOLIC_EXPONENTS=0` leaves only the literals.
///
/// The literals keep `^Int`'s domain (negative exponents, the bases 1 and -1, `0 ^Int 0`) in
/// every run; a symbolic exponent covers the translation's reading of a power whose exponent is
/// not a numeral (`guard_powers` in smt.rs), `0 ^Int Y` at `Y = 0` included (GAP K16). Before GAP
/// K32 that reading was Z3's own power, whose nonlinear arithmetic evaluates the power at the
/// values its candidate models give the operands, a bignum computation that polls neither its
/// timeout nor its resource limit, so symbolic exponents were off by default: the query
/// `known: [even(half(-1) ^Int half(Y)) = (Y in_keys(.Map)) \or (#if (N in_keys(.Map)) #then N
/// +Int -1 #else Y #fi +Int divInt((2 +Int Y) ^Int half(N), -2)) = 2], checked:
/// \ceil(divInt(X, Y))` ran past 40 s under a 100 ms timeout, and one generated case ran 2 h 20
/// min (GAP K19 report). Those queries are now a test of their own
/// (`the_symbolic_power_queries_k19_found_return_under_either_bound`).
fn power_exponent() -> BoxedStrategy<Box<IntT>> {
    let literal = (-2i8..=2).prop_map(|value| Box::new(IntT::Lit(value)));
    if std::env::var_os("SOLVER_TRANSLATION_SYMBOLIC_EXPONENTS").is_none_or(|value| value != "0") {
        prop_oneof![1 => literal, 1 => power_base()].boxed()
    } else {
        literal.boxed()
    }
}

/// Terms of each sort of depth at most `depth`, built bottom-up so that sorts nest in each
/// other. Partial applications are weighted up, and a quotient by a literal (a nonzero one
/// mostly) gets its own weight: an argument a conditional ceil equation's condition does not
/// mention is where a domain composes with another.
struct Terms {
    int: BoxedStrategy<IntT>,
    bool: BoxedStrategy<BoolT>,
    map: BoxedStrategy<MapT>,
}

fn terms(depth: u32) -> Terms {
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
        .prop_map(|value| Box::new(IntT::Lit(value)));
        let next_int = prop_oneof![
            12 => int_leaf(),
            1 => (b(&int), b(&int)).prop_map(|(a, c)| IntT::Add(a, c)),
            3 => b(&int).prop_map(IntT::Half),
            2 => (b(&int), b(&int)).prop_map(|(a, c)| IntT::Div(a, c)),
            3 => (b(&int), literal).prop_map(|(a, c)| IntT::Div(a, c)),
            2 => b(&int).prop_map(IntT::Pf),
            1 => (power_base(), power_exponent()).prop_map(|(a, c)| IntT::Pow(a, c)),
            2 => (bool.clone().prop_map(Box::new), b(&int), b(&int))
                .prop_map(|(c, a, d)| IntT::Ite(c, a, d)),
            1 => b(&int).prop_map(IntT::G),
            2 => (map.clone().prop_map(Box::new), b(&int)).prop_map(|(m, k)| IntT::Lookup(m, k)),
        ]
        .boxed();
        let next_bool = prop_oneof![
            5 => bool_leaf(),
            2 => (b(&int), b(&int)).prop_map(|(a, c)| BoolT::Eq(a, c)),
            2 => (b(&int), b(&int)).prop_map(|(a, c)| BoolT::Lt(a, c)),
            1 => bool.clone().prop_map(|a| BoolT::Not(Box::new(a))),
            2 => b(&int).prop_map(BoolT::Even),
            1 => (b(&int), map.clone().prop_map(Box::new)).prop_map(|(k, m)| BoolT::InKeys(k, m)),
        ]
        .boxed();
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

fn atom(terms: &Terms) -> BoxedStrategy<Pred> {
    let any = prop_oneof![
        5 => terms.int.clone().prop_map(AnyT::Int),
        1 => terms.bool.clone().prop_map(AnyT::Bool),
        1 => terms.map.clone().prop_map(AnyT::Map),
    ];
    let literal = (-2i8..=2).prop_map(|value| AnyT::Int(IntT::Lit(value)));
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

fn predicate(terms: &Terms) -> BoxedStrategy<Pred> {
    let binder = prop_oneof![
        1 => Just(Binder::Bool),
        1 => prop_oneof![Just(IntVar::X), Just(IntVar::Y), Just(IntVar::Z)].prop_map(Binder::Int),
        3 => Just(Binder::Int(IntVar::N)),
    ];
    atom(terms)
        .prop_recursive(3, 4, 2, move |inner| {
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
        })
        .boxed()
}

fn case() -> impl Strategy<Value = Case> {
    let terms = terms(3);
    let binding_terms = terms_at(2);
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

fn terms_at(depth: u32) -> BoxedStrategy<IntT> {
    terms(depth).int
}

// ---------------------------------------------------------------------------------------------
// The checks.

#[derive(Default)]
struct Stats {
    valid: Cell<usize>,
    refuted: Cell<usize>,
    inconsistent: Cell<usize>,
    contingent: Cell<usize>,
    unknown: Cell<usize>,
    errors: Cell<usize>,
    unknown_sat: Cell<usize>,
    errors_sat: Cell<usize>,
    unsat: Cell<usize>,
    sat: Cell<usize>,
    exact: Cell<usize>,
    models_checked: Cell<usize>,
    /// `Contingent` where every domain valuation of the known predicates makes the checked one
    /// true (or every one makes it false): a completeness gap on the domain, never a failure.
    contingent_but_decided_on_domain: Cell<usize>,
    vacuous: Cell<usize>,
}

fn bump(counter: &Cell<usize>) {
    counter.set(counter.get() + 1);
}

impl fmt::Display for Stats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "check_predicates: {} Valid, {} Refuted, {} InconsistentGroundTruth, {} Contingent \
             ({} of them decided on the domain), {} Unknown, {} errors; is_sat: {} Unsat, {} Sat, \
             {} Unknown, {} errors; {} exact queries, {} models checked; {} cases with no domain valuation of known",
            self.valid.get(),
            self.refuted.get(),
            self.inconsistent.get(),
            self.contingent.get(),
            self.contingent_but_decided_on_domain.get(),
            self.unknown.get(),
            self.errors.get(),
            self.unsat.get(),
            self.sat.get(),
            self.unknown_sat.get(),
            self.errors_sat.get(),
            self.exact.get(),
            self.models_checked.get(),
            self.vacuous.get(),
        )
    }
}

fn failure(case: &Case, free: &Free, answer: &str, env: &Env) -> TestCaseError {
    let mut lines = vec![
        format!("case: {case}"),
        format!("answer: {answer}"),
        format!("counter-valuation: {}", env.show(free)),
    ];
    for (index, predicate) in case.known.iter().enumerate() {
        lines.push(format!(
            "  known[{index}] is {:?} there",
            eval_pred(predicate, env)
        ));
    }
    if let Some((var, term)) = &case.binding {
        lines.push(format!(
            "  binding {} |-> {term}: the term is {:?} there",
            var.name(),
            eval_int(term, env)
        ));
    }
    lines.push(format!(
        "  checked is {:?} there",
        eval_pred(&case.checked, env)
    ));
    TestCaseError::fail(lines.join("\n"))
}

/// The model's integer and Boolean values of the case's variables, the variables it binds.
fn model_env(backend: &Backend, model: &Substitution) -> (Env, BTreeSet<IntVar>, Option<bool>) {
    let mut env = Env {
        ints: [0; 4],
        bool: false,
        map: 0,
        pf_total: false,
        alt_values: false,
    };
    let mut bound = BTreeSet::new();
    for var in INT_VARS {
        if let Some(value) = model.get(&backend.ints[var.index()]).and_then(domain_value)
            && let Ok(value) = value.parse::<i128>()
        {
            env.ints[var.index()] = value;
            bound.insert(var);
        }
    }
    let bool = model
        .get(&backend.bool)
        .and_then(domain_value)
        .and_then(|value| value.parse::<bool>().ok());
    if let Some(value) = bool {
        env.bool = value;
    }
    (env, bound, bool)
}

fn domain_value(term: &Term) -> Option<String> {
    match term.kind() {
        TermKind::DomainValue { value, .. } => value.as_utf8().ok().map(str::to_owned),
        _ => None,
    }
}

fn check_case(
    backend: &Backend,
    solver: &Z3Solver,
    case: &Case,
    stats: &Stats,
) -> Result<(), TestCaseError> {
    let free = case.free();
    let base = Env {
        ints: [0; 4],
        bool: false,
        map: 0,
        pf_total: false,
        alt_values: false,
    };
    let rows = valuations(&free, &base, &BTreeSet::new())
        .into_iter()
        .map(|env| {
            let (known, checked) = truths(case, &env);
            (env, known, checked)
        })
        .collect::<Vec<_>>();
    let find = |wanted: &dyn Fn(Truth, Truth) -> bool| {
        rows.iter()
            .find(|(_, known, checked)| wanted(*known, *checked))
            .map(|(env, ..)| env)
    };
    let known = case
        .known
        .iter()
        .map(|predicate| backend.predicate(predicate))
        .collect::<Vec<_>>();
    let checked = backend.predicate(&case.checked);
    let substitution = backend.substitution(case.binding.as_ref());

    let validity = solver
        .check_predicates(&known, &substitution, std::slice::from_ref(&checked))
        .map_err(|stop| {
            TestCaseError::fail(format!("case: {case}\ncheck_predicates stopped: {stop:?}"))
        })?;
    match validity {
        Ok(Validity::Valid) => {
            bump(&stats.valid);
            if let Some(env) = find(&|k, c| k == Truth::True && c == Truth::False) {
                return Err(failure(case, &free, "check_predicates: Valid", env));
            }
        }
        Ok(Validity::Refuted) => {
            bump(&stats.refuted);
            if let Some(env) = find(&|k, c| k == Truth::True && c == Truth::True) {
                return Err(failure(case, &free, "check_predicates: Refuted", env));
            }
        }
        Ok(Validity::InconsistentGroundTruth) => {
            bump(&stats.inconsistent);
            if let Some(env) = find(&|k, _| k == Truth::True) {
                return Err(failure(
                    case,
                    &free,
                    "check_predicates: InconsistentGroundTruth",
                    env,
                ));
            }
        }
        Ok(Validity::Contingent) => {
            bump(&stats.contingent);
            let mut under_known = rows
                .iter()
                .filter(|(_, known, _)| *known == Truth::True)
                .peekable();
            if under_known.peek().is_some() {
                let checked = under_known
                    .map(|(_, _, checked)| *checked)
                    .collect::<Vec<_>>();
                if checked.iter().all(|truth| *truth == Truth::True)
                    || checked.iter().all(|truth| *truth == Truth::False)
                {
                    bump(&stats.contingent_but_decided_on_domain);
                }
            }
        }
        Ok(Validity::Unknown(_)) => bump(&stats.unknown),
        Err(_) => bump(&stats.errors),
    }
    if !rows.iter().any(|(_, known, _)| *known == Truth::True) {
        bump(&stats.vacuous);
    }

    let mut all = known;
    all.push(checked);
    let satisfiability = solver
        .is_sat(&all, &substitution)
        .map_err(|stop| TestCaseError::fail(format!("case: {case}\nis_sat stopped: {stop:?}")))?;
    match satisfiability {
        Ok(Satisfiability::Unsat) => {
            bump(&stats.unsat);
            if let Some(env) = find(&|k, c| k == Truth::True && c == Truth::True) {
                return Err(failure(case, &free, "is_sat: Unsat", env));
            }
        }
        Ok(Satisfiability::Sat) => bump(&stats.sat),
        Ok(Satisfiability::Unknown(_)) => bump(&stats.unknown_sat),
        Err(_) => bump(&stats.errors_sat),
    }

    // A model is a K valuation only of an exact translation; check it where there is one.
    if let Some((var, term)) = &case.binding {
        all.push(Predicate::Equals(
            backend.term(&IntT::Var(*var).kore()),
            backend.term(&term.kore()),
        ));
    }
    // A model of a query over `pf` or `g` may give them values none of the evaluator's models
    // gives, so it is checked only over symbols whose model is unique.
    if !free.open && translation_exactness(&all) == Exactness::Exact {
        bump(&stats.exact);
        let conjunction = Predicate::And(Arc::from(all));
        let model = model_of(&backend.definition, &conjunction, solver).map_err(|stop| {
            TestCaseError::fail(format!("case: {case}\nmodel_of stopped: {stop:?}"))
        })?;
        match model {
            Ok(ModelResult::Sat(model)) => {
                bump(&stats.models_checked);
                let (env, bound, bool) = model_env(backend, &model);
                let mut rest = free.clone();
                if bool.is_some() {
                    rest.bool = false;
                }
                // Variables the model leaves out are completed over the domain; the model is
                // refuted only if no completion satisfies the case.
                let completions = valuations(&rest, &env, &bound);
                let satisfied = completions.iter().any(|env| {
                    let (known, checked) = truths(case, env);
                    known.and(checked) != Truth::False
                });
                if !satisfied {
                    return Err(failure(
                        case,
                        &free,
                        &format!("model_of: Sat {model:?}"),
                        &completions[0],
                    ));
                }
            }
            Ok(ModelResult::Unsat) => {
                if let Some(env) = find(&|k, c| k == Truth::True && c == Truth::True) {
                    return Err(failure(case, &free, "model_of: Unsat", env));
                }
            }
            Ok(ModelResult::Unknown(_)) | Err(_) => {}
        }
    }
    Ok(())
}

fn configured_runner() -> (TestRunner, u32, Option<u64>) {
    let cases = std::env::var("PROPTEST_CASES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(512);
    let seed = std::env::var("SOLVER_TRANSLATION_SEED")
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

/// A short wall-clock bound per Z3 check and no retry (`SOLVER_TRANSLATION_TIMEOUT_MS`, default
/// 100), and a bound on Z3's own memory (`memory_max_size`, megabytes): both make an answer
/// `Unknown`, which is counted and refutes nothing, so they bound the test's cost without
/// weakening any check. Which cases are decided can then vary with the machine's load; every
/// decided answer is checked whatever it is, so a failure is a wrong answer on any run, and the
/// failure prints its shrunk case for a rerun.
///
/// Not the clock-free mode (`Z3Options::resource_limit`): Z3's resource units do not count its
/// arithmetic on numerals, and a power with a symbolic exponent makes its nonlinear check
/// evaluate powers of growing model values. Under resource units alone one query ran 362 s,
/// another (`Y = (2 +Int Y) ^Int N` beside a map equality) did not end in 300 s, and a power of a
/// power exhausted 8 GiB (GAP K19 report). The wall clock stopped those three, though not every
/// query over a symbolic exponent (`power_exponent`).
fn solver(definition: &BackendDefinition) -> Z3Solver {
    z3::set_global_param("memory_max_size", "256");
    let timeout_ms = std::env::var("SOLVER_TRANSLATION_TIMEOUT_MS")
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

/// Every answer of `check_predicates` and `is_sat` that claims something about all valuations or
/// about none, and every model of an exact query, agrees with K truth at each valuation of the
/// domain in each model of the definition (module docs).
#[test]
fn every_decided_solver_answer_agrees_with_k_truth_on_the_domain() {
    let backend = Backend::new();
    let solver = solver(&backend.definition);
    let stats = Stats::default();
    let (mut runner, cases, seed) = configured_runner();
    let started = std::time::Instant::now();
    let trace = std::env::var_os("SOLVER_TRANSLATION_TRACE").is_some();
    // Cases run until the first failure, which counts generated cases: shrinking starts there.
    let (runs, first_failure) = (Cell::new(0usize), Cell::new(None));
    let outcome = runner.run(&case(), |case| {
        let before = std::time::Instant::now();
        if trace {
            eprintln!("case: {case}");
        }
        runs.set(runs.get() + 1);
        let result = check_case(&backend, &solver, &case, &stats);
        if result.is_err() && first_failure.get().is_none() {
            first_failure.set(Some(runs.get()));
        }
        if trace {
            eprintln!("  {:.3} s", before.elapsed().as_secs_f64());
        }
        result
    });
    if let Some(first) = first_failure.get() {
        eprintln!("solver_translation: the first failure was generated case {first}");
    }
    eprintln!(
        "solver_translation: {cases} cases (seed {}), {:.1} s; {stats}",
        seed.map_or_else(|| "fixed".to_owned(), |seed| seed.to_string()),
        started.elapsed().as_secs_f64()
    );
    match outcome {
        Ok(()) => {}
        Err(TestError::Fail(reason, case)) => {
            panic!("a solver answer disagrees with K truth (shrunk case: {case})\n{reason}")
        }
        Err(TestError::Abort(reason)) => panic!("the property run aborted: {reason}"),
    }
}

/// The evaluator's model of each hooked symbol agrees with k-rust's ground evaluation where the
/// backend decides a ground application (a check of the oracle, not of the solver): a value it
/// computes is the evaluator's, and an application it finds undefined is undefined in the
/// evaluator. Symbols with no K hook (`half`, `pf`, `even`, `g`) have no ground evaluation to
/// compare with; their models are argued in the definition's doc.
#[test]
fn the_oracles_model_agrees_with_ground_evaluation_of_the_hooked_symbols() {
    let backend = Backend::new();
    let env = Env {
        ints: [0; 4],
        bool: false,
        map: 0,
        pf_total: false,
        alt_values: false,
    };
    let lit = |value: i128| Box::new(IntT::Lit(i8::try_from(value).expect("a small literal")));
    let map_literals = [
        MapT::Unit,
        MapT::Item(lit(0), lit(1)),
        MapT::Item(lit(1), lit(0)),
        MapT::Concat(
            Box::new(MapT::Item(lit(0), lit(1))),
            Box::new(MapT::Item(lit(1), lit(1))),
        ),
        MapT::Concat(
            Box::new(MapT::Item(lit(0), lit(1))),
            Box::new(MapT::Item(lit(0), lit(0))),
        ),
    ];
    let mut ground = Vec::new();
    for a in DOMAIN {
        for b in DOMAIN {
            for t in [
                IntT::Add(lit(a), lit(b)),
                IntT::Div(lit(a), lit(b)),
                IntT::Pow(lit(a), lit(b)),
                IntT::Ite(Box::new(BoolT::Lt(lit(a), lit(b))), lit(a), lit(b)),
                IntT::Ite(
                    Box::new(BoolT::Lit(true)),
                    lit(a),
                    Box::new(IntT::Div(lit(b), lit(0))),
                ),
            ] {
                ground.push(AnyT::Int(t));
            }
            ground.push(AnyT::Bool(BoolT::Eq(lit(a), lit(b))));
            ground.push(AnyT::Bool(BoolT::Lt(lit(a), lit(b))));
        }
        for map in &map_literals {
            ground.push(AnyT::Int(IntT::Lookup(Box::new(map.clone()), lit(a))));
            ground.push(AnyT::Bool(BoolT::InKeys(lit(a), Box::new(map.clone()))));
        }
    }
    for map in &map_literals {
        ground.push(AnyT::Map(map.clone()));
    }
    ground.push(AnyT::Bool(BoolT::Not(Box::new(BoolT::Lit(true)))));
    ground.push(AnyT::Bool(BoolT::Not(Box::new(BoolT::Lit(false)))));

    let simplified = |predicate: &Pred| {
        simplify_predicate_with_solver(
            &backend.definition,
            &backend.predicate(predicate),
            &[],
            SimplificationOptions::unbounded(),
            &NoSolver,
        )
        .expect("no stop is armed")
        .ok()
    };
    let (mut decided, mut disagreements) = (0, Vec::new());
    for term in &ground {
        let value = eval_any(term, &env).expect("ground values are small");
        let ceil = simplified(&Pred::Ceil(term.clone()));
        let expected_ceil = if value.is_some() {
            Predicate::True
        } else {
            Predicate::False
        };
        if let Some(answer @ (Predicate::True | Predicate::False)) = ceil {
            decided += 1;
            if answer != expected_ceil {
                disagreements.push(format!(
                    "\\ceil({term}): backend {answer:?}, oracle {value:?}"
                ));
            }
        }
        if let Some(value) = value {
            let literal = match value {
                Value::Int(value) => AnyT::Int(IntT::Lit(
                    i8::try_from(value).expect("ground values here are small"),
                )),
                Value::Bool(value) => AnyT::Bool(BoolT::Lit(value)),
                Value::Map(_) => continue,
            };
            if let Some(answer @ (Predicate::True | Predicate::False)) =
                simplified(&Pred::Eq(term.clone(), literal.clone()))
            {
                decided += 1;
                if answer != Predicate::True {
                    disagreements.push(format!("{term} = {literal}: backend {answer:?}"));
                }
            }
        }
    }
    eprintln!(
        "oracle sanity: {} ground terms, {decided} backend decisions",
        ground.len()
    );
    assert!(disagreements.is_empty(), "{disagreements:#?}");
    assert!(
        decided > ground.len(),
        "the backend decided too few ground applications: {decided}"
    );
}

/// The queries over symbolic `^Int` exponents that GAP K19 found no bound stopped (K32): the
/// reported reproduction, the generated case it was shrunk from (case 8,455 of seed 19), a power
/// of a symbolic power beside a map equality, and `Y = (2 +Int Y) ^Int N` beside one.
fn unbounded_power_cases() -> Vec<(&'static str, Case)> {
    use IntVar::{N, X, Y};
    let int = |value: i8| Box::new(IntT::Lit(value));
    let var = |var: IntVar| Box::new(IntT::Var(var));
    let empty_has = |key: IntVar| Box::new(BoolT::InKeys(var(key), Box::new(MapT::Unit)));
    let reported_known = Pred::Or(
        Box::new(Pred::Eq(
            AnyT::Bool(BoolT::Even(Box::new(IntT::Pow(
                Box::new(IntT::Half(int(-1))),
                Box::new(IntT::Half(var(Y))),
            )))),
            AnyT::Bool(*empty_has(Y)),
        )),
        Box::new(Pred::Eq(
            AnyT::Int(IntT::Add(
                Box::new(IntT::Ite(
                    empty_has(N),
                    Box::new(IntT::Add(var(N), int(-1))),
                    var(Y),
                )),
                Box::new(IntT::Div(
                    Box::new(IntT::Pow(
                        Box::new(IntT::Add(int(2), var(Y))),
                        Box::new(IntT::Half(var(N))),
                    )),
                    int(-2),
                )),
            )),
            AnyT::Int(IntT::Lit(2)),
        )),
    );
    let quotient = || AnyT::Int(IntT::Div(var(X), var(Y)));
    let map_of = |key: IntVar, value: Box<IntT>| {
        Pred::Eq(AnyT::Map(MapT::Var), AnyT::Map(MapT::Item(var(key), value)))
    };
    vec![
        (
            "the reported reproduction",
            Case {
                known: vec![reported_known.clone()],
                checked: Pred::Ceil(quotient()),
                binding: None,
            },
        ),
        (
            "generated case 8,455 of seed 19",
            Case {
                known: vec![reported_known],
                checked: Pred::Or(
                    Box::new(Pred::Eq(AnyT::Int(IntT::Lit(-2)), AnyT::Int(IntT::Var(N)))),
                    Box::new(Pred::Eq(quotient(), AnyT::Int(IntT::Lit(-2)))),
                ),
                binding: None,
            },
        ),
        (
            "a power of a symbolic power beside a map equality",
            Case {
                known: vec![map_of(
                    X,
                    Box::new(IntT::Pow(
                        Box::new(IntT::Pow(int(2), var(X))),
                        Box::new(IntT::Ite(Box::new(BoolT::Lit(true)), var(X), int(2))),
                    )),
                )],
                checked: Pred::Eq(AnyT::Int(IntT::Var(X)), AnyT::Int(IntT::Lit(1))),
                binding: None,
            },
        ),
        (
            "Y = (2 +Int Y) ^Int N beside a map equality",
            Case {
                known: vec![
                    Pred::Eq(
                        AnyT::Int(IntT::Var(Y)),
                        AnyT::Int(IntT::Pow(Box::new(IntT::Add(int(2), var(Y))), var(N))),
                    ),
                    map_of(N, var(Y)),
                ],
                checked: Pred::Eq(AnyT::Int(IntT::Var(N)), AnyT::Int(IntT::Lit(0))),
                binding: None,
            },
        ),
    ]
}

/// Each query of [`unbounded_power_cases`] returns, under the wall clock and under resource units
/// alone, within [`POWER_QUERY_WATCHDOG`] (each took 0.01-0.04 s when GAP K32 landed); its decided
/// answers agree with K truth on the domain. Before GAP K32 the first two ran past 30 s in both
/// modes, and the last past 30 s under resource units: the translation read each power as Z3's
/// own, whose evaluation at model values nothing stopped. The queries run on a thread of their
/// own and the test waits for each with a timeout, so a regression fails here, naming the query,
/// instead of hanging the test binary (the stuck Z3 thread ends with the failing process).
#[test]
fn the_symbolic_power_queries_k19_found_return_under_either_bound() {
    /// The wait for one query, far above its measured time and below a hang's.
    const POWER_QUERY_WATCHDOG: std::time::Duration = std::time::Duration::from_secs(30);
    enum Progress {
        Started(String),
        Returned(String, f64),
    }
    let (sender, receiver) = std::sync::mpsc::channel();
    let worker = std::thread::spawn(move || {
        let backend = Backend::new();
        let stats = Stats::default();
        let modes = [
            (
                "the wall clock",
                Z3Options {
                    timeout_ms: 100,
                    retry_limit: 0,
                    resource_limit: None,
                },
            ),
            (
                "resource units",
                Z3Options {
                    timeout_ms: 100,
                    retry_limit: 1,
                    resource_limit: NonZeroU32::new(500_000),
                },
            ),
        ];
        for (mode, options) in modes {
            let solver = Z3Solver::with_options(&backend.definition, options)
                .expect("the solver loads the definition");
            for (name, case) in unbounded_power_cases() {
                let label = format!("{mode}, {name}");
                let _ = sender.send(Progress::Started(label.clone()));
                let started = std::time::Instant::now();
                check_case(&backend, &solver, &case, &stats)
                    .unwrap_or_else(|failure| panic!("{label}: {failure}"));
                let _ = sender.send(Progress::Returned(label, started.elapsed().as_secs_f64()));
            }
        }
        eprintln!("{stats}");
    });
    let mut running = String::from("loading the solver");
    loop {
        match receiver.recv_timeout(POWER_QUERY_WATCHDOG) {
            Ok(Progress::Started(label)) => running = label,
            Ok(Progress::Returned(label, seconds)) => {
                eprintln!("{label}: {seconds:.2} s");
                running = String::from("loading the solver");
            }
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => panic!(
                "{running}: no answer within {} s",
                POWER_QUERY_WATCHDOG.as_secs()
            ),
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => break,
        }
    }
    if let Err(panic) = worker.join() {
        std::panic::resume_unwind(panic);
    }
}
