//! The matching-logic position matrix: every matching-logic construct at every sentence position
//! and on the search-pattern route, each cell with the outcome the K text's meaning requires.
//!
//! # The meaning standard
//!
//! Until `docs/compatibility.md` states it (ticket MLP/5), the standard is the one of the audit
//! `ADD3-ml-positions`, "What the K text means":
//!
//! > A rule `l => r requires ψ ensures φ` is the axiom `l ∧ ψ̂ ⇒ •(r ∧ φ̂)`, and an equation
//! > `f(..) => r requires ψ ensures φ` is `ψ̂ → f(..) = r ∧ φ̂`. ψ̂ is the condition read as a
//! > predicate: the matching-logic connectives at the root of the condition are predicate
//! > connectives, and each Bool term t below them, where a predicate is expected, stands for
//! > `t = true`. A connective below a non-ML symbol is a term-level operation on sets of values
//! > (so `(X #Or 5) <Int 3` is `{X <Int 3, false}`, never {true}). At a term position each
//! > connective has its set meaning (`1 #Or 2` matches either; `X #And {X #Equals 1}` is X where
//! > X = 1; `#Bottom` is nothing).
//!
//! The operands of `#Equals`, `#Ceil`, `#Floor` and `#In` are term positions.
//!
//! # Expectations
//!
//! Each cell states one of:
//! - `Accept`: the sentence compiles through the library route kink uses
//!   (`load_for_compilation`, or `load_with_options` for claims, then
//!   `compile_loaded_definition` and `Backend::new`), and every run gives the stated leaves,
//!   compared by the term of the `<k>` cell and the halt reason only, never by constraint text,
//!   and every claim the stated verdict (`NotProven` is `disproved` or `failed`);
//! - `Refuse`: compilation stops with the stated diagnostic code at the line of the probed
//!   sentence, or loading stops with a parse error located at that line; the code may differ
//!   between the portable and the Z3 build where each build's parser decides the refusal.
//!
//! A step whose result denotes no state (an `ensures` that does not hold, a right side such as
//! `#Bottom` or `X #And 1` at X = 3) is expected as a `Trivial` leaf at the state before the
//! step: the convention of k-rust's halt reasons (`HaltReasonOutput::Trivial`), which reports
//! such a pre-state as having no defined successor rather than as a state of the run.
//!
//! A run may also list optional leaves, which the meaning neither requires nor excludes (the
//! definedness branch `Trivial` of a partial function's application that no equation
//! evaluates, whose constraint the contract does not check); a run whose leaves are all
//! optional needs one of its non-Trivial ones. A cell may carry an allowance for a construct the
//! build does not decide (a quantified predicate or a claim's arithmetic implication without a
//! solver, and `#Floor`). A run then conforms when it is the single leaf `Indeterminate` at the
//! program or at an expected state (the unheated state of a context), or when every expected leaf other than a Trivial one is observed (constrained or
//! not, or as the unevaluated application of `f` that stands for it) and every other observed
//! leaf is a leaf of the construct's other truth value that is constrained or holds that
//! unevaluated application; a claim may be `indeterminate` or `failed` instead of `proven`, and
//! `indeterminate` instead of not proven.
//!
//! A panic during a cell (a kompile invariant in the test profile, a backend assertion) never
//! conforms.
//!
//! Independently of PENDING, the compiled KORE of every `Accept` cell must write each condition
//! as the predicate it states: no `\equals{SortBool{}, R}(P, ..)` whose operand P is a
//! matching-logic pattern (the root encoding of a whole condition as one Bool term). And the
//! compiled KORE of every cell that compiles must hold no axiom whose result side (a rewrite's
//! right side, an equation's value and `ensures`) has a free generated variable (`_Gen<N>`) that
//! its matched side does not hold: such a variable, universal over the axiom, would make the
//! result empty (a guard alias of a disjunction in an `ensures`). This holds independently of the
//! kompile invariant R3, which catches the same defect only where kompile invariants run.
//!
//! # PENDING
//!
//! [`PENDING`] lists the cells that deviate from their expectation at the base of the ML lane
//! (`main` 7a43fc511, which holds MLP/8's backend predicate reading), each with the ticket after which its design makes the cell conform and,
//! for each build, how it deviates there ([`Class`]: `Wrong`, `Refused`, `Panic`, `Undecided`,
//! `Accepted`, or `Conforms` where it does not deviate). A refused cell is classified against the
//! runs its meaning states, where it states any. A pending cell must still deviate, in the
//! recorded class: a change that makes it conform, or that changes how it deviates (a wrong
//! answer becoming a refusal, a refusal becoming a wrong answer), fails the shard until the
//! change records it in the list, so every later ticket's regression test is its cells leaving
//! or changing in the list. A cell that is not pending must conform. The ticket `unassigned` marks a deviation that no ticket of the ML lane covers, kept
//! visible until the programme assigns it.
//!
//! # Running
//!
//! The shards are ignored by default and run by the `ml-positions` gate
//! (`scripts/run-gates.sh ml-positions`), in the portable build and with
//! `--features z3-inference`. With `ML_POSITIONS_OUT=<directory>` every shard writes one line
//! per cell (cell, build, conforms or deviates, outcome) to `<directory>/<shard>-<build>.tsv`.

use std::{
    cell::Cell as ThreadFlag,
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    panic::{AssertUnwindSafe, catch_unwind},
    sync::Once,
    time::Instant,
};

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest, ProveRequest, SearchPatternRequest},
    builtin::embedded,
    definition::{Attributes, CheckMode, LOCATION_ATTRIBUTE, ResolvedDefinition, SOURCE_ATTRIBUTE},
    diagnostic::Severity,
    inner::definition_with_named_projections,
    kompile::{
        CompilationBackend, CompileOptions, CompileSearchPatternError, compile_loaded_definition,
        compile_search_pattern,
    },
    kore::{
        ast::{Pattern, Sentence as KoreSentence},
        codec,
        parser::parse_definition,
    },
    outer::{
        LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation, load_with_options,
    },
};

#[path = "ml_positions/cells.rs"]
mod cells;

// ---------------------------------------------------------------- expectations

/// The build a shard runs in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Build {
    Portable,
    Z3,
}

impl Build {
    pub const CURRENT: Build = if cfg!(feature = "z3-inference") {
        Build::Z3
    } else {
        Build::Portable
    };

    fn name(self) -> &'static str {
        match self {
            Build::Portable => "portable",
            Build::Z3 => "z3",
        }
    }
}

/// How a cell deviates from its expectation in one build, recorded for each pending cell.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Class {
    /// The cell does not deviate in this build.
    Conforms,
    /// A run gives a leaf, or a claim a verdict, that the meaning contradicts (a state the
    /// rule does not reach, `proven` for a false claim, `disproved` for a true one), or the
    /// sentence states an axiom with no model and runs.
    Wrong,
    /// Loading, compiling, `Backend::new` or a run refuses the cell (at run time also a
    /// `SimplificationError` halt).
    Refused,
    /// A kompile invariant or another assertion panics.
    Panic,
    /// The runs give no leaf the meaning contradicts but miss a state, or stay undecided
    /// (`Indeterminate`, constrained leaves the meaning does not list, `failed` or
    /// `indeterminate` for a true claim).
    Undecided,
    /// A refused cell runs and agrees with its meaning, or with no stated meaning.
    Accepted,
}

/// How a cell's definition is compiled and exercised.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Route {
    /// `kcompile` of module `P` (syntax module `P-SYNTAX`), then runs.
    Kompile,
    /// `kcompile --for-proving` of module `P-SPEC` over `P`, then claims.
    Kprove,
    /// `kcompile` of `P`, then the search pattern compiled by `compile_search_pattern` and
    /// searched for final states from each run's program.
    Search,
}

/// One expected leaf: the term of the `<k>` cell and the halt reason (`Match` for a search
/// match).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Leaf {
    pub term: String,
    pub halt: String,
}

pub fn leaf(term: impl Into<String>, halt: &str) -> Leaf {
    Leaf {
        term: term.into(),
        halt: halt.to_owned(),
    }
}

/// One program and its expected leaves.
#[derive(Clone, Debug)]
pub struct Run {
    pub program: String,
    pub leaves: Vec<Leaf>,
    /// Leaves the meaning neither requires nor excludes.
    pub optional: Vec<Leaf>,
    /// Leaves of the other truth value of an undecided construct, allowed under an allowance.
    pub undecided: Vec<Leaf>,
    /// Under an allowance, leaves that stand for the expected ones left unevaluated (the
    /// application `f(n)` an undecided equation would evaluate).
    pub unevaluated: Vec<Leaf>,
}

impl Run {
    pub fn new(program: impl Into<String>, leaves: Vec<Leaf>) -> Self {
        Self {
            program: program.into(),
            leaves,
            optional: Vec::new(),
            undecided: Vec::new(),
            unevaluated: Vec::new(),
        }
    }

    pub fn optional(mut self, leaves: Vec<Leaf>) -> Self {
        self.optional = leaves;
        self
    }

    pub fn undecided(mut self, leaves: Vec<Leaf>) -> Self {
        self.undecided = leaves;
        self
    }

    pub fn unevaluated(mut self, leaves: Vec<Leaf>) -> Self {
        self.unevaluated = leaves;
        self
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Verdict {
    Proven,
    NotProven,
    /// Proven, in every build whatever the cell's allowance: the proof needs no solver.
    ProvenAlways,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Code {
    /// A compile diagnostic of this spelling, located at a probed sentence's line.
    Diag(&'static str),
    /// A load (parse) error located at a probed sentence's line.
    Parse,
}

#[derive(Clone, Debug)]
pub enum Expect {
    Accept {
        runs: Vec<Run>,
        proofs: Vec<(&'static str, Verdict)>,
    },
    Refuse {
        portable: Code,
        z3: Code,
    },
}

pub const ML_CONSTRUCT_POSITION: Code = Code::Diag("MlConstructPosition");

impl Expect {
    pub fn refuse(code: Code) -> Self {
        Expect::Refuse {
            portable: code,
            z3: code,
        }
    }

    pub fn runs(runs: Vec<Run>) -> Self {
        Expect::Accept {
            runs,
            proofs: Vec::new(),
        }
    }

    pub fn proofs(proofs: Vec<(&'static str, Verdict)>) -> Self {
        Expect::Accept {
            runs: Vec::new(),
            proofs,
        }
    }
}

/// What the meaning of a refused cell states about its runs.
#[derive(Clone, Debug)]
pub enum Meaning {
    /// No outcome: the sentence is ill-formed, or its value is no finite set of states.
    Unstated,
    /// The sentence states an axiom with no model (an equation `f(2) = 10 +Int X` for every X):
    /// any run's answer is wrong.
    NoModel,
    /// The runs or verdicts the meaning states (an `Accept` expectation).
    States(Expect),
}

/// The builds in which a cell's undecided construct may stay undecided.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Allow {
    None,
    /// `#Floor`: no build decides it.
    Undecided,
    /// A quantified predicate, or a claim's arithmetic implication: the portable build has no
    /// solver for it.
    PortableUndecided,
}

impl Allow {
    fn applies(self, build: Build) -> bool {
        match self {
            Allow::None => false,
            Allow::Undecided => true,
            Allow::PortableUndecided => build == Build::Portable,
        }
    }
}

pub struct CellSpec {
    /// `<group>/<position>__<construct>`, as in the audit's probe matrix.
    pub name: String,
    pub route: Route,
    /// The sentences of module `P` after the shared header (claims: also module `P-SPEC`).
    pub text: String,
    /// For [`Route::Search`]: the search pattern.
    pub pattern: Option<String>,
    /// The programs run from (or searched from); an `Accept` cell's runs are these, in order.
    pub programs: Vec<String>,
    pub meaning: String,
    pub expect: Expect,
    pub allow: Allow,
    /// For a refused cell, what its meaning states, against which a pending cell that runs is
    /// classified ([`Class`]).
    pub meaning_runs: Meaning,
}

pub const HEADER: &str = "module P-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
               | pair(Int, Step) [symbol(pair)]
               | \"pick\" [symbol(pick)]
               | \"pick3\" [symbol(pick3)]
  syntax Step ::= \"sa\" [symbol(sa)] | \"sb\" [symbol(sb)]
endmodule

module P
  imports P-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= done(Int) [symbol(done)] | stuck(Int) [symbol(stuck)]
";

impl CellSpec {
    fn source(&self) -> String {
        format!("{HEADER}{}endmodule\n", self.text)
    }

    fn path(&self) -> String {
        format!("ml_positions/{}.k", self.name)
    }

    /// The lines of the sentences labelled `p` or `q`, where a refusal must be located.
    fn probed_lines(&self) -> Vec<u32> {
        self.source()
            .lines()
            .enumerate()
            .filter(|(_, line)| line.contains("[p]:") || line.contains("[q]:"))
            .map(|(index, _)| index as u32 + 1)
            .collect()
    }
}

// ---------------------------------------------------------------- PENDING

/// The number of cells of the matrix.
const CELL_COUNT: usize = 511;

/// The cells that deviate at the ML lane's base, each with the ticket after which it conforms
/// and the builds in which it deviates (see the module documentation).
#[rustfmt::skip]
pub const PENDING: &[(&str, &str, Class, Class)] = &[
    // MLP/4 (141): shapes no k-rust route loads or the backend misreads: refused at compile with MlConstructPosition.
    // Since MLP/8 the backend refuses at load, naming the axiom, an #Equals with a connective operand and a connective over terms conjoined at a matched or shared position (Refused).
    // An #Equals on a condition's spine whose operands are not both terms or both predicates is refused at compile since MLP/3, without that code (Refused).
    // Since MLP/1 (no guard alias in a condition): the `__or-inner` ensures are refused at Backend::new instead of panicking.
    ("cond/claim-ensures__as", "MLP/4", Class::Conforms, Class::Refused),
    ("cond/claim-ensures__fun", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-ensures__let", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-ensures__or-inner", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-ensures__predarg", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__as", "MLP/4", Class::Conforms, Class::Accepted),
    ("cond/claim-requires__eqop-and", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__eqop-ceil-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__eqop-eq-false", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__eqop-eq-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__eqop-not-eq-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__eqop-or-int", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__eqop-or-or", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__eqop-or-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__eqop-true-or", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__fun", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__let", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__or-inner", "MLP/4", Class::Refused, Class::Refused),
    ("cond/claim-requires__predarg", "MLP/4", Class::Refused, Class::Refused),
    ("cond/context-requires__as", "MLP/4", Class::Conforms, Class::Refused),
    ("cond/context-requires__or-inner", "MLP/4", Class::Refused, Class::Refused),
    ("cond/context-requires__predarg", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-ensures__as", "MLP/4", Class::Conforms, Class::Refused),
    ("cond/fun-ensures__or-inner", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-ensures__predarg", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-requires__as", "MLP/4", Class::Conforms, Class::Undecided),
    ("cond/fun-requires__eqop-and", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-requires__eqop-ceil-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-requires__eqop-eq-false", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-requires__eqop-eq-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-requires__eqop-not-eq-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-requires__eqop-or-int", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-requires__eqop-or-or", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-requires__eqop-or-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-requires__eqop-true-or", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-requires__or-inner", "MLP/4", Class::Refused, Class::Refused),
    ("cond/fun-requires__predarg", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-ensures__as", "MLP/4", Class::Conforms, Class::Refused),
    ("cond/rule-ensures__or-inner", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-ensures__predarg", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-requires__as", "MLP/4", Class::Conforms, Class::Accepted),
    ("cond/rule-requires__eqop-and", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-requires__eqop-ceil-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-requires__eqop-eq-false", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-requires__eqop-eq-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-requires__eqop-not-eq-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-requires__eqop-or-int", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-requires__eqop-or-or", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-requires__eqop-or-true", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-requires__eqop-true-or", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-requires__or-inner", "MLP/4", Class::Refused, Class::Refused),
    ("cond/rule-requires__predarg", "MLP/4", Class::Refused, Class::Refused),
    ("cond/simp-ensures__as", "MLP/4", Class::Conforms, Class::Refused),
    ("cond/simp-ensures__or-inner", "MLP/4", Class::Refused, Class::Refused),
    ("cond/simp-ensures__predarg", "MLP/4", Class::Refused, Class::Refused),
    ("cond/simp-requires__as", "MLP/4", Class::Conforms, Class::Undecided),
    ("cond/simp-requires__or-inner", "MLP/4", Class::Refused, Class::Refused),
    ("cond/simp-requires__predarg", "MLP/4", Class::Refused, Class::Refused),
    ("left/claim-lhs__bottom", "MLP/4", Class::Refused, Class::Refused),
    ("left/claim-lhs__exists", "MLP/4", Class::Refused, Class::Refused),
    ("left/claim-lhs__forall", "MLP/4", Class::Refused, Class::Refused),
    ("left/claim-lhs__implies", "MLP/4", Class::Refused, Class::Refused),
    ("left/claim-lhs__not", "MLP/4", Class::Refused, Class::Refused),
    ("left/claim-lhs__top", "MLP/4", Class::Refused, Class::Refused),
    ("left/fun-lhs__and-pred", "MLP/4", Class::Refused, Class::Refused),
    ("left/fun-lhs__bottom", "MLP/4", Class::Refused, Class::Refused),
    ("left/fun-lhs__exists", "MLP/4", Class::Refused, Class::Refused),
    ("left/fun-lhs__floor", "MLP/4", Class::Refused, Class::Refused),
    ("left/fun-lhs__forall", "MLP/4", Class::Refused, Class::Refused),
    ("left/fun-lhs__implies", "MLP/4", Class::Refused, Class::Refused),
    ("left/fun-lhs__not", "MLP/4", Class::Refused, Class::Refused),
    ("left/fun-lhs__top", "MLP/4", Class::Refused, Class::Refused),
    ("left/rule-lhs__and-implies", "MLP/4", Class::Refused, Class::Refused),
    ("left/rule-lhs__bottom", "MLP/4", Class::Refused, Class::Refused),
    ("left/rule-lhs__exists", "MLP/4", Class::Refused, Class::Refused),
    ("left/rule-lhs__forall", "MLP/4", Class::Refused, Class::Refused),
    ("left/rule-lhs__implies", "MLP/4", Class::Refused, Class::Refused),
    ("left/rule-lhs__not", "MLP/4", Class::Refused, Class::Refused),
    ("left/rule-lhs__top", "MLP/4", Class::Refused, Class::Refused),
    ("left/rule-shared__exists", "MLP/4", Class::Refused, Class::Refused),
    ("left/rule-shared__forall", "MLP/4", Class::Refused, Class::Refused),
    ("left/rule-shared__implies", "MLP/4", Class::Refused, Class::Refused),
    ("left/rule-shared__not", "MLP/4", Class::Refused, Class::Refused),
    ("left/simp-lhs__and-pred", "MLP/4", Class::Refused, Class::Refused),
    ("left/simp-lhs__bottom", "MLP/4", Class::Refused, Class::Refused),
    ("left/simp-lhs__ceil", "MLP/4", Class::Refused, Class::Refused),
    ("left/simp-lhs__exists", "MLP/4", Class::Refused, Class::Refused),
    ("left/simp-lhs__floor", "MLP/4", Class::Refused, Class::Refused),
    ("left/simp-lhs__forall", "MLP/4", Class::Refused, Class::Refused),
    ("left/simp-lhs__implies", "MLP/4", Class::Refused, Class::Refused),
    ("left/simp-lhs__not", "MLP/4", Class::Refused, Class::Refused),
    ("left/simp-lhs__or", "MLP/4", Class::Refused, Class::Refused),
    ("left/simp-lhs__or-var", "MLP/4", Class::Refused, Class::Refused),
    ("left/simp-lhs__top", "MLP/4", Class::Refused, Class::Refused),
    ("right/alias-rhs__exists", "MLP/4", Class::Refused, Class::Refused),
    ("right/alias-rhs__exists-pred", "MLP/4", Class::Refused, Class::Refused),
    ("right/alias-rhs__forall", "MLP/4", Class::Refused, Class::Refused),
    ("right/alias-rhs__implies", "MLP/4", Class::Refused, Class::Refused),
    ("right/alias-rhs__not", "MLP/4", Class::Refused, Class::Refused),
    ("right/alias-rhs__top", "MLP/4", Class::Refused, Class::Refused),
    ("right/anywhere-rhs__exists", "MLP/4", Class::Refused, Class::Refused),
    ("right/anywhere-rhs__exists-pred", "MLP/4", Class::Refused, Class::Refused),
    ("right/anywhere-rhs__forall", "MLP/4", Class::Refused, Class::Refused),
    ("right/anywhere-rhs__implies", "MLP/4", Class::Refused, Class::Refused),
    ("right/anywhere-rhs__not", "MLP/4", Class::Refused, Class::Refused),
    ("right/anywhere-rhs__or", "MLP/4", Class::Refused, Class::Refused),
    ("right/anywhere-rhs__top", "MLP/4", Class::Refused, Class::Refused),
    ("right/claim-rhs__bottom", "MLP/4", Class::Refused, Class::Refused),
    ("right/claim-rhs__exists", "MLP/4", Class::Refused, Class::Refused),
    ("right/claim-rhs__exists-pred", "MLP/4", Class::Refused, Class::Refused),
    ("right/claim-rhs__forall", "MLP/4", Class::Refused, Class::Refused),
    ("right/claim-rhs__fun", "MLP/4", Class::Refused, Class::Refused),
    ("right/claim-rhs__implies", "MLP/4", Class::Refused, Class::Refused),
    ("right/claim-rhs__let", "MLP/4", Class::Refused, Class::Refused),
    ("right/claim-rhs__not", "MLP/4", Class::Refused, Class::Refused),
    ("right/claim-rhs__top", "MLP/4", Class::Refused, Class::Refused),
    ("right/fun-rhs__exists", "MLP/4", Class::Refused, Class::Refused),
    ("right/fun-rhs__exists-pred", "MLP/4", Class::Refused, Class::Refused),
    ("right/fun-rhs__forall", "MLP/4", Class::Refused, Class::Refused),
    ("right/fun-rhs__implies", "MLP/4", Class::Refused, Class::Refused),
    ("right/fun-rhs__not", "MLP/4", Class::Refused, Class::Refused),
    ("right/fun-rhs__or", "MLP/4", Class::Refused, Class::Refused),
    ("right/fun-rhs__top", "MLP/4", Class::Refused, Class::Refused),
    ("right/macro-rhs__exists", "MLP/4", Class::Refused, Class::Refused),
    ("right/macro-rhs__exists-pred", "MLP/4", Class::Refused, Class::Refused),
    ("right/macro-rhs__forall", "MLP/4", Class::Refused, Class::Refused),
    ("right/macro-rhs__implies", "MLP/4", Class::Refused, Class::Refused),
    ("right/macro-rhs__not", "MLP/4", Class::Refused, Class::Refused),
    ("right/macro-rhs__top", "MLP/4", Class::Refused, Class::Refused),
    ("right/rule-rhs__exists", "MLP/4", Class::Refused, Class::Refused),
    ("right/rule-rhs__exists-pred", "MLP/4", Class::Refused, Class::Refused),
    ("right/rule-rhs__forall", "MLP/4", Class::Refused, Class::Refused),
    ("right/rule-rhs__implies", "MLP/4", Class::Refused, Class::Refused),
    ("right/rule-rhs__not", "MLP/4", Class::Refused, Class::Refused),
    ("right/rule-rhs__top", "MLP/4", Class::Refused, Class::Refused),
    ("right/simp-rhs__exists", "MLP/4", Class::Refused, Class::Refused),
    ("right/simp-rhs__exists-pred", "MLP/4", Class::Refused, Class::Refused),
    ("right/simp-rhs__forall", "MLP/4", Class::Refused, Class::Refused),
    ("right/simp-rhs__implies", "MLP/4", Class::Refused, Class::Refused),
    ("right/simp-rhs__not", "MLP/4", Class::Refused, Class::Refused),
    ("right/simp-rhs__or", "MLP/4", Class::Refused, Class::Refused),
    // MLP/4b (2): the shapes of left/fun-lhs__or-var and right/rule-rhs__and-or built by a macro, refused only once the expanded sentences are checked.
    ("extra/fun-lhs__macro-or-var", "MLP/4b", Class::Wrong, Class::Wrong),
    ("extra/rule-rhs__macro-and-or", "MLP/4b", Class::Wrong, Class::Wrong),
    // MLP/9 (24): search-pattern conditions: refused unlocated at run time, or read as Bool terms.
    ("search/final__and-bt", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__and-pr", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__as", "MLP/9", Class::Conforms, Class::Refused),
    ("search/final__bottom", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__ceil", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__eq", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__eq-bool", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__ex-bt", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__ex-pr", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__fa-bt", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__fa-pr", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__floor", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__fun", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__imp-bt", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__imp-pr", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__let", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__not-bt", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__not-pr", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__or-bt", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__or-inner", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__or-mix", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__or-pr", "MLP/9", Class::Refused, Class::Refused),
    ("search/final__predarg", "MLP/9", Class::Accepted, Class::Accepted),
    ("search/final__top", "MLP/9", Class::Refused, Class::Refused),
    // unassigned (2): follow-ups FU-20 and FU-21 (decisions.toml, "MLP/0 questions"): a predicate lemma whose subject is a disjunction, and a predicate lemma on a ground atom of a rewrite rule's condition, are not applied.
    // One cause (FU-48, the proposed ticket MLP/10): predicate lemmas are matched after definedness hoisting has rewritten each atom to ⌈f(X)⌉ ∧ atom, so a disjunction's left side no longer matches, and the ceil hoisted beside a lemma's result is never absorbed. The answers are incomplete, not wrong.
    ("psimp/pred-simp__eq-eq-ground", "unassigned", Class::Undecided, Class::Undecided),
    ("psimp/pred-simp__or-lhs", "unassigned", Class::Conforms, Class::Undecided),
];

// ---------------------------------------------------------------- observation

#[derive(Debug)]
struct ObservedLeaf {
    term: String,
    halt: String,
    constrained: bool,
}

#[derive(Debug)]
enum Outcome {
    Panic(String),
    LoadRefused(String),
    CompileRefused {
        codes: Vec<(String, Option<u32>)>,
        message: String,
    },
    SearchRefused {
        code: Option<(String, Option<u32>)>,
        parse: bool,
        message: String,
    },
    BackendRefused(String),
    Ran {
        runs: Vec<(String, Result<Vec<ObservedLeaf>, String>)>,
        proofs: Vec<(String, Result<String, String>)>,
    },
}

fn one_line(text: &str) -> String {
    text.split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .chars()
        .take(300)
        .collect()
}

impl Outcome {
    fn summary(&self) -> String {
        match self {
            Outcome::Panic(message) => format!("PANIC {}", one_line(message)),
            Outcome::LoadRefused(message) => format!("load refused: {}", one_line(message)),
            Outcome::CompileRefused { codes, message } => {
                format!("compile refused {codes:?}: {}", one_line(message))
            }
            Outcome::SearchRefused {
                code,
                parse,
                message,
            } => format!(
                "pattern refused {code:?}{}: {}",
                if *parse { " (parse)" } else { "" },
                one_line(message)
            ),
            Outcome::BackendRefused(message) => {
                format!("Backend::new refused: {}", one_line(message))
            }
            Outcome::Ran { runs, proofs } => {
                let mut text = String::from("ran;");
                for (program, result) in runs {
                    let _ = write!(text, " {program} -> ");
                    match result {
                        Err(error) => {
                            let _ = write!(text, "error {};", one_line(error));
                        }
                        Ok(leaves) => {
                            let leaves = leaves
                                .iter()
                                .map(|leaf| {
                                    format!(
                                        "{} {}{}",
                                        leaf.halt,
                                        leaf.term,
                                        if leaf.constrained {
                                            " (constrained)"
                                        } else {
                                            ""
                                        }
                                    )
                                })
                                .collect::<Vec<_>>();
                            let _ = write!(text, "[{}];", leaves.join(" | "));
                        }
                    }
                }
                for (claim, result) in proofs {
                    match result {
                        Ok(status) => {
                            let _ = write!(text, " {claim}: {status};");
                        }
                        Err(error) => {
                            let _ = write!(text, " {claim}: error {};", one_line(error));
                        }
                    }
                }
                text
            }
        }
    }
}

fn panic_message(panic: Box<dyn std::any::Any + Send>) -> String {
    panic
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| panic.downcast_ref::<&str>().map(|text| (*text).to_owned()))
        .unwrap_or_default()
}

thread_local! {
    static IN_CELL: ThreadFlag<bool> = const { ThreadFlag::new(false) };
}

/// Panics inside a cell are outcomes, not test failures: keep them off standard error, and
/// report every other panic as the default hook does.
fn quiet_cell_panics() {
    static HOOK: Once = Once::new();
    HOOK.call_once(|| {
        let default = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !IN_CELL.with(ThreadFlag::get) {
                default(info);
            }
        }));
    });
}

fn guarded<T>(work: impl FnOnce() -> T) -> Result<T, String> {
    IN_CELL.with(|flag| flag.set(true));
    let result = catch_unwind(AssertUnwindSafe(work)).map_err(panic_message);
    IN_CELL.with(|flag| flag.set(false));
    result
}

fn resolver(_: &str, required: &str) -> Result<ResolvedSource, String> {
    embedded(required).ok_or_else(|| format!("unexpected require {required}"))
}

fn load(cell: &CellSpec) -> Result<LoadedDefinition, String> {
    let mut resolver = resolver;
    let source = ResolvedSource::new(cell.path(), cell.source());
    if cell.route == Route::Kprove {
        load_with_options(
            source,
            "P-SPEC",
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                configuration_module: Some("P".to_owned()),
                ..CompilationBackend::Rust.load_options()
            },
        )
        .map_err(|error| error.to_string())
    } else {
        let options = LoadOptions {
            implicit_sources: vec![
                embedded("kast.md").unwrap(),
                embedded("prelude.md").unwrap(),
            ],
            ..CompilationBackend::Rust.load_options()
        };
        load_for_compilation(source, "P", Some("P-SYNTAX"), &mut resolver, &options)
            .map(|(loaded, _)| loaded)
            .map_err(|error| error.to_string())
    }
}

fn compile_options(route: Route) -> CompileOptions {
    if route == Route::Kprove {
        CompileOptions {
            backend: CompilationBackend::Rust,
            default_claims_to_all_path: true,
            check_mode: CheckMode::Proof {
                definition_module: "P".to_owned(),
            },
            ..CompileOptions::default()
        }
    } else {
        CompileOptions::default()
    }
}

fn int(value: &str) -> String {
    format!("\\dv{{SortInt{{}}}}(\"{value}\")")
}

/// The initial configuration of a program `go(N)`, `pair(N, sa)`, `pick` or `pick3`.
fn initial_state(program: &str) -> Pattern {
    let pgm = if let Some(rest) = program.strip_prefix("go(") {
        format!("Lblgo{{}}({})", int(rest.trim_end_matches(')')))
    } else if let Some(rest) = program.strip_prefix("pair(") {
        let value = rest.split(',').next().unwrap().trim();
        format!("Lblpair{{}}({}, Lblsa{{}}())", int(value))
    } else if program == "pick" || program == "pick3" {
        format!("Lbl{program}{{}}()")
    } else {
        panic!("unknown program {program}")
    };
    k_rust::kore::parser::parse_pattern(&format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortPgm{{}}, SortKItem{{}}}}({pgm}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}({}))",
        int("0")
    ))
    .unwrap()
}

/// A compact rendering of a term: `Lbl` prefixes, injections and the `kseq` unit dropped,
/// every variable written `_`.
fn render(pattern: &Pattern) -> String {
    let list = |arguments: &[Pattern]| arguments.iter().map(render).collect::<Vec<_>>().join(", ");
    match pattern {
        Pattern::Application { symbol, arguments } => {
            let name = symbol.name.as_str();
            if name == "inj" && arguments.len() == 1 {
                return render(&arguments[0]);
            }
            if name == "kseq" && arguments.len() == 2 {
                let rest = render(&arguments[1]);
                let head = render(&arguments[0]);
                return if rest == "." {
                    head
                } else {
                    format!("{head} ~> {rest}")
                };
            }
            if name == "dotk" {
                return ".".to_owned();
            }
            let name = name.strip_prefix("Lbl").unwrap_or(name);
            if arguments.is_empty() {
                name.to_owned()
            } else {
                format!("{name}({})", list(arguments))
            }
        }
        Pattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            let name = symbol.name.as_str();
            format!(
                "{}({})",
                name.strip_prefix("Lbl").unwrap_or(name),
                list(arguments)
            )
        }
        Pattern::DomainValue { value, .. } => value.as_utf8().unwrap_or("?").to_owned(),
        Pattern::String(value) => format!("{:?}", value.as_utf8().unwrap_or("?")),
        Pattern::Variable(_) => "_".to_owned(),
        Pattern::Top { .. } => "\\top".to_owned(),
        Pattern::Bottom { .. } => "\\bottom".to_owned(),
        Pattern::And { arguments, .. } => format!("\\and({})", list(arguments)),
        Pattern::Or { arguments, .. } => format!("\\or({})", list(arguments)),
        Pattern::Not { argument, .. } => format!("\\not({})", render(argument)),
        Pattern::Next { argument, .. } => format!("\\next({})", render(argument)),
        Pattern::Ceil { argument, .. } => format!("\\ceil({})", render(argument)),
        Pattern::Floor { argument, .. } => format!("\\floor({})", render(argument)),
        Pattern::Implies { left, right, .. } => {
            format!("\\implies({}, {})", render(left), render(right))
        }
        Pattern::Iff { left, right, .. } => format!("\\iff({}, {})", render(left), render(right)),
        Pattern::Rewrites { left, right, .. } => {
            format!("\\rewrites({}, {})", render(left), render(right))
        }
        Pattern::Equals { left, right, .. } => {
            format!("\\equals({}, {})", render(left), render(right))
        }
        Pattern::In { left, right, .. } => format!("\\in({}, {})", render(left), render(right)),
        Pattern::Exists { body, .. } => format!("\\exists(_, {})", render(body)),
        Pattern::Forall { body, .. } => format!("\\forall(_, {})", render(body)),
        Pattern::Mu { body, .. } => format!("\\mu(_, {})", render(body)),
        Pattern::Nu { body, .. } => format!("\\nu(_, {})", render(body)),
    }
}

const K_CELL: &str = "Lbl'-LT-'k'-GT-'";
const TOP_CELL: &str = "Lbl'-LT-'generatedTop'-GT-'";

fn k_cells<'a>(pattern: &'a Pattern, found: &mut Vec<&'a Pattern>) {
    match pattern {
        Pattern::Application { symbol, arguments } if symbol.name == K_CELL => {
            found.extend(arguments.first());
        }
        Pattern::Application { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. } => {
            for argument in arguments {
                k_cells(argument, found);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => k_cells(argument, found),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            k_cells(left, found);
            k_cells(right, found);
        }
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => k_cells(body, found),
        _ => {}
    }
}

fn observe_state(state: &serde_json::Value, halt: String) -> ObservedLeaf {
    let pattern = codec::from_value(state).expect("a result state is KORE JSON");
    let mut found = Vec::new();
    k_cells(&pattern, &mut found);
    let term = if found.is_empty() {
        format!("<no k cell: {}>", render(&pattern))
    } else {
        found
            .into_iter()
            .map(render)
            .collect::<Vec<_>>()
            .join(" | ")
    };
    let constrained = !matches!(
        &pattern,
        Pattern::Application { symbol, .. } if symbol.name == TOP_CELL
    );
    ObservedLeaf {
        term,
        halt,
        constrained,
    }
}

fn prove(backend: &mut Backend, claim: &str) -> Result<String, String> {
    let request = |claim: String| ProveRequest {
        claim: Some(claim),
        max_depth: Some(20),
        ..ProveRequest::default()
    };
    match backend.prove(request(format!("P-SPEC.{claim}"))) {
        Ok(result) => Ok(result.status.to_string()),
        Err(error) => {
            let message = error.to_string();
            // A claim with a disjunctive left side is one claim per disjunct; it holds when
            // every disjunct does.
            let Some(indices) = message.split("select each by its index: ").nth(1) else {
                return Err(message);
            };
            let mut statuses = Vec::new();
            for index in indices.split(", ") {
                let index = index.trim().trim_end_matches('.');
                let result = backend
                    .prove(request(index.to_owned()))
                    .map_err(|error| error.to_string())?;
                statuses.push(result.status.to_string());
            }
            Ok(statuses
                .iter()
                .find(|status| status.as_str() != "proven")
                .cloned()
                .unwrap_or_else(|| "proven".to_owned()))
        }
    }
}

/// The cell's outcome, the first condition its compiled KORE writes in the root encoding (see
/// [`root_encoding`]) and the first axiom with an unbound generated variable (see
/// [`unbound_generated_variable`]), when it compiles.
fn observe(cell: &CellSpec) -> (Outcome, Option<String>, Option<String>) {
    let mut encoded = None;
    let mut unbound = None;
    let result = guarded(|| observe_unguarded(cell, &mut encoded, &mut unbound));
    (result.unwrap_or_else(Outcome::Panic), encoded, unbound)
}

/// The first `\equals{SortBool{}, R}(P, ..)` of `kore` whose left operand P is a matching-logic
/// pattern: a condition whose root is a connective written as one Bool term, which as a pattern
/// states something else than the condition (a predicate at sort Bool is all of Bool or empty,
/// never `{true}`). The compiler writes each condition as the predicate it states, so no
/// Rust-target definition holds one.
fn root_encoding(kore: &str) -> Option<String> {
    let kore = kore.split_whitespace().collect::<Vec<_>>().join(" ");
    let prefix = "\\equals{SortBool{}, ";
    let mut from = 0;
    while let Some(at) = kore[from..].find(prefix) {
        let start = from + at;
        let rest = &kore[start + prefix.len()..];
        let operand = rest.find("}(").map(|close| rest[close + 2..].trim_start());
        if let Some(operand) = operand
            && operand.starts_with('\\')
            && !operand.starts_with("\\dv{")
        {
            return Some(kore[start..].chars().take(240).collect());
        }
        from = start + prefix.len();
    }
    None
}

/// The first axiom of `kore` whose result side holds a generated variable (`_Gen<N>`, the name
/// of a guard alias or of an anonymous variable) free in the axiom that its matched side does not
/// hold. Such a variable is universally quantified over the whole axiom, so the axiom states its
/// result for every value of it; a variable of a result that no match binds (a guard alias of a
/// disjunction in an `ensures`) makes the result, read for every value, empty. The matched side
/// is the first operand of `\rewrites`, and of `\implies` the premise together with the left
/// operand of the conclusion's `\equals` (the function application an equation defines); the
/// result side is the rest of the axiom.
fn unbound_generated_variable(kore: &str) -> Option<String> {
    let definition = parse_definition(kore).expect("compiled KORE parses");
    for module in &definition.modules {
        for sentence in &module.sentences {
            let KoreSentence::Axiom { pattern, .. } = sentence else {
                continue;
            };
            let (matched, result): (Vec<&Pattern>, &Pattern) = match pattern.as_ref() {
                Pattern::Rewrites { left, right, .. } => (vec![left], right),
                Pattern::Implies { left, right, .. } => match right.as_ref() {
                    Pattern::Equals {
                        left: defined,
                        right: value,
                        ..
                    } => (vec![left, defined], value),
                    _ => (vec![left], right),
                },
                _ => continue,
            };
            let bound: BTreeSet<String> = matched
                .iter()
                .flat_map(|side| side.free_variables())
                .map(|variable| variable.name)
                .collect();
            if let Some(variable) = result.free_variables().into_iter().find(|variable| {
                variable.name.starts_with("Var'Unds'Gen") && !bound.contains(&variable.name)
            }) {
                let text = kore_text(pattern);
                return Some(format!(
                    "{} in {}",
                    variable.name,
                    text.chars().take(240).collect::<String>()
                ));
            }
        }
    }
    None
}

fn kore_text(pattern: &Pattern) -> String {
    k_rust::kore::printer::Printer::compact().print_pattern(pattern)
}

fn observe_unguarded(
    cell: &CellSpec,
    encoded: &mut Option<String>,
    unbound: &mut Option<String>,
) -> Outcome {
    let loaded = match load(cell) {
        Ok(loaded) => loaded,
        Err(message) => return Outcome::LoadRefused(message),
    };
    let artifacts = match compile_loaded_definition(&loaded, compile_options(cell.route)) {
        Ok(artifacts) => artifacts,
        Err(error) => {
            let codes = error
                .diagnostics
                .iter()
                .filter(|diagnostic| diagnostic.severity == Severity::Error)
                .map(|diagnostic| {
                    (
                        diagnostic.code.as_str().to_owned(),
                        diagnostic.location.map(|location| location.start_line),
                    )
                })
                .collect();
            return Outcome::CompileRefused {
                codes,
                message: error.to_string(),
            };
        }
    };
    *encoded = root_encoding(&artifacts.definition_kore);
    *unbound = unbound_generated_variable(&artifacts.definition_kore);
    let main = if cell.route == Route::Kprove {
        "P-SPEC"
    } else {
        "P"
    };
    let mut backend =
        match Backend::new(&artifacts.definition_kore, main, BackendOptions::default()) {
            Ok(backend) => backend,
            Err(error) => return Outcome::BackendRefused(error.to_string()),
        };
    let mut runs = Vec::new();
    let mut proofs = Vec::new();
    match (&cell.route, &cell.expect) {
        (
            Route::Kprove,
            Expect::Accept {
                proofs: expected, ..
            },
        ) => {
            for (claim, _) in expected {
                proofs.push(((*claim).to_owned(), prove(&mut backend, claim)));
            }
        }
        (Route::Kprove, Expect::Refuse { .. }) => {
            for claim in ["p", "q"] {
                if cell.text.contains(&format!("claim [{claim}]")) {
                    proofs.push((claim.to_owned(), prove(&mut backend, claim)));
                }
            }
        }
        (Route::Search, _) => {
            let contents = cell
                .pattern
                .as_deref()
                .expect("a search cell has a pattern");
            let parsing = definition_with_named_projections(loaded.definition());
            let parsing = ResolvedDefinition::resolve(&parsing).unwrap();
            let execution = ResolvedDefinition::resolve(&artifacts.execution_definition).unwrap();
            let mut attributes = Attributes::default();
            attributes.insert(SOURCE_ATTRIBUTE, serde_json::json!("<pattern>"));
            attributes.insert(
                LOCATION_ATTRIBUTE,
                serde_json::json!([1, 1, 1, contents.len() + 1]),
            );
            let compiled =
                match compile_search_pattern(&parsing, &execution, "P", contents, attributes) {
                    Ok(compiled) => compiled,
                    Err(error) => {
                        let code = match &error {
                            CompileSearchPatternError::Denotation(diagnostic) => Some((
                                diagnostic.code.as_str().to_owned(),
                                diagnostic.location.map(|location| location.start_line),
                            )),
                            _ => None,
                        };
                        return Outcome::SearchRefused {
                            code,
                            parse: matches!(error, CompileSearchPatternError::Rule(_)),
                            message: error.to_string(),
                        };
                    }
                };
            for program in programs(cell) {
                let request = SearchPatternRequest {
                    max_depth: Some(5),
                    ..SearchPatternRequest::new(initial_state(&program), compiled.pattern.clone())
                };
                let result = backend
                    .search_pattern(request)
                    .map(|response| {
                        response
                            .matches
                            .iter()
                            .map(|found| observe_state(&found.state.state, "Match".to_owned()))
                            .chain(response.incomplete.iter().map(|incomplete| ObservedLeaf {
                                term: format!("<incomplete {incomplete:?}>"),
                                halt: "Incomplete".to_owned(),
                                constrained: false,
                            }))
                            .collect()
                    })
                    .map_err(|error| error.to_string());
                runs.push((program, result));
            }
        }
        (Route::Kompile, _) => {
            for program in programs(cell) {
                let request = ExecuteRequest {
                    max_depth: Some(5),
                    ..ExecuteRequest::new(initial_state(&program))
                };
                let result = backend
                    .execute(request)
                    .map(|result| {
                        result
                            .leaves
                            .iter()
                            .map(|leaf| observe_state(&leaf.state, format!("{:?}", leaf.reason)))
                            .collect()
                    })
                    .map_err(|error| error.to_string());
                runs.push((program, result));
            }
        }
    }
    Outcome::Ran { runs, proofs }
}

fn programs(cell: &CellSpec) -> Vec<String> {
    cell.programs.clone()
}

// ---------------------------------------------------------------- conformance

fn conforms(cell: &CellSpec, build: Build, outcome: &Outcome) -> Result<(), String> {
    match &cell.expect {
        Expect::Refuse { portable, z3 } => {
            let code = if build == Build::Portable {
                portable
            } else {
                z3
            };
            refused_as(cell, *code, outcome)
        }
        Expect::Accept { runs, proofs } => {
            let Outcome::Ran {
                runs: observed_runs,
                proofs: observed_proofs,
            } = outcome
            else {
                return Err("expected acceptance".to_owned());
            };
            let allowed = cell.allow.applies(build);
            assert_eq!(
                runs.len(),
                observed_runs.len(),
                "{}: one observed run per expected run",
                cell.name
            );
            assert_eq!(
                proofs.len(),
                observed_proofs.len(),
                "{}: one observed verdict per expected verdict",
                cell.name
            );
            for (run, (program, observed)) in runs.iter().zip(observed_runs) {
                debug_assert_eq!(&run.program, program);
                let observed = observed
                    .as_ref()
                    .map_err(|error| format!("{program}: error {}", one_line(error)))?;
                run_conforms(run, observed, allowed)
                    .map_err(|error| format!("{program}: {error}"))?;
            }
            for ((claim, verdict), (_, observed)) in proofs.iter().zip(observed_proofs) {
                let status = observed
                    .as_ref()
                    .map_err(|error| format!("claim {claim}: error {}", one_line(error)))?;
                let fits = match (verdict, status.as_str()) {
                    (Verdict::Proven | Verdict::ProvenAlways, "proven") => true,
                    (Verdict::NotProven, "disproved" | "failed") => true,
                    (Verdict::Proven, "indeterminate" | "failed") => allowed,
                    (Verdict::NotProven, "indeterminate") => allowed,
                    _ => false,
                };
                if !fits {
                    return Err(format!("claim {claim}: expected {verdict:?}, got {status}"));
                }
            }
            Ok(())
        }
    }
}

fn run_conforms(run: &Run, observed: &[ObservedLeaf], allowed: bool) -> Result<(), String> {
    let key = |leaf: &ObservedLeaf| Leaf {
        term: leaf.term.clone(),
        halt: leaf.halt.clone(),
    };
    let seen: BTreeSet<Leaf> = observed.iter().map(key).collect();
    let required: BTreeSet<Leaf> = run.leaves.iter().cloned().collect();
    let mut permitted = required.clone();
    permitted.extend(run.optional.iter().cloned());
    let expected = || {
        format!(
            "expected {:?}{}",
            run.leaves
                .iter()
                .map(|leaf| format!("{} {}", leaf.halt, leaf.term))
                .collect::<Vec<_>>(),
            if run.optional.is_empty() {
                String::new()
            } else {
                format!(
                    " with optional {:?}",
                    run.optional
                        .iter()
                        .map(|leaf| format!("{} {}", leaf.halt, leaf.term))
                        .collect::<Vec<_>>()
                )
            }
        )
    };
    // A run whose leaves are all optional needs one of its non-Trivial ones: the meaning gives
    // a successor state.
    let some_leaf = !required.is_empty()
        || run.optional.is_empty()
        || seen.iter().any(|leaf| leaf.halt != "Trivial");
    if required.is_subset(&seen) && seen.is_subset(&permitted) && some_leaf {
        return Ok(());
    }
    if allowed {
        // The build did not decide the construct at all: the run halts Indeterminate at the
        // program, or at an expected state from which the undecided construct is reached (the
        // unheated state of a context).
        let mut undecided_at: BTreeSet<String> = run
            .leaves
            .iter()
            .chain(&run.undecided)
            .map(|leaf| leaf.term.clone())
            .collect();
        undecided_at.insert(render_program(&run.program));
        if observed.len() == 1
            && observed[0].halt == "Indeterminate"
            && undecided_at.contains(&observed[0].term)
        {
            return Ok(());
        }
        let mut undecided = permitted.clone();
        undecided.extend(run.undecided.iter().cloned());
        undecided.extend(run.unevaluated.iter().cloned());
        // A leaf outside the expected ones carries the undecided construct: in its constraint,
        // or as the application of `f` the undecided equation would evaluate.
        let fits = observed.iter().all(|leaf| {
            let key = key(leaf);
            undecided.contains(&key)
                && (permitted.contains(&key) || leaf.constrained || leaf.term.contains("f("))
        });
        // Every expected state is still reached: each required leaf other than a Trivial one
        // (which denotes no state) is observed, constrained or not, or left unevaluated.
        let covered = run
            .leaves
            .iter()
            .filter(|leaf| leaf.halt != "Trivial")
            .all(|leaf| {
                seen.contains(leaf) || run.unevaluated.iter().any(|stand| seen.contains(stand))
            });
        if fits && covered && !observed.is_empty() {
            return Ok(());
        }
    }
    Err(expected())
}

/// The `<k>` term [`render`] gives for a program's initial state.
fn render_program(program: &str) -> String {
    let mut found = Vec::new();
    let state = initial_state(program);
    k_cells(&state, &mut found);
    render(found[0])
}

fn refused_as(cell: &CellSpec, code: Code, outcome: &Outcome) -> Result<(), String> {
    let lines = cell.probed_lines();
    let path = cell.path();
    let located = |line: Option<u32>| line.is_some_and(|line| lines.contains(&line));
    let fits = match (code, outcome) {
        (Code::Parse, Outcome::LoadRefused(message)) => lines
            .iter()
            .any(|line| message.contains(&format!("{path}:{line}:"))),
        (Code::Diag(expected), Outcome::CompileRefused { codes, .. }) => codes
            .iter()
            .any(|(code, line)| code == expected && located(*line)),
        (Code::Diag(expected), Outcome::SearchRefused { code, .. }) => code
            .as_ref()
            .is_some_and(|(code, line)| code == expected && line.is_some()),
        (Code::Parse, Outcome::SearchRefused { parse, .. }) => *parse,
        _ => false,
    };
    if fits {
        Ok(())
    } else {
        Err(format!("expected refusal {code:?} at lines {lines:?}"))
    }
}

/// How a deviating outcome deviates ([`Class`]): against the expectation of an `Accept` cell,
/// and against the stated meaning of a refused one.
fn classify(cell: &CellSpec, outcome: &Outcome) -> Class {
    let (observed_runs, observed_proofs) = match outcome {
        Outcome::Panic(_) => return Class::Panic,
        Outcome::LoadRefused(_)
        | Outcome::CompileRefused { .. }
        | Outcome::SearchRefused { .. }
        | Outcome::BackendRefused(_) => return Class::Refused,
        Outcome::Ran { runs, proofs } => (runs, proofs),
    };
    let meaning = match (&cell.expect, &cell.meaning_runs) {
        (Expect::Accept { .. }, _) => &cell.expect,
        (Expect::Refuse { .. }, Meaning::States(meaning)) => meaning,
        (Expect::Refuse { .. }, Meaning::NoModel) => return no_model_class(observed_runs),
        (Expect::Refuse { .. }, Meaning::Unstated) => return Class::Accepted,
    };
    let Expect::Accept { runs, proofs } = meaning else {
        unreachable!("a stated meaning is an Accept expectation");
    };
    let mut class = Class::Accepted;
    let mut worse = |found: Class| {
        let rank = |class: Class| match class {
            Class::Wrong => 3,
            Class::Refused => 2,
            Class::Undecided => 1,
            _ => 0,
        };
        if rank(found) > rank(class) {
            class = found;
        }
    };
    for run in runs {
        let Some((_, observed)) = observed_runs
            .iter()
            .find(|(program, _)| *program == run.program)
        else {
            continue;
        };
        let Ok(observed) = observed else {
            worse(Class::Refused);
            continue;
        };
        let mut permitted: BTreeSet<Leaf> = run.leaves.iter().cloned().collect();
        permitted.extend(run.optional.iter().cloned());
        let mut seen = BTreeSet::new();
        for leaf in observed {
            let key = Leaf {
                term: leaf.term.clone(),
                halt: leaf.halt.clone(),
            };
            seen.insert(key.clone());
            match leaf.halt.as_str() {
                "SimplificationError" | "UnsupportedHook" => worse(Class::Refused),
                "Stuck" | "Trivial" | "Vacuous" | "Match" if !permitted.contains(&key) => {
                    // A constrained leaf may have no instance: its constraint is not read.
                    worse(if leaf.constrained || leaf.term.contains("f(") {
                        Class::Undecided
                    } else {
                        Class::Wrong
                    });
                }
                "Stuck" | "Trivial" | "Vacuous" | "Match" => {}
                _ => worse(Class::Undecided),
            }
        }
        if run
            .leaves
            .iter()
            .any(|leaf| leaf.halt != "Trivial" && !seen.contains(leaf))
        {
            worse(Class::Undecided);
        }
    }
    for (claim, verdict) in proofs {
        let Some((_, observed)) = observed_proofs.iter().find(|(name, _)| name == claim) else {
            continue;
        };
        match (verdict, observed.as_deref()) {
            (_, Err(_)) => worse(Class::Refused),
            (Verdict::Proven | Verdict::ProvenAlways, Ok("proven"))
            | (Verdict::NotProven, Ok("disproved" | "failed")) => {}
            (Verdict::Proven | Verdict::ProvenAlways, Ok("disproved"))
            | (Verdict::NotProven, Ok("proven")) => worse(Class::Wrong),
            _ => worse(Class::Undecided),
        }
    }
    class
}

/// A sentence with no model has no right answer: a run that reaches a state answers wrong; one
/// that halts refusing the step, or leaves the application unevaluated, does not answer.
fn no_model_class(observed_runs: &[(String, Result<Vec<ObservedLeaf>, String>)]) -> Class {
    let mut class = Class::Undecided;
    for (_, observed) in observed_runs {
        let Ok(leaves) = observed else {
            class = Class::Refused;
            continue;
        };
        for leaf in leaves {
            match leaf.halt.as_str() {
                "SimplificationError" | "UnsupportedHook" => class = Class::Refused,
                "Stuck" | "Vacuous" | "Match" if !leaf.term.contains("f(") => {
                    return Class::Wrong;
                }
                _ => {}
            }
        }
    }
    class
}

// ---------------------------------------------------------------- shards

/// The ticket and the base class of a cell pending in `build`.
fn pending(name: &str, build: Build) -> Option<(&'static str, Class)> {
    PENDING
        .iter()
        .find(|(cell, ..)| *cell == name)
        .map(|(_, ticket, portable, z3)| {
            (
                *ticket,
                if build == Build::Portable {
                    *portable
                } else {
                    *z3
                },
            )
        })
        .filter(|(_, class)| *class != Class::Conforms)
}

fn run_shard(shard: &str, cells: Vec<CellSpec>) {
    quiet_cell_panics();
    let build = Build::CURRENT;
    let started = Instant::now();
    let names: BTreeSet<&str> = cells.iter().map(|cell| cell.name.as_str()).collect();
    assert_eq!(
        names.len(),
        cells.len(),
        "cell names are unique in shard {shard}"
    );
    let mut failures = Vec::new();
    let mut lines = Vec::new();
    let mut counts = BTreeMap::new();
    for cell in &cells {
        let (outcome, encoded, unbound) = observe(cell);
        let verdict = conforms(cell, build, &outcome);
        if let (Expect::Accept { .. }, Some(snippet)) = (&cell.expect, &encoded) {
            failures.push(format!(
                "{} ({}) compiles a condition in the root encoding: {snippet}",
                cell.name,
                build.name()
            ));
        }
        if let Some(snippet) = &unbound {
            failures.push(format!(
                "{} ({}) compiles an axiom whose result holds a generated variable its matched side does not bind: {snippet}",
                cell.name,
                build.name()
            ));
        }
        let status = if verdict.is_ok() {
            "conforms"
        } else {
            "deviates"
        };
        *counts.entry(status).or_insert(0usize) += 1;
        let class = if verdict.is_ok() {
            Class::Conforms
        } else {
            classify(cell, &outcome)
        };
        lines.push(format!(
            "{}\t{}\t{status}\t{class:?}\t{}\t{}",
            cell.name,
            build.name(),
            outcome.summary(),
            verdict.as_ref().err().map(String::as_str).unwrap_or("")
        ));
        match (pending(&cell.name, build), verdict) {
            (None, Ok(())) => {}
            (Some((_, recorded)), Err(_)) if recorded == class => {}
            (Some((ticket, recorded)), Err(_)) => failures.push(format!(
                "{} ({}) is pending {ticket} as {recorded:?} but is now {class:?}: record the \
                 change in PENDING\n    outcome: {}",
                cell.name,
                build.name(),
                outcome.summary()
            )),
            (None, Err(deviation)) => failures.push(format!(
                "{} ({}) deviates from its meaning: {deviation}\n    meaning: {}\n    outcome: {}",
                cell.name,
                build.name(),
                cell.meaning,
                outcome.summary()
            )),
            (Some((ticket, _)), Ok(())) => failures.push(format!(
                "{} ({}) is pending {ticket} but conforms: remove it from PENDING\n    outcome: {}",
                cell.name,
                build.name(),
                outcome.summary()
            )),
        }
    }
    for (name, ..) in PENDING {
        if cells::shard_of(name) == shard && !names.contains(name) {
            failures.push(format!("PENDING names {name}, which shard {shard} lacks"));
        }
    }
    if let Ok(directory) = std::env::var("ML_POSITIONS_OUT") {
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            format!(
                "{directory}/{}-{}.tsv",
                shard.replace('/', "-"),
                build.name()
            ),
            lines.join("\n") + "\n",
        )
        .unwrap();
    }
    println!(
        "ml-positions shard {shard} ({}): {} cells, {counts:?}, {:.1} s",
        build.name(),
        cells.len(),
        started.elapsed().as_secs_f64()
    );
    assert!(
        failures.is_empty(),
        "shard {shard} ({}): {} cell(s) contradict the matrix:\n{}",
        build.name(),
        failures.len(),
        failures.join("\n")
    );
}

/// The shards run on a thread with a stack large enough for any cell's compilation.
fn shard(shard: &'static str) {
    let cells = cells::shard(shard);
    assert!(!cells.is_empty(), "shard {shard} has cells");
    std::thread::Builder::new()
        .name(format!("ml-positions-{shard}"))
        .stack_size(256 << 20)
        .spawn(move || run_shard(shard, cells))
        .unwrap()
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}

macro_rules! shards {
    ($($name:ident => $shard:literal,)*) => {
        $(
            #[test]
            #[ignore = "ML position matrix: scripts/run-gates.sh ml-positions"]
            fn $name() {
                shard($shard);
            }
        )*

        /// Every cell belongs to one shard, and every shard has a test.
        #[test]
        fn every_cell_belongs_to_a_shard_with_a_test() {
            let shards = [$($shard,)*];
            let mut total = 0;
            for shard in shards {
                total += cells::shard(shard).len();
            }
            assert_eq!(total, cells::all().len());
            // The cell set is pinned: a cell dropped from or added to a table is a visible diff.
            let names: BTreeSet<String> =
                cells::all().into_iter().map(|cell| cell.name).collect();
            assert_eq!(names.len(), cells::all().len(), "cell names are unique");
            assert_eq!(names.len(), CELL_COUNT, "the matrix has CELL_COUNT cells");
            for (name, ..) in PENDING {
                assert!(
                    shards.contains(&cells::shard_of(name)),
                    "PENDING names {name}, which belongs to no shard"
                );
                assert!(
                    cells::all().iter().any(|cell| cell.name == *name),
                    "PENDING names {name}, which is no cell"
                );
            }
        }
    };
}

shards! {
    cond_rule_requires => "cond/rule-requires",
    cond_rule_ensures => "cond/rule-ensures",
    cond_fun_requires => "cond/fun-requires",
    cond_fun_ensures => "cond/fun-ensures",
    cond_simp_requires => "cond/simp-requires",
    cond_simp_ensures => "cond/simp-ensures",
    cond_context_requires => "cond/context-requires",
    cond_claim_requires => "cond/claim-requires",
    cond_claim_ensures => "cond/claim-ensures",
    cond_owise_requires => "cond/owise-requires",
    left_rule_lhs => "left/rule-lhs",
    left_rule_shared => "left/rule-shared",
    left_fun_lhs => "left/fun-lhs",
    left_simp_lhs => "left/simp-lhs",
    left_claim_lhs => "left/claim-lhs",
    right_rule_rhs => "right/rule-rhs",
    right_fun_rhs => "right/fun-rhs",
    right_simp_rhs => "right/simp-rhs",
    right_macro_rhs => "right/macro-rhs",
    right_alias_rhs => "right/alias-rhs",
    right_anywhere_rhs => "right/anywhere-rhs",
    right_claim_rhs => "right/claim-rhs",
    psimp => "psimp/pred-simp",
    extra => "extra",
    search => "search/final",
}
