//! The cells of the matching-logic position matrix: the audit's tables (condition constructs,
//! matched and built constructs, predicate simplifications, extra probes) and the positions they
//! are placed at, each with the expectation its meaning states.
//!
//! Cell names are those of the audit's probe matrix (`<group>/<position>__<construct>`); the
//! cells added after its review keep the same scheme.

use crate::{
    Allow, CellSpec, Code, Expect, Leaf, ML_CONSTRUCT_POSITION, Meaning, Route, Run, Verdict, leaf,
};

const INVALID_SEARCH_PATTERN: Code = Code::Diag("InvalidSearchPattern");
const INVALID_FUNCTION_PATTERN: Code = Code::Diag("InvalidFunctionPattern");
const ILLEGAL_FUNCTION_ON_LHS: Code = Code::Diag("IllegalFunctionOnLhs");
const INVALID_REWRITE: Code = Code::Diag("InvalidRewrite");
const UNBOUND_VARIABLE: Code = Code::Diag("UnboundVariable");

/// The shard a cell belongs to: its group and position (`extra` cells form one shard).
pub fn shard_of(name: &str) -> &str {
    if name.starts_with("extra/") {
        "extra"
    } else {
        name.split("__").next().unwrap_or(name)
    }
}

pub fn shard(name: &str) -> Vec<CellSpec> {
    all()
        .into_iter()
        .filter(|cell| shard_of(&cell.name) == name)
        .collect()
}

pub fn all() -> Vec<CellSpec> {
    let mut cells = Vec::new();
    condition_cells(&mut cells);
    left_cells(&mut cells);
    right_cells(&mut cells);
    predicate_simplification_cells(&mut cells);
    extra_cells(&mut cells);
    cells
}

fn stuck(term: impl Into<String>) -> Leaf {
    leaf(term, "Stuck")
}

fn trivial(term: impl Into<String>) -> Leaf {
    leaf(term, "Trivial")
}

fn matched(term: impl Into<String>) -> Leaf {
    leaf(term, "Match")
}

fn go(n: i64) -> String {
    format!("go({n})")
}

fn done(value: impl std::fmt::Display) -> String {
    format!("done({value})")
}

// ---------------------------------------------------------------- conditions

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind {
    /// A condition every position accepts with its meaning.
    Plain,
    /// A quantified predicate: the portable build has no solver for it.
    Quantified,
    /// `#Floor`: no build decides it.
    Floor,
    /// `#as` in a condition: a condition is matched against nothing, so the alias names nothing
    /// (refused in both builds; the portable parser refuses it at load).
    Alias,
    /// `#let` and `#fun`: Bool-valued terms, accepted except in a claim's condition, which no
    /// route loads.
    LetFun,
    /// A matching-logic construct below a Bool symbol or inside an operand of a predicate atom:
    /// the construct is a set operation there, which no route reads.
    TermLevel,
}

struct Condition {
    id: &'static str,
    text: &'static str,
    truth: fn(i64) -> bool,
    kind: Kind,
    meaning: &'static str,
}

const fn condition(
    id: &'static str,
    text: &'static str,
    truth: fn(i64) -> bool,
    kind: Kind,
    meaning: &'static str,
) -> Condition {
    Condition {
        id,
        text,
        truth,
        kind,
        meaning,
    }
}

fn never(_: i64) -> bool {
    false
}

/// The audit's condition constructs over X: the truth set of each, read as a predicate with a
/// Bool-term operand t of a matching-logic connective read as `t = true`.
const CONDITIONS: &[Condition] = &[
    condition(
        "bool",
        "X <Int 3",
        |x| x < 3,
        Kind::Plain,
        "plain Bool term: X < 3",
    ),
    condition(
        "or-bt",
        "(X ==Int 1) #Or (X ==Int 2)",
        |x| x == 1 || x == 2,
        Kind::Plain,
        "X = 1 or X = 2",
    ),
    condition(
        "or-pr",
        "{X #Equals 1} #Or {X #Equals 2}",
        |x| x == 1 || x == 2,
        Kind::Plain,
        "X = 1 or X = 2",
    ),
    condition(
        "or-mix",
        "{X #Equals 1} #Or (X ==Int 2)",
        |x| x == 1 || x == 2,
        Kind::Plain,
        "X = 1 or X = 2",
    ),
    condition(
        "or-inner",
        "(X #Or 5) <Int 3",
        never,
        Kind::TermLevel,
        "a term-level #Or below a Bool symbol: {X <Int 3, 5 <Int 3} = {true} never holds; refused (BoolLeaf)",
    ),
    condition(
        "and-bt",
        "(X >=Int 1) #And (X <=Int 2)",
        |x| (1..=2).contains(&x),
        Kind::Plain,
        "1 <= X <= 2",
    ),
    condition(
        "and-pr",
        "{X #Equals 1} #And #Ceil(1 /Int X)",
        |x| x == 1,
        Kind::Plain,
        "X = 1",
    ),
    condition("not-bt", "#Not(X >=Int 3)", |x| x < 3, Kind::Plain, "X < 3"),
    condition(
        "not-pr",
        "#Not({X #Equals 3})",
        |x| x != 3,
        Kind::Plain,
        "X != 3",
    ),
    condition(
        "ceil",
        "#Ceil(1 /Int (X -Int 3))",
        |x| x != 3,
        Kind::Plain,
        "X != 3",
    ),
    condition(
        "floor",
        "#Floor(1 /Int (X -Int 3))",
        never,
        Kind::Floor,
        "never: a single value is not all of Int",
    ),
    condition("eq", "{X #Equals 1}", |x| x == 1, Kind::Plain, "X = 1"),
    condition(
        "eq-bool",
        "{true #Equals X ==Int 1}",
        |x| x == 1,
        Kind::Plain,
        "X = 1",
    ),
    condition(
        "ex-bt",
        "#Exists Y:Int . ((X ==Int Y) andBool (Y <Int 3))",
        |x| x < 3,
        Kind::Quantified,
        "exists Y. X = Y and Y < 3, i.e. X < 3",
    ),
    condition(
        "ex-pr",
        "#Exists Y:Int . ({X #Equals Y} #And {true #Equals Y <Int 3})",
        |x| x < 3,
        Kind::Quantified,
        "X < 3",
    ),
    condition(
        "fa-bt",
        "#Forall Y:Int . ((Y ==Int X) impliesBool (Y <Int 3))",
        |x| x < 3,
        Kind::Quantified,
        "forall Y. Y = X implies Y < 3, i.e. X < 3",
    ),
    condition(
        "fa-pr",
        "#Forall Y:Int . (#Not({Y #Equals X}) #Or {true #Equals Y <Int 3})",
        |x| x < 3,
        Kind::Quantified,
        "X < 3",
    ),
    condition(
        "imp-bt",
        "(X >=Int 3) #Implies (X ==Int 4)",
        |x| x < 3 || x == 4,
        Kind::Plain,
        "X < 3 or X = 4",
    ),
    condition(
        "imp-pr",
        "{X #Equals 3} #Implies {X #Equals 4}",
        |x| x != 3,
        Kind::Plain,
        "X != 3",
    ),
    condition("top", "#Top", |_| true, Kind::Plain, "always"),
    condition("bottom", "#Bottom", never, Kind::Plain, "never"),
    condition(
        "as",
        "(X ==Int 1) #as B",
        |x| x == 1,
        Kind::Alias,
        "#as in a condition: a condition is matched against nothing, so the alias names nothing; refused",
    ),
    condition(
        "let",
        "#let Z = X #in (Z ==Int 1)",
        |x| x == 1,
        Kind::LetFun,
        "X = 1",
    ),
    condition(
        "fun",
        "#fun(Z => Z ==Int 1)(X)",
        |x| x == 1,
        Kind::LetFun,
        "X = 1",
    ),
    condition(
        "predarg",
        "notBool {X #Equals 3}",
        never,
        Kind::TermLevel,
        "a predicate where a Bool value is required (BoolLeaf): ill-formed; refused",
    ),
];

/// Matching-logic connectives and predicates inside an operand of a predicate atom (review
/// finding 1): each operand is a term position, where a connective is a set operation no route
/// reads and a predicate at sort Bool is all of Bool or nothing.
const OPERAND_CONDITIONS: &[Condition] = &[
    condition(
        "eqop-and",
        "{((X ==Int 1) #And (X ==Int 2)) #Equals false}",
        |x| x != 1 && x != 2,
        Kind::TermLevel,
        "{X ==Int 1} ∩ {X ==Int 2} = {false}: X not in {1, 2}; a connective in an operand of #Equals is refused (PredicateOperand)",
    ),
    condition(
        "eqop-true-or",
        "{true #Equals ((X ==Int 1) #Or (X ==Int 2))}",
        never,
        Kind::TermLevel,
        "{true} = {X ==Int 1, X ==Int 2}: never; refused (PredicateOperand)",
    ),
    condition(
        "eqop-or-true",
        "{((X ==Int 1) #Or (X ==Int 2)) #Equals true}",
        never,
        Kind::TermLevel,
        "{X ==Int 1, X ==Int 2} = {true}: never; refused (PredicateOperand)",
    ),
    condition(
        "eqop-or-int",
        "{X #Equals (1 #Or 2)}",
        never,
        Kind::TermLevel,
        "{X} = {1, 2}: never; refused (PredicateOperand)",
    ),
    // A conjunction of two terms, each at most one value, is defined exactly where they are
    // equal: the backend reads `#Ceil(t1 #And t2)` as `⌈t1⌉ ∧ t1 = t2`.
    condition(
        "ceilop-and",
        "#Ceil(X #And 1)",
        |x| x == 1,
        Kind::Plain,
        "X ∩ {1} is defined where X = 1",
    ),
    condition(
        "eqop-or-or",
        "{ ((X ==Int 1) #Or (X ==Int 1)) #Equals ((X ==Int 1) #Or false) }",
        |x| x != 1,
        Kind::TermLevel,
        "{X ==Int 1} = {X ==Int 1, false}: X != 1; two connectives over terms compare sets of values; refused (PredicateOperand)",
    ),
    // A predicate as an operand of #Equals beside a Bool term: at sort Bool a predicate is all of
    // Bool or nothing, never one Bool value.
    condition(
        "eqop-eq-true",
        "{ {X #Equals 1} #Equals true }",
        never,
        Kind::TermLevel,
        "{X #Equals 1} at Bool is all of Bool or nothing, never {true}: never; refused (PredicateOperand)",
    ),
    condition(
        "eqop-ceil-true",
        "{ #Ceil(1 /Int (X -Int 1)) #Equals true }",
        never,
        Kind::TermLevel,
        "#Ceil(..) at Bool is all of Bool or nothing, never {true}: never; refused (PredicateOperand)",
    ),
    condition(
        "eqop-eq-false",
        "{ {X #Equals 1} #Equals false }",
        never,
        Kind::TermLevel,
        "{X #Equals 1} at Bool is all of Bool or nothing, never {false}: never; refused (PredicateOperand)",
    ),
    condition(
        "eqop-not-eq-true",
        "#Not({ {X #Equals 1} #Equals true })",
        |_| true,
        Kind::TermLevel,
        "the negation of an equality that never holds: always; refused (PredicateOperand)",
    ),
    // An #Equals of two predicates is their iff, at any depth.
    condition(
        "eqop-pred-pred",
        "{ #Not({X #Equals 2}) #Equals {X #Equals 1} }",
        |x| x == 1 || x == 2,
        Kind::Plain,
        "X != 2 iff X = 1: X in {1, 2}",
    ),
    // The rule of the spine applies below it: the inner #Equals mixes a predicate and a Bool term.
    condition(
        "eqop-nested-mixed",
        "{ {{X #Equals 1} #Equals true} #Equals #Top }",
        never,
        Kind::TermLevel,
        "{X #Equals 1} at Bool is never {true}, so the iff with #Top never holds; refused (PredicateOperand below an atom)",
    ),
    // ⌊t⌋ holds only where t is every value of its sort; a conjunction of terms is at most one
    // value, and no route decides the complement this needs.
    condition(
        "floorop-and",
        "#Floor(X #And 1)",
        never,
        Kind::TermLevel,
        "X ∩ {1} is at most one value, never all of Int: never; #Floor over a term conjunction is refused",
    ),
];

/// Partial Bool leaves (review finding 5): a Bool term below the spine means `t = true`, so
/// `#Not(t)` and `t #Implies b` hold where t is undefined, and `notBool t` does not.
/// `t impliesBool (X ==Int 3)` is undefined at X = 0: its second operand is false there, so the
/// undefined first operand is relevant. `orBool` has no cell here: its value over an undefined
/// operand is the strict one docs/compatibility.md ("Conditionals and Boolean connectives are
/// strict") states and `krun_keeps_the_definedness_of_an_untaken_conditional_branch` pins.
const PARTIAL_CONDITIONS: &[Condition] = &[
    condition(
        "partial-not",
        "#Not((10 /Int X) ==Int 5)",
        |x| x == 0 || 10 / x != 5,
        Kind::Plain,
        "holds where 10 /Int X is undefined (X = 0) or not 5",
    ),
    condition(
        "partial-notbool",
        "notBool ((10 /Int X) ==Int 5)",
        |x| x != 0 && 10 / x != 5,
        Kind::Plain,
        "undefined at X = 0, so it does not hold there",
    ),
    condition(
        "partial-implies",
        "((10 /Int X) ==Int 5) #Implies (X ==Int 3)",
        |x| x == 0 || 10 / x != 5 || x == 3,
        Kind::Plain,
        "holds where 10 /Int X is undefined, not 5, or X = 3",
    ),
    condition(
        "partial-impliesbool",
        "((10 /Int X) ==Int 5) impliesBool (X ==Int 3)",
        |x| x != 0 && (10 / x != 5 || x == 3),
        Kind::Plain,
        "undefined at X = 0, where the second operand is false and the undefined first one decides",
    ),
    condition(
        "partial-or",
        "((10 /Int X) ==Int 5) #Or (X ==Int 0)",
        |x| x == 0 || 10 / x == 5,
        Kind::Plain,
        "holds at X = 0 by the second disjunct although the first is undefined there",
    ),
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CondPos {
    RuleRequires,
    RuleEnsures,
    FunRequires,
    FunEnsures,
    SimpRequires,
    SimpEnsures,
    ContextRequires,
    ClaimRequires,
    ClaimEnsures,
    OwiseRequires,
    Search,
}

impl CondPos {
    fn name(self) -> &'static str {
        match self {
            CondPos::RuleRequires => "cond/rule-requires",
            CondPos::RuleEnsures => "cond/rule-ensures",
            CondPos::FunRequires => "cond/fun-requires",
            CondPos::FunEnsures => "cond/fun-ensures",
            CondPos::SimpRequires => "cond/simp-requires",
            CondPos::SimpEnsures => "cond/simp-ensures",
            CondPos::ContextRequires => "cond/context-requires",
            CondPos::ClaimRequires => "cond/claim-requires",
            CondPos::ClaimEnsures => "cond/claim-ensures",
            CondPos::OwiseRequires => "cond/owise-requires",
            CondPos::Search => "search/final",
        }
    }

    fn route(self) -> Route {
        match self {
            CondPos::ClaimRequires | CondPos::ClaimEnsures => Route::Kprove,
            CondPos::Search => Route::Search,
            _ => Route::Kompile,
        }
    }

    fn is_claim(self) -> bool {
        self.route() == Route::Kprove
    }

    /// The sentences that place condition `c` (a K text over X).
    fn text(self, c: &str) -> String {
        const F: &str = "  syntax Int ::= f(Int) [function, symbol(f)]\n";
        const G: &str = "  rule [g]: <k> go(X) => done(f(X)) ... </k>\n";
        match self {
            CondPos::RuleRequires => {
                format!("  rule [p]: <k> go(X) => done(X) ... </k> requires {c}\n")
            }
            CondPos::RuleEnsures => {
                format!("  rule [p]: <k> go(X) => done(X) ... </k> ensures {c}\n")
            }
            CondPos::FunRequires => format!("{F}  rule [p]: f(X) => X requires {c}\n{G}"),
            CondPos::FunEnsures => format!("{F}  rule [p]: f(X) => X ensures {c}\n{G}"),
            CondPos::SimpRequires => {
                format!("{F}  rule [p]: f(X) => X requires {c} [simplification]\n{G}")
            }
            CondPos::SimpEnsures => {
                format!("{F}  rule [p]: f(X) => X ensures {c} [simplification]\n{G}")
            }
            // go(N) steps to c2(N, e(N)); the context heats e(N) where the condition over N
            // holds, and e(N) evaluates to N, which cools back: c2(N, N).
            CondPos::ContextRequires => format!(
                "  syntax Exp ::= Int | e(Int) [symbol(e)]\n  syntax KResult ::= Int\n  syntax KItem ::= c2(Int, Exp) [symbol(c2)]\n  rule [e]: <k> e(N) => N ... </k>\n  rule [g]: <k> go(N) => c2(N, e(N)) ... </k>\n  context [p]: c2(N:Int, HOLE:Exp) requires {}\n",
                c.replace('X', "N")
            ),
            CondPos::ClaimRequires => format!(
                "  rule [g]: <k> go(X) => done(X) ... </k> requires X <Int 3\nendmodule\n\nmodule P-SPEC\n  imports P\n  claim [p]: <k> go(X) => done(X) ... </k> requires {c}\n  claim [q]: <k> go(X) => stuck(X) ... </k> requires {c}\n"
            ),
            CondPos::ClaimEnsures => {
                let c = c.replace('X', "?W");
                format!(
                    "  rule [g1]: <k> pick => done(1) ... </k>\n  rule [g3]: <k> pick3 => done(3) ... </k>\nendmodule\n\nmodule P-SPEC\n  imports P\n  claim [p]: <k> pick => done(?W) ... </k> ensures {c}\n  claim [q]: <k> pick3 => done(?W) ... </k> ensures {c}\n"
                )
            }
            CondPos::OwiseRequires => format!(
                "{F}  rule [p]: f(X) => 1 requires {c}\n  rule [o]: f(_) => 0 [owise]\n{G}"
            ),
            CondPos::Search => "  rule [s1]: <k> pick => done(1) ... </k>\n  rule [s2]: <k> pick => done(2) ... </k>\n  rule [s3]: <k> pick => done(3) ... </k>\n".to_owned(),
        }
    }

    fn default_programs(self) -> Vec<i64> {
        match self {
            CondPos::ContextRequires => vec![1, 3],
            CondPos::ClaimRequires | CondPos::ClaimEnsures | CondPos::Search => Vec::new(),
            CondPos::OwiseRequires => vec![1, 2, 3],
            _ => vec![1, 3],
        }
    }

    /// The run of program go(n) when the condition's truth at n is `holds`.
    fn run(self, n: i64, holds: bool) -> Run {
        let applied = || vec![stuck(done(n))];
        let unevaluated = || vec![stuck(done(format!("f({n})")))];
        match self {
            CondPos::RuleRequires => {
                if holds {
                    Run::new(go(n), applied()).undecided(vec![stuck(go(n))])
                } else {
                    Run::new(go(n), vec![stuck(go(n))]).undecided(applied())
                }
            }
            CondPos::RuleEnsures | CondPos::FunEnsures | CondPos::SimpEnsures => {
                if holds {
                    Run::new(go(n), applied()).undecided(vec![trivial(go(n))])
                } else {
                    Run::new(go(n), vec![trivial(go(n))]).undecided(applied())
                }
            }
            // An application of f that no equation evaluates is either undefined or an unknown
            // value: the definedness branch is optional.
            CondPos::FunRequires | CondPos::SimpRequires => {
                if holds {
                    Run::new(go(n), applied())
                        .undecided(vec![trivial(go(n))])
                        .unevaluated(unevaluated())
                } else {
                    Run::new(go(n), unevaluated())
                        .optional(vec![trivial(go(n))])
                        .undecided(applied())
                }
            }
            CondPos::ContextRequires => {
                let heated = stuck(format!("c2({n}, {n})"));
                let unheated = stuck(format!("c2({n}, e({n}))"));
                if holds {
                    Run::new(go(n), vec![heated]).undecided(vec![unheated])
                } else {
                    Run::new(go(n), vec![unheated]).undecided(vec![heated])
                }
            }
            // A build that cannot decide the competitor's condition can apply neither the
            // competitor nor the owise equation: f(n) stays unevaluated, as for a function
            // requires. The Trivial go(n) leaf is the definedness branch the backend keeps for
            // that unevaluated f(n); its constraint is infeasible, since the owise equation makes
            // f defined everywhere, and the leaf is admitted only under the cell's allowance and
            // only constrained, so it stands for no wrong value.
            CondPos::OwiseRequires => Run::new(go(n), vec![stuck(done(if holds { 1 } else { 0 }))])
                .undecided(vec![stuck(done(if holds { 0 } else { 1 })), trivial(go(n))])
                .unevaluated(unevaluated()),
            CondPos::ClaimRequires | CondPos::ClaimEnsures | CondPos::Search => {
                unreachable!("{self:?} has no go(n) runs")
            }
        }
    }
}

fn condition_cell(position: CondPos, c: &Condition, programs: &[i64]) -> CellSpec {
    let name = format!("{}__{}", position.name(), c.id);
    let route = position.route();
    let mut allow = match c.kind {
        Kind::Quantified => Allow::PortableUndecided,
        Kind::Floor => Allow::Undecided,
        _ => Allow::None,
    };
    if position == CondPos::ClaimRequires && allow == Allow::None {
        // The claim's proof decides an implication over symbolic integers (the condition
        // implies `X <Int 3`), for which the portable build has no solver.
        allow = Allow::PortableUndecided;
    }
    let refused = match c.kind {
        Kind::TermLevel if position == CondPos::Search => {
            Some(Expect::refuse(INVALID_SEARCH_PATTERN))
        }
        Kind::TermLevel => Some(Expect::refuse(ML_CONSTRUCT_POSITION)),
        Kind::Alias if position == CondPos::Search => Some(Expect::Refuse {
            portable: Code::Parse,
            z3: INVALID_SEARCH_PATTERN,
        }),
        Kind::Alias => Some(Expect::Refuse {
            portable: Code::Parse,
            z3: ML_CONSTRUCT_POSITION,
        }),
        Kind::LetFun if position.is_claim() => Some(Expect::refuse(ML_CONSTRUCT_POSITION)),
        // The search-pattern route lowers no local function, as the claim route does not.
        Kind::LetFun if position == CondPos::Search => Some(Expect::refuse(INVALID_SEARCH_PATTERN)),
        _ => None,
    };
    let (text, pattern, programs_list) = if position == CondPos::Search {
        (
            position.text(c.text),
            Some(format!("<k> done(X) </k> requires {}", c.text)),
            vec!["pick".to_owned()],
        )
    } else {
        (
            position.text(c.text),
            None,
            programs.iter().map(|n| go(*n)).collect::<Vec<_>>(),
        )
    };
    let meaning_expect = match position {
        CondPos::ClaimRequires => {
            let truth_set: Vec<i64> = (-20..=20).filter(|x| (c.truth)(*x)).collect();
            let p = if truth_set.iter().all(|x| *x < 3) {
                Verdict::Proven
            } else {
                Verdict::NotProven
            };
            let q = if truth_set.is_empty() {
                Verdict::Proven
            } else {
                Verdict::NotProven
            };
            Expect::proofs(vec![("p", p), ("q", q)])
        }
        CondPos::ClaimEnsures => {
            let verdict = |holds: bool| {
                if holds {
                    Verdict::Proven
                } else {
                    Verdict::NotProven
                }
            };
            Expect::proofs(vec![
                ("p", verdict((c.truth)(1))),
                ("q", verdict((c.truth)(3))),
            ])
        }
        CondPos::Search => {
            let (holding, failing): (Vec<i64>, Vec<i64>) = (1..=3).partition(|n| (c.truth)(*n));
            Expect::runs(vec![
                Run::new("pick", holding.iter().map(|n| matched(done(n))).collect())
                    .undecided(failing.iter().map(|n| matched(done(n))).collect()),
            ])
        }
        _ => Expect::runs(
            programs
                .iter()
                .map(|n| position.run(*n, (c.truth)(*n)))
                .collect(),
        ),
    };
    // `notBool {X #Equals 3}` is ill-formed: it states no truth set.
    let meaning_runs = match (&refused, c.id) {
        (None, _) | (Some(_), "predarg") => Meaning::Unstated,
        (Some(_), _) => Meaning::States(meaning_expect.clone()),
    };
    CellSpec {
        name,
        route,
        text,
        pattern,
        programs: programs_list,
        meaning: c.meaning.to_owned(),
        expect: refused.unwrap_or(meaning_expect),
        allow,
        meaning_runs,
    }
}

fn condition_cells(cells: &mut Vec<CellSpec>) {
    use CondPos::*;
    for position in [
        RuleRequires,
        RuleEnsures,
        FunRequires,
        FunEnsures,
        SimpRequires,
        SimpEnsures,
        ContextRequires,
        ClaimRequires,
        ClaimEnsures,
        Search,
    ] {
        for c in CONDITIONS {
            cells.push(condition_cell(position, c, &position.default_programs()));
        }
    }
    for position in [RuleRequires, FunRequires, ClaimRequires] {
        for c in OPERAND_CONDITIONS {
            cells.push(condition_cell(position, c, &position.default_programs()));
        }
    }
    for position in [RuleRequires, FunRequires] {
        for c in PARTIAL_CONDITIONS {
            cells.push(condition_cell(position, c, &[0, 2, 3]));
        }
    }
    // De Morgan spelling of a predicate disjunction (review finding 10).
    let demorgan = condition(
        "demorgan-pr",
        "#Not(#Not({X #Equals 1}) #And #Not({X #Equals 2}))",
        |x| x == 1 || x == 2,
        Kind::Plain,
        "X = 1 or X = 2, spelled without #Or",
    );
    for position in [RuleRequires, RuleEnsures] {
        cells.push(condition_cell(position, &demorgan, &[1, 2, 3]));
    }
    // Owise competitors with a matching-logic condition.
    for c in [
        condition(
            "or-bt",
            "(X ==Int 1) #Or (X ==Int 2)",
            |x| x == 1 || x == 2,
            Kind::Plain,
            "f(1) = f(2) = 1, f(3) = 0 by the owise equation",
        ),
        condition(
            "eq",
            "{X #Equals 1}",
            |x| x == 1,
            Kind::Plain,
            "f(1) = 1, f(2) = f(3) = 0",
        ),
        condition(
            "not-pr",
            "#Not({X #Equals 3})",
            |x| x != 3,
            Kind::Plain,
            "f(1) = f(2) = 1, f(3) = 0",
        ),
        // A quantifier in a competitor's condition: the owise equation's antecedent states that
        // no instance of the competitor's free variables satisfies it, the quantified Y staying
        // bound by its own quantifier.
        condition(
            "ex-pr",
            "#Exists Y:Int . ({X #Equals Y} #And {true #Equals Y <Int 3})",
            |x| x < 3,
            Kind::Quantified,
            "f(1) = f(2) = 1, f(3) = 0",
        ),
        condition(
            "fa-pr",
            "#Forall Y:Int . (#Not({Y #Equals X}) #Or {true #Equals Y <Int 3})",
            |x| x < 3,
            Kind::Quantified,
            "f(1) = f(2) = 1, f(3) = 0",
        ),
    ] {
        cells.push(condition_cell(
            OwiseRequires,
            &c,
            &OwiseRequires.default_programs(),
        ));
    }
    macro_condition_cells(cells);
    // An existential ensures of a rewrite rule.
    cells.push(CellSpec {
        name: "cond/rule-ensures__exists-or-bt".to_owned(),
        route: Route::Kompile,
        text: "  rule [p]: <k> pick => done(?W) ... </k> ensures (?W ==Int 1) #Or (?W ==Int 2)\n"
            .to_owned(),
        pattern: None,
        programs: vec!["pick".to_owned()],
        meaning: "pick steps to done(W) for some W in {1, 2}; a Trivial leaf, whose constraint the contract does not check, may state the empty remainder".to_owned(),
        expect: Expect::runs(vec![
            Run::new("pick", Vec::new()).optional(vec![
                stuck(done("_")),
                stuck(done(1)),
                stuck(done(2)),
                trivial("pick"),
            ]),
        ]),
        allow: Allow::None,
        meaning_runs: Meaning::Unstated,
    });
    // The same rule decides claims over the state it reaches: done(W) with W in {1, 2}, and no
    // undefined step.
    cells.push(CellSpec {
        name: "cond/claim-ensures__exists-or-bt".to_owned(),
        route: Route::Kprove,
        text: "  rule [p]: <k> pick => done(?W) ... </k> ensures (?W ==Int 1) #Or (?W ==Int 2)\nendmodule\n\nmodule P-SPEC\n  imports P\n  claim [q]: <k> pick => done(?W) ... </k> ensures (?W ==Int 1) #Or (?W ==Int 2)\n  claim [r]: <k> pick => done(?W) ... </k> ensures ?W ==Int 1\n"
            .to_owned(),
        pattern: None,
        programs: Vec::new(),
        meaning: "pick reaches done(W) for some W in {1, 2}: the rule's own ensures holds on every path, W = 1 does not".to_owned(),
        expect: Expect::proofs(vec![("q", Verdict::Proven), ("r", Verdict::NotProven)]),
        // The portable build has no solver to decide the existential's disjunction.
        allow: Allow::PortableUndecided,
        meaning_runs: Meaning::Unstated,
    });
}

/// Conditions a macro brings in (review finding 3): expansion runs after every pass that
/// rewrites conditions, so these reach the emitter as written.
fn macro_condition_cells(cells: &mut Vec<CellSpec>) {
    const BOOL_MACRO: &str = "  syntax Bool ::= oneOrTwo(Int) [macro, symbol(oneOrTwo)]\n  rule oneOrTwo(X) => (X ==Int 1) #Or (X ==Int 2)\n";
    const PREDICATE_MACRO: &str = "  syntax Bool ::= oneOrTwoP(Int) [macro, symbol(oneOrTwoP)]\n  rule oneOrTwoP(X) => {X #Equals 1} #Or {X #Equals 2}\n";
    let truth = |n: i64| n == 1 || n == 2;
    for (position, construct, declaration, use_) in [
        (
            CondPos::RuleRequires,
            "macro-or-bt",
            BOOL_MACRO,
            "oneOrTwo(X)",
        ),
        (
            CondPos::RuleEnsures,
            "macro-or-bt",
            BOOL_MACRO,
            "oneOrTwo(X)",
        ),
        (
            CondPos::FunRequires,
            "macro-or-bt",
            BOOL_MACRO,
            "oneOrTwo(X)",
        ),
        (
            CondPos::RuleRequires,
            "macro-or-pr",
            PREDICATE_MACRO,
            "oneOrTwoP(X)",
        ),
    ] {
        let programs = [1, 3];
        cells.push(CellSpec {
            name: format!("{}__{construct}", position.name()),
            route: Route::Kompile,
            text: format!("{declaration}{}", position.text(use_)),
            pattern: None,
            programs: programs.iter().map(|n| go(*n)).collect(),
            meaning: "X = 1 or X = 2, the disjunction a macro expands to".to_owned(),
            expect: Expect::runs(
                programs
                    .iter()
                    .map(|n| position.run(*n, truth(*n)))
                    .collect(),
            ),
            allow: Allow::None,
            meaning_runs: Meaning::Unstated,
        });
    }
}

// ---------------------------------------------------------------- matched positions

/// The audit's matched constructs at an Int position: (id, text, value variable, meaning).
const LEFT: &[(&str, &str, &str, &str)] = &[
    ("plain", "X", "X", "every Int, binds X"),
    ("or", "1 #Or 2", "0", "{1, 2}"),
    (
        "or-var",
        "X #Or 2",
        "X",
        "{X, 2}: go(2) matches for every X (X unconstrained)",
    ),
    ("and-term", "X #And 1", "X", "{1}, binds X = 1"),
    ("and-pred", "X #And {X #Equals 1}", "X", "{1}"),
    ("not", "#Not(3)", "0", "Int minus {3}"),
    (
        "ceil",
        "X #And #Ceil(1 /Int (X -Int 3))",
        "X",
        "Int minus {3}",
    ),
    ("floor", "X #And #Floor(X)", "X", "empty"),
    ("exists", "#Exists Y:Int . Y", "0", "every Int"),
    ("forall", "#Forall Y:Int . Y", "0", "empty"),
    ("implies", "3 #Implies 4", "0", "Int minus {3}"),
    ("top", "#Top", "0", "every Int"),
    ("bottom", "#Bottom", "0", "empty"),
    ("as", "X #as Y", "Y", "every Int, binds X and Y"),
    (
        "let",
        "#let Z = 1 #in Z",
        "0",
        "a function-like construct in a pattern: not a pattern",
    ),
    (
        "fun",
        "#fun(Z => Z)(1)",
        "0",
        "a function-like construct in a pattern: not a pattern",
    ),
    (
        "and-implies",
        "X #And (3 #Implies 4)",
        "X",
        "X where X != 3; a connective below #And at a matched position",
    ),
];

/// The values the matched construct `id` binds its value variable to on input n (empty: no
/// match; `_` an unconstrained value).
fn left_values(id: &str, n: i64) -> Vec<String> {
    let value = |v: i64| vec![v.to_string()];
    match id {
        "plain" | "as" => value(n),
        "or" => {
            if n == 1 || n == 2 {
                value(0)
            } else {
                Vec::new()
            }
        }
        "or-var" => {
            if n == 2 {
                vec!["2".to_owned(), "_".to_owned()]
            } else {
                value(n)
            }
        }
        "and-term" | "and-pred" => {
            if n == 1 {
                value(1)
            } else {
                Vec::new()
            }
        }
        "not" | "implies" => {
            if n != 3 {
                value(0)
            } else {
                Vec::new()
            }
        }
        "ceil" | "and-implies" => {
            if n != 3 {
                value(n)
            } else {
                Vec::new()
            }
        }
        "exists" | "top" => value(0),
        "floor" | "forall" | "bottom" | "let" | "fun" => Vec::new(),
        _ => unreachable!("matched construct {id}"),
    }
}

enum Decision {
    Meaning,
    /// The meaning, with `#Floor` undecided.
    Undecided,
    Refuse(Expect),
}

fn left_decision(position: &str, id: &str) -> Decision {
    let refuse = |code| Decision::Refuse(Expect::refuse(code));
    match (id, position) {
        ("let" | "fun", _) => refuse(INVALID_FUNCTION_PATTERN),
        ("plain" | "and-term" | "as", _) => Decision::Meaning,
        ("or", "rule-lhs" | "rule-shared" | "fun-lhs" | "claim-lhs") => Decision::Meaning,
        ("or-var", "rule-lhs" | "rule-shared" | "claim-lhs") => Decision::Meaning,
        ("and-pred", "rule-lhs" | "rule-shared" | "claim-lhs") => Decision::Meaning,
        ("top" | "bottom", "rule-shared") => Decision::Meaning,
        ("floor", "rule-lhs" | "rule-shared") => Decision::Undecided,
        ("floor" | "ceil", "claim-lhs") => Decision::Meaning,
        ("ceil", "rule-lhs" | "rule-shared" | "fun-lhs") => refuse(ILLEGAL_FUNCTION_ON_LHS),
        _ => refuse(ML_CONSTRUCT_POSITION),
    }
}

fn left_cells(cells: &mut Vec<CellSpec>) {
    for position in [
        "rule-lhs",
        "rule-shared",
        "fun-lhs",
        "simp-lhs",
        "claim-lhs",
    ] {
        for (id, text, value, meaning) in LEFT {
            if *id == "and-implies" && position != "rule-lhs" {
                continue;
            }
            cells.push(left_cell(position, id, text, value, meaning));
        }
    }
}

fn left_cell(position: &str, id: &str, text: &str, value: &str, meaning: &str) -> CellSpec {
    let sentences = match position {
        "rule-lhs" => format!("  rule [p]: <k> go({text}) => done({value}) ... </k>\n"),
        "rule-shared" => format!("  rule [p]: <k> pair({text}, (sa => sb)) ... </k>\n"),
        "fun-lhs" => format!(
            "  syntax Int ::= f(Int) [function, symbol(f)]\n  rule [p]: f({text}) => 10 +Int {value}\n  rule [o]: f(_) => 0 [owise]\n  rule [g]: <k> go(X) => done(f(X)) ... </k>\n"
        ),
        "simp-lhs" => format!(
            "  syntax Int ::= f(Int) [function, symbol(f)]\n  rule [p]: f({text}) => 10 +Int {value} [simplification]\n  rule [g]: <k> go(X) => done(f(X)) ... </k>\n"
        ),
        "claim-lhs" => format!(
            "  rule [g]: <k> go(X) => done(X) ... </k> requires X <Int 3\n  rule [h]: <k> pair(X, sa) => pair(X, sb) ... </k>\nendmodule\n\nmodule P-SPEC\n  imports P\n  claim [p]: <k> go({text}) => done(?_) ... </k>\n  claim [q]: <k> pair({text}, sa) => pair(?_, sb) ... </k>\n"
        ),
        _ => unreachable!(),
    };
    let programs: Vec<String> = match position {
        "rule-shared" => (1..=3).map(|n| format!("pair({n}, sa)")).collect(),
        "claim-lhs" => Vec::new(),
        _ => (1..=3).map(go).collect(),
    };
    let decision = left_decision(position, id);
    let run = |n: i64| -> Run {
        let values = left_values(id, n);
        let program = if position == "rule-shared" {
            format!("pair({n}, sa)")
        } else {
            go(n)
        };
        let ten_plus = |v: &String| (10 + v.parse::<i64>().expect("a numeric value")).to_string();
        match position {
            "rule-lhs" => {
                if values.is_empty() {
                    Run::new(program, vec![stuck(go(n))]).undecided(vec![stuck(done(n))])
                } else {
                    Run::new(program, values.iter().map(|v| stuck(done(v))).collect())
                }
            }
            "rule-shared" => {
                if values.is_empty() {
                    Run::new(program, vec![stuck(format!("pair({n}, sa)"))])
                        .undecided(vec![stuck(format!("pair({n}, sb)"))])
                } else {
                    Run::new(program, vec![stuck(format!("pair({n}, sb)"))])
                }
            }
            "fun-lhs" => {
                if values.is_empty() {
                    Run::new(program, vec![stuck(done(0))])
                } else {
                    Run::new(
                        program,
                        values.iter().map(|v| stuck(done(ten_plus(v)))).collect(),
                    )
                }
            }
            "simp-lhs" => {
                if values.is_empty() {
                    Run::new(program, vec![stuck(done(format!("f({n})")))])
                        .optional(vec![trivial(go(n))])
                } else {
                    Run::new(
                        program,
                        values.iter().map(|v| stuck(done(ten_plus(v)))).collect(),
                    )
                }
            }
            _ => unreachable!(),
        }
    };
    // Claim p holds when every input its left side matches is below 3, the condition of the rule
    // that drives go; claim q, over the unconditional rule h, holds for every left side.
    let claim_verdict = if (-20..=20).all(|n| left_values(id, n).is_empty() || n < 3) {
        Verdict::Proven
    } else {
        Verdict::NotProven
    };
    let meaning_expect = || {
        if position == "claim-lhs" {
            // The vacuous q of `#Floor`, which no build decides, keeps the allowance.
            let q = if id == "floor" {
                Verdict::Proven
            } else {
                Verdict::ProvenAlways
            };
            Expect::proofs(vec![("p", claim_verdict), ("q", q)])
        } else {
            Expect::runs((1..=3).map(run).collect())
        }
    };
    let (expect, allow, meaning_runs) = match decision {
        Decision::Refuse(expect) => {
            let meaning = match (id, position) {
                ("let" | "fun", _) => Meaning::Unstated,
                // `f(X #Or 2) => 10 +Int X` states f(2) = 10 +Int X for every X.
                ("or-var", "fun-lhs" | "simp-lhs") => Meaning::NoModel,
                _ => Meaning::States(meaning_expect()),
            };
            (expect, Allow::None, meaning)
        }
        Decision::Meaning | Decision::Undecided => {
            let allow = if matches!(decision, Decision::Undecided) || id == "floor" {
                Allow::Undecided
            } else if position == "claim-lhs" {
                // The proof of p decides `X <Int 3` over the matched inputs.
                Allow::PortableUndecided
            } else {
                Allow::None
            };
            (meaning_expect(), allow, Meaning::Unstated)
        }
    };
    CellSpec {
        name: format!("left/{position}__{id}"),
        route: if position == "claim-lhs" {
            Route::Kprove
        } else {
            Route::Kompile
        },
        text: sentences,
        pattern: None,
        programs,
        meaning: format!("matches {meaning}"),
        expect,
        allow,
        meaning_runs,
    }
}

// ---------------------------------------------------------------- built positions

/// The audit's built constructs at an Int position, X bound: (id, text, meaning).
const RIGHT: &[(&str, &str, &str)] = &[
    ("plain", "X", "{X}"),
    ("or", "X #Or 0", "{X, 0}: either"),
    ("and-term", "X #And 1", "X where X = 1, else empty"),
    (
        "and-pred",
        "X #And {X #Equals 1}",
        "X where X = 1, else empty",
    ),
    ("not", "#Not(X)", "Int minus {X}"),
    (
        "ceil",
        "X #And #Ceil(1 /Int (X -Int 3))",
        "X where X != 3, else empty",
    ),
    ("floor", "X #And #Floor(X)", "empty"),
    ("exists", "#Exists Y:Int . Y", "every Int"),
    (
        "exists-pred",
        "#Exists Y:Int . (Y #And {Y #Equals X +Int 1})",
        "{X + 1}",
    ),
    ("forall", "#Forall Y:Int . Y", "empty"),
    ("implies", "X #Implies 0", "(Int minus {X}) union {0}"),
    ("top", "#Top", "every Int"),
    ("bottom", "#Bottom", "empty"),
    ("as", "(X +Int 1) #as Y", "an alias outside a pattern"),
    ("let", "#let Z = X #in Z +Int 1", "{X + 1}"),
    ("fun", "#fun(Z => Z +Int 1)(X)", "{X + 1}"),
    (
        "and-or",
        "(X #Or 0) #And 1",
        "{X, 0} ∩ {1}: 1 where X = 1, else empty; a connective in an operand of a built #And",
    ),
];

/// The values built construct `id` denotes at X = n (empty: undefined).
fn right_values(id: &str, n: i64) -> Vec<i64> {
    match id {
        "plain" => vec![n],
        "or" => vec![n, 0],
        "and-term" | "and-pred" | "and-or" => {
            if n == 1 {
                vec![1]
            } else {
                Vec::new()
            }
        }
        "ceil" => {
            if n != 3 {
                vec![n]
            } else {
                Vec::new()
            }
        }
        "let" | "fun" | "exists-pred" => vec![n + 1],
        "floor" | "forall" | "bottom" | "not" | "exists" | "implies" | "top" | "as" => Vec::new(),
        _ => unreachable!("built construct {id}"),
    }
}

fn right_decision(position: &str, id: &str) -> Decision {
    let function_like = matches!(position, "fun-rhs" | "simp-rhs" | "anywhere-rhs");
    match (id, position) {
        ("as", "rule-rhs") => Decision::Refuse(Expect::refuse(INVALID_REWRITE)),
        // A claim's right side is a pattern, which an alias may name (extra/claim-rhs__as-*); the
        // alias variable Y here is bound by neither side.
        ("as", "claim-rhs") => Decision::Refuse(Expect::refuse(UNBOUND_VARIABLE)),
        ("as", _) => Decision::Refuse(Expect::Refuse {
            portable: Code::Parse,
            z3: INVALID_REWRITE,
        }),
        ("bottom" | "let" | "fun", "claim-rhs") => {
            Decision::Refuse(Expect::refuse(ML_CONSTRUCT_POSITION))
        }
        ("or", _) if function_like => Decision::Refuse(Expect::refuse(ML_CONSTRUCT_POSITION)),
        ("plain" | "or" | "and-term" | "and-pred" | "ceil" | "bottom" | "let" | "fun", _) => {
            Decision::Meaning
        }
        ("floor", _) => Decision::Undecided,
        _ => Decision::Refuse(Expect::refuse(ML_CONSTRUCT_POSITION)),
    }
}

fn right_cells(cells: &mut Vec<CellSpec>) {
    for position in [
        "rule-rhs",
        "fun-rhs",
        "simp-rhs",
        "macro-rhs",
        "alias-rhs",
        "anywhere-rhs",
        "claim-rhs",
    ] {
        for (id, text, meaning) in RIGHT {
            if *id == "and-or" && position != "rule-rhs" {
                continue;
            }
            cells.push(right_cell(position, id, text, meaning));
        }
    }
}

fn right_cell(position: &str, id: &str, text: &str, meaning: &str) -> CellSpec {
    let sentences = match position {
        "rule-rhs" => format!("  rule [p]: <k> go(X) => done({text}) ... </k>\n"),
        "fun-rhs" => format!(
            "  syntax Int ::= f(Int) [function, symbol(f)]\n  rule [p]: f(X) => {text}\n  rule [g]: <k> go(X) => done(f(X)) ... </k>\n"
        ),
        "simp-rhs" => format!(
            "  syntax Int ::= f(Int) [function, symbol(f)]\n  rule [p]: f(X) => {text} [simplification]\n  rule [g]: <k> go(X) => done(f(X)) ... </k>\n"
        ),
        // A macro or alias body is judged where it is used, in the context of the use, so the
        // use is probed too.
        "macro-rhs" => format!(
            "  syntax Int ::= m(Int) [macro, symbol(m)]\n  rule [p]: m(X) => {text}\n  rule [q]: <k> go(X) => done(m(X)) ... </k>\n"
        ),
        "alias-rhs" => format!(
            "  syntax Int ::= al(Int) [alias, symbol(al)]\n  rule [p]: al(X) => {text}\n  rule [q]: <k> go(X) => done(al(X)) ... </k>\n"
        ),
        "anywhere-rhs" => format!(
            "  syntax Int ::= f(Int) [function, symbol(f)]\n  rule [p]: f(X) => {text} [anywhere]\n  rule [g]: <k> go(X) => done(f(X)) ... </k>\n"
        ),
        "claim-rhs" => format!(
            "  rule [g]: <k> go(X) => done(X) ... </k>\nendmodule\n\nmodule P-SPEC\n  imports P\n  claim [p]: <k> go(X) => done({text}) ... </k>\n"
        ),
        _ => unreachable!(),
    };
    let is_claim = position == "claim-rhs";
    let programs: Vec<String> = if is_claim {
        Vec::new()
    } else {
        [1, 3].into_iter().map(go).collect()
    };
    let decision = right_decision(position, id);
    let function_like = matches!(position, "fun-rhs" | "simp-rhs" | "anywhere-rhs");
    let meaning_expect = || {
        if is_claim {
            // The claim holds when done(X), which go(X) reaches, is among the values the right
            // side denotes for every X.
            let holds = match id {
                "exists" | "top" => true,
                "not" | "implies" => false,
                _ => (-20..=20).all(|x| right_values(id, x).contains(&x)),
            };
            let verdict = if holds {
                Verdict::Proven
            } else {
                Verdict::NotProven
            };
            Expect::proofs(vec![("p", verdict)])
        } else {
            let runs = [1, 3]
                .into_iter()
                .map(|n| {
                    let values = right_values(id, n);
                    if values.is_empty() {
                        Run::new(go(n), vec![trivial(go(n))]).undecided(vec![stuck(done(n))])
                    } else {
                        Run::new(go(n), values.iter().map(|v| stuck(done(v))).collect())
                    }
                })
                .collect();
            Expect::runs(runs)
        }
    };
    let (expect, allow, meaning_runs) = match decision {
        Decision::Refuse(expect) => {
            let meaning = match id {
                "as" => Meaning::Unstated,
                // A function application has at most one value: an equation whose right side
                // denotes several (or every) value states an axiom with no model.
                "or" | "not" | "exists" | "implies" | "top" if function_like => Meaning::NoModel,
                // A rule whose right side denotes infinitely many states has no finite leaf set.
                "not" | "exists" | "implies" | "top" if !is_claim => Meaning::Unstated,
                _ => Meaning::States(meaning_expect()),
            };
            (expect, Allow::None, meaning)
        }
        Decision::Meaning | Decision::Undecided => {
            let allow = if matches!(decision, Decision::Undecided) {
                Allow::Undecided
            } else if is_claim {
                // Disproving the claim needs a model of X, which the portable build has no
                // solver to find.
                Allow::PortableUndecided
            } else {
                Allow::None
            };
            (meaning_expect(), allow, Meaning::Unstated)
        }
    };
    CellSpec {
        name: format!("right/{position}__{id}"),
        route: if is_claim {
            Route::Kprove
        } else {
            Route::Kompile
        },
        text: sentences,
        pattern: None,
        programs,
        meaning: format!("denotes {meaning}"),
        expect,
        allow,
        meaning_runs,
    }
}

// ---------------------------------------------------------------- predicate simplifications

fn predicate_simplification_cells(cells: &mut Vec<CellSpec>) {
    const F: &str = "  syntax Int ::= f(Int) [function, symbol(f)]\n";
    const VALUE: &str = "  rule [g]: <k> go(X) => done(f(X)) ... </k>\n";
    // (id, lemma, driver rule, programs with the expected run, meaning)
    let table: Vec<(&str, &str, String, Vec<Run>, &str)> = vec![
        (
            "ceil-top",
            "#Ceil(f(X)) => #Top",
            VALUE.to_owned(),
            vec![
                Run::new(go(1), vec![stuck(done("f(1)"))]),
                Run::new(go(3), vec![stuck(done("f(3)"))]),
            ],
            "f is defined everywhere, so go(X) steps to done(f(X)) with no undefined branch",
        ),
        (
            "ceil-bool",
            "#Ceil(f(X)) => {true #Equals X >Int 0}",
            VALUE.to_owned(),
            vec![
                Run::new(go(1), vec![stuck(done("f(1)"))]),
                Run::new(go(0), vec![trivial(go(0))]),
            ],
            "f(X) is defined iff X > 0: done(f(1)), and go(0)'s step is undefined",
        ),
    ];
    // A predicate lemma about f(X) decides a claim over a symbolic X: the claim holds where the
    // lemma's right side implies X < 3 (the rule's condition).
    let claimed: [(&str, &str, &str, Verdict, &str); 6] = [
        (
            "eq-eq",
            "{f(X) #Equals 1} => {X #Equals 1}",
            "{f(X) #Equals 1}",
            Verdict::Proven,
            "f(X) = 1 iff X = 1",
        ),
        (
            "eq-or",
            "{f(X) #Equals 1} => {X #Equals 1} #Or {X #Equals 2}",
            "{f(X) #Equals 1}",
            Verdict::Proven,
            "f(X) = 1 iff X in {1, 2}",
        ),
        (
            "eq-not",
            "{f(X) #Equals 1} => #Not({X #Equals 3})",
            "{f(X) #Equals 1}",
            Verdict::NotProven,
            "f(X) = 1 iff X != 3 (X = 4 is stuck)",
        ),
        (
            "eq-ex",
            "{f(X) #Equals 1} => #Exists Y:Int . {X #Equals Y +Int 1}",
            "{f(X) #Equals 1}",
            Verdict::NotProven,
            "f(X) = 1 always (X = 3 is stuck)",
        ),
        (
            "eq-bottom",
            "{f(X) #Equals 1} => #Bottom",
            "{f(X) #Equals 1}",
            Verdict::Proven,
            "f(X) is never 1: the claim is vacuous",
        ),
        (
            "or-lhs",
            "{f(X) #Equals 1} #Or {f(X) #Equals 2} => {X #Equals 1}",
            "{f(X) #Equals 1} #Or {f(X) #Equals 2}",
            Verdict::Proven,
            "a disjunction as a simplification's subject: f(X) in {1, 2} iff X = 1",
        ),
    ];
    for (id, lemma, condition, verdict, meaning) in claimed {
        cells.push(CellSpec {
            name: format!("psimp/pred-simp__{id}"),
            route: Route::Kprove,
            text: format!(
                "{F}  rule [p]: {lemma} [simplification]\n  rule [g]: <k> go(X) => done(X) ... </k> requires X <Int 3\nendmodule\n\nmodule P-SPEC\n  imports P\n  claim [q]: <k> go(X) => done(X) ... </k> requires {condition}\n"
            ),
            pattern: None,
            programs: Vec::new(),
            meaning: meaning.to_owned(),
            expect: Expect::proofs(vec![("q", verdict)]),
            // The claim decides an implication over symbolic integers.
            allow: Allow::PortableUndecided,
            meaning_runs: Meaning::Unstated,
        });
    }
    // The lemma of eq-eq on a ground atom: a rewrite rule's condition {f(1) #Equals 1}. The
    // lemma says nothing where the operand it consumes, f(1), is undefined (docs/compatibility.md,
    // the predicate-lemma contract), so the condition is ⌈f(1)⌉, which no equation of f decides:
    // go(1) gives done(1) under ⌈f(1)⌉ and is stuck otherwise, or halts undecided.
    cells.push(CellSpec {
        name: "psimp/pred-simp__eq-eq-ground".to_owned(),
        route: Route::Kompile,
        text: format!(
            "{F}  rule [p]: {{f(X) #Equals 1}} => {{X #Equals 1}} [simplification]\n  rule [g]: <k> go(X) => done(X) ... </k> requires {{f(X) #Equals 1}}\n"
        ),
        pattern: None,
        programs: vec![go(1), go(3)],
        meaning: "f(X) = 1 iff X = 1 where f(X) is defined, so go(1) steps to done(1) under \\ceil(f(1)) and is stuck otherwise, and go(3) is stuck".to_owned(),
        expect: Expect::runs(vec![
            Run::new(go(1), vec![stuck(done(1)), stuck(go(1))]),
            Run::new(go(3), vec![stuck(go(3))]),
        ]),
        allow: Allow::Undecided,
        meaning_runs: Meaning::Unstated,
    });
    for (id, lemma, driver, runs, meaning) in table {
        cells.push(CellSpec {
            name: format!("psimp/pred-simp__{id}"),
            route: Route::Kompile,
            text: format!("{F}  rule [p]: {lemma} [simplification]\n{driver}"),
            pattern: None,
            programs: runs.iter().map(|run| run.program.clone()).collect(),
            meaning: meaning.to_owned(),
            expect: Expect::runs(runs),
            allow: Allow::None,
            meaning_runs: Meaning::Unstated,
        });
    }
}

// ---------------------------------------------------------------- extra probes

fn extra_cells(cells: &mut Vec<CellSpec>) {
    let table: [(&str, &str, &str, [i64; 2]); 3] = [
        (
            "rule-requires-matchk__or",
            "  rule [p]: <k> go(X) => done(X) ... </k> requires (1 #Or 2) :=K X\n",
            "an or-pattern inside a :=K pattern in a condition: X in {1, 2}",
            [1, 0],
        ),
        (
            "rule-rhs__or-excl",
            "  rule [p]: <k> go(X) => done(({X #Equals 1} #And 10) #Or (#Not({X #Equals 1}) #And 20)) ... </k>\n",
            "denotes 10 where X = 1, else 20 (one value)",
            [10, 20],
        ),
        (
            "fun-rhs__or-excl",
            "  syntax Int ::= f(Int) [function, symbol(f)]\n  rule [p]: f(X) => ({X #Equals 1} #And 10) #Or (#Not({X #Equals 1}) #And 20)\n  rule [g]: <k> go(X) => done(f(X)) ... </k>\n",
            "f(X) is 10 where X = 1, else 20 (functional)",
            [10, 20],
        ),
    ];
    macro_built_cells(cells);
    walk_cells(cells);
    nested_quantifier_cells(cells);
    for (name, text, meaning, [at1, at3]) in table {
        let run = |n: i64, value: i64| {
            if name == "rule-requires-matchk__or" && value == 0 {
                Run::new(go(n), vec![stuck(go(n))])
            } else {
                Run::new(go(n), vec![stuck(done(if value == 1 { n } else { value }))])
            }
        };
        cells.push(CellSpec {
            name: format!("extra/{name}"),
            route: Route::Kompile,
            text: text.to_owned(),
            pattern: None,
            programs: vec![go(1), go(3)],
            meaning: meaning.to_owned(),
            expect: Expect::runs(vec![run(1, at1), run(3, at3)]),
            allow: Allow::None,
            meaning_runs: Meaning::Unstated,
        });
    }
}

/// The shapes of `left/fun-lhs__or-var` and `right/rule-rhs__and-or` built by a macro: the check
/// that refuses them runs on the sentences as written, so these are refused only once the
/// expanded sentences are checked (MLP/4b).
fn macro_built_cells(cells: &mut Vec<CellSpec>) {
    cells.push(CellSpec {
        name: "extra/fun-lhs__macro-or-var".to_owned(),
        route: Route::Kompile,
        text: "  syntax Int ::= orTwo(Int) [macro, symbol(orTwo)]\n  rule orTwo(X) => X #Or 2\n  syntax Int ::= f(Int) [function, symbol(f)]\n  rule [p]: f(orTwo(X)) => 10 +Int X\n  rule [o]: f(_) => 0 [owise]\n  rule [g]: <k> go(X) => done(f(X)) ... </k>\n".to_owned(),
        pattern: None,
        programs: (1..=3).map(go).collect(),
        // `f(X #Or 2) => 10 +Int X` after expansion states f(2) = 10 +Int X for every X.
        meaning: "matches X or 2, a macro's expansion; X unbound in the alternative 2".to_owned(),
        expect: Expect::refuse(ML_CONSTRUCT_POSITION),
        allow: Allow::None,
        meaning_runs: Meaning::NoModel,
    });
    let runs = [1, 3]
        .into_iter()
        .map(|n| {
            if n == 1 {
                Run::new(go(n), vec![stuck(done(1))])
            } else {
                Run::new(go(n), vec![trivial(go(n))]).undecided(vec![stuck(done(n))])
            }
        })
        .collect();
    cells.push(CellSpec {
        name: "extra/rule-rhs__macro-and-or".to_owned(),
        route: Route::Kompile,
        text: "  syntax Int ::= orZero(Int) [macro, symbol(orZero)]\n  rule orZero(X) => X #Or 0\n  rule [p]: <k> go(X) => done(orZero(X) #And 1) ... </k>\n".to_owned(),
        pattern: None,
        programs: vec![go(1), go(3)],
        meaning: "denotes {X, 0} ∩ {1}, a macro's expansion: 1 where X = 1, else empty".to_owned(),
        expect: Expect::refuse(ML_CONSTRUCT_POSITION),
        allow: Allow::None,
        meaning_runs: Meaning::States(Expect::runs(runs)),
    });
}

/// Shapes the position check decides outside the audit's tables (MLP/4b): a set variable bound by
/// a quantifier, or-patterns of an equation below a symbol or at an argument's root, a predicate
/// alone at a shared or built position, and guarded or unguarded alternatives of an equation's
/// result.
fn walk_cells(cells: &mut Vec<CellSpec>) {
    const KITEMS: &str = "  syntax KItem ::= g(Int) [symbol(g)] | h(Int) [symbol(h)]\n  syntax Int ::= ff(KItem) [function, symbol(ff)]\n  rule [d]: <k> go(X) => done(ff(g(X))) ... </k>\n  rule [o]: ff(_) => 7 [owise]\n";
    const F: &str = "  syntax Int ::= f(Int) [function, symbol(f)]\n  rule [g]: <k> go(X) => done(f(X)) ... </k>\n";
    let refused = |name: &str, text: String, meaning: &str, meaning_runs: Meaning| CellSpec {
        name: format!("extra/{name}"),
        route: Route::Kompile,
        text,
        pattern: None,
        programs: vec![go(1), go(3)],
        meaning: meaning.to_owned(),
        expect: Expect::refuse(ML_CONSTRUCT_POSITION),
        allow: Allow::None,
        meaning_runs,
    };
    let accepted = |name: &str, text: String, meaning: &str, runs: Vec<Run>| CellSpec {
        name: format!("extra/{name}"),
        route: Route::Kompile,
        text,
        pattern: None,
        programs: runs.iter().map(|run| run.program.clone()).collect(),
        meaning: meaning.to_owned(),
        expect: Expect::runs(runs),
        allow: Allow::None,
        meaning_runs: Meaning::Unstated,
    };
    cells.push(refused(
        "rule-requires__exists-setvar",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires #Exists @T:Int . {X #Equals @T}\n"
            .to_owned(),
        "a quantifier binds an element variable; @T is a set variable, bound only by a fixpoint: not a pattern",
        Meaning::Unstated,
    ));
    cells.push(refused(
        "fun-lhs__or-below-symbol",
        format!("{KITEMS}  rule [p]: ff(g(1 #Or 2)) => 5\n"),
        "g(1 #Or 2) is g(1) #Or g(2): ff(g(1)) = ff(g(2)) = 5, ff(g(3)) = 7; an equation's or-pattern below a symbol is refused (matched only at an argument's root)",
        Meaning::States(Expect::runs(vec![
            Run::new(go(1), vec![stuck(done(5))]),
            Run::new(go(3), vec![stuck(done(7))]),
        ])),
    ));
    cells.push(accepted(
        "fun-lhs__or-of-or-root",
        format!("{KITEMS}  rule [p]: ff((g(1) #Or g(2)) #Or h(3)) => 5\n"),
        "an or-pattern of or-patterns at an argument's root: ff(g(1)) = ff(g(2)) = ff(h(3)) = 5, ff(g(3)) = 7",
        vec![
            Run::new(go(1), vec![stuck(done(5))]),
            Run::new(go(3), vec![stuck(done(7))]),
        ],
    ));
    cells.push(accepted(
        "rule-shared__pred",
        "  rule [p]: <k> pair({1 #Equals 1}, (sa => sb)) ... </k>\n".to_owned(),
        "a predicate at a shared position constrains the match: {1 = 1} is every Int, so pair(n, sa) steps to pair(n, sb)",
        vec![Run::new("pair(1, sa)", vec![stuck("pair(1, sb)")])],
    ));
    cells.push(refused(
        "rule-rhs__eq",
        "  rule [p]: <k> go(X) => done({X #Equals 1}) ... </k>\n".to_owned(),
        "a predicate alone where a value is built: every Int where X = 1, none elsewhere; refused",
        Meaning::Unstated,
    ));
    cells.push(accepted(
        "fun-rhs__or-guards",
        format!("{F}  rule [p]: f(X) => ({{X #Equals 1}} #And 10) #Or ({{X #Equals 2}} #And 20)\n"),
        "alternatives guarded by exclusive predicates: f(1) = 10, f(2) = 20, f(3) undefined",
        vec![
            Run::new(go(1), vec![stuck(done(10))]),
            Run::new(go(2), vec![stuck(done(20))]),
            Run::new(go(3), vec![trivial(go(3))]),
        ],
    ));
    // In a claim's right side, the pattern every path must reach, `P #as ?Y` names the reached
    // term matching P.
    for (name, right, ensures, verdict, meaning) in [
        (
            "claim-rhs__as-existential",
            "done(X #as ?Y)",
            " ensures ?Y ==Int X",
            Verdict::Proven,
            "go(X) reaches done(X), and ?Y names X",
        ),
        (
            "claim-rhs__as-other",
            "done((X +Int 1) #as ?Y)",
            "",
            Verdict::NotProven,
            "go(X) reaches done(X), which is not done(X + 1)",
        ),
    ] {
        cells.push(CellSpec {
            name: format!("extra/{name}"),
            route: Route::Kprove,
            text: format!("  rule [g]: <k> go(X) => done(X) ... </k>\nendmodule\n\nmodule P-SPEC\n  imports P\n  claim [p]: <k> go(X) => {right} ... </k>{ensures}\n"),
            pattern: None,
            programs: Vec::new(),
            meaning: meaning.to_owned(),
            expect: Expect::proofs(vec![("p", verdict)]),
            // Disproving or proving the claim decides equalities over symbolic integers.
            allow: Allow::PortableUndecided,
            meaning_runs: Meaning::Unstated,
        });
    }
    cells.push(refused(
        "fun-rhs__or-half-guard",
        format!("{F}  rule [p]: f(X) => ({{X #Equals 1}} #And 10) #Or 20\n"),
        "an unguarded alternative beside a guarded one: f(1) would be both 10 and 20, an axiom with no model",
        Meaning::NoModel,
    ));
}

/// A quantifier below a symbol of a left side: a left side is matched against a state, or an
/// equation's against the application's arguments, and a quantifier there has no matching meaning
/// at any depth, so it is refused at its rule as at the direct position (`left/*__exists`,
/// `left/*__forall`), below a constructor of a rewrite rule's left side and of a function or
/// simplification equation's argument.
fn nested_quantifier_cells(cells: &mut Vec<CellSpec>) {
    const WRAP: &str = "  syntax KItem ::= wrap(KItem) [symbol(wrap)] | g(Int) [symbol(g)]\n";
    const K: &str =
        "  syntax KItem ::= g(Int) [symbol(g)]\n  syntax Int ::= k(KItem) [function, symbol(k)]\n";
    let table = [
        (
            "rule-lhs__nested-exists",
            format!("{WRAP}  rule [p]: <k> wrap(g(#Exists Y:Int . Y)) => done(0) ... </k>\n"),
        ),
        (
            "rule-lhs__nested-forall",
            format!("{WRAP}  rule [p]: <k> wrap(g(#Forall Y:Int . Y)) => done(0) ... </k>\n"),
        ),
        (
            "fun-lhs__nested-exists",
            format!(
                "{K}  rule [p]: k(g(#Exists Y:Int . Y)) => 1\n  rule [o]: k(_) => 0 [owise]\n  rule [g]: <k> go(X) => done(k(g(X))) ... </k>\n"
            ),
        ),
        (
            "simp-lhs__nested-forall",
            format!(
                "{K}  rule [p]: k(g(#Forall Y:Int . Y)) => 1 [simplification]\n  rule [g]: <k> go(X) => done(k(g(X))) ... </k>\n"
            ),
        ),
    ];
    for (name, text) in table {
        cells.push(CellSpec {
            name: format!("extra/{name}"),
            route: Route::Kompile,
            text,
            pattern: None,
            programs: vec![go(1)],
            meaning: "a quantifier below a symbol of a matched position: no matching meaning"
                .to_owned(),
            expect: Expect::refuse(ML_CONSTRUCT_POSITION),
            allow: Allow::None,
            meaning_runs: Meaning::Unstated,
        });
    }
}
