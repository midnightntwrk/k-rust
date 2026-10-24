//! K5's inputs: one broken header per KRS entry point, every dependent present.
//!
//! [`BASE`] is one package that uses all 53 entry points of `krs-macros` (29 attributes and 24
//! function-like macros) and passes `krs check` and `cargo check` without a diagnostic. Each
//! [`Mutation`] breaks the header of one entry point's use, or adds a use whose header is broken
//! where the base has none (the retired `#[k::priority]`, the facade's hidden
//! `k::__framework_sorts!`, and `k::raw_k!`, which needs `allow-raw-k`), and leaves every item that
//! depends on it in place. A broken item must still be one error: whatever rustc reports about its
//! dependents is the cascade K5 counts.
//!
//! The mutations are no class-test cases ([`super::cases`]): they are judged per package, by
//! counts, and only in the full tier.

use std::ops::Range;

/// The package every mutation edits.
pub const BASE: &str = r#"use k::builtin::{Int, KSequence, List, Map, int, list, map};
use k::{KItem, KResult, Term};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
    Loc: KResult;
}

#[k::sort(alias = Expr)]
#[k::bracket("({value})")]
pub trait ExprSort {}
pub type Expr = Term<dyn ExprSort>;

#[k::sort(alias = Num, parents = [Expr, KResult])]
pub trait NumSort: ExprSort + k::KResultSort {}
pub type Num = Term<dyn NumSort>;

impl ExprSort for Int {}

#[k::subsort(sort = Num)]
impl NumSort for Int {}

#[k::symbol("class::Neg")]
#[k::constructor(sort = Expr, syntax = "neg({value})", group = "unary")]
#[k::strict(sequence = [value], result = KResult)]
pub struct Neg {
    pub value: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} plus {rhs}", group = "additive")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Plus {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

#[k::constructor(sort = Expr, syntax = "{lhs} times {rhs}", group = "multiplicative")]
#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Times {
    pub lhs: Term<dyn ExprSort>,
    pub rhs: Term<dyn ExprSort>,
}

k::precedence! {
    unary > multiplicative > additive
}

k::associativity! {
    left: multiplicative;
    left: additive;
}

/// A closed token sort, for `k::lexeme!`.
#[k::token(regex = r"w[a-z]*")]
pub struct Word(pub String);

k::lexical! {
    Lower = r"[a-z]";
}

k::layout! {
    r"([\ \n\r\t])",
}

/// A comma-separated list of integers.
#[k::syntax_list(separator = ",")]
pub enum Ints {
    Cons { head: Int, tail: Ints },
    Nil(),
}

#[k::constructors(sort = Loc, result = KResult)]
#[k::precedence((At))]
#[rustfmt::skip]
pub enum LocSyntax {
    #[k::syntax("at({n})")] At { n: Int },
}

#[k::function(total, fresh_generator, sort = Loc, syntax = "freshLoc({seed})")]
pub struct FreshLoc {
    pub seed: Term<Int>,
}

#[k::equation]
fn fresh_loc(k::term![FreshLoc(seed)]: Term<Loc>) -> Term<Loc> {
    LocSyntax::At(seed)
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Cmd {
    #[k::syntax("go")] Go(),
    #[k::syntax("hold({a})")] Hold { a: KItem },
    #[k::syntax("alloc({a})")] Alloc { a: KItem },
    #[k::syntax("mark({a})")] Mark { a: KItem },
    #[k::syntax("look({a})")] Look { a: KItem },
    #[k::syntax("sum({items})")] Sum { items: Ints },
    #[k::syntax("swap")] #[k::desugar] Swap(),
    #[k::syntax("nest({items})")] #[k::alias] Nest { items: Ints },
}

#[k::desugar]
fn swap(k::term![Cmd::Swap()]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Go()
}

#[k::alias]
fn nest(k::term![Cmd::Nest(items)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Sum(items)
}

/// A function of one item.
#[k::function(partial, sort = Int, syntax = "probe({a})")]
pub struct Probe {
    pub a: Term<KItem>,
}

/// A function the equation table defines.
#[k::function(partial, sort = Int, syntax = "size({a})")]
pub struct Size {
    pub a: Term<KItem>,
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub ret: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub stack: List,
    #[k::cell(nested)]
    pub frame: Frame,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: k::map![],
            stack: list::empty(),
            frame: Frame { ret: 0 },
        }
    }
}

#[k::constant]
pub const START: Stmt = Cmd::Go();

k::rules! {
    for Machine;
    use Cmd::*;

    step: { k: [Go(), ..], env: e } => { k: [..], env: map::update(e, 0, 1) };
}

k::rules! {
    for Stmt;
    use Cmd::*;

    sum: Sum(Ints::Nil()) => Go();
}

#[k::rule(label = "hold")]
#[k::requires(k::is!(Int, x))]
fn hold(k::term![Cmd::Hold(x)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Hold(int::add(k::project!(Int, x), 1))
}

#[k::fresh(l: Loc)]
#[k::rule(label = "alloc")]
pub fn alloc(
    k::cells! {
        k: k::configuration::KCell(Cmd::Alloc(k::id!("$x")), tail @ ..),
        env: k::configuration::Cell(map![0 -> _, ..]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(Cmd::Hold(l), ..tail),
        ..state
    }
}

#[k::rule(label = "frame")]
pub fn frame(
    k::cells! {
        k: k::configuration::KCell(k::rewrite!(Cmd::Mark(k::bytes!(b"ab")) => Cmd::Go()), ..),
        frame: k::fragment![crate::Frame { ret: 0 }],
        state @ ..
    }: Machine,
) {
}

#[k::rule(label = "lexeme")]
#[k::requires(k::matches!(x, Cmd::Hold(_)))]
fn lexeme(k::term![Cmd::Look(Cmd::Hold(x))]: Term<Stmt>) -> Term<Stmt> {
    Cmd::Hold(k::lexeme!(Word, "word"))
}

#[k::context(hole = h)]
fn neg_operand(k::term![Neg(h)]: Term<Expr>) {}

#[k::context_alias(name = here, here = site)]
fn here_alias(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: Machine,
) {
}

#[k::equation]
fn probe_int(k::term![Probe(x)]: Term<Int>) -> Term<Int> {
    int::add(Size(x), 0)
}

#[k::simplification]
fn probe_hold(k::term![Probe(Cmd::Hold(x))]: Term<Int>) -> Term<Int> {
    Probe(x)
}

k::equations! {
    for Size;

    go: (Cmd::Go()) => 0;
}

#[k::spec_module(imports = [crate])]
mod proofs {
    use super::{Cmd, Machine};

    #[k::claim(all_paths, label = "goes")]
    #[k::requires(k::or_bool!(true, false))]
    #[k::exists(n: k::builtin::Int)]
    #[k::ensures(k::builtin::int::ge(n, 0))]
    pub fn goes(
        k::cells! { k: k::configuration::KCell(Cmd::Go(), tail @ ..), state @ .. }: Machine,
    ) -> Machine {
        k::cells! { k: k::configuration::KCell(..tail), ..state }
    }
}

k::claims! {
    for Machine;
    use Cmd::*;

    #[k::claim(all_paths)]
    anon: { k: [Hold(k::anonymous!(Int, "_V")), ..] } => { k: [..] };
}
"#;

/// One mutated package.
#[derive(Clone, Debug)]
pub struct Mutation {
    /// The ID, `entry/attribute/NAME` or `entry/function/NAME`.
    pub id: String,
    /// The mutated source.
    pub source: String,
    /// The mutated header in the mutated source: the replacement, without the end it shares with
    /// the base's text.
    pub header: Range<usize>,
}

/// `(entry point, the base's text, its replacement)`: each text occurs once in [`BASE`].
const MUTATIONS: [(&str, &str, &str); 53] = [
    (
        "attribute/sort",
        r"#[k::sort(alias = Expr)]",
        r"#[k::sort(alias = Expr, bogus)]",
    ),
    (
        "attribute/symbol",
        r#"#[k::symbol("class::Neg")]"#,
        r"#[k::symbol(1)]",
    ),
    (
        "attribute/constructor",
        r#"#[k::constructor(sort = Expr, syntax = "neg({value})", group = "unary")]"#,
        r#"#[k::constructor(sort = Expr, syntax = 1, group = "unary")]"#,
    ),
    (
        "attribute/function",
        r#"#[k::function(partial, sort = Int, syntax = "probe({a})")]"#,
        r#"#[k::function(partial, sort = Int, syntax = "probe({a})", bogus)]"#,
    ),
    (
        "attribute/constructors",
        r"#[k::constructors(sort = Stmt, result = KResult)]",
        r"#[k::constructors(sort = Stmt, result = KResult, bogus)]",
    ),
    (
        "attribute/token",
        r#"#[k::token(regex = r"w[a-z]*")]"#,
        r"#[k::token(regex = 1)]",
    ),
    (
        "attribute/bracket",
        r#"#[k::bracket("({value})")]"#,
        r"#[k::bracket(1)]",
    ),
    (
        "attribute/subsort",
        r"#[k::subsort(sort = Num)]",
        r"#[k::subsort(sort = 1)]",
    ),
    (
        "attribute/strict",
        r"#[k::strict(sequence = [value], result = KResult)]",
        r"#[k::strict(sequence = 1, result = KResult)]",
    ),
    (
        "attribute/seqstrict",
        r"#[k::seqstrict(sequence = [lhs, rhs], result = KResult)]
pub struct Plus",
        r"#[k::seqstrict(sequence = 1, result = KResult)]
pub struct Plus",
    ),
    (
        "attribute/configuration",
        r"#[k::configuration]",
        r"#[k::configuration(bogus)]",
    ),
    (
        "attribute/cell",
        r"#[k::cell(nested)]",
        r"#[k::cell(bogus)]",
    ),
    ("attribute/init", r"#[k::init]", r"#[k::init(bogus)]"),
    (
        "attribute/rule",
        r#"#[k::rule(label = "hold")]"#,
        r"#[k::rule(label = 1)]",
    ),
    (
        "attribute/equation",
        r"#[k::equation]
fn probe_int",
        r"#[k::equation(bogus)]
fn probe_int",
    ),
    (
        "attribute/simplification",
        r"#[k::simplification]",
        r"#[k::simplification(bogus)]",
    ),
    (
        "attribute/claim",
        r#"#[k::claim(all_paths, label = "goes")]"#,
        r#"#[k::claim(bogus, label = "goes")]"#,
    ),
    (
        "attribute/alias",
        r"#[k::alias]
fn nest",
        r"#[k::alias(bogus)]
fn nest",
    ),
    (
        "attribute/context_alias",
        r"#[k::context_alias(name = here, here = site)]",
        r"#[k::context_alias(name = 1, here = site)]",
    ),
    (
        "attribute/priority",
        r"#[k::equation]
fn probe_int",
        r"#[k::priority(1)]
#[k::equation]
fn probe_int",
    ),
    (
        "attribute/requires",
        r"#[k::requires(k::is!(Int, x))]",
        r"#[k::requires]",
    ),
    (
        "attribute/exists",
        r"#[k::exists(n: k::builtin::Int)]",
        r"#[k::exists(n)]",
    ),
    (
        "attribute/ensures",
        r"#[k::ensures(k::builtin::int::ge(n, 0))]",
        r"#[k::ensures]",
    ),
    ("attribute/fresh", r"#[k::fresh(l: Loc)]", r"#[k::fresh(l)]"),
    (
        "attribute/syntax_list",
        r#"#[k::syntax_list(separator = ",")]"#,
        r"#[k::syntax_list(separator = 1)]",
    ),
    (
        "attribute/desugar",
        r"#[k::desugar]
fn swap",
        r"#[k::desugar(bogus)]
fn swap",
    ),
    (
        "attribute/spec_module",
        r"#[k::spec_module(imports = [crate])]",
        r"#[k::spec_module(imports = 1)]",
    ),
    (
        "attribute/context",
        r"#[k::context(hole = h)]",
        r"#[k::context(hole = 1)]",
    ),
    (
        "attribute/constant",
        r"#[k::constant]",
        r"#[k::constant(bogus)]",
    ),
    (
        "function/sorts",
        r"k::sorts! {
    Stmt;",
        r"k::sorts! {
    1;",
    ),
    (
        "function/__framework_sorts",
        r"k::claims! {",
        r"k::__framework_sorts!(1);

k::claims! {",
    ),
    (
        "function/rules",
        r"k::rules! {
    for Machine;",
        r"k::rules! {
    for Nope;",
    ),
    (
        "function/claims",
        r"k::claims! {
    for Machine;",
        r"k::claims! {
    for Nope;",
    ),
    ("function/equations", r"for Size;", r"for Nope;"),
    (
        "function/term",
        r"k::term![Probe(x)]",
        r"k::term![Probe(x) Probe(x)]",
    ),
    ("function/id", r#"k::id!("$x")"#, r"k::id!(1)"),
    ("function/bytes", r#"k::bytes!(b"ab")"#, r"k::bytes!(1)"),
    (
        "function/anonymous",
        r#"k::anonymous!(Int, "_V")"#,
        r"k::anonymous!(1)",
    ),
    (
        "function/or_bool",
        r"k::or_bool!(true, false)",
        r"k::or_bool!()",
    ),
    (
        "function/fragment",
        r"k::fragment![crate::Frame { ret: 0 }]",
        r"k::fragment![1]",
    ),
    ("function/k", r"k: k::k![pgm],", r"k: k::k![pgm pgm],"),
    ("function/map", r"map![0 -> _, ..]", r"map![0 _, ..]"),
    (
        "function/cells",
        r"k::cells! {
        k: k::configuration::KCell(Cmd::Alloc",
        r"k::cells! {
        1, k: k::configuration::KCell(Cmd::Alloc",
    ),
    (
        "function/precedence",
        r"unary > multiplicative > additive",
        r"unary > > additive",
    ),
    (
        "function/associativity",
        r"left: multiplicative;",
        r"sideways: multiplicative;",
    ),
    (
        "function/lexeme",
        r#"k::lexeme!(Word, "word")"#,
        r"k::lexeme!(1)",
    ),
    ("function/lexical", r#"Lower = r"[a-z]";"#, r"Lower = 1;"),
    ("function/layout", r#"r"([\ \n\r\t])","#, r"1,"),
    (
        "function/raw_k",
        r"k::claims! {",
        r"k::raw_k!(1);

k::claims! {",
    ),
    ("function/is", r"k::is!(Int, x)", r"k::is!(1)"),
    (
        "function/project",
        r"k::project!(Int, x)",
        r"k::project!(1)",
    ),
    (
        "function/matches",
        r"k::matches!(x, Cmd::Hold(_))",
        r"k::matches!()",
    ),
    (
        "function/rewrite",
        r#"k::rewrite!(Cmd::Mark(k::bytes!(b"ab")) => Cmd::Go())"#,
        r#"k::rewrite!(Cmd::Mark(k::bytes!(b"ab")) Cmd::Go())"#,
    ),
];

/// Every mutation, in ID order.
///
/// # Panics
///
/// Panics if a mutation's text does not occur exactly once in the base.
#[must_use]
pub fn mutations() -> Vec<Mutation> {
    let mut mutations = MUTATIONS
        .iter()
        .map(|(name, old, new)| {
            assert_eq!(
                BASE.matches(old).count(),
                1,
                "the text of the {name} mutation occurs once in the base"
            );
            let start = BASE.find(old).expect("the text occurs");
            // The header is the replacement up to the suffix it shares with the text it
            // replaces: the broken attribute or invocation, or the inserted item.
            let suffix = old
                .bytes()
                .rev()
                .zip(new.bytes().rev())
                .take_while(|(left, right)| left == right)
                .count();
            Mutation {
                id: format!("entry/{name}"),
                source: BASE.replacen(old, new, 1),
                header: start..start + new.len() - suffix,
            }
        })
        .collect::<Vec<_>>();
    mutations.sort_by(|left, right| left.id.cmp(&right.id));
    mutations
}
