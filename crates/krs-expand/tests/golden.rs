//! Golden expansions: the expanded token text of one small input per
//! `krs-macros` entry point, and of the helper and error paths that each entry
//! point dispatches to.
//!
//! Each case is one item of an authored file. Its first KRS attribute, or the
//! item-level macro itself, is expanded once with a [`BrowserEnvironment`]
//! whose call site is that invocation; nested invocations in the output are
//! not expanded. The expected text is `tests/golden/<case>.txt`: the output
//! printed by `prettyplease` when it is a sequence of items, otherwise its
//! `TokenStream` spelling, or one line per diagnostic.
//!
//! Set `UPDATE_EXPECT=1` to rewrite the expected files after an
//! intended output change.

use std::fmt::Write as _;
use std::path::PathBuf;

use krs_expand::BrowserEnvironment;
use krs_expand::sink::AuthoredFile;
use krs_syntax::surface::{AttributeMacro, FunctionMacro};
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::spanned::Spanned;

/// (case name, authored source).
const CASES: &[(&str, &str)] = &[
    // Sort declarations.
    (
        "sort",
        r"
#[k::sort]
pub trait Value: Expr + KResult {}
",
    ),
    (
        "sort_bracket",
        r#"
#[k::sort]
#[k::bracket("({value})")]
pub trait Expr: KItem {}
"#,
    ),
    (
        "sorts",
        r"
k::sorts! {
    ObjectTerm: KResult;
}
",
    ),
    (
        "sorts_readable",
        r#"
k::sorts! {
    #[k::bracket("(", ")")]
    ReadableExpr;
    impl ReadableExpr for Id;

    ReadableValue: ReadableExpr + k::KResult;
    impl ReadableValue for Int, Bool;

    DiamondTop;
    DiamondLeft: DiamondTop;
    DiamondRight: DiamondTop;
    Diamond: DiamondLeft + DiamondRight;
    impl Diamond for Int;
}
"#,
    ),
    (
        "framework_sorts",
        r"
k::__framework_sorts! {
    KItem;
    KResult: KItem;
}
",
    ),
    (
        "framework_sorts_membership",
        r"
k::__framework_sorts! {
    KItem;
    impl KItem for Int;
}
",
    ),
    (
        "framework_sorts_bracket",
        r#"
k::__framework_sorts! {
    #[k::bracket("(", ")")]
    KItem;
}
"#,
    ),
    (
        "subsort",
        r"
#[k::subsort]
impl Value for Identifier {}
",
    ),
    (
        "bracket_orphan",
        r#"
#[k::bracket("(", ")")]
pub trait Expr {}
"#,
    ),
    // Productions.
    (
        "symbol",
        r#"
#[k::symbol("api::Halt")]
#[k::constructor(sort = Expr, syntax = "halt", group = "atoms")]
pub struct Halt;
"#,
    ),
    (
        "constructor",
        r#"
#[k::constructor(
    sort = Expr,
    syntax = "{second} pair {first}",
    group = "pair",
    avoid = true,
    format = "%1 %2 %3"
)]
#[k::seqstrict(sequence = [first, second], result = KResult)]
pub struct Pair {
    pub first: Term<dyn Expr>,
    pub second: Term<dyn Expr>,
}
"#,
    ),
    (
        "constructor_strict",
        r#"
#[k::constructor(sort = Expr, syntax = "-{value}", group = "prefix", format = "%1%2")]
#[k::strict(sequence = [value], result = KResult)]
pub struct Neg {
    pub value: Term<dyn Expr>,
}
"#,
    ),
    (
        "function",
        r##"
#[k::function(total, sort = k::builtin::int::Int, syntax = "#increment({value})")]
pub struct Increment {
    pub value: Term<k::builtin::int::Int>,
}
"##,
    ),
    (
        "function_memo",
        r#"
#[k::function(total, memo, sort = k::builtin::int::Int, syntax = "square({value})")]
pub struct Square {
    pub value: Term<k::builtin::int::Int>,
}
"#,
    ),
    (
        "function_hook",
        r#"
#[k::function(
    total,
    sort = k::builtin::Bytes,
    syntax = "Keccak256raw({value})",
    hook = krypto::keccak256_raw,
)]
pub struct Keccak256Raw {
    pub value: Term<k::builtin::Bytes>,
}
"#,
    ),
    (
        "constructors",
        r#"
#[k::constructors(sort = ObjectTerm, result = KResult)]
#[k::precedence((Foo, Bar))]
pub enum Object {
    #[k::syntax("foo")]
    Foo(),
    #[k::syntax("bar")]
    Bar(),
}
"#,
    ),
    (
        "constructors_helpers",
        r#"
#[k::constructors(sort = Expr, result = k::KResult)]
#[k::precedence((ZeroAlias, Double, Block) > left (And))]
pub enum StaticExpr {
    #[k::syntax("zeroAlias")]
    #[k::alias]
    ZeroAlias(),

    #[k::syntax("double({value})")]
    #[k::seqstrict(using = operand_eval)]
    Double { value: Expr },

    #[k::syntax("{lhs} && {rhs}")]
    #[k::strict(lhs)]
    And { lhs: Expr, rhs: Expr },

    #[k::syntax("{{{body}}}")]
    #[k::format("{{%i%n{body}%d%n}}")]
    Block { body: Expr },
}
"#,
    ),
    (
        "constructors_prefer",
        r#"
#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((IfThen, IfThenElse))]
pub enum StmtSyntax {
    #[k::syntax("if {condition} then {body}", prefer)]
    IfThen { condition: Bool, body: Stmt },
    #[k::syntax("if {condition} then {then_branch} else {else_branch}")]
    IfThenElse { condition: Bool, then_branch: Stmt, else_branch: Stmt },
}
"#,
    ),
    (
        "constructors_overload",
        r#"
#[k::constructors(sort = LVal, result = k::KResult)]
#[k::precedence((LvalDot))]
pub enum LValSyntax {
    #[k::syntax("{base}.{field}", overload = ExpSyntax::Dot)]
    LvalDot { base: LVal, field: Id },
}
"#,
    ),
    (
        "constructors_records",
        r#"
#[k::constructors(sort = Value)]
pub enum Boolean {
    #[k::syntax("true", group = "atoms")]
    True,
    #[k::syntax("false", group = "atoms")]
    False,
    #[k::syntax("tag {value}", group = "atoms", format = "%1%2")]
    Tagged { value: Term<dyn Expr> },
}
"#,
    ),
    (
        "token",
        r#"
#[k::token(regex = r"[a-zA-Z][a-zA-Z0-9_]*", prec = 2)]
pub struct Identifier(pub String);
"#,
    ),
    (
        "token_stack",
        r#"
#[k::token(regex = r"[a-z][a-zA-Z0-9]*")]
#[k::token(terminal = "main")]
pub struct Name(pub String);
"#,
    ),
    (
        "token_alias",
        r#"
#[k::token(regex = r"\$[a-zA-Z0-9_]+")]
pub type DollarId = k::builtin::Id;
"#,
    ),
    (
        "strict_orphan",
        r"
#[k::strict(sequence = [value], result = KResult)]
pub struct Neg {
    pub value: Term<dyn Expr>,
}
",
    ),
    (
        "seqstrict_orphan",
        r"
#[k::seqstrict(sequence = [first], result = KResult)]
pub struct Pair {
    pub first: Term<dyn Expr>,
}
",
    ),
    (
        "precedence",
        r"
k::precedence! {
    pair > atoms;
}
",
    ),
    (
        "associativity",
        r"
k::associativity! {
    left: pair;
    non_associative: atoms;
}
",
    ),
    (
        "lexical",
        r#"
k::lexical! {
    /// One ASCII letter.
    Alpha = r"[a-zA-Z]";
    AlphaNum = r"[a-zA-Z0-9_]";
}
"#,
    ),
    (
        "layout",
        r#"
k::layout! {
    r"(;[^\n\r]*)",
    r"([\ \n\r\t])",
}
"#,
    ),
    (
        "raw_k",
        r##"
k::raw_k!(r#"rule <k> double(I:Int) => I +Int I ... </k> [label(raw-double)]"#);
"##,
    ),
    (
        "function_quoted_hook",
        r##"
#[k::function(total, sort = k::builtin::string::String, syntax = "#keccak({value})", hook = "KRYPTO.keccak256")]
pub struct KeccakHex {
    pub value: Term<k::builtin::string::String>,
}
"##,
    ),
    // Configuration and initializers.
    (
        "configuration",
        r"
#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}
",
    ),
    (
        "configuration_root",
        r#"
#[k::configuration(root = "machine")]
pub struct Machine {
    pub k: instrumented::KCell<k::builtin::KSequence>,
    #[k::cell(name = "environment", color = "blue")]
    pub env: k::configuration::Cell<
        k::builtin::Map<k::builtin::Id, Term<dyn Value>>,
    >,
}
"#,
    ),
    (
        "configuration_nested",
        r"
#[k::configuration]
pub struct NestedMachine {
    pub k: k::configuration::KCell<k::builtin::KSequence>,
    pub store: Store,
}
",
    ),
    (
        "cell",
        r"
#[k::cell]
pub struct Store {
    pub env: k::configuration::Cell<
        k::builtin::Map<k::builtin::Id, Term<dyn Value>>,
    >,
}
",
    ),
    (
        "init",
        r"
#[k::init]
pub fn init() -> Self {
    Self {
        k: k::k![Object::Foo()],
    }
}
",
    ),
    (
        "init_config_vars",
        r#"
#[k::init]
pub fn init(
    #[k::config_var(name = "PGM", main)] pgm: ReadableStmt,
    #[k::config_var(name = "ENV")] env: k::builtin::Map<k::builtin::Id, ReadableValue>,
) -> Self {
    Self {
        k: k::configuration::KCell::new(k::k![pgm]),
        store: Store {
            env: k::configuration::Cell::new(env),
        },
    }
}
"#,
    ),
    // Rules, equations, and claims.
    (
        "rules",
        r"
k::rules! {
    for ObjectTerm;
    use Object::*;

    foo_to_bar: Foo() => Bar();
}
",
    ),
    (
        "rules_lexeme",
        r#"
k::rules! {
    for Stmt;
    use StmtSyntax::*;

    call_main: Call(k::lexeme!(Name, "main")) => Halt();
}
"#,
    ),
    (
        "rules_sort_test",
        r"
k::rules! {
    for Expr;
    use Op::*;

    #[k::requires(k::is!(Value, e))]
    prj: Prj { e } => int::add(k::project!(Int, e), 1);
}
",
    ),
    (
        "rules_pattern_as",
        r"
k::rules! {
    for Exp;
    use ExpSyntax::*;

    dup_pair: Dup(p @ Pair(a, b)) => Pair(p, Pair(b, a));
}
",
    ),
    (
        "rule_pattern_as",
        r"
#[k::equation]
fn rest_long(k::term![Rest(Cons(_, more @ Cons(_, _)))]: Term<Seq>) -> Term<Seq> {
    more
}
",
    ),
    (
        "rules_pattern_or",
        r"
k::rules! {
    for Exp;
    use ExpSyntax::*;

    rgb: Color(Red() | Green() | Blue()) => 1;
    primary: Red() | Green() | Blue() => 1;
}
",
    ),
    (
        "rule_pattern_or",
        r"
#[k::equation]
fn code_rgb(k::term![ColorCode(Red() | Green() | Blue())]: Term<Int>) -> Term<Int> {
    1
}
",
    ),
    (
        "rules_heads",
        r#"
k::rules! {
    for Expr;

    /// Evaluate integer negation after strictness has produced a value.
    eval_neg:     Neg { value }           => int::sub(0, value);
    #[k::rule(owise, label = "eval-not")]
    eval_not:     Not { value }           => bool::not(value);
    eval_bool_eq: Eq { lhs, rhs }         => bool::eq(lhs, rhs) where lhs: Bool, rhs: Bool;
    and_false:    And { lhs: false, .. }  => false;
}
"#,
    ),
    (
        "rules_configuration",
        r"
k::rules! {
    for ReadableRuleMachine;
    use StmtSyntax::Assign;

    var: {
        computation: [name, ..],
        env: { name -> value, .. },
    } => {
        computation: [value, ..],
    }
    where name: Id;

    assign: {
        computation: [Assign(name, value), ..],
        env: e,
    } => {
        computation: [..],
        env: set(e, name, value),
    }
    where value: Value;
}
",
    ),
    (
        "rule",
        r"
#[k::rule]
fn double(k::term![StaticExpr::Double(value)]: Term<Expr>) -> Term<Expr> {
    int::add(value, value)
}
",
    ),
    (
        "rule_typed_binders",
        r"
#[k::rule]
fn double_int(value: Term<Int>, k::term![StaticExpr::Double(value)]: Term<Expr>) -> Term<Expr> {
    int::add(value, value)
}
",
    ),
    (
        "rule_cells",
        r"
#[k::rule]
fn explicit_step(
    s1: k::Term<Stmt>,
    s2: k::Term<Stmt>,
    k::cells! {
        computation: KCell(StmtSyntax::Sequence(s1, s2), tail @ ..),
        state @ ..
    }: ReadableRuleMachine,
) -> ReadableRuleMachine {
    k::cells! {
        computation: KCell(s1, s2, ..tail),
        ..state
    }
}
",
    ),
    (
        "rule_exists",
        r#"
#[k::rule(label = "unknown")]
#[k::exists(x: Int)]
#[k::ensures(int::lt(x, 5))]
fn unknown(k::term![StaticExpr::Double(value)]: Term<Expr>) -> Term<Expr> {
    x
}
"#,
    ),
    (
        "rule_cells_exists",
        r#"
#[k::rule(label = "unknown")]
#[k::exists(x: Int)]
#[k::ensures(int::ne(x, 0))]
fn unknown(
    k::cells! {
        computation: KCell(0, tail @ ..),
        state @ ..
    }: ReadableRuleMachine,
) -> ReadableRuleMachine {
    k::cells! {
        computation: KCell(x, ..tail),
        ..state
    }
}
"#,
    ),
    (
        "exists_rule",
        r#"
#[k::exists(x: Int)]
#[k::ensures(int::ne(x, 0))]
#[k::rule(label = "unknown")]
fn unknown(
    k::cells! {
        computation: KCell(0, tail @ ..),
        state @ ..
    }: ReadableRuleMachine,
) -> ReadableRuleMachine {
    k::cells! {
        computation: KCell(x, ..tail),
        ..state
    }
}
"#,
    ),
    (
        "rules_exists",
        r"
k::rules! {
    for ReadableRuleMachine;

    #[k::exists(x: Int)]
    #[k::ensures(int::ne(x, 0))]
    unknown: {
        computation: [0, ..],
    } => {
        computation: [x, ..],
    };
}
",
    ),
    (
        "rule_fresh",
        r#"
#[k::rule(label = "allocate")]
#[k::fresh(n: Int)]
fn allocate(k::term![StaticExpr::Double(value)]: Term<Expr>) -> Term<Expr> {
    n
}
"#,
    ),
    (
        "fresh_rule",
        r#"
#[k::fresh(n: Int)]
#[k::rule(label = "allocate")]
fn allocate(
    k::cells! {
        computation: KCell(0, tail @ ..),
        state @ ..
    }: ReadableRuleMachine,
) -> ReadableRuleMachine {
    k::cells! {
        computation: KCell(n, ..tail),
        ..state
    }
}
"#,
    ),
    (
        "rules_fresh",
        r"
k::rules! {
    for ReadableRuleMachine;

    #[k::fresh(n: Int)]
    allocate: {
        computation: [0, ..],
    } => {
        computation: [n, ..],
    };
}
",
    ),
    (
        "function_fresh_generator",
        r#"
#[k::function(total, fresh_generator, sort = Expr, syntax = "freshExpr({seed})")]
pub struct FreshExpr {
    pub seed: Term<k::builtin::int::Int>,
}
"#,
    ),
    (
        "function_smt_hook",
        r#"
#[k::function(total, sort = Int, syntax = "clampSub({low}, {value})", smt_hook = "(ite (< {value} {low}) 0 (- {value} {low}))")]
pub struct ClampSub {
    pub low: Term<k::builtin::int::Int>,
    pub value: Term<k::builtin::int::Int>,
}
"#,
    ),
    (
        "function_smtlib",
        r#"
#[k::function(total, sort = Int, syntax = "probeH({value})", smtlib = "probeH")]
pub struct ProbeH {
    pub value: Term<k::builtin::int::Int>,
}
"#,
    ),
    (
        "equation_restriction",
        r"
#[k::equation(concrete, smt_lemma)]
fn chop(k::term![Chop(i)]: Term<Int>) -> Term<Int> {
    int::rem_euclid(i, 256)
}
",
    ),
    (
        "simplification_restriction",
        r"
#[k::simplification(priority = 40, concrete(c, d), symbolic(s))]
fn fold_constant(k::term![int::add(int::add(s, c), d)]: Term<Int>) -> Term<Int> {
    int::add(s, int::add(c, d))
}
",
    ),
    (
        "equation",
        r"
#[k::equation]
fn add_one(k::term![AddOne(value)]: Term<Int>) -> Term<Int> {
    int::add(value, 1)
}
",
    ),
    (
        "requires_equation",
        r"
#[k::requires(int::le(0, value))]
#[k::equation]
fn nonnegative_identity(k::term![NonnegativeIdentity(value)]: Term<Int>) -> Term<Int> {
    value
}
",
    ),
    (
        "equation_requires",
        r"
#[k::equation]
#[k::requires(int::le(0, value))]
fn nonnegative_identity(k::term![NonnegativeIdentity(value)]: Term<Int>) -> Term<Int> {
    value
}
",
    ),
    (
        "requires_orphan",
        r"
#[k::requires(int::le(0, value))]
#[k::rule]
fn positive(k::term![Positive(value)]: Term<Int>) -> Term<Int> {
    value
}
",
    ),
    (
        "priority",
        r"
#[k::priority(40)]
#[k::equation]
fn priority_choice_zero(k::term![PriorityChoice(0)]: Term<Int>) -> Term<Int> {
    111
}
",
    ),
    (
        "equation_priority",
        r"
#[k::equation(priority = 40)]
fn priority_choice_zero(k::term![PriorityChoice(0)]: Term<Int>) -> Term<Int> {
    111
}
",
    ),
    (
        "equation_owise",
        r"
#[k::equation(owise)]
fn priority_choice_other(k::term![PriorityChoice(_)]: Term<Int>) -> Term<Int> {
    0
}
",
    ),
    (
        "rule_priority",
        r#"
#[k::rule(priority = 40, label = "prefer-zero")]
fn prefer_zero(k::term![PriorityChoice(_)]: Term<Int>) -> Term<Int> {
    0
}
"#,
    ),
    (
        "simplification",
        r"
#[k::simplification]
fn normalize_gt(k::term![int::gt(lhs, rhs)]: Term<Bool>) -> Term<Bool> {
    int::lt(rhs, lhs)
}
",
    ),
    (
        "alias",
        r"
#[k::alias]
fn zero_alias(k::term![StaticExpr::ZeroAlias]: Term<Expr>) -> Term<Expr> {
    0
}
",
    ),
    (
        "alias_orphan",
        r"
#[k::alias]
pub struct Zero;
",
    ),
    (
        "context_alias",
        r"
#[k::context_alias(name = operand_eval, here = site)]
fn operand_eval(
    k::cells! {
        k: k::configuration::KCell(site, tail @ ..),
        state @ ..
    }: Machine,
) {
}
",
    ),
    (
        "claim",
        r#"
#[k::claim(all_paths, label = "branching")]
#[k::exists(n: Int)]
#[k::ensures(k::or_bool![int::eq(n, 5), int::eq(n, 6)])]
fn branching(
    k::cells! {
        k: k::configuration::KCell(
            StmtSyntax::Sequence(
                StmtSyntax::Assign(k::id!("$n"), 7),
                StmtSyntax::IfThenElse(
                    k::anonymous!(Bool, "_B"),
                    StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 6)),
                    StmtSyntax::Block(StmtSyntax::Assign(k::id!("$n"), 5)),
                ),
            ),
            tail @ ..
        ),
        env: k::configuration::Cell(map![k::id!("$n") -> 0]),
        state @ ..
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(..tail),
        env: k::configuration::Cell(map![k::id!("$n") -> n]),
        ..state
    }
}
"#,
    ),
    (
        "exists_claim",
        r"
#[k::exists(n: Int)]
#[k::claim(one_path)]
fn reaches(
    k::cells! { k: k::configuration::KCell(Start(), tail @ ..), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(Done(n), ..tail), ..state }
}
",
    ),
    (
        "ensures_orphan",
        r"
#[k::ensures(true)]
fn orphan() {}
",
    ),
    // Term islands.
    (
        "term",
        r"
k::term![StaticExpr::Double(int::add(value, 1))];
",
    ),
    (
        "k",
        r"
k::k![s, StmtSyntax::EmptyBlock()];
",
    ),
    (
        "map_items",
        r#"
k::map![k::id!("$x") -> 1, key -> value];
"#,
    ),
    (
        "map_empty",
        r"
k::map![.Map];
",
    ),
    (
        "cells",
        r"
k::cells! {
    k: k::configuration::KCell(s1, s2, ..tail),
    env: k::configuration::Cell(map![name -> value]),
    ..state
}
",
    ),
    (
        "fragment",
        r"
k::fragment![CallState { program: caller_program, pc: int::add(pc, 1) }];
",
    ),
    ("id", "k::id!(\"$n\");"),
    ("bytes", "k::bytes!(b\"\\x00A\");"),
    ("anonymous", "k::anonymous!(Bool, \"_B\");"),
    ("or_bool", "k::or_bool![int::eq(n, 5), int::eq(n, 6)];"),
    ("lexeme", "k::lexeme!(Name, \"main\");"),
    ("is", "k::is!(Value, e);"),
    ("project", "k::project!(Int, e);"),
    (
        "syntax_list",
        r#"
/// A comma-separated list of integers.
#[k::syntax_list(separator = ",")]
pub enum Ints {
    /// One integer, then the rest.
    Cons { head: Int, tail: Ints },
    Nil(),
}
"#,
    ),
    (
        "syntax_list_reference",
        r#"
#[k::syntax_list(separator = "|", non_empty, reference)]
pub enum Args {
    #[k::strict(sequence = [head, tail], result = k::KResult)]
    Cons { head: k::Term<dyn crate::ExprSort>, tail: k::Term<crate::Args> },
    Nil(),
}
"#,
    ),
    (
        "desugar",
        r"
#[k::desugar]
fn unless(k::term![Sugar::Unless(c, s)]: Term<Stmt>) -> Term<Stmt> {
    IfThenElse(c, EmptyBlock(), s)
}
",
    ),
    (
        "constructors_static_modes",
        r#"
#[k::constructors(sort = Stmt, result = k::KResult)]
#[k::precedence((Unless, DeclareMany, Zeros))]
pub enum Sugar {
    #[k::syntax("unless ({c}) {s}")]
    #[k::desugar]
    Unless { c: Expr, s: Stmt },

    #[k::syntax("int {names};")]
    #[k::desugar(recursive)]
    DeclareMany { names: Ids },

    #[k::syntax("zeros({n})")]
    #[k::alias(recursive)]
    Zeros { n: Int },
}
"#,
    ),
    (
        "constructor_desugar",
        r#"
#[k::constructor(sort = Stmt, syntax = "skip")]
#[k::desugar(recursive)]
pub struct Skip;
"#,
    ),
    (
        "desugar_unbound_variables",
        r"
#[k::desugar(unbound_variables = [n, _])]
fn twin(k::term![Shapes::Twin()]: Term<Value>) -> Term<Value> {
    Pair(n, Pair(n, _))
}
",
    ),
    (
        "spec_module",
        r#"
#[k::spec_module(name = "ORG-LEMMAS", imports = [crate])]
mod lemmas {
    use super::*;

    #[k::token(terminal = "main")]
    pub type MainName = crate::Name;

    #[k::simplification]
    fn lt_irreflexive(k::term![int::lt(value, value)]: Term<Bool>) -> Term<Bool> {
        false
    }
}
"#,
    ),
];

/// The invocation of one case: the entry point, its call site, and its input.
enum Invocation {
    Attribute {
        entry: AttributeMacro,
        call_site: Span,
        arguments: TokenStream,
        item: TokenStream,
    },
    Function {
        entry: FunctionMacro,
        call_site: Span,
        input: TokenStream,
    },
}

/// The entry name of a `k::<entry>` path.
fn facade_member(path: &syn::Path) -> Option<String> {
    let [facade, entry] = [path.segments.first()?, path.segments.last()?];
    (path.segments.len() == 2 && facade.ident == "k").then(|| entry.ident.to_string())
}

fn item_attributes(item: &mut syn::Item) -> &mut Vec<syn::Attribute> {
    match item {
        syn::Item::Enum(item) => &mut item.attrs,
        syn::Item::Fn(item) => &mut item.attrs,
        syn::Item::Impl(item) => &mut item.attrs,
        syn::Item::Struct(item) => &mut item.attrs,
        syn::Item::Trait(item) => &mut item.attrs,
        syn::Item::Type(item) => &mut item.attrs,
        syn::Item::Mod(item) => &mut item.attrs,
        other => panic!("unsupported golden item: {}", other.to_token_stream()),
    }
}

fn invocation(tokens: TokenStream) -> Invocation {
    let file: syn::File = syn::parse2(tokens).expect("a golden case parses as a file");
    let [mut item] = <[syn::Item; 1]>::try_from(file.items).expect("one item per golden case");
    if let syn::Item::Macro(item) = &item {
        let name = facade_member(&item.mac.path).expect("a facade-qualified macro");
        return Invocation::Function {
            entry: FunctionMacro::from_name(&name).expect("a krs-macros entry point"),
            call_site: item.mac.span(),
            input: item.mac.tokens.clone(),
        };
    }
    let attributes = item_attributes(&mut item);
    let index = attributes
        .iter()
        .position(|attribute| {
            facade_member(attribute.path())
                .and_then(|name| AttributeMacro::from_name(&name))
                .is_some()
        })
        .expect("a KRS attribute");
    let attribute = attributes.remove(index);
    let entry = facade_member(attribute.path())
        .and_then(|name| AttributeMacro::from_name(&name))
        .expect("a KRS attribute");
    let arguments = match &attribute.meta {
        syn::Meta::Path(_) => TokenStream::new(),
        syn::Meta::List(list) => list.tokens.clone(),
        syn::Meta::NameValue(_) => panic!("KRS attributes take no `=` value"),
    };
    Invocation::Attribute {
        entry,
        call_site: attribute.span(),
        arguments,
        item: item.to_token_stream(),
    }
}

fn render(result: krs_expand::Result<TokenStream>) -> String {
    match result {
        Ok(output) => {
            if let Ok(file) = syn::parse2::<syn::File>(output.clone()) {
                prettyplease::unparse(&file)
            } else {
                let mut text = output.to_string();
                text.push('\n');
                text
            }
        }
        Err(error) => error
            .into_diagnostics()
            .fold(String::new(), |mut text, error| {
                let span = match error.primary.location {
                    krs_diagnostic::Location::Span(span) => span,
                    _ => Span::call_site(),
                };
                let (start, end) = (span.start(), span.end());
                let _ = writeln!(
                    text,
                    "error[{}] {}:{}-{}:{}: {}",
                    error.code, start.line, start.column, end.line, end.column, error.message
                );
                text
            }),
    }
}

fn expand(source: &str) -> String {
    let (authored, tokens) = AuthoredFile::lex("src/lib.rs", source).expect("a golden case lexes");
    let env = BrowserEnvironment::new(&authored, syn::parse_str("::k").unwrap());
    let result = match invocation(tokens) {
        Invocation::Attribute {
            entry,
            call_site,
            arguments,
            item,
        } => {
            env.set_call_site(call_site);
            krs_expand::expand_attribute(entry, &env, arguments, item)
        }
        Invocation::Function {
            entry,
            call_site,
            input,
        } => {
            env.set_call_site(call_site);
            krs_expand::expand_function(entry, &env, input)
        }
    };
    render(result)
}

fn golden_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/golden")
}

#[test]
fn every_entry_point_has_a_golden_case() {
    let covered = CASES
        .iter()
        .map(|(_, source)| {
            let (_, tokens) = AuthoredFile::lex("src/lib.rs", source).unwrap();
            match invocation(tokens) {
                Invocation::Attribute { entry, .. } => entry.name(),
                Invocation::Function { entry, .. } => entry.name(),
            }
        })
        .collect::<std::collections::BTreeSet<_>>();
    let missing = AttributeMacro::ALL
        .iter()
        .map(|entry| entry.name())
        .chain(FunctionMacro::ALL.iter().map(|entry| entry.name()))
        .filter(|name| !covered.contains(name))
        .collect::<Vec<_>>();
    assert!(
        missing.is_empty(),
        "entry points without a golden case: {missing:?}"
    );
}

/// Every case in one test, so the cases share one `proc_macro2` fallback
/// source map in a fixed order.
#[test]
fn expansions_match_the_goldens() {
    let dir = golden_dir();
    for (name, source) in CASES {
        let actual = expand(source);
        expect_test::expect_file![format!("golden/{name}.txt")].assert_eq(&actual);
    }
    let mut stale = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .filter(|file| {
            !CASES
                .iter()
                .any(|(name, _)| file.strip_suffix(".txt") == Some(name))
        })
        .collect::<Vec<_>>();
    stale.sort();
    assert!(stale.is_empty(), "golden files without a case: {stale:?}");
}
