use std::sync::atomic::{AtomicUsize, Ordering};

extern crate language_host as k;

use krs_macros::{cells, map, term};
use language_host::Term;
use language_host::configuration::{Cell, KCell};

// Anonymous precedence, associativity, and subsort grammar descriptors
// are named by a nonce over their source position,
// so adding or removing a line above them
// changes their names in the summary golden.

mod split_config;
mod split_init;

mod readable_sorts {
    use language_host::builtin::{Bool, Id, Int};

    language_host::sorts! {
        #[k::bracket("(", ")")]
        ReadableExpr;
        impl ReadableExpr for Id;

        ReadableValue: ReadableExpr + language_host::KResult;
        impl ReadableValue for Int, Bool;

        ReadableStmt;

        DiamondTop;
        DiamondLeft: DiamondTop;
        DiamondRight: DiamondTop;
        Diamond: DiamondLeft + DiamondRight;
        impl Diamond for Int;
    }

    pub fn rust_membership_is_exact() {
        fn expression_member<T: ReadableExprSort>() {}
        fn value_member<T: ReadableValueSort>() {}
        fn diamond_member<T: DiamondSort>() {}

        expression_member::<Id>();
        value_member::<Int>();
        value_member::<Bool>();
        diamond_member::<Int>();
        let _: Option<ReadableExpr> = None;
        let _: Option<ReadableValue> = None;
        let _: Option<ReadableStmt> = None;
    }
}

mod readable_imp_grammar {
    use super::readable_sorts::{
        ReadableExpr as Expr, ReadableStmt as Stmt, ReadableValue as Value,
    };
    use language_host::KResult;
    use language_host::builtin::map::update as set;
    use language_host::builtin::{Bool, Id, Int, KSequence, Map, bool, int};
    #[language_host::constructors(sort = Expr, result = KResult)]
    #[language_host::precedence(
        (Neg, Not)
        > left (Mul, Div)
        > left (Add, Sub)
        > left (Ge, Gt, Le, Lt)
        > left (Eq, Ne)
        > left (And)
        > left (Or)
    )]
    #[expect(
        dead_code,
        reason = "The compile fixture checks the authored surface without executing every declaration."
    )]
    pub enum Op {
        #[language_host::syntax("-{value}")]
        #[language_host::strict]
        Neg { value: Expr },
        #[language_host::syntax("!{value}")]
        #[language_host::strict]
        Not { value: Expr },
        #[language_host::syntax("{lhs} * {rhs}")]
        #[language_host::seqstrict]
        Mul { lhs: Expr, rhs: Expr },
        #[language_host::syntax("{lhs} / {rhs}")]
        #[language_host::seqstrict]
        Div { lhs: Expr, rhs: Expr },
        #[language_host::syntax("{lhs} + {rhs}")]
        #[language_host::seqstrict]
        Add { lhs: Expr, rhs: Expr },
        #[language_host::syntax("{lhs} - {rhs}")]
        #[language_host::seqstrict]
        Sub { lhs: Expr, rhs: Expr },
        #[language_host::syntax("{lhs} >= {rhs}")]
        #[language_host::seqstrict]
        Ge { lhs: Expr, rhs: Expr },
        #[language_host::syntax("{lhs} > {rhs}")]
        #[language_host::seqstrict]
        Gt { lhs: Expr, rhs: Expr },
        #[language_host::syntax("{lhs} <= {rhs}")]
        #[language_host::seqstrict]
        Le { lhs: Expr, rhs: Expr },
        #[language_host::syntax("{lhs} < {rhs}")]
        #[language_host::seqstrict]
        Lt { lhs: Expr, rhs: Expr },
        #[language_host::syntax("{lhs} == {rhs}")]
        #[language_host::seqstrict]
        Eq { lhs: Expr, rhs: Expr },
        #[language_host::syntax("{lhs} != {rhs}")]
        #[language_host::seqstrict]
        Ne { lhs: Expr, rhs: Expr },
        #[language_host::syntax("{lhs} && {rhs}")]
        #[language_host::strict(lhs)]
        And { lhs: Expr, rhs: Expr },
        #[language_host::syntax("{lhs} || {rhs}")]
        #[language_host::strict(lhs)]
        Or { lhs: Expr, rhs: Expr },
    }

    #[cfg_attr(
        not(test),
        expect(
            clippy::enum_glob_use,
            reason = "Readable rules import every constructor variant into the DSL scope; Clippy exempts test targets."
        )
    )]
    use Op::*;

    language_host::rules! {
        for Expr;

        /// Evaluate integer negation after strictness has produced a value.
        eval_neg:     Neg { value }           => int::sub(0, value);
        #[language_host::rule(owise, label = "eval-not")]
        eval_not:     Not { value }           => bool::not(value);

        eval_add:     Add { lhs, rhs }        => int::add(lhs, rhs);
        eval_sub:     Sub { lhs, rhs }        => int::sub(lhs, rhs);
        eval_mul:     Mul { lhs, rhs }        => int::mul(lhs, rhs);
        eval_div:     Div { lhs, rhs }        => int::div(lhs, rhs);

        eval_ge:      Ge { lhs, rhs }         => int::ge(lhs, rhs);
        eval_gt:      Gt { lhs, rhs }         => int::gt(lhs, rhs);
        eval_le:      Le { lhs, rhs }         => int::le(lhs, rhs);
        eval_lt:      Lt { lhs, rhs }         => int::lt(lhs, rhs);

        eval_bool_eq: Eq { lhs, rhs }         => bool::eq(lhs, rhs) where lhs: Bool, rhs: Bool;
        eval_int_eq:  Eq { lhs, rhs }         => int::eq(lhs, rhs)  where lhs: Int,  rhs: Int;
        eval_bool_ne: Ne { lhs, rhs }         => bool::ne(lhs, rhs) where lhs: Bool, rhs: Bool;
        eval_int_ne:  Ne { lhs, rhs }         => int::ne(lhs, rhs)  where lhs: Int,  rhs: Int;

        and_true:     And { lhs: true, rhs }  => rhs;
        and_false:    And { lhs: false, .. }  => false;
        or_true:      Or { lhs: true, .. }    => true;
        or_false:     Or { lhs: false, rhs }  => rhs;

    }

    fn _sort_narrowing_paths_are_block_local(_: Option<Value>) {}

    #[language_host::constructors(sort = Stmt, result = KResult)]
    #[language_host::precedence(
        stmt (Assign, IfThenElse, IfThen, While, Block, EmptyBlock)
        > right seq_stmt (Sequence)
    )]
    #[expect(
        dead_code,
        reason = "The compile fixture checks the authored surface without executing every declaration."
    )]
    pub enum StmtSyntax {
        #[language_host::syntax("{name} = {value};")]
        #[language_host::strict(value)]
        Assign { name: Id, value: Expr },
        #[language_host::syntax("if ({condition}) {then_branch} else {else_branch}", avoid)]
        #[language_host::strict(condition)]
        IfThenElse {
            condition: Expr,
            then_branch: Stmt,
            else_branch: Stmt,
        },
        #[language_host::syntax("if ({condition}) {body}")]
        IfThen { condition: Expr, body: Stmt },
        #[language_host::syntax("while ({condition}) {body}")]
        While { condition: Expr, body: Stmt },
        #[language_host::syntax("{{{body}}}")]
        #[language_host::format("{{%i%n{body}%d%n}}")]
        Block { body: Stmt },
        #[language_host::syntax("{{}}")]
        EmptyBlock(),
        #[language_host::syntax("{first} {second}")]
        #[language_host::format("{first}%n{second}")]
        Sequence { first: Stmt, second: Stmt },
    }

    #[cfg_attr(
        not(test),
        expect(
            clippy::enum_glob_use,
            reason = "Readable rules import every constructor variant into the DSL scope; Clippy exempts test targets."
        )
    )]
    use StmtSyntax::*;

    #[language_host::configuration]
    pub struct ReadableRuleMachine {
        #[language_host::cell]
        pub computation: KSequence,
        #[language_host::cell]
        pub env: Map<Id, Value>,
    }

    #[expect(
        dead_code,
        reason = "The compile fixture checks the authored surface without executing every declaration."
    )]
    impl ReadableRuleMachine {
        #[language_host::init]
        pub fn init(pgm: Stmt, env: Map<Id, Value>) -> Self {
            Self {
                computation: k![pgm],
                env,
            }
        }
    }

    language_host::rules! {
        for Stmt;

        step:     Sequence(s1, s2) => k![s1, s2];
        if_true:  IfThenElse(true, s1, _)  => s1;
        if_false: IfThenElse(false, _, s2) => s2;
        if_else:  IfThen(c, s) => StmtSyntax::IfThenElse(c, s, StmtSyntax::EmptyBlock());
        r#while:  While(c, s) => StmtSyntax::IfThen(c, StmtSyntax::Block(StmtSyntax::Sequence(s, StmtSyntax::While(c, s))));
        block:    Block(s) => k![s, StmtSyntax::EmptyBlock()];
        done:     EmptyBlock() => ();

    }

    language_host::rules! {
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

    use language_host::builtin::map::update as persistent_update;
    use language_host::configuration::{Cell, KCell};
    use language_host::map;

    #[language_host::rule]
    fn explicit_step(
        s1: language_host::Term<Stmt>,
        s2: language_host::Term<Stmt>,
        language_host::cells! {
            computation: KCell(StmtSyntax::Sequence(s1, s2), tail @ ..),
            state @ ..
        }: ReadableRuleMachine,
    ) -> ReadableRuleMachine {
        language_host::cells! {
            computation: KCell(s1, s2, ..tail),
            ..state
        }
    }

    #[language_host::rule]
    fn explicit_if_true(
        s1: language_host::Term<Stmt>,
        language_host::cells! {
            computation: KCell(StmtSyntax::IfThenElse(true, s1, _), tail @ ..),
            state @ ..
        }: ReadableRuleMachine,
    ) -> ReadableRuleMachine {
        language_host::cells! { computation: KCell(s1, ..tail), ..state }
    }

    #[language_host::rule]
    fn explicit_if_false(
        s2: language_host::Term<Stmt>,
        language_host::cells! {
            computation: KCell(StmtSyntax::IfThenElse(false, _, s2), tail @ ..),
            state @ ..
        }: ReadableRuleMachine,
    ) -> ReadableRuleMachine {
        language_host::cells! { computation: KCell(s2, ..tail), ..state }
    }

    #[language_host::rule]
    fn explicit_if_else(
        c: language_host::Term<Expr>,
        s: language_host::Term<Stmt>,
        language_host::cells! {
            computation: KCell(StmtSyntax::IfThen(c, s), tail @ ..),
            state @ ..
        }: ReadableRuleMachine,
    ) -> ReadableRuleMachine {
        language_host::cells! {
            computation: KCell(
                StmtSyntax::IfThenElse(c, s, StmtSyntax::EmptyBlock()),
                ..tail
            ),
            ..state
        }
    }

    #[language_host::rule]
    fn explicit_while(
        c: language_host::Term<Expr>,
        s: language_host::Term<Stmt>,
        language_host::cells! {
            computation: KCell(StmtSyntax::While(c, s), tail @ ..),
            state @ ..
        }: ReadableRuleMachine,
    ) -> ReadableRuleMachine {
        language_host::cells! {
            computation: KCell(
                StmtSyntax::IfThen(
                    c,
                    StmtSyntax::Block(StmtSyntax::Sequence(
                        s,
                        StmtSyntax::While(c, s)
                    ))
                ),
                ..tail
            ),
            ..state
        }
    }

    #[language_host::rule]
    fn explicit_block(
        s: language_host::Term<Stmt>,
        language_host::cells! {
            computation: KCell(StmtSyntax::Block(s), tail @ ..),
            state @ ..
        }: ReadableRuleMachine,
    ) -> ReadableRuleMachine {
        language_host::cells! {
            computation: KCell(s, StmtSyntax::EmptyBlock(), ..tail),
            ..state
        }
    }

    #[language_host::rule]
    fn explicit_done(
        language_host::cells! {
            computation: KCell(StmtSyntax::EmptyBlock(), tail @ ..),
            state @ ..
        }: ReadableRuleMachine,
    ) -> ReadableRuleMachine {
        language_host::cells! { computation: KCell(..tail), ..state }
    }

    #[language_host::rule]
    fn explicit_var(
        name: language_host::Term<Id>,
        value: language_host::Term<Value>,
        language_host::cells! {
            computation: KCell(name, tail @ ..),
            env: Cell(map![name -> value, rest @ ..]),
            state @ ..
        }: ReadableRuleMachine,
    ) -> ReadableRuleMachine {
        language_host::cells! {
            computation: KCell(value, ..tail),
            ..state
        }
    }

    #[language_host::rule]
    fn explicit_assign(
        name: language_host::Term<Id>,
        value: language_host::Term<Value>,
        e: language_host::Term<language_host::builtin::Map>,
        language_host::cells! {
            computation: KCell(StmtSyntax::Assign(name, value), tail @ ..),
            env: Cell(e),
            state @ ..
        }: ReadableRuleMachine,
    ) -> ReadableRuleMachine {
        language_host::cells! {
            computation: KCell(..tail),
            env: Cell(persistent_update(e, name, value)),
            ..state
        }
    }
}

mod standalone_island_hygiene {
    use super::{Cell, Halt, KCell, Machine};
    use krs_macros::{cells, map};

    #[expect(
        dead_code,
        reason = "The compile fixture checks the authored surface without executing every declaration."
    )]
    fn checked() -> Machine {
        cells! {
            k: KCell(Halt),
            env: Cell(map![.Map])
        }
    }
}

static RUNTIME_CELL_CONSTRUCTIONS: AtomicUsize = AtomicUsize::new(0);

mod instrumented {
    use std::marker::PhantomData;

    use super::{Ordering, RUNTIME_CELL_CONSTRUCTIONS};

    pub struct KCell<T> {
        marker: PhantomData<fn() -> T>,
    }

    impl KCell<language_host::builtin::KSequence> {
        pub fn new(_contents: language_host::builtin::KSequence) -> Self {
            RUNTIME_CELL_CONSTRUCTIONS.fetch_add(1, Ordering::SeqCst);
            Self {
                marker: PhantomData,
            }
        }
    }
}

#[language_host::sort]
pub trait KItem {}

#[language_host::sort]
#[language_host::bracket("({value})")]
pub trait Expr: KItem {}

#[language_host::sort]
pub trait KResult: KItem {}

#[language_host::sort]
pub trait Value: Expr + KResult {}

#[language_host::symbol("api::Halt")]
#[language_host::constructor(sort = Expr, syntax = "halt", group = "atoms")]
pub struct Halt;

#[language_host::constructor(
    sort = Expr,
    syntax = "{second} pair {first}",
    group = "pair",
    avoid = true,
    format = "%1 %2 %3"
)]
#[language_host::seqstrict(sequence = [first, second], result = KResult)]
pub struct Pair {
    pub first: Term<dyn Expr>,
    pub second: Term<dyn Expr>,
}

#[language_host::constructor(sort = Expr, syntax = "wrap({value})")]
pub struct Wrap {
    pub value: Term<dyn Expr>,
}

#[language_host::constructor(sort = Expr, syntax = "guarded({value})")]
pub struct Guarded {
    pub value: Term<language_host::builtin::int::Int>,
}

#[language_host::function(total, sort = language_host::builtin::int::Int, syntax = "#increment({value})")]
pub struct Increment {
    pub value: Term<language_host::builtin::int::Int>,
}

#[language_host::function(
    total,
    sort = language_host::builtin::Bytes,
    syntax = "Keccak256raw({value})",
    hook = krypto::keccak256_raw,
)]
pub struct Keccak256Raw {
    pub value: Term<language_host::builtin::Bytes>,
}

#[language_host::function(
    total,
    sort = language_host::builtin::Bytes,
    syntax = "Sha256raw({value})",
    hook = krypto::sha256_raw,
)]
pub struct Sha256Raw {
    pub value: Term<language_host::builtin::Bytes>,
}

#[language_host::function(
    total,
    sort = language_host::builtin::Bytes,
    syntax = "Ripemd160raw({value})",
    hook = krypto::ripemd160_raw,
)]
pub struct Ripemd160Raw {
    pub value: Term<language_host::builtin::Bytes>,
}

#[language_host::function(
    total,
    sort = language_host::builtin::Bytes,
    syntax = "EcdsaRecover({hash}, {recovery}, {r}, {s})",
    hook = krypto::ecdsa_recover,
)]
pub struct EcdsaRecover {
    pub hash: Term<language_host::builtin::Bytes>,
    pub recovery: Term<language_host::builtin::int::Int>,
    pub r: Term<language_host::builtin::Bytes>,
    pub s: Term<language_host::builtin::Bytes>,
}

#[language_host::equation]
fn increment(
    language_host::term![Increment(value)]: Term<language_host::builtin::int::Int>,
) -> Term<language_host::builtin::int::Int> {
    language_host::builtin::int::add(value, 1)
}

#[language_host::token(regex = r"[a-zA-Z][a-zA-Z0-9_]*", prec = 2)]
pub struct Identifier(pub String);

impl KItem for Identifier {}
impl Expr for Identifier {}
impl KResult for Identifier {}

#[language_host::subsort]
impl Value for Identifier {}

#[language_host::constructors(sort = Value)]
pub enum Boolean {
    #[k::syntax("true", group = "atoms")]
    True,
    #[k::syntax("false", group = "atoms")]
    False,
    #[k::syntax("tag {value}", group = "atoms", format = "%1%2")]
    Tagged { value: Term<dyn Expr> },
}

impl KItem for Boolean {}
impl Expr for Boolean {}
impl KResult for Boolean {}
impl Value for Boolean {}

use Boolean as Truth;

language_host::precedence! {
    pair > atoms;
}

language_host::associativity! {
    left: pair;
    non_associative: atoms;
}

#[language_host::configuration(root = "machine")]
pub struct Machine {
    pub k: instrumented::KCell<language_host::builtin::KSequence>,
    #[k::cell(name = "environment", color = "blue")]
    pub env: language_host::configuration::Cell<
        language_host::builtin::Map<language_host::builtin::Id, Term<dyn Value>>,
    >,
}

impl Machine {
    #[language_host::init]
    pub fn init() -> Self {
        Self {
            k: instrumented::KCell::new(k![Halt]),
            env: language_host::configuration::Cell::new(krs_macros::map![]),
        }
    }
}

#[language_host::cell]
pub struct Store {
    pub env: language_host::configuration::Cell<
        language_host::builtin::Map<language_host::builtin::Id, Term<dyn Value>>,
    >,
}

#[language_host::configuration]
pub struct NestedMachine {
    pub k: language_host::configuration::KCell<language_host::builtin::KSequence>,
    pub store: Store,
}

impl NestedMachine {
    #[language_host::init]
    pub fn init() -> Self {
        Self {
            k: language_host::configuration::KCell::new(k![Halt]),
            store: Store {
                env: language_host::configuration::Cell::new(krs_macros::map![.Map]),
            },
        }
    }
}

#[language_host::configuration(root = "secondary")]
pub struct Secondary {
    pub k: language_host::configuration::KCell<language_host::builtin::KSequence>,
}

impl Secondary {
    #[language_host::init]
    pub fn init(#[language_host::config_var(name = "PGM", main)] program: Term<dyn KItem>) -> Self {
        Self {
            k: language_host::configuration::KCell::new(k![program]),
        }
    }
}

#[language_host::configuration]
pub struct TwoComputationMachine {
    pub first: language_host::configuration::KCell<language_host::builtin::KSequence>,
    pub second: language_host::configuration::KCell<language_host::builtin::KSequence>,
}

impl TwoComputationMachine {
    #[language_host::init]
    pub fn init() -> Self {
        Self {
            first: language_host::configuration::KCell::new(k![Halt]),
            second: language_host::configuration::KCell::new(k![]),
        }
    }
}

#[language_host::configuration]
pub struct ExplicitEquivalentMachine {
    pub k: language_host::configuration::KCell<language_host::builtin::KSequence>,
    pub env: language_host::configuration::Cell<
        language_host::builtin::Map<language_host::builtin::Id, readable_sorts::ReadableValue>,
    >,
}

impl ExplicitEquivalentMachine {
    #[language_host::init]
    pub fn init(
        #[language_host::config_var(name = "PGM", main)] pgm: readable_sorts::ReadableStmt,
        #[language_host::config_var(name = "ENV")] env: language_host::builtin::Map<
            language_host::builtin::Id,
            readable_sorts::ReadableValue,
        >,
    ) -> Self {
        Self {
            k: language_host::configuration::KCell::new(k![pgm]),
            env: language_host::configuration::Cell::new(env),
        }
    }
}

#[language_host::configuration]
pub struct ReadableEquivalentMachine {
    #[language_host::cell]
    pub k: language_host::builtin::KSequence,
    #[language_host::cell]
    pub env: language_host::builtin::Map<language_host::builtin::Id, readable_sorts::ReadableValue>,
}

impl ReadableEquivalentMachine {
    #[language_host::init]
    pub fn init(
        pgm: readable_sorts::ReadableStmt,
        env: language_host::builtin::Map<language_host::builtin::Id, readable_sorts::ReadableValue>,
    ) -> Self {
        Self { k: k![pgm], env }
    }
}

#[language_host::rule]
pub fn native_pair(Pair { first, second }: Term<dyn Expr>) -> Term<dyn Expr> {
    Pair {
        first: second,
        second: first,
    }
}

#[language_host::rule]
pub fn macro_pair(term![Pair { first, second }]: Term<dyn Expr>) -> Term<dyn Expr> {
    term![Wrap { value: first }]
}

#[language_host::rule]
pub fn binder_gap(
    term![Pair {
        first: 日本,
        second: nested::Done,
    }]: Term<dyn Expr>,
) -> Term<dyn Expr> {
    term![nested::Keep {
        value: 日本,
        marker: nested::Done
    }]
}

#[language_host::rule(label = "enum-false")]
pub fn enum_alias(Truth::False: Term<Boolean>) -> Term<Boolean> {
    Truth::True
}

#[language_host::rule]
pub fn enum_record(Truth::Tagged { value }: Term<Boolean>) -> Term<Boolean> {
    Truth::Tagged { value }
}

#[language_host::rule]
pub fn subject_wildcard(
    Pair {
        first: _,
        second: value,
    }: Term<dyn Expr>,
) -> Term<dyn Expr> {
    value
}

#[language_host::rule]
pub fn boolean_literal(
    false: Term<language_host::builtin::bool::Bool>,
) -> Term<language_host::builtin::bool::Bool> {
    true
}

#[language_host::rule]
pub fn builtin_application(
    term![Pair {
        first: lhs,
        second: rhs,
    }]: Term<dyn Expr>,
) -> Term<language_host::builtin::int::Int> {
    term![language_host::builtin::int::add(lhs, rhs)]
}

#[language_host::rule]
#[language_host::requires(language_host::builtin::int::gt(value, 0))]
pub fn guarded_term(Guarded { value }: Term<dyn Expr>) -> Term<dyn Expr> {
    Halt
}

#[language_host::rule(label = "state-var")]
pub fn whole_state_var(
    x: Term<language_host::builtin::Id>,
    value: Term<dyn Value>,
    cells! {
        k: KCell(x, tail @ ..),
        env: Cell(map![x -> value, rest @ ..]),
        state @ ..
    }: Machine,
) -> Machine {
    cells! {
        k: KCell(value, ..tail),
        ..state
    }
}

#[language_host::rule]
pub fn nested_state_var(
    x: Term<language_host::builtin::Id>,
    value: Term<dyn Value>,
    cells! {
        k: KCell(x, tail @ ..),
        Store::env: Cell(map![x -> value, rest @ ..]),
        state @ ..
    }: NestedMachine,
) -> NestedMachine {
    cells! {
        k: KCell(value, ..tail),
        ..state
    }
}

#[language_host::rule]
#[language_host::requires(language_host::builtin::int::gt(value, 0))]
pub fn guarded_state(
    value: Term<language_host::builtin::int::Int>,
    krs_macros::cells! {
        k: instrumented::KCell(value, tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    krs_macros::cells! {
        k: instrumented::KCell(value, ..tail),
        ..state
    }
}

#[language_host::rule]
pub fn whole_state_wildcard(
    value: Term<dyn Expr>,
    krs_macros::cells! {
        k: instrumented::KCell(Pair(value, _), tail @ ..),
        state @ ..
    }: Machine,
) -> Machine {
    krs_macros::cells! {
        k: instrumented::KCell(value, ..tail),
        ..state
    }
}

pub mod nested {
    use super::{Expr, Term};

    #[language_host::constructor(sort = Expr, syntax = "done")]
    pub struct Done;

    #[language_host::constructor(sort = Expr)]
    pub struct Keep {
        pub value: Term<dyn Expr>,
        pub marker: Term<dyn Expr>,
    }

    #[language_host::rule]
    pub fn stay(Done: Term<dyn Expr>) -> Term<dyn Expr> {
        Done
    }
}

#[expect(
    dead_code,
    reason = "The compile fixture checks the authored surface without executing every declaration."
)]
fn standalone_term(value: Term<dyn Expr>) -> Term<dyn Expr> {
    term![Wrap { value }]
}

fn main() {
    let mut descriptors = language_host::host_descriptors()
        .map(Result::unwrap)
        .collect::<Vec<_>>();
    descriptors.sort_by(|left, right| left.id.cmp(&right.id));
    for descriptor in &descriptors {
        println!(
            "{}|{}|{:?}|{}",
            descriptor.id.rust_module_path().join("::"),
            descriptor.id.item_name(),
            descriptor.id.item_kind(),
            descriptor.provenance.authored().len()
        );
    }
}

const _: fn() = readable_sorts::rust_membership_is_exact;
const _: fn() -> split_config::Split = split_config::Split::init;

#[cfg(test)]
mod tests {
    use super::*;
    use language_host::{
        FormatFragment, HostApplicationIdentity, HostDescriptorPayload, HostGrammarDescriptor,
        HostProductionAttribute, HostProductionItem, HostProductionOwner, HostTerm, ItemKind,
        ProtocolInitializerStateTerm, ProtocolRuleBindingKind, ProtocolRuleStateTerm,
        ProvenanceRole, SchemaVersion,
    };

    #[test]
    fn rust_membership_and_macro_signatures() {
        readable_sorts::rust_membership_is_exact();
        let _: fn(Term<dyn Expr>) -> Term<dyn Expr> = macro_pair;
        let _: fn() -> Machine = Machine::init;
        let _: fn(Term<dyn KItem>) -> Secondary = Secondary::init;
        let _: fn() -> TwoComputationMachine = TwoComputationMachine::init;
        let _: fn(
            readable_sorts::ReadableStmt,
            language_host::builtin::Map<language_host::builtin::Id, readable_sorts::ReadableValue>,
        ) -> ExplicitEquivalentMachine = ExplicitEquivalentMachine::init;
        let _: fn(
            readable_sorts::ReadableStmt,
            language_host::builtin::Map<language_host::builtin::Id, readable_sorts::ReadableValue>,
        ) -> ReadableEquivalentMachine = ReadableEquivalentMachine::init;
        let _: fn() -> split_config::Split = split_config::Split::init;
        let _: fn() -> NestedMachine = NestedMachine::init;
        let _: fn(Term<language_host::builtin::Id>, Term<dyn Value>, Machine) -> Machine =
            whole_state_var;
        let _: fn(
            Term<language_host::builtin::Id>,
            Term<dyn Value>,
            NestedMachine,
        ) -> NestedMachine = nested_state_var;
        let _: fn(Term<language_host::builtin::int::Int>, Machine) -> Machine = guarded_state;
        let _: fn(Term<dyn Expr>, Machine) -> Machine = whole_state_wildcard;
    }

    #[test]
    fn registry_counts_and_provenance() {
        let descriptors = sorted_descriptors();
        assert_eq!(descriptors.len(), 160);
        assert_eq!(kind_count(&descriptors, ItemKind::Sort), 15);
        assert_eq!(kind_count(&descriptors, ItemKind::Constructor), 35);
        assert_eq!(kind_count(&descriptors, ItemKind::Grammar), 50);
        assert_eq!(kind_count(&descriptors, ItemKind::Rule), 50);
        assert_eq!(kind_count(&descriptors, ItemKind::Equation), 1);
        assert_eq!(
            descriptors
                .iter()
                .filter(|descriptor| descriptor.id.item_kind() == ItemKind::Configuration)
                .count(),
            8
        );
        assert_eq!(kind_count(&descriptors, ItemKind::Cell), 1);
        assert!(
            descriptors
                .iter()
                .all(|descriptor| descriptor.protocol_version == SchemaVersion::CURRENT)
        );
        assert!(descriptors.iter().all(|descriptor| {
            descriptor.provenance.authored().iter().all(|anchor| {
                !krs_ir::DisplayPath::is_absolute_spelling(anchor.anchor().display_file())
            })
        }));
        assert_eq!(RUNTIME_CELL_CONSTRUCTIONS.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn framework_sort_identity() {
        let descriptors = sorted_descriptors();
        let framework_result = descriptors
            .iter()
            .find(|descriptor| {
                descriptor.id.package().cargo_name() == "krs"
                    && descriptor.id.item_name() == "KResult"
                    && descriptor.id.item_kind() == ItemKind::Sort
            })
            .expect("a readable KResult bound requests the framework identities");
        assert_eq!(
            framework_result
                .declared_type
                .expect("framework sorts expose an exact type identity")
                .resolve(),
            HostApplicationIdentity::Nominal(std::any::TypeId::of::<language_host::KResult>())
        );
        let HostDescriptorPayload::Sort(framework_result) = &framework_result.payload else {
            panic!("framework KResult must be a sort descriptor")
        };
        assert_eq!(framework_result.parents.len(), 1);
        assert_eq!(
            framework_result.parents[0].key.resolve(),
            std::any::TypeId::of::<language_host::KItem>()
        );
    }

    #[test]
    fn missing_and_ambiguous_implicit_rule_configuration() {
        let descriptors = sorted_descriptors();
        let context = krs_collector::PackageContext::new(
            "KRS-MACROS-POSITIVE",
            env!("CARGO_PKG_NAME"),
            env!("CARGO_PKG_VERSION"),
            "path+fixture",
            "krs_macros_positive",
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"),
        )
        .unwrap();
        let head_rules = descriptors
            .iter()
            .filter(|descriptor| matches!(descriptor.payload, HostDescriptorPayload::HeadRule(_)))
            .cloned()
            .collect::<Vec<_>>();
        let implicit_head_rules = head_rules
            .iter()
            .filter(|descriptor| {
                matches!(
                    &descriptor.payload,
                    HostDescriptorPayload::HeadRule(rule) if rule.head_sort.is_some()
                )
            })
            .cloned()
            .collect::<Vec<_>>();
        let missing_configuration = krs_collector::collect_host_descriptors_with_builtins(
            [context.clone()],
            implicit_head_rules.clone().into_iter().map(Ok),
            &language_host::builtin_registry(),
        )
        .unwrap_err();
        assert_eq!(
            missing_configuration.kind(),
            krs_collector::CollectionErrorKind::InvalidConfiguration
        );
        assert!(
            missing_configuration
                .detail()
                .contains("none was collected")
        );

        let mut ambiguous_descriptors = implicit_head_rules.clone();
        ambiguous_descriptors.extend(
            descriptors
                .iter()
                .filter(|descriptor| {
                    matches!(
                        descriptor.payload,
                        HostDescriptorPayload::FixedConfiguration(_)
                    ) && descriptor
                        .id
                        .rust_module_path()
                        .last()
                        .is_none_or(|module| module != "readable_imp_grammar")
                })
                .take(2)
                .cloned(),
        );
        let ambiguous_configuration = krs_collector::collect_host_descriptors_with_builtins(
            [context.clone()],
            ambiguous_descriptors.into_iter().map(Ok),
            &language_host::builtin_registry(),
        )
        .unwrap_err();
        assert!(
            ambiguous_configuration
                .detail()
                .contains("2 candidates were collected"),
            "{}",
            ambiguous_configuration.detail()
        );
    }

    #[test]
    fn local_configuration_does_not_imply_ownership() {
        let descriptors = sorted_descriptors();
        let context = package_context();
        let implicit_head_rules = implicit_head_rules(&descriptors);
        let local_configuration = descriptors
            .iter()
            .find(|descriptor| {
                descriptor.id.item_name() == "ReadableRuleMachine"
                    && matches!(
                        descriptor.payload,
                        HostDescriptorPayload::FixedConfiguration(_)
                    )
            })
            .cloned()
            .unwrap();
        let unrelated_configuration = descriptors
            .iter()
            .find(|descriptor| {
                descriptor.id.item_name() == "Machine"
                    && matches!(
                        descriptor.payload,
                        HostDescriptorPayload::FixedConfiguration(_)
                    )
            })
            .cloned()
            .unwrap();
        let local_is_not_ownership = krs_collector::collect_host_descriptors_with_builtins(
            [context.clone()],
            implicit_head_rules
                .iter()
                .cloned()
                .chain([local_configuration.clone(), unrelated_configuration])
                .map(Ok),
            &language_host::builtin_registry(),
        )
        .unwrap_err();
        assert!(
            local_is_not_ownership
                .detail()
                .contains("2 candidates were collected")
        );
    }

    #[test]
    fn explicit_rule_configuration_ownership() {
        let descriptors = sorted_descriptors();
        let context = package_context();
        let explicitly_owned_descriptors = descriptors
            .iter()
            .filter(|descriptor| {
                !matches!(descriptor.payload, HostDescriptorPayload::HeadRule(_))
                    || matches!(
                        &descriptor.payload,
                        HostDescriptorPayload::HeadRule(rule) if rule.configuration.is_some()
                    )
            })
            .cloned()
            .collect::<Vec<_>>();
        let explicitly_owned_bundle = krs_collector::collect_host_descriptors_with_builtins(
            [context.clone()],
            explicitly_owned_descriptors.into_iter().map(Ok),
            &language_host::builtin_registry(),
        )
        .expect("configuration-owned rules ignore unrelated fixed configurations");
        assert!(
            explicitly_owned_bundle
                .descriptors()
                .iter()
                .any(|descriptor| {
                    descriptor.id().item_kind() == ItemKind::Rule
                        && descriptor.id().item_name() == "assign"
                        && descriptor
                            .id()
                            .module_path()
                            .last()
                            .is_some_and(|module| module == "readable_imp_grammar")
                })
        );
    }

    #[test]
    fn computation_cell_selection() {
        let descriptors = sorted_descriptors();
        let context = package_context();
        let implicit_head_rules = implicit_head_rules(&descriptors);
        let local_configuration =
            descriptor(&descriptors, "ReadableRuleMachine", ItemKind::Configuration).clone();
        let mut no_computation = local_configuration.clone();
        let HostDescriptorPayload::FixedConfiguration(configuration) = &mut no_computation.payload
        else {
            unreachable!()
        };
        let language_host::ProtocolCellContent::Leaf { wrapper, .. } =
            &mut configuration.declaration.fields[0].content
        else {
            unreachable!()
        };
        *wrapper = language_host::CellWrapper::Cell;
        let language_host::ProtocolInitializerCellContent::Leaf { wrapper, value, .. } =
            &mut configuration.initializer.cells[0].content
        else {
            unreachable!()
        };
        *wrapper = language_host::CellWrapper::Cell;
        let language_host::ProtocolInitializerStateTerm::KSequence(sequence) = value else {
            unreachable!()
        };
        *value = language_host::ProtocolInitializerStateTerm::Term(sequence.items[0].value.clone());
        let sort_descriptors = descriptors
            .iter()
            .filter(|descriptor| descriptor.id.item_kind() == ItemKind::Sort)
            .cloned()
            .collect::<Vec<_>>();
        let no_computation = krs_collector::collect_host_descriptors_with_builtins(
            [context.clone()],
            sort_descriptors
                .iter()
                .cloned()
                .chain(implicit_head_rules.iter().cloned())
                .chain(std::iter::once(no_computation))
                .map(Ok),
            &language_host::builtin_registry(),
        )
        .unwrap_err();
        assert!(
            no_computation
                .detail()
                .contains("no matching top-level KCell<KSequence>"),
            "{}",
            no_computation.detail()
        );

        let two_computations = descriptors
            .iter()
            .find(|descriptor| descriptor.id.item_name() == "TwoComputationMachine")
            .cloned()
            .unwrap();
        let two_computations = krs_collector::collect_host_descriptors_with_builtins(
            [context.clone()],
            sort_descriptors
                .iter()
                .cloned()
                .chain(implicit_head_rules.iter().cloned())
                .chain(std::iter::once(two_computations))
                .map(Ok),
            &language_host::builtin_registry(),
        )
        .unwrap_err();
        assert!(
            two_computations
                .detail()
                .contains("2 matching top-level KCell<KSequence>"),
            "{}",
            two_computations.detail()
        );
    }

    #[test]
    fn registry_collection_is_order_independent() {
        let descriptors = sorted_descriptors();
        let context = package_context();
        let head_rules = head_rules(&descriptors);
        // This fixture intentionally registers several independent definitions.
        // Collect its broad descriptor audit without the definition-owned readable
        // head rules, then collect those rules with their one selected machine.
        let non_head_descriptors = descriptors
            .iter()
            .filter(|descriptor| !matches!(descriptor.payload, HostDescriptorPayload::HeadRule(_)))
            .cloned()
            .collect::<Vec<_>>();
        let bundle = krs_collector::collect_host_descriptors_with_builtins(
            [context.clone()],
            non_head_descriptors.clone().into_iter().map(Ok),
            &language_host::builtin_registry(),
        )
        .unwrap();
        let mut reversed_descriptors = non_head_descriptors;
        reversed_descriptors.reverse();
        let reversed_bundle = krs_collector::collect_host_descriptors_with_builtins(
            [context.clone()],
            reversed_descriptors.into_iter().map(Ok),
            &language_host::builtin_registry(),
        )
        .unwrap();
        assert_eq!(
            bundle.to_canonical_json().unwrap(),
            reversed_bundle.to_canonical_json().unwrap()
        );
        assert_eq!(
            bundle.descriptors().len(),
            descriptors.len() - head_rules.len()
        );
    }

    #[test]
    fn serialized_keccak_and_sha_hooks() {
        let descriptors = sorted_descriptors();
        let bundle = broad_bundle(&descriptors);
        let serialized_hook = bundle
            .descriptors()
            .iter()
            .find(|descriptor| descriptor.id().item_name() == "__krs_grammar_Keccak256Raw")
            .expect("hooked grammar survives host collection");
        let krs_ir::DescriptorPayload::Grammar(serialized_hook) = serialized_hook.payload() else {
            panic!("collected hooked descriptor must remain grammar")
        };
        let krs_ir::GrammarDescriptor::Production(serialized_hook) = serialized_hook.as_ref()
        else {
            panic!("collected hooked grammar must remain a production")
        };
        assert!(serialized_hook.attributes.iter().any(|attribute| matches!(
            attribute,
            krs_ir::DescriptorProductionAttribute::Hook {
                operation: krs_ir::HookOperation::KryptoKeccak256Raw,
                ..
            }
        )));
        let serialized_sha256_hook = bundle
            .descriptors()
            .iter()
            .find(|descriptor| descriptor.id().item_name() == "__krs_grammar_Sha256Raw")
            .expect("SHA-256 hook survives host collection");
        let krs_ir::DescriptorPayload::Grammar(serialized_sha256_hook) =
            serialized_sha256_hook.payload()
        else {
            panic!("collected SHA-256 hook descriptor must remain grammar")
        };
        let krs_ir::GrammarDescriptor::Production(serialized_sha256_hook) =
            serialized_sha256_hook.as_ref()
        else {
            panic!("collected SHA-256 hook grammar must remain a production")
        };
        assert!(
            serialized_sha256_hook
                .attributes
                .iter()
                .any(|attribute| matches!(
                    attribute,
                    krs_ir::DescriptorProductionAttribute::Hook {
                        operation: krs_ir::HookOperation::KryptoSha256Raw,
                        ..
                    }
                ))
        );
    }

    #[test]
    fn serialized_ripemd_and_ecdsa_hooks() {
        let descriptors = sorted_descriptors();
        let bundle = broad_bundle(&descriptors);
        let serialized_ripemd160_hook = bundle
            .descriptors()
            .iter()
            .find(|descriptor| descriptor.id().item_name() == "__krs_grammar_Ripemd160Raw")
            .expect("RIPEMD-160 hook survives host collection");
        let krs_ir::DescriptorPayload::Grammar(serialized_ripemd160_hook) =
            serialized_ripemd160_hook.payload()
        else {
            panic!("collected RIPEMD-160 hook descriptor must remain grammar")
        };
        let krs_ir::GrammarDescriptor::Production(serialized_ripemd160_hook) =
            serialized_ripemd160_hook.as_ref()
        else {
            panic!("collected RIPEMD-160 hook grammar must remain a production")
        };
        assert!(
            serialized_ripemd160_hook
                .attributes
                .iter()
                .any(|attribute| matches!(
                    attribute,
                    krs_ir::DescriptorProductionAttribute::Hook {
                        operation: krs_ir::HookOperation::KryptoRipemd160Raw,
                        ..
                    }
                ))
        );
        let serialized_ecdsa_recover_hook = bundle
            .descriptors()
            .iter()
            .find(|descriptor| descriptor.id().item_name() == "__krs_grammar_EcdsaRecover")
            .expect("ECDSA recovery hook survives host collection");
        let krs_ir::DescriptorPayload::Grammar(serialized_ecdsa_recover_hook) =
            serialized_ecdsa_recover_hook.payload()
        else {
            panic!("collected ECDSA recovery hook descriptor must remain grammar")
        };
        let krs_ir::GrammarDescriptor::Production(serialized_ecdsa_recover_hook) =
            serialized_ecdsa_recover_hook.as_ref()
        else {
            panic!("collected ECDSA recovery hook grammar must remain a production")
        };
        assert!(
            serialized_ecdsa_recover_hook
                .attributes
                .iter()
                .any(|attribute| matches!(
                    attribute,
                    krs_ir::DescriptorProductionAttribute::Hook {
                        operation: krs_ir::HookOperation::KryptoEcdsaRecover,
                        ..
                    }
                ))
        );
    }

    #[test]
    fn semantic_hooked_grammar() {
        let descriptors = sorted_descriptors();
        let context = package_context();
        let readable_descriptors = descriptors
            .iter()
            .filter(|descriptor| {
                matches!(
                    descriptor.id.item_kind(),
                    ItemKind::Sort | ItemKind::Constructor | ItemKind::Grammar
                ) || (descriptor.id.item_kind() == ItemKind::Configuration
                    && descriptor.id.item_name() == "ReadableRuleMachine")
                    || (descriptor.id.item_kind() == ItemKind::Rule
                        && descriptor
                            .id
                            .rust_module_path()
                            .last()
                            .is_some_and(|module| module == "readable_imp_grammar"))
            })
            .cloned()
            .collect::<Vec<_>>();
        let readable_bundle = krs_collector::collect_host_descriptors_with_builtins(
            [context.clone()],
            readable_descriptors.into_iter().map(Ok),
            &language_host::builtin_registry(),
        )
        .unwrap();
        let semantic = krs_compiler::lower_descriptor_bundle(&readable_bundle).unwrap();
        let semantic_hook = semantic
            .modules()
            .iter()
            .flat_map(krs_ir_levels::SemanticModule::productions)
            .find(|production| production.id().item_name() == "Keccak256Raw")
            .expect("hooked production survives Semantic IR lowering");
        assert!(semantic_hook.attributes().iter().any(|attribute| matches!(
            attribute,
            krs_ir::ProductionAttribute::Hook {
                operation: krs_ir::HookOperation::KryptoKeccak256Raw,
                ..
            }
        )));
        let semantic_sha256_hook = semantic
            .modules()
            .iter()
            .flat_map(krs_ir_levels::SemanticModule::productions)
            .find(|production| production.id().item_name() == "Sha256Raw")
            .expect("SHA-256 hook survives Semantic IR lowering");
        assert!(
            semantic_sha256_hook
                .attributes()
                .iter()
                .any(|attribute| matches!(
                    attribute,
                    krs_ir::ProductionAttribute::Hook {
                        operation: krs_ir::HookOperation::KryptoSha256Raw,
                        ..
                    }
                ))
        );
        let semantic_ripemd160_hook = semantic
            .modules()
            .iter()
            .flat_map(krs_ir_levels::SemanticModule::productions)
            .find(|production| production.id().item_name() == "Ripemd160Raw")
            .expect("RIPEMD-160 hook survives Semantic IR lowering");
        assert!(
            semantic_ripemd160_hook
                .attributes()
                .iter()
                .any(|attribute| matches!(
                    attribute,
                    krs_ir::ProductionAttribute::Hook {
                        operation: krs_ir::HookOperation::KryptoRipemd160Raw,
                        ..
                    }
                ))
        );
        let semantic_ecdsa_recover_hook = semantic
            .modules()
            .iter()
            .flat_map(krs_ir_levels::SemanticModule::productions)
            .find(|production| production.id().item_name() == "EcdsaRecover")
            .expect("ECDSA recovery hook survives Semantic IR lowering");
        assert!(
            semantic_ecdsa_recover_hook
                .attributes()
                .iter()
                .any(|attribute| matches!(
                    attribute,
                    krs_ir::ProductionAttribute::Hook {
                        operation: krs_ir::HookOperation::KryptoEcdsaRecover,
                        ..
                    }
                ))
        );
    }

    #[test]
    fn semantic_readable_rules() {
        let descriptors = sorted_descriptors();
        let readable_bundle = readable_bundle(&descriptors);
        let semantic = krs_compiler::lower_descriptor_bundle(&readable_bundle).unwrap();
        let expression_rules = semantic
            .modules()
            .iter()
            .flat_map(krs_ir_levels::SemanticModule::rules)
            .filter(|rule| {
                rule.id()
                    .module_path()
                    .last()
                    .is_some_and(|module| module == "readable_imp_grammar")
            })
            .collect::<Vec<_>>();
        assert_eq!(expression_rules.len(), 36);
        let semantic_rule = |name: &str| {
            expression_rules
                .iter()
                .copied()
                .find(|rule| rule.id().item_name() == name)
                .unwrap_or_else(|| panic!("missing readable semantic rule `{name}`"))
        };
        for (readable, explicit) in [
            ("step", "explicit_step"),
            ("if_true", "explicit_if_true"),
            ("if_false", "explicit_if_false"),
            ("if_else", "explicit_if_else"),
            ("while", "explicit_while"),
            ("block", "explicit_block"),
            ("done", "explicit_done"),
            ("var", "explicit_var"),
            ("assign", "explicit_assign"),
        ] {
            assert_semantic_rule_equivalent(semantic_rule(readable), semantic_rule(explicit));
        }
        let eval_add = semantic_rule("eval_add");
        assert_eq!(
            eval_add
                .variables()
                .iter()
                .map(krs_ir_levels::SemanticVariable::sort)
                .collect::<Vec<_>>(),
            [
                &krs_ir_levels::SemanticSortRef::Builtin(language_host::BuiltinSort::Int),
                &krs_ir_levels::SemanticSortRef::Builtin(language_host::BuiltinSort::Int),
            ]
        );
        let krs_ir_levels::RuleBodyRef::Configuration { body: eval_add_body, .. } =
            eval_add.relational_body()
        else {
            panic!("eval_add must lower to one configuration rewrite")
        };
        let krs_ir::CellPost::Replace {
            term: eval_add_result,
        } = eval_add_body.clauses()[0].after()
        else {
            panic!("eval_add must replace its computation-cell head")
        };
        let krs_ir_levels::SemanticTermKind::KSequence { items, .. } = eval_add_result.kind() else {
            panic!("eval_add result must retain K-sequence structure")
        };
        assert!(matches!(
            items[0].kind(),
            krs_ir_levels::SemanticTermKind::Application {
                application: krs_ir::ApplicationRef::Builtin(
                    language_host::BuiltinOperation::IntAdd
                ),
                ..
            }
        ));
        assert_eq!(
            semantic_rule("eval_bool_eq")
                .variables()
                .iter()
                .map(krs_ir_levels::SemanticVariable::sort)
                .collect::<Vec<_>>(),
            [
                &krs_ir_levels::SemanticSortRef::Builtin(language_host::BuiltinSort::Bool),
                &krs_ir_levels::SemanticSortRef::Builtin(language_host::BuiltinSort::Bool),
            ]
        );
        assert_eq!(semantic_rule("and_false").variables().len(), 1);
        assert_eq!(
            semantic_rule("eval_not").label().unwrap().name(),
            "eval-not"
        );
        assert_eq!(semantic_rule("eval_not").priority().unwrap().value(), 200);
    }

    #[test]
    fn open_sort_analysis_and_semantic_configuration() {
        let descriptors = sorted_descriptors();
        let bundle = broad_bundle(&descriptors);
        let analysis = krs_compiler::analyze_open_sorts(&bundle).unwrap();
        assert_semantic_configuration_equivalent(&bundle);
        let diamond_id = bundle
            .descriptors()
            .iter()
            .find(|descriptor| descriptor.id().item_name() == "Diamond")
            .map(krs_ir::Descriptor::id)
            .expect("the readable diamond sort was collected");
        assert_eq!(analysis.direct_parents()[diamond_id].len(), 2);
        assert_eq!(analysis.transitive_parents()[diamond_id].len(), 3);
    }

    #[test]
    fn machine_configuration_and_initializer() {
        let descriptors = sorted_descriptors();
        let machine = descriptor(&descriptors, "Machine", ItemKind::Configuration);
        machine.validate_state_ownership().unwrap();
        let HostDescriptorPayload::FixedConfiguration(machine) = &machine.payload else {
            panic!("Machine must be a configuration descriptor")
        };
        assert!(matches!(
            &machine.root,
            language_host::DescriptorConfigurationRoot::Named { name, .. } if name == "machine"
        ));
        assert_eq!(machine.declaration.fields.len(), 2);
        assert_eq!(machine.declaration.fields[0].rust_field, "k");
        assert_eq!(machine.declaration.fields[1].rust_field, "env");
        assert_eq!(
            machine.declaration.fields[1]
                .emitted_name
                .as_ref()
                .unwrap()
                .value,
            "environment"
        );
        assert_eq!(
            machine.declaration.fields[1].color.as_ref().unwrap().value,
            "blue"
        );
        assert_eq!(machine.initializer.cells.len(), 2);
        assert!(machine.initializer.variables.is_empty());
        assert_eq!(
            machine.declaration.fields[0].reference.cell.resolve(),
            machine.initializer.cells[0].field.cell.resolve()
        );
        let language_host::ProtocolInitializerCellContent::Leaf { value, .. } =
            &machine.initializer.cells[0].content
        else {
            panic!("k initializer must be a leaf")
        };
        let ProtocolInitializerStateTerm::KSequence(sequence) = value else {
            panic!("k initializer must contain a K sequence")
        };
        assert_eq!(sequence.items.len(), 1);
        let HostTerm::Application { reference, .. } = &sequence.items[0].value.term else {
            panic!("Halt initializer must be a nominal reference")
        };
        assert_eq!(
            reference.target.resolve(),
            HostApplicationIdentity::Nominal(std::any::TypeId::of::<Halt>())
        );
        let machine_roles = machine
            .declaration
            .fields
            .iter()
            .map(|field| field.reference.key.role())
            .collect::<Vec<_>>();
        assert_eq!(
            machine_roles,
            [
                ProvenanceRole::ConfigurationField,
                ProvenanceRole::ConfigurationField
            ]
        );
        let descriptor_roles = descriptor(&descriptors, "Machine", ItemKind::Configuration)
            .provenance
            .authored()
            .iter()
            .map(|anchor| anchor.key().role())
            .collect::<Vec<_>>();
        assert!(descriptor_roles.contains(&ProvenanceRole::InitializerDeclaration));
        assert!(descriptor_roles.contains(&ProvenanceRole::InitializerTermPath));
    }

    #[test]
    fn secondary_initializer() {
        let descriptors = sorted_descriptors();
        let secondary = descriptor(&descriptors, "Secondary", ItemKind::Configuration);
        secondary.validate_state_ownership().unwrap();
        let HostDescriptorPayload::FixedConfiguration(secondary) = &secondary.payload else {
            panic!("Secondary must be a configuration descriptor")
        };
        let variable = &secondary.initializer.variables[0];
        assert_eq!(variable.binding, "program");
        assert_eq!(variable.external_name, "PGM");
        assert_eq!(
            variable.sort.key.role(),
            ProvenanceRole::ConfigurationVariableType
        );
        assert_eq!(variable.sort.key.ordinal(), 0);
        assert_eq!(
            variable.sort.target.key.resolve(),
            std::any::TypeId::of::<dyn KItem>()
        );
        assert!(variable.main_key.is_some());
    }

    #[test]
    fn readable_configuration_equivalence() {
        let descriptors = sorted_descriptors();
        let explicit_equivalent = descriptor(
            &descriptors,
            "ExplicitEquivalentMachine",
            ItemKind::Configuration,
        );
        explicit_equivalent.validate_state_ownership().unwrap();
        let HostDescriptorPayload::FixedConfiguration(explicit_equivalent) =
            &explicit_equivalent.payload
        else {
            panic!("ExplicitEquivalentMachine must be a fixed configuration")
        };
        let readable_equivalent = descriptor(
            &descriptors,
            "ReadableEquivalentMachine",
            ItemKind::Configuration,
        );
        readable_equivalent.validate_state_ownership().unwrap();
        let HostDescriptorPayload::FixedConfiguration(readable_equivalent) =
            &readable_equivalent.payload
        else {
            panic!("ReadableEquivalentMachine must be a fixed configuration")
        };
        assert_host_configuration_equivalent(explicit_equivalent, readable_equivalent);

        let explicit_roles = descriptor(
            &descriptors,
            "ExplicitEquivalentMachine",
            ItemKind::Configuration,
        )
        .provenance
        .authored()
        .iter()
        .map(|anchor| anchor.key().clone())
        .collect::<std::collections::BTreeSet<_>>();
        let readable_roles = descriptor(
            &descriptors,
            "ReadableEquivalentMachine",
            ItemKind::Configuration,
        )
        .provenance
        .authored()
        .iter()
        .map(|anchor| anchor.key().clone())
        .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(explicit_roles, readable_roles);
    }

    #[test]
    fn split_configuration_and_cell() {
        let descriptors = sorted_descriptors();
        let split = descriptor(&descriptors, "Split", ItemKind::Configuration);
        split.validate_state_ownership().unwrap();
        let HostDescriptorPayload::FixedConfiguration(_) = &split.payload else {
            panic!("Split must be a configuration descriptor")
        };
        assert_eq!(
            split.provenance.invocation().display_file(),
            "src/split_config.rs"
        );
        assert!(
            split
                .provenance
                .authored()
                .iter()
                .any(|anchor| anchor.key().role() == ProvenanceRole::InitializerDeclaration)
        );

        let store = descriptor(&descriptors, "Store", ItemKind::Cell);
        store.validate_state_ownership().unwrap();
        let HostDescriptorPayload::Cell(store) = &store.payload else {
            panic!("Store must be a nominal cell descriptor")
        };
        assert_eq!(store.fields.len(), 1);
    }

    #[test]
    fn configuration_and_guarded_rules() {
        let descriptors = sorted_descriptors();
        let nested_rule = descriptor(&descriptors, "nested_state_var", ItemKind::Rule);
        nested_rule.validate_state_ownership().unwrap();
        let HostDescriptorPayload::ConfigurationRule(nested_rule) = &nested_rule.payload else {
            panic!("nested_state_var must be a configuration rule")
        };
        assert_eq!(nested_rule.subject.cells.len(), 2);
        assert_eq!(
            nested_rule.subject.cells[1].field.cell.owner.resolve(),
            std::any::TypeId::of::<Store>()
        );

        let whole = descriptor(&descriptors, "whole_state_var", ItemKind::Rule);
        whole.validate_state_ownership().unwrap();
        let HostDescriptorPayload::ConfigurationRule(whole) = &whole.payload else {
            panic!("whole_state_var must be a configuration rule")
        };
        assert_eq!(whole.label.as_ref().unwrap().name, "state-var");
        assert_eq!(
            whole.label.as_ref().unwrap().key.role(),
            ProvenanceRole::RuleLabel
        );
        assert_eq!(whole.bindings.len(), 5);
        assert!(matches!(
            whole.bindings[0].kind,
            ProtocolRuleBindingKind::Term { .. }
        ));
        assert!(matches!(
            whole.bindings[1].kind,
            ProtocolRuleBindingKind::KSequenceFrame
        ));
        assert!(matches!(
            whole.subject.cells[1].value,
            ProtocolRuleStateTerm::Map(_)
        ));

        let guarded = descriptor(&descriptors, "guarded_term", ItemKind::Rule);
        guarded.validate_state_ownership().unwrap();
        let HostDescriptorPayload::StructuredRule(guarded) = &guarded.payload else {
            panic!("guarded_term must be a structured rule")
        };
        let condition = guarded
            .requires
            .as_ref()
            .expect("ordinary guard is retained");
        assert_eq!(condition.key.role(), ProvenanceRole::RuleRequires);
        assert!(matches!(
            condition.term,
            HostTerm::Application { ref path_key, .. }
                if path_key.role() == ProvenanceRole::RuleRequiresPath
        ));

        let guarded = descriptor(&descriptors, "guarded_state", ItemKind::Rule);
        guarded.validate_state_ownership().unwrap();
        let HostDescriptorPayload::ConfigurationRule(guarded) = &guarded.payload else {
            panic!("guarded_state must be a configuration rule")
        };
        assert_eq!(
            guarded.requires.as_ref().unwrap().key.role(),
            ProvenanceRole::RuleRequires
        );

        let wildcard = descriptor(&descriptors, "whole_state_wildcard", ItemKind::Rule);
        wildcard.validate_state_ownership().unwrap();
        let HostDescriptorPayload::ConfigurationRule(wildcard) = &wildcard.payload else {
            panic!("whole_state_wildcard must be a configuration rule")
        };
        let ProtocolRuleStateTerm::KSequence(sequence) = &wildcard.subject.cells[0].value else {
            panic!("whole_state_wildcard must select the k cell")
        };
        let HostTerm::Application { arguments, .. } = &sequence.items[0].value else {
            panic!("whole-state wildcard must be nested in Pair")
        };
        let krs_ir::Arguments::Positional(arguments) = arguments else {
            panic!("Pair must have positional arguments")
        };
        assert!(matches!(arguments[1].as_ref(), HostTerm::Wildcard { .. }));
    }

    #[test]
    fn sort_parentage() {
        let descriptors = sorted_descriptors();
        let value = descriptor(&descriptors, "Value", ItemKind::Sort);
        let HostDescriptorPayload::Sort(value) = &value.payload else {
            panic!("Value must be a sort descriptor")
        };
        assert_eq!(value.parents.len(), 2);

        let readable_value = descriptor(&descriptors, "ReadableValue", ItemKind::Sort);
        let HostDescriptorPayload::Sort(readable_value) = &readable_value.payload else {
            panic!("ReadableValue must be a sort descriptor")
        };
        assert_eq!(readable_value.parents.len(), 2);
        let diamond = descriptor(&descriptors, "Diamond", ItemKind::Sort);
        let HostDescriptorPayload::Sort(diamond) = &diamond.payload else {
            panic!("Diamond must be a sort descriptor")
        };
        assert_eq!(diamond.parents.len(), 2);
    }

    #[test]
    fn bracket_and_subsort_grammar() {
        let descriptors = sorted_descriptors();
        let readable_bracket = descriptor(
            &descriptors,
            "__krs_grammar_bracket_ReadableExpr_0",
            ItemKind::Grammar,
        );
        let HostDescriptorPayload::Grammar(readable_bracket) = &readable_bracket.payload else {
            panic!("readable bracket must be a grammar descriptor")
        };
        let HostGrammarDescriptor::Production(readable_bracket) = readable_bracket.as_ref() else {
            panic!("readable bracket must be a production")
        };
        assert!(matches!(
            readable_bracket.items.as_slice(),
            [
                HostProductionItem::Terminal { text: open, .. },
                HostProductionItem::NonTerminal { .. },
                HostProductionItem::Terminal { text: close, .. },
            ] if open == "(" && close == ")"
        ));
        let explicit_bracket = descriptor(
            &descriptors,
            "__krs_grammar_bracket_Expr_0",
            ItemKind::Grammar,
        );
        let HostDescriptorPayload::Grammar(explicit_bracket) = &explicit_bracket.payload else {
            panic!("explicit bracket must be a grammar descriptor")
        };
        let HostGrammarDescriptor::Production(explicit_bracket) = explicit_bracket.as_ref() else {
            panic!("explicit bracket must be a production")
        };
        assert_eq!(explicit_bracket.items.len(), readable_bracket.items.len());
        assert_eq!(
            explicit_bracket
                .items
                .iter()
                .filter_map(|item| match item {
                    HostProductionItem::Terminal { text, .. } => Some(text),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            readable_bracket
                .items
                .iter()
                .filter_map(|item| match item {
                    HostProductionItem::Terminal { text, .. } => Some(text),
                    _ => None,
                })
                .collect::<Vec<_>>()
        );
        let subsort_descriptor = |subsort_type, supersort_type| {
            descriptors
                .iter()
                .find(|descriptor| {
                    matches!(
                        &descriptor.payload,
                        HostDescriptorPayload::Grammar(grammar)
                            if matches!(
                                grammar.as_ref(),
                                HostGrammarDescriptor::Subsort { subsort, supersort, .. }
                                    if subsort.target.key.resolve() == subsort_type
                                        && supersort.target.key.resolve() == supersort_type
                            )
                    )
                })
                .expect("the requested subsort descriptor is registered")
        };
        let explicit_membership = subsort_descriptor(
            std::any::TypeId::of::<Identifier>(),
            std::any::TypeId::of::<dyn Value>(),
        );
        let readable_membership = subsort_descriptor(
            std::any::TypeId::of::<language_host::builtin::Id>(),
            std::any::TypeId::of::<readable_sorts::ReadableExpr>(),
        );
        assert_eq!(
            readable_membership.id.item_name().as_bytes(),
            b"__krs_grammar_subsort(member=relative:Id;supersort=relative:ReadableExpr)"
        );
        assert_eq!(
            explicit_membership
                .provenance
                .authored()
                .iter()
                .map(|anchor| anchor.key().role())
                .collect::<Vec<_>>(),
            readable_membership
                .provenance
                .authored()
                .iter()
                .map(|anchor| anchor.key().role())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn constructor_fields_and_pair_grammar() {
        let descriptors = sorted_descriptors();
        let pair = descriptor(&descriptors, "Pair", ItemKind::Constructor);
        let HostDescriptorPayload::Constructor(pair) = &pair.payload else {
            panic!("Pair must be a constructor descriptor")
        };
        assert_eq!(pair.fields.len(), 2);
        assert_eq!(pair.fields[0].name, "first");
        assert_eq!(pair.fields[1].name, "second");

        let halt = descriptor(&descriptors, "Halt", ItemKind::Constructor);
        assert!(halt.provenance.authored().iter().any(|anchor| {
            anchor.key().role() == ProvenanceRole::StableSymbol && anchor.key().ordinal() == 0
        }));
        let halt_grammar = descriptor(&descriptors, "__krs_grammar_Halt", ItemKind::Grammar);
        assert!(halt_grammar.provenance.authored().iter().any(|anchor| {
            anchor.key().role() == ProvenanceRole::StableSymbol && anchor.key().ordinal() == 0
        }));

        let pair_grammar = descriptor(&descriptors, "__krs_grammar_Pair", ItemKind::Grammar);
        let HostDescriptorPayload::Grammar(pair_grammar) = &pair_grammar.payload else {
            panic!("Pair grammar descriptor has the wrong payload")
        };
        let HostGrammarDescriptor::Production(pair_production) = pair_grammar.as_ref() else {
            panic!("Pair grammar must be a production")
        };
        let HostProductionOwner::Constructor { constructor } = &pair_production.owner else {
            panic!("Pair production must have constructor ownership")
        };
        assert_eq!(
            constructor.target.resolve(),
            HostApplicationIdentity::Nominal(std::any::TypeId::of::<Pair>())
        );
        assert!(matches!(
            &pair_production.items[0],
            HostProductionItem::NonTerminal { field, .. } if field.as_str() == "second"
        ));
        assert!(matches!(
            &pair_production.items[2],
            HostProductionItem::NonTerminal { field, .. } if field.as_str() == "first"
        ));
        assert!(pair_production.attributes.iter().any(|attribute| matches!(
            attribute,
            HostProductionAttribute::Group { reference } if reference.group.as_str() == "pair"
        )));
    }

    #[test]
    fn function_hook_and_equation_grammar() {
        let descriptors = sorted_descriptors();
        let pair_production = pair_production(&descriptors);
        let function_grammar =
            descriptor(&descriptors, "__krs_grammar_Increment", ItemKind::Grammar);
        let HostDescriptorPayload::Grammar(function_grammar) = &function_grammar.payload else {
            panic!("Increment grammar descriptor has the wrong payload")
        };
        let HostGrammarDescriptor::Production(function_production) = function_grammar.as_ref()
        else {
            panic!("Increment grammar must be a production")
        };
        assert!(
            function_production
                .attributes
                .iter()
                .any(|attribute| matches!(attribute, HostProductionAttribute::Function { .. }))
        );
        assert!(
            function_production
                .attributes
                .iter()
                .any(|attribute| matches!(attribute, HostProductionAttribute::Total { .. }))
        );
        let hooked_descriptor = descriptor(
            &descriptors,
            "__krs_grammar_Keccak256Raw",
            ItemKind::Grammar,
        );
        assert!(
            hooked_descriptor
                .provenance
                .authored()
                .iter()
                .any(|anchor| {
                    anchor.key().role() == ProvenanceRole::FunctionHook
                        && anchor.key().ordinal() == 0
                })
        );
        let HostDescriptorPayload::Grammar(hooked_grammar) = &hooked_descriptor.payload else {
            panic!("Keccak256Raw grammar descriptor has the wrong payload")
        };
        let HostGrammarDescriptor::Production(hooked_production) = hooked_grammar.as_ref() else {
            panic!("Keccak256Raw grammar must be a production")
        };
        assert!(
            hooked_production
                .attributes
                .iter()
                .any(|attribute| matches!(
                    attribute,
                    HostProductionAttribute::Hook {
                        operation: language_host::HookOperation::KryptoKeccak256Raw,
                        ..
                    }
                ))
        );
        let equation = descriptor(&descriptors, "increment", ItemKind::Equation);
        let HostDescriptorPayload::StructuredRule(equation) = &equation.payload else {
            panic!("increment must be a structured equation descriptor")
        };
        assert_eq!(
            equation.sentence_kind,
            language_host::SentenceKind::Equation
        );
        assert!(
            pair_production
                .attributes
                .iter()
                .any(|attribute| matches!(attribute, HostProductionAttribute::Avoid { .. }))
        );
        assert!(pair_production.attributes.iter().any(|attribute| matches!(
            attribute,
            HostProductionAttribute::Format { fragments, .. } if fragments.len() == 5
        )));
        assert!(pair_production.attributes.iter().any(|attribute| matches!(
            attribute,
            HostProductionAttribute::Strictness { fields, .. }
                if fields.iter().map(|field| field.field.as_str()).collect::<Vec<_>>() == ["first", "second"]
        )));
    }

    #[test]
    fn enum_variant_constructor_identity() {
        let descriptors = sorted_descriptors();
        let false_constructor = descriptors
            .iter()
            .find(|descriptor| {
                descriptor.id.item_name() == "False"
                    && descriptor.id.item_kind() == ItemKind::Constructor
                    && descriptor.id.disambiguator() == "enum:Boolean"
            })
            .expect("False enum variant constructor is registered");
        assert_eq!(
            false_constructor
                .declared_type
                .expect("enum variants expose an exact declaration key")
                .resolve(),
            HostApplicationIdentity::EnumVariant {
                enum_type: std::any::TypeId::of::<Boolean>(),
                variant: Truth::__krs_variant_type_id_False(),
            }
        );
    }

    #[test]
    fn readable_constructor_and_grammar() {
        let descriptors = sorted_descriptors();
        assert!(!descriptors.iter().any(|descriptor| {
            descriptor
                .id
                .rust_module_path()
                .last()
                .is_some_and(|module| module == "readable_imp_grammar")
                && descriptor.id.item_name() == "Op"
                && descriptor.id.item_kind() == ItemKind::Sort
        }));
        let assign = descriptor(&descriptors, "Assign", ItemKind::Constructor);
        let HostDescriptorPayload::Constructor(assign) = &assign.payload else {
            panic!("readable Assign must be a constructor")
        };
        assert_eq!(
            assign.sort.target.key.resolve(),
            std::any::TypeId::of::<readable_sorts::ReadableStmt>()
        );
        assert_eq!(
            assign.fields[0].sort.key.resolve(),
            std::any::TypeId::of::<language_host::builtin::Id>()
        );
        let assign_grammar = descriptor(
            &descriptors,
            "__krs_grammar_StmtSyntax_Assign",
            ItemKind::Grammar,
        );
        let HostDescriptorPayload::Grammar(assign_grammar) = &assign_grammar.payload else {
            panic!("readable Assign grammar has the wrong payload")
        };
        let HostGrammarDescriptor::Production(assign_production) = assign_grammar.as_ref() else {
            panic!("readable Assign grammar must be a production")
        };
        assert!(
            assign_production
                .attributes
                .iter()
                .any(|attribute| matches!(
                    attribute,
                    HostProductionAttribute::Strictness { fields, result_sort, .. }
                        if fields.len() == 1
                            && fields[0].field.as_str() == "value"
                            && result_sort.target.key.resolve()
                                == std::any::TypeId::of::<language_host::KResult>()
                ))
        );
        assert!(
            assign_production
                .attributes
                .iter()
                .any(|attribute| matches!(
                    attribute,
                    HostProductionAttribute::Format { fragments, .. }
                        if fragments.iter().map(|fragment| &fragment.fragment).collect::<Vec<_>>()
                            == [
                                &FormatFragment::Item(1),
                                &FormatFragment::Literal(" ".to_owned()),
                                &FormatFragment::Item(2),
                                &FormatFragment::Literal(" ".to_owned()),
                                &FormatFragment::Item(3),
                                &FormatFragment::Item(4),
                            ]
                ))
        );
    }

    #[test]
    fn operator_precedence_and_associativity() {
        let descriptors = sorted_descriptors();
        let op_precedence = descriptor(
            &descriptors,
            "__krs_grammar_Op_precedence",
            ItemKind::Grammar,
        );
        let HostDescriptorPayload::Grammar(op_precedence) = &op_precedence.payload else {
            panic!("Op precedence has the wrong payload")
        };
        let HostGrammarDescriptor::Precedence { chains, .. } = op_precedence.as_ref() else {
            panic!("Op precedence must be a precedence declaration")
        };
        assert_eq!(chains.len(), 1);
        assert_eq!(
            chains[0]
                .groups
                .iter()
                .map(|group| group.group.as_str())
                .collect::<Vec<_>>(),
            [
                "op_tier0", "op_tier1", "op_tier2", "op_tier3", "op_tier4", "op_tier5", "op_tier6",
            ]
        );
        let op_associativity = descriptor(
            &descriptors,
            "__krs_grammar_Op_associativity",
            ItemKind::Grammar,
        );
        let HostDescriptorPayload::Grammar(op_associativity) = &op_associativity.payload else {
            panic!("Op associativity has the wrong payload")
        };
        let HostGrammarDescriptor::Associativity { sentences, .. } = op_associativity.as_ref()
        else {
            panic!("Op associativity must be an associativity declaration")
        };
        assert_eq!(sentences.len(), 6);
        assert_eq!(
            sentences
                .iter()
                .map(|sentence| sentence.associativity)
                .collect::<Vec<_>>(),
            [
                language_host::GroupAssociativity::Left,
                language_host::GroupAssociativity::Left,
                language_host::GroupAssociativity::Left,
                language_host::GroupAssociativity::Left,
                language_host::GroupAssociativity::Left,
                language_host::GroupAssociativity::Left,
            ]
        );
    }

    #[test]
    fn readable_head_rules() {
        let descriptors = sorted_descriptors();
        let eval_add = descriptor(&descriptors, "eval_add", ItemKind::Rule);
        assert_eq!(
            eval_add.id.rust_module_path().last().map(String::as_str),
            Some("readable_imp_grammar")
        );
        eval_add.validate_state_ownership().unwrap();
        let HostDescriptorPayload::HeadRule(eval_add) = &eval_add.payload else {
            panic!("readable eval_add must be a head-anchored rule")
        };
        assert_eq!(
            eval_add
                .head_sort
                .as_ref()
                .expect("the expression table has a head sort")
                .target
                .key
                .resolve(),
            std::any::TypeId::of::<readable_sorts::ReadableExpr>()
        );
        let HostTerm::Application { reference, .. } = &eval_add.subject else {
            panic!("readable eval_add subject must be an enum application")
        };
        assert_eq!(
            reference.target.resolve(),
            HostApplicationIdentity::EnumVariant {
                enum_type: std::any::TypeId::of::<readable_imp_grammar::Op>(),
                variant: readable_imp_grammar::Op::__krs_variant_type_id_Add(),
            }
        );
        let language_host::HostApplicationTarget::EnumVariant(target) = &reference.target else {
            panic!("module-scope Op glob must retain enum-variant ownership")
        };
        assert_eq!(target.authored_path(), "Op::Add");
        assert_eq!(target.enum_type().authored_path, "Op");
        let eval_not = descriptor(&descriptors, "eval_not", ItemKind::Rule);
        assert!(eval_not.provenance.authored().iter().any(|anchor| {
            anchor.key().role() == ProvenanceRole::RuleLabel && anchor.key().ordinal() == 0
        }));
        assert!(eval_not.provenance.authored().iter().any(|anchor| {
            anchor.key().role() == ProvenanceRole::RuleOwise && anchor.key().ordinal() == 0
        }));
        let HostDescriptorPayload::HeadRule(eval_not) = &eval_not.payload else {
            panic!("readable eval_not must be a head-anchored rule")
        };
        assert_eq!(eval_not.priority.as_ref().unwrap().value, 200);
        let and_false = descriptor(&descriptors, "and_false", ItemKind::Rule);
        let HostDescriptorPayload::HeadRule(and_false) = &and_false.payload else {
            panic!("readable and_false must be a head-anchored rule")
        };
        let HostTerm::Application { arguments, .. } = &and_false.subject else {
            panic!("readable and_false subject must be an enum application")
        };
        assert_eq!(arguments.len(), 1, "record `..` stays a partial subject");
    }

    #[test]
    fn statement_grammar_and_heads() {
        let descriptors = sorted_descriptors();
        let assign_production = assign_production(&descriptors);
        let stmt_precedence = descriptor(
            &descriptors,
            "__krs_grammar_StmtSyntax_precedence",
            ItemKind::Grammar,
        );
        let HostDescriptorPayload::Grammar(stmt_precedence) = &stmt_precedence.payload else {
            panic!("Stmt precedence has the wrong payload")
        };
        assert!(matches!(
            stmt_precedence.as_ref(),
            HostGrammarDescriptor::Precedence { chains, .. }
                if chains[0]
                    .groups
                    .iter()
                    .map(|group| group.group.as_str())
                    .collect::<Vec<_>>() == ["stmt", "seq_stmt"]
        ));
        let stmt_associativity = descriptor(
            &descriptors,
            "__krs_grammar_StmtSyntax_associativity",
            ItemKind::Grammar,
        );
        let HostDescriptorPayload::Grammar(stmt_associativity) = &stmt_associativity.payload else {
            panic!("Stmt associativity has the wrong payload")
        };
        assert!(matches!(
            stmt_associativity.as_ref(),
            HostGrammarDescriptor::Associativity { sentences, .. }
                if sentences
                    .iter()
                    .map(|sentence| sentence.associativity)
                    .collect::<Vec<_>>()
                    == [language_host::GroupAssociativity::Right]
        ));
        let readable_stmt_head = |name| {
            let descriptor = descriptor(&descriptors, name, ItemKind::Rule);
            let HostDescriptorPayload::HeadRule(rule) = &descriptor.payload else {
                panic!("{name} must be a readable head rule")
            };
            let HostTerm::Application { reference, .. } = &rule.subject else {
                panic!("{name} must have an application head")
            };
            reference.target.resolve()
        };
        assert_eq!(
            readable_stmt_head("step"),
            HostApplicationIdentity::EnumVariant {
                enum_type: std::any::TypeId::of::<readable_imp_grammar::StmtSyntax>(),
                variant: readable_imp_grammar::StmtSyntax::__krs_variant_type_id_Sequence(),
            }
        );
        assert_eq!(
            readable_stmt_head("done"),
            HostApplicationIdentity::EnumVariant {
                enum_type: std::any::TypeId::of::<readable_imp_grammar::StmtSyntax>(),
                variant: readable_imp_grammar::StmtSyntax::__krs_variant_type_id_EmptyBlock(),
            }
        );
        assert!(assign_production.attributes.iter().any(|attribute| matches!(
            attribute,
            HostProductionAttribute::Group { reference } if reference.group.as_str() == "stmt"
        )));
    }

    #[test]
    fn token_and_grammar_registration() {
        let descriptors = sorted_descriptors();
        let token_grammar = descriptor(
            &descriptors,
            "__krs_grammar_token_Identifier",
            ItemKind::Grammar,
        );
        let HostDescriptorPayload::Grammar(token_grammar) = &token_grammar.payload else {
            panic!("token grammar has the wrong payload")
        };
        let HostGrammarDescriptor::Production(token) = token_grammar.as_ref() else {
            panic!("token grammar must be a production")
        };
        assert!(matches!(token.owner, HostProductionOwner::TokenSort { .. }));
        assert!(matches!(
            &token.items[..],
            [HostProductionItem::RegexTerminal { regex, .. }] if regex == "[a-zA-Z][a-zA-Z0-9_]*"
        ));
        assert!(matches!(
            &token.attributes[..],
            [HostProductionAttribute::Token { lexical_precedence: Some(precedence), .. }]
                if precedence.value == 2
        ));

        assert!(descriptors.iter().any(|descriptor| {
            matches!(
                &descriptor.payload,
                HostDescriptorPayload::Grammar(grammar)
                    if matches!(grammar.as_ref(), HostGrammarDescriptor::Precedence { chains, .. } if chains.len() == 1)
            )
        }));
        assert!(descriptors.iter().any(|descriptor| {
            matches!(
                &descriptor.payload,
                HostDescriptorPayload::Grammar(grammar)
                    if matches!(grammar.as_ref(), HostGrammarDescriptor::Associativity { sentences, .. } if sentences.len() == 2)
            )
        }));
    }

    #[test]
    fn structured_rule_bindings_and_provenance() {
        let descriptors = sorted_descriptors();
        let gap_descriptor = descriptor(&descriptors, "binder_gap", ItemKind::Rule);
        let HostDescriptorPayload::StructuredRule(gap_rule) = &gap_descriptor.payload else {
            panic!("binder_gap must be a structured rule descriptor")
        };
        assert_eq!(gap_rule.bindings, ["日本"]);
        let keys = gap_descriptor
            .provenance
            .authored()
            .iter()
            .map(|anchor| (anchor.key().role(), anchor.key().ordinal()))
            .collect::<Vec<_>>();
        assert!(keys.contains(&(ProvenanceRole::RuleLeftPath, 0)));
        assert!(keys.contains(&(ProvenanceRole::RuleLeftPath, 1)));
        assert!(keys.contains(&(ProvenanceRole::RuleLeftPath, 2)));
        assert!(keys.contains(&(ProvenanceRole::RuleRightPath, 0)));
        assert!(keys.contains(&(ProvenanceRole::RuleRightPath, 1)));
        assert!(keys.contains(&(ProvenanceRole::RuleRightPath, 2)));
        assert!(keys.contains(&(ProvenanceRole::RuleLeftApplicationHead, 0)));
        assert!(keys.contains(&(ProvenanceRole::RuleRightApplicationHead, 0)));
        let nested_anchor = gap_descriptor
            .provenance
            .authored()
            .iter()
            .find(|anchor| {
                anchor.key().role() == ProvenanceRole::RuleRightPath && anchor.key().ordinal() == 2
            })
            .expect("nested path anchor exists")
            .anchor();
        let source_line = include_str!("main.rs")
            .lines()
            .nth((nested_anchor.start().line() - 1) as usize)
            .expect("anchor line exists");
        let nested_byte = source_line
            .find("nested::Done")
            .expect("nested path remains on the Unicode-bearing line");
        assert_eq!(
            nested_anchor.start().scalar_column() as usize,
            source_line[..nested_byte].chars().count() + 1
        );
    }

    #[test]
    fn structured_rule_terms() {
        let descriptors = sorted_descriptors();
        let enum_rule = descriptor(&descriptors, "enum_alias", ItemKind::Rule);
        let HostDescriptorPayload::StructuredRule(enum_rule) = &enum_rule.payload else {
            panic!("enum_alias must be structured")
        };
        assert_eq!(enum_rule.label.as_ref().unwrap().name, "enum-false");
        assert_eq!(
            enum_rule.label.as_ref().unwrap().key.role(),
            ProvenanceRole::RuleLabel
        );
        let HostTerm::Application { reference, .. } = &enum_rule.subject else {
            panic!("enum subject is a zero-argument application")
        };
        assert_eq!(
            reference.target.resolve(),
            HostApplicationIdentity::EnumVariant {
                enum_type: std::any::TypeId::of::<Boolean>(),
                variant: Truth::__krs_variant_type_id_False(),
            }
        );

        let record_rule = descriptor(&descriptors, "enum_record", ItemKind::Rule);
        let HostDescriptorPayload::StructuredRule(record_rule) = &record_rule.payload else {
            panic!("enum_record must be structured")
        };
        let HostTerm::Application { arguments, .. } = &record_rule.result else {
            panic!("enum record result must be an application")
        };
        let krs_ir::Arguments::Named(arguments) = arguments else {
            panic!("enum record must have named arguments")
        };
        assert_eq!(arguments.len(), 1);
        assert_eq!(arguments.first().field.as_str(), "value");

        let wildcard_rule = descriptor(&descriptors, "subject_wildcard", ItemKind::Rule);
        let HostDescriptorPayload::StructuredRule(wildcard_rule) = &wildcard_rule.payload else {
            panic!("subject_wildcard must be structured")
        };
        let HostTerm::Application { arguments, .. } = &wildcard_rule.subject else {
            panic!("wildcard subject must be an application")
        };
        let krs_ir::Arguments::Named(arguments) = arguments else {
            panic!("wildcard subject must have named arguments")
        };
        assert!(matches!(
            arguments.first().value.as_ref(),
            HostTerm::Wildcard { .. }
        ));

        let literal_rule = descriptor(&descriptors, "boolean_literal", ItemKind::Rule);
        let HostDescriptorPayload::StructuredRule(literal_rule) = &literal_rule.payload else {
            panic!("boolean_literal must be structured")
        };
        assert!(matches!(literal_rule.subject, HostTerm::Literal { .. }));
        assert!(matches!(literal_rule.result, HostTerm::Literal { .. }));

        let builtin_rule = descriptor(&descriptors, "builtin_application", ItemKind::Rule);
        let HostDescriptorPayload::StructuredRule(builtin_rule) = &builtin_rule.payload else {
            panic!("builtin_application must be structured")
        };
        let HostTerm::Application { reference, .. } = &builtin_rule.result else {
            panic!("builtin result must be an application")
        };
        assert_eq!(
            reference.target.resolve(),
            HostApplicationIdentity::Nominal(std::any::TypeId::of::<
                language_host::builtin::int::add,
            >())
        );
    }

    fn sorted_descriptors() -> Vec<language_host::HostDescriptor> {
        let mut descriptors = language_host::host_descriptors()
            .map(Result::unwrap)
            .collect::<Vec<_>>();
        descriptors.sort_by(|left, right| left.id.cmp(&right.id));
        descriptors
    }

    fn package_context() -> krs_collector::PackageContext {
        krs_collector::PackageContext::new(
            "KRS-MACROS-POSITIVE",
            env!("CARGO_PKG_NAME"),
            env!("CARGO_PKG_VERSION"),
            "path+fixture",
            "krs_macros_positive",
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"),
        )
        .unwrap()
    }

    fn head_rules(
        descriptors: &[language_host::HostDescriptor],
    ) -> Vec<language_host::HostDescriptor> {
        descriptors
            .iter()
            .filter(|descriptor| matches!(descriptor.payload, HostDescriptorPayload::HeadRule(_)))
            .cloned()
            .collect()
    }

    fn implicit_head_rules(
        descriptors: &[language_host::HostDescriptor],
    ) -> Vec<language_host::HostDescriptor> {
        head_rules(descriptors).into_iter().filter(|descriptor| matches!(&descriptor.payload, HostDescriptorPayload::HeadRule(rule) if rule.head_sort.is_some())).collect()
    }

    fn broad_bundle(descriptors: &[language_host::HostDescriptor]) -> krs_ir::DescriptorBundle {
        krs_collector::collect_host_descriptors_with_builtins(
            [package_context()],
            descriptors
                .iter()
                .filter(|descriptor| {
                    !matches!(descriptor.payload, HostDescriptorPayload::HeadRule(_))
                })
                .cloned()
                .map(Ok),
            &language_host::builtin_registry(),
        )
        .unwrap()
    }

    fn readable_bundle(descriptors: &[language_host::HostDescriptor]) -> krs_ir::DescriptorBundle {
        let readable_descriptors = descriptors
            .iter()
            .filter(|descriptor| {
                matches!(
                    descriptor.id.item_kind(),
                    ItemKind::Sort | ItemKind::Constructor | ItemKind::Grammar
                ) || (descriptor.id.item_kind() == ItemKind::Configuration
                    && descriptor.id.item_name() == "ReadableRuleMachine")
                    || (descriptor.id.item_kind() == ItemKind::Rule
                        && descriptor
                            .id
                            .rust_module_path()
                            .last()
                            .is_some_and(|module| module == "readable_imp_grammar"))
            })
            .cloned()
            .collect::<Vec<_>>();
        krs_collector::collect_host_descriptors_with_builtins(
            [package_context()],
            readable_descriptors.into_iter().map(Ok),
            &language_host::builtin_registry(),
        )
        .unwrap()
    }

    fn pair_production(
        descriptors: &[language_host::HostDescriptor],
    ) -> &language_host::HostProduction {
        let pair_grammar = descriptor(descriptors, "__krs_grammar_Pair", ItemKind::Grammar);
        let HostDescriptorPayload::Grammar(pair_grammar) = &pair_grammar.payload else {
            panic!("Pair grammar has the wrong payload")
        };
        let HostGrammarDescriptor::Production(pair_production) = pair_grammar.as_ref() else {
            panic!("Pair grammar must be a production")
        };
        pair_production
    }

    fn assign_production(
        descriptors: &[language_host::HostDescriptor],
    ) -> &language_host::HostProduction {
        let assign_grammar = descriptor(
            descriptors,
            "__krs_grammar_StmtSyntax_Assign",
            ItemKind::Grammar,
        );
        let HostDescriptorPayload::Grammar(assign_grammar) = &assign_grammar.payload else {
            panic!("Assign grammar has the wrong payload")
        };
        let HostGrammarDescriptor::Production(assign_production) = assign_grammar.as_ref() else {
            panic!("Assign grammar must be a production")
        };
        assign_production
    }

    fn kind_count(descriptors: &[language_host::HostDescriptor], kind: ItemKind) -> usize {
        descriptors
            .iter()
            .filter(|descriptor| descriptor.id.item_kind() == kind)
            .count()
    }

    fn descriptor<'a>(
        descriptors: &'a [language_host::HostDescriptor],
        name: &str,
        kind: ItemKind,
    ) -> &'a language_host::HostDescriptor {
        descriptors
            .iter()
            .find(|descriptor| {
                descriptor.id.item_name() == name && descriptor.id.item_kind() == kind
            })
            .unwrap_or_else(|| panic!("missing {kind:?} descriptor `{name}`"))
    }

    fn assert_host_configuration_equivalent(
        explicit: &language_host::HostFixedConfiguration,
        readable: &language_host::HostFixedConfiguration,
    ) {
        assert!(matches!(
            (&explicit.root, &readable.root),
            (
                language_host::DescriptorConfigurationRoot::GeneratedTop,
                language_host::DescriptorConfigurationRoot::GeneratedTop
            )
        ));
        assert_eq!(
            explicit.declaration.fields.len(),
            readable.declaration.fields.len()
        );
        for (explicit, readable) in explicit
            .declaration
            .fields
            .iter()
            .zip(&readable.declaration.fields)
        {
            assert_eq!(explicit.rust_field, readable.rust_field);
            assert_eq!(
                explicit.emitted_name.as_ref().map(|name| &name.value),
                readable.emitted_name.as_ref().map(|name| &name.value)
            );
            match (&explicit.content, &readable.content) {
                (
                    language_host::ProtocolCellContent::Leaf {
                        wrapper: explicit_wrapper,
                        sort: explicit_sort,
                        ..
                    },
                    language_host::ProtocolCellContent::Leaf {
                        wrapper: readable_wrapper,
                        sort: readable_sort,
                        ..
                    },
                ) => {
                    assert_eq!(explicit_wrapper, readable_wrapper);
                    assert_eq!(
                        explicit_sort.target.key.resolve(),
                        readable_sort.target.key.resolve()
                    );
                }
                _ => panic!("equivalent configurations must use the same leaf shape"),
            }
        }

        assert_eq!(
            explicit.initializer.variables.len(),
            readable.initializer.variables.len()
        );
        for (explicit, readable) in explicit
            .initializer
            .variables
            .iter()
            .zip(&readable.initializer.variables)
        {
            assert_eq!(explicit.binding, readable.binding);
            assert_eq!(explicit.external_name, readable.external_name);
            assert_eq!(
                explicit.sort.target.key.resolve(),
                readable.sort.target.key.resolve()
            );
            assert_eq!(explicit.main_key.is_some(), readable.main_key.is_some());
        }

        assert_eq!(
            explicit.initializer.cells.len(),
            readable.initializer.cells.len()
        );
        for (explicit, readable) in explicit
            .initializer
            .cells
            .iter()
            .zip(&readable.initializer.cells)
        {
            let (
                language_host::ProtocolInitializerCellContent::Leaf {
                    wrapper: explicit_wrapper,
                    value: explicit_value,
                    ..
                },
                language_host::ProtocolInitializerCellContent::Leaf {
                    wrapper: readable_wrapper,
                    value: readable_value,
                    ..
                },
            ) = (&explicit.content, &readable.content)
            else {
                panic!("equivalent initializers must use the same leaf shape")
            };
            assert_eq!(explicit_wrapper, readable_wrapper);
            assert_initializer_state_equivalent(explicit_value, readable_value);
        }
    }

    fn assert_initializer_state_equivalent(
        explicit: &language_host::HostInitializerStateTerm,
        readable: &language_host::HostInitializerStateTerm,
    ) {
        match (explicit, readable) {
            (
                language_host::ProtocolInitializerStateTerm::KSequence(explicit),
                language_host::ProtocolInitializerStateTerm::KSequence(readable),
            ) => {
                assert_eq!(explicit.notation, readable.notation);
                assert_eq!(explicit.items.len(), readable.items.len());
                for (explicit, readable) in explicit.items.iter().zip(&readable.items) {
                    assert_eq!(
                        host_variable_name(&explicit.value.term),
                        host_variable_name(&readable.value.term)
                    );
                }
            }
            (
                language_host::ProtocolInitializerStateTerm::Term(explicit),
                language_host::ProtocolInitializerStateTerm::Term(readable),
            ) => assert_eq!(
                host_variable_name(&explicit.term),
                host_variable_name(&readable.term)
            ),
            _ => panic!("equivalent initializers must use the same state family"),
        }
    }

    fn host_variable_name(term: &HostTerm) -> &str {
        let HostTerm::Variable { name, .. } = term else {
            panic!("equivalence fixture initializers contain only variables")
        };
        name
    }

    fn assert_semantic_configuration_equivalent(bundle: &krs_ir::DescriptorBundle) {
        let lower = |configuration_name: &str| {
            let descriptors = bundle
                .descriptors()
                .iter()
                .filter(|descriptor| {
                    descriptor.id().item_kind() == ItemKind::Sort
                        || (descriptor.id().item_kind() == ItemKind::Configuration
                            && descriptor.id().item_name() == configuration_name)
                })
                .cloned()
                .collect();
            krs_compiler::lower_descriptor_bundle(
                &krs_ir::DescriptorBundle::new(descriptors).unwrap(),
            )
            .unwrap()
            .modules()
            .iter()
            .find_map(krs_ir_levels::SemanticModule::configuration)
            .cloned()
            .expect("the selected bundle has one semantic configuration")
        };
        let explicit = lower("ExplicitEquivalentMachine");
        let readable = lower("ReadableEquivalentMachine");

        assert_eq!(explicit.root().name(), readable.root().name());
        assert_eq!(explicit.cells().len(), readable.cells().len());
        for (explicit, readable) in explicit.cells().iter().zip(readable.cells()) {
            assert_eq!(explicit.name(), readable.name());
            assert_eq!(explicit.attributes().len(), readable.attributes().len());
            match (explicit.content(), readable.content()) {
                (
                    krs_ir::FixedCellContent::Term { sort: explicit },
                    krs_ir::FixedCellContent::Term { sort: readable },
                ) => assert_eq!(explicit, readable),
                _ => panic!("equivalent semantic configurations must use leaf cells"),
            }
        }

        assert_eq!(explicit.variables().len(), readable.variables().len());
        for (explicit, readable) in explicit.variables().iter().zip(readable.variables()) {
            assert_eq!(explicit.id(), readable.id());
            assert_eq!(explicit.external_name(), readable.external_name());
            assert_eq!(explicit.sort(), readable.sort());
            assert_eq!(explicit.is_main(), readable.is_main());
        }

        assert_eq!(explicit.initializer().len(), readable.initializer().len());
        for (explicit, readable) in explicit.initializer().iter().zip(readable.initializer()) {
            match (explicit.content(), readable.content()) {
                (
                    krs_ir::FixedInitializerContent::Term { term: explicit },
                    krs_ir::FixedInitializerContent::Term { term: readable },
                ) => assert_semantic_term_equivalent(explicit, readable),
                _ => panic!("equivalent semantic initializers must use leaf terms"),
            }
        }
    }

    fn assert_semantic_term_equivalent(
        explicit: &krs_ir_levels::SemanticTerm,
        readable: &krs_ir_levels::SemanticTerm,
    ) {
        assert_eq!(explicit.sort(), readable.sort());
        match (explicit.kind(), readable.kind()) {
            (
                krs_ir_levels::SemanticTermKind::Variable { variable: explicit },
                krs_ir_levels::SemanticTermKind::Variable { variable: readable },
            ) => assert_eq!(explicit, readable),
            (
                krs_ir_levels::SemanticTermKind::Application {
                    application: explicit_application,
                    arguments: explicit_arguments,
                },
                krs_ir_levels::SemanticTermKind::Application {
                    application: readable_application,
                    arguments: readable_arguments,
                },
            ) => {
                assert_eq!(explicit_application, readable_application);
                assert_eq!(explicit_arguments.len(), readable_arguments.len());
                for (explicit, readable) in explicit_arguments.iter().zip(readable_arguments) {
                    assert_semantic_term_equivalent(explicit, readable);
                }
            }
            (
                krs_ir_levels::SemanticTermKind::Token { value: explicit },
                krs_ir_levels::SemanticTermKind::Token { value: readable },
            ) => assert_eq!(explicit, readable),
            (
                krs_ir_levels::SemanticTermKind::KSequence {
                    item_sort: explicit_sort,
                    items: explicit_items,
                },
                krs_ir_levels::SemanticTermKind::KSequence {
                    item_sort: readable_sort,
                    items: readable_items,
                },
            ) => {
                assert_eq!(explicit_sort, readable_sort);
                assert_eq!(explicit_items.len(), readable_items.len());
                for (explicit, readable) in explicit_items.iter().zip(readable_items) {
                    assert_semantic_term_equivalent(explicit, readable);
                }
            }
            (
                krs_ir_levels::SemanticTermKind::Map(explicit_operands),
                krs_ir_levels::SemanticTermKind::Map(readable_operands),
            ) => {
                assert_eq!(explicit_operands.operation(), readable_operands.operation());
                assert_eq!(
                    explicit_operands.operands().count(),
                    readable_operands.operands().count()
                );
                for (explicit, readable) in explicit_operands
                    .operands()
                    .zip(readable_operands.operands())
                {
                    assert_semantic_term_equivalent(explicit, readable);
                }
            }
            _ => panic!("equivalent semantic terms have different forms"),
        }
    }

    fn assert_semantic_rule_equivalent(
        readable: &krs_ir_levels::SemanticRule,
        explicit: &krs_ir_levels::SemanticRule,
    ) {
        assert_eq!(readable.kind(), explicit.kind());
        for readable_variable in readable.variables() {
            let explicit_variable = explicit
                .variables()
                .iter()
                .find(|candidate| candidate.id() == readable_variable.id())
                .unwrap_or_else(|| {
                    panic!(
                        "explicit equivalent lacks readable binding {:?}",
                        readable_variable.id()
                    )
                });
            assert_eq!(
                readable_variable.sort(),
                explicit_variable.sort(),
                "binding {:?} has different inferred sorts",
                readable_variable.id()
            );
        }
        let (
            krs_ir_levels::RuleBodyRef::Configuration { body: readable, .. },
            krs_ir_levels::RuleBodyRef::Configuration { body: explicit, .. },
        ) = (readable.relational_body(), explicit.relational_body())
        else {
            panic!("equivalent readable and explicit rules must rewrite configurations")
        };
        assert_eq!(readable.configuration(), explicit.configuration());
        assert_eq!(readable.omitted_siblings(), explicit.omitted_siblings());
        assert_eq!(readable.clauses().len(), explicit.clauses().len());
        for (readable, explicit) in readable.clauses().iter().zip(explicit.clauses()) {
            assert_eq!(readable.cell(), explicit.cell());
            assert_semantic_term_equivalent(readable.before(), explicit.before());
            match (readable.after(), explicit.after()) {
                (krs_ir::CellPost::Preserve, krs_ir::CellPost::Preserve) => {}
                (
                    krs_ir::CellPost::Replace { term: readable },
                    krs_ir::CellPost::Replace { term: explicit },
                ) => assert_semantic_term_equivalent(readable, explicit),
                _ => panic!("equivalent cell clauses have different post states"),
            }
            assert!(matches!(
                (readable.frame(), explicit.frame()),
                (
                    krs_ir::CellContentFrame::Exact,
                    krs_ir::CellContentFrame::Exact
                ) | (
                    krs_ir::CellContentFrame::KSequenceTail { .. },
                    krs_ir::CellContentFrame::KSequenceTail { .. }
                ) | (
                    krs_ir::CellContentFrame::MapRemainder { .. },
                    krs_ir::CellContentFrame::MapRemainder { .. }
                )
            ));
        }
    }
}
