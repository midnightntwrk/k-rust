use k::builtin::{Int, KSequence, List, Map, Set};
use k::KResult;
use k::Term;

k::sorts! {
    Stmt;
    Arg;
    Value: KResult;
    impl Value for Int;
    impl Arg for Int;
}

#[k::constructors(sort = Arg, result = KResult)]
pub enum ArgSyntax {
    #[k::syntax("pair {a} {b}")]
    Pair { a: Int, b: Int },
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence((Div, Look, Key, Elem, Pick, Flag, Read, Bits, Pop, Stop, Reset, Skip, Proj, Part, Save, Input))]
pub enum StmtSyntax {
    #[k::syntax("div {a}")]
    Div { a: Int },
    #[k::syntax("look {a}")]
    Look { a: Int },
    #[k::syntax("key {a}")]
    Key { a: Int },
    #[k::syntax("elem {a}")]
    Elem { a: Int },
    #[k::syntax("pick {a}")]
    #[k::desugar]
    Pick { a: Int },
    #[k::syntax("flag {b}")]
    Flag { b: k::builtin::Bool },
    #[k::syntax("read {a}")]
    Read { a: Int },
    #[k::syntax("bits {a}")]
    Bits { a: Int },
    #[k::syntax("pop")]
    Pop(),
    #[k::syntax("stop")]
    Stop(),
    #[k::syntax("reset")]
    Reset(),
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("proj {a}")]
    Proj { a: Arg },
    #[k::syntax("part {a}")]
    Part { a: Arg },
    #[k::syntax("save")]
    Save(),
    #[k::syntax("input")]
    Input(),
}

#[k::cell]
pub struct Frame {
    #[k::cell]
    pub pc: Int,
    #[k::cell]
    pub fuel: Int,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub env: Map,
    #[k::cell]
    pub keys: Map,
    #[k::cell]
    pub items: List,
    #[k::cell]
    pub elems: Set,
    #[k::cell]
    pub acc: Value,
    #[k::cell(nested)]
    pub frame: Frame,
    #[k::cell(stream = "stdin")]
    pub input: List,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            env: k::builtin::map![1 -> 5],
            keys: k::builtin::map![1 -> 1],
            items: k::builtin::list::item(7),
            elems: k::builtin::set::item(1),
            acc: 0,
            frame: Frame { pc: 1, fuel: 2 },
            input: k::builtin::list::empty(),
        }
    }
}

#[k::desugar]
fn pick(k::term![StmtSyntax::Pick(a)]: Term<Stmt>) -> Term<Stmt> {
    StmtSyntax::Flag(k::matches!(10 / a, 5))
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    #[k::requires(10 / a > 1)]
    div: { k: [Div(a), ..], acc: _ } => { k: [..], acc: 1 };
    #[k::requires(m[a] > 0)]
    look: { k: [Look(a), ..], env: m, acc: _ } => { k: [..], acc: 1 };
    key: { k: [Key(a), ..], keys: kk, env: { kk[a] -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
    elem: { k: [Elem(a), ..], keys: kk, elems: k::builtin::set::item(kk[a]), acc: _ } => { k: [..], acc: 1 };
    #[k::requires(b)]
    flag: { k: [Flag(b), ..], acc: _ } => { k: [..], acc: 1 };
    pop: { k: [Pop(), ..], items: [_, ..] } => { k: [..], items: [..] };
    stop: { k: [Stop()] } => { k: [] };
    proj: { k: [Proj(a), ..], keys: { k::project!(Int, a) -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
    part: { k: [Part(a), ..], keys: { { let ArgSyntax::Pair { a: _, b } = a; b } -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
    save: { k: [Save(), ..], frame: f @ Frame { pc: 1, .. } } => { k: [..], frame: Frame { fuel: 0, ..f } };
    input: { k: [Input(), ..], input: k::builtin::list::concat(k::builtin::list::item(i), more), acc: _ } => { k: [..], input: more, acc: i } where i: Int;
}

k::rules! {
    for Stmt;
    use StmtSyntax::*;

    read: Read(a) => Skip() where have env[a -> let _];
    bits: Bits(k::bits!("0aaa")) => Read(a);
}

#[k::rule]
pub fn reset(
    k::cells! { k: k::configuration::KCell(StmtSyntax::Reset(), tail @ ..), acc: k::configuration::Cell(_), state @ .. }: Machine,
) -> Machine {
    k::cells! { k: k::configuration::KCell(..tail), acc: k::configuration::Cell(2), ..state }
}

#[k::rule]
pub fn drain(x: Term<k::KItem>, k::term![k::builtin::set::item(x)]: Term<k::KItem>) -> Term<k::KItem> {
    StmtSyntax::Skip()
}

#[k::context_alias(name = operand_eval, here = site)]
fn operand_eval(
    k::cells! { k: k::configuration::KCell(site, tail @ ..), state @ .. }: Machine,
) {
}

#[k::constant]
pub const LIMIT: Int = 9;

#[k::function(total, internal)]
pub fn Clamp(value: Term<Int>) -> Term<Int> {
    if value < 0 { 0 } else { value + LIMIT }
}
