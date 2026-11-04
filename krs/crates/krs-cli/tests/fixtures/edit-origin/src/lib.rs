use k::builtin::{Bool, Int, KSequence, Map};
use k::{KItem, Term};

k::sorts! {
    Stmt: KItem;
    Arg: KItem;
    impl Arg for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("go {n}")]
    Go { n: Int },
    #[k::syntax("probe {a}")]
    Probe { a: Arg },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub mem: Map,
    #[k::cell]
    pub acc: Int,
    #[k::cell]
    pub seen: Bool,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self {
            k: k::k![pgm],
            mem: k::builtin::map![1 -> 5],
            acc: 0,
            seen: false,
        }
    }
}

k::rules! {
    for Machine;
    use StmtSyntax::*;

    go: { k: [Go(n), ..], mem: { n -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
    probe: { k: [Probe(a), ..], acc: _, seen: _ } => { k: [..], acc: 1, seen: k::matches!(k::project!(Int, a), 3) };
}

#[k::function(total, internal)]
pub fn Twice(value: Term<Int>) -> Term<Int> {
    value + value
}

#[k::function(total, sort = Int, syntax = "double({value})")]
pub struct Double {
    pub value: Term<Int>,
}

#[k::function(total, sort = Int, syntax = "halve({value})")]
pub struct Halve {
    pub value: Term<Int>,
}

#[k::equation]
fn double_value(k::term![Double(value)]: Term<Int>) -> Term<Int> {
    value * 2
}

#[k::equation]
fn halve_value(k::term![Halve(value)]: Term<Int>) -> Term<Int> {
    value / 2
}
