#![allow(dead_code, unused_imports, unused_variables)]

use k::builtin::{Bool, Id, Int, Map};
use k::{Cell, KCell, KSequence, Term};
#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait KResult: KItem {}

#[k::sort]
pub trait Expr: KItem {}

#[k::sort]
pub trait Value: Expr + KResult {}

#[k::token(r"[0-9]+")]
pub struct Integer(pub Int);

impl Value for Integer {}

#[k::constructors]
pub enum Boolean { True, False }

impl Value for Boolean {}
#[k::syntax("{lhs} + {rhs}", precedence = 60, assoc = "left")]
#[k::strict(sequence = [lhs, rhs])]
pub struct Add {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

impl Expr for Add {}

#[k::syntax("{lhs} && {rhs}", precedence = 30, assoc = "left")]
#[k::strict(sequence = [lhs])]
pub struct And {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

impl Expr for And {}

#[k::sort]
pub trait Stmt: KItem {}

#[k::syntax("{name} = {value};")]
#[k::strict(sequence = [value])]
pub struct Assign {
    pub name: Id,
    pub value: Term<dyn Expr>,
}

impl Stmt for Assign {}

#[k::syntax("{first}\n{second}", precedence = 10, assoc = "right")]
pub struct Seq {
    pub first: Term<dyn Stmt>,
    pub second: Term<dyn Stmt>,
}

impl Stmt for Seq {}

#[k::configuration]
pub struct Machine {
    pub k: KCell<KSequence>,
    pub env: Cell<Map<Id, Term<dyn Value>>>,
}

impl Machine {
    #[k::init]
    pub fn init(program: Term<dyn Stmt>) -> Self {
        Self {
            k: KCell::new(program),
            env: Cell::new(Map::empty()),
        }
    }
}

#[k::rule(label = "assign")]
fn assign(state: Machine) -> Option<Machine> {
    match state {
        Machine {
            k: k![Assign { name, value }, rest @ ..],
            env: map_cell![env],
        } if k::is_sort::<dyn Value>(&value) => Some(Machine {
            k: k![..rest],
            env: map_cell![env.update(name, value)],
        }),
        _ => None,
    }
}

#[k::rule(label = "and-false")]
fn and_false(term: Term<dyn Expr>) -> Option<Term<dyn Expr>> {
    match term {
        term![And { lhs: Boolean::False, rhs: _ }] => Some(term![Boolean::False]),
        _ => None,
    }
}
