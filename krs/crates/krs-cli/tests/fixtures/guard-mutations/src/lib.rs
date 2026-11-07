//! The definition whose condition flips `tests/kink_flips.rs` generates and judges: a small
//! machine whose `boundary` step is four transitions kept apart by complementary conditions
//! (`boundary_dispatch`/`boundary_step` on `!halted && [!]Dispatches(ime, pending)`,
//! `boundary_wake`/`boundary_halted` on `[!]Requested(pending) && halted`), and no rule ever sets
//! `halted`; an `if`/`else` chain (`VectorOf`); a 4-bit `k::bits!` decode whose `inc` and `dec`
//! arms differ in bit 0; two transitions kept apart by a `k::matches!` test; two transitions that
//! share a `k::matches!` test and are kept apart by `ime` beside it; and a transition whose
//! condition reads a looked-up value.

use k::builtin::{map, Bool, Int, KSequence, Map};
use k::{KItem, KResult, Term};

k::sorts! {
    Cmd: KItem;
}

#[k::constructors(sort = Cmd, result = KResult)]
#[k::precedence((Boundary, Raise, Exec, Vector, Tag, Mark, Peek) > (Seq))]
pub enum CmdSyntax {
    #[k::syntax("{first} ; {rest}")]
    Seq { first: Cmd, rest: Cmd },
    #[k::syntax("boundary")]
    Boundary(),
    #[k::syntax("raise {bits}")]
    Raise { bits: Int },
    #[k::syntax("exec {op}")]
    Exec { op: Int },
    #[k::syntax("vector")]
    Vector(),
    #[k::syntax("tag {next}")]
    Tag { next: Cmd },
    #[k::syntax("mark {next}")]
    Mark { next: Cmd },
    #[k::syntax("peek {a}")]
    Peek { a: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub halted: Bool,
    #[k::cell]
    pub ime: Bool,
    #[k::cell]
    pub pending: Int,
    #[k::cell]
    pub acc: Int,
    #[k::cell]
    pub idx: Map,
    #[k::cell]
    pub mem: Map,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Cmd) -> Self {
        Self {
            k: k::k![pgm],
            halted: false,
            ime: true,
            pending: 0,
            acc: 0,
            idx: map![1 -> 1, 2 -> 2],
            mem: map![1 -> 5, 2 -> 2],
        }
    }
}

/// Whether a pending interrupt is dispatched.
#[k::function(total, internal)]
pub fn Dispatches(ime: Term<Bool>, pending: Term<Int>) -> Term<Bool> {
    ime && pending != 0
}

/// Whether an interrupt is pending.
#[k::function(total, internal)]
pub fn Requested(pending: Term<Int>) -> Term<Bool> {
    pending != 0
}

k::rules! {
    for Machine;
    use CmdSyntax::*;

    seq: { k: [Seq(first, rest), ..] } => { k: [first, rest, ..] };
    raise: { k: [Raise(bits), ..], pending: _ } => { k: [..], pending: bits };
    #[k::requires(!halted && Dispatches(ime, pending))]
    boundary_dispatch: { k: [Boundary(), ..], halted: halted, ime: ime, pending: pending, acc: _ } => { k: [..], pending: 0, acc: 1 };
    #[k::requires(!halted && !Dispatches(ime, pending))]
    boundary_step: { k: [Boundary(), ..], halted: halted, ime: ime, pending: pending, acc: _ } => { k: [..], acc: 2 };
    #[k::requires(Requested(pending) && halted)]
    boundary_wake: { k: [Boundary(), ..], halted: halted, ime: ime, pending: pending, acc: _ } => { k: [..], halted: false, acc: 3 };
    #[k::requires(!Requested(pending) && halted)]
    boundary_halted: { k: [Boundary(), ..], halted: halted, ime: ime, pending: pending, acc: _ } => { k: [..], acc: 4 };
    exec: { k: [Exec(op), ..], acc: _ } => { k: [..], acc: crate::Decode(op) };
    vector: { k: [Vector(), ..], pending: p, acc: _ } => { k: [..], acc: crate::VectorOf(p) };
    #[k::requires(k::matches!(next, Raise { .. }))]
    tag_raise: { k: [Tag(next), ..], acc: _ } => { k: [next, ..], acc: 7 };
    #[k::requires(!k::matches!(next, Raise { .. }))]
    tag_other: { k: [Tag(next), ..], acc: _ } => { k: [..], acc: 8 };
    #[k::requires(k::matches!(next, Raise { .. }) && ime)]
    mark_raise: { k: [Mark(next), ..], ime: ime, acc: _ } => { k: [next, ..], acc: 9 };
    #[k::requires(k::matches!(next, Raise { .. }) && !ime)]
    mark_held: { k: [Mark(next), ..], ime: ime, acc: _ } => { k: [..], acc: 10 };
    #[k::requires(v > 3)]
    peek: { k: [Peek(a), ..], idx: ix, mem: { ix[a] -> v, .. }, acc: _ } => { k: [..], acc: v } where v: Int;
}

/// The interrupt vector of the highest pending request.
#[k::function(total, internal)]
pub fn VectorOf(p: Term<Int>) -> Term<Int> {
    if p >= 4 { 80 } else if p >= 2 { 72 } else if p >= 1 { 64 } else { 0 }
}

/// What an opcode does to its operand.
#[k::function(total, internal)]
pub fn Decode(op: Term<Int>) -> Term<Int>;

k::equations! {
    for Decode;
    decode_inc  : k::bits!("0 yy 0") => y + 1;
    decode_dec  : k::bits!("0 yy 1") => y - 1;
    decode_load : k::bits!("1 yyy")  => y;
    #[k::equation(owise)]
    decode_other: _                  => 0;
}
